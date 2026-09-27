/*
 * The Boehm-Demers-Weiser GC API implemented on Fil-C's FUGC.
 *
 * Fil-C already garbage collects every allocation, precisely and
 * concurrently, so this library does not collect anything itself: it maps
 * the libgc API onto the Fil-C runtime (<stdfil.h>).  See
 * docs/boehm-on-fugc.md for the design and the semantic differences.
 *
 *   GC_malloc*            zgc_alloc (memory is zeroed, as in libgc)
 *   uncollectable         a strong zexact_ptrtable holds the object
 *   GC_free               zgc_free (later accesses trap)
 *   GC_gcollect           zgc_request_and_wait
 *   finalizers            weak map obj -> sentinel; the sentinel is a
 *                         zgc_finq object that points at obj, so when obj
 *                         dies the sentinel is revived and queued
 *   disappearing links    zweak on the link's object and the target,
 *                         swept whenever a completed GC cycle is observed
 *   GC_HIDE_POINTER       weak zexact_ptrtable (see gc.h under __FILC__)
 *   kinds, mark procs,    accepted and ignored; FUGC scans objects
 *   descriptors, roots    precisely
 */

#define GC_THREADS 1
#define GC_NO_THREAD_REDIRECTS 1
#define GC_I_HIDE_POINTERS 1

#include "gc/gc.h"
#include "gc/gc_mark.h"
#include "gc/gc_typed.h"
#include "gc/gc_gcj.h"
#include "gc/gc_disclaim.h"
#include "gc/gc_inline.h"
#include "gc/javaxfc.h"

#include <stdfil.h>

#pragma clang diagnostic ignored "-Wdeprecated-declarations"

#include <dlfcn.h>
#include <pthread.h>
#include <signal.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <wchar.h>

/* ------------------------------------------------------------------ */
/* Deprecated public variables.  Clients may read or write these      */
/* directly, so the library consults them rather than private copies. */

GC_word GC_gc_no = 0;
int GC_parallel = 0;
static void *GC_CALLBACK default_oom_fn(size_t n)
{
    (void)n;
    return NULL;
}
GC_oom_func GC_oom_fn = default_oom_fn;
GC_on_heap_resize_proc GC_on_heap_resize = 0;
int GC_find_leak = 0;
int GC_all_interior_pointers = 1;
int GC_finalize_on_demand = 0;
int GC_java_finalization = 1;
GC_finalizer_notifier_proc GC_finalizer_notifier = 0;
int GC_dont_expand = 0;
int GC_use_entire_heap = 0;
int GC_full_freq = 19;
GC_word GC_non_gc_bytes = 0;
int GC_no_dls = 0;
GC_word GC_free_space_divisor = 3;
GC_word GC_max_retries = 0;
char *GC_stackbottom = 0;
int GC_dont_precollect = 0;
unsigned long GC_time_limit = GC_TIME_UNLIMITED;
int GC_dont_gc = 0;
void *GC_least_plausible_heap_addr = 0;
void *GC_greatest_plausible_heap_addr = 0;
static void GC_CALLBACK default_on_abort(const char *msg)
{
    if (msg)
        fprintf(stderr, "%s\n", msg);
}
GC_abort_func GC_on_abort = default_on_abort;
int GC_gcj_kind = 0;
int GC_gcj_debug_kind = 0;
size_t GC_debug_header_size = 0;
static void GC_CALLBACK default_print_proc(void *p)
{
    (void)p;
}
static void GC_CALLBACK default_same_obj_print_proc(void *p, void *q)
{
    (void)p;
    (void)q;
}
void (GC_CALLBACK *GC_same_obj_print_proc)(void *, void *) =
    default_same_obj_print_proc;
void (GC_CALLBACK *GC_is_valid_displacement_print_proc)(void *) =
    default_print_proc;
void (GC_CALLBACK *GC_is_visible_print_proc)(void *) = default_print_proc;

/* Internal free-list pointers that libgc happens to export.  Clients
   that peek at them find empty lists and fall back to the API. */
#define FUGC_TINY_FREELISTS 129
static void *empty_freelists[4][FUGC_TINY_FREELISTS];
void **GC_objfreelist_ptr = empty_freelists[0];
void **GC_aobjfreelist_ptr = empty_freelists[1];
void **GC_uobjfreelist_ptr = empty_freelists[2];
void **GC_auobjfreelist_ptr = empty_freelists[3];

/* ------------------------------------------------------------------ */
/* Settings that FUGC has no equivalent for.                          */

static GC_on_collection_event_proc on_collection_event;
static GC_on_thread_event_proc on_thread_event;
static GC_start_callback_proc start_callback;
static GC_push_other_roots_proc push_other_roots;
static GC_stop_func stop_func;
static GC_warn_proc warn_proc;
static GC_toggleref_func toggleref_func;
static GC_await_finalize_proc await_finalize_proc;
static GC_sp_corrector_proc sp_corrector;
static int markers_count;
static int pages_executable;
static size_t min_bytes_allocd = 1;
static int gc_rate = 10;
static int max_prior_attempts = 1;
static int manual_vdb_allowed = 1;
static int force_unmap_on_gcollect;
static GC_word allocd_bytes_per_finalizer = 10000;
static struct GC_timeval_s time_limit_tv = {GC_TIME_UNLIMITED, 0};
static int suspend_signal = SIGPWR;
static int thr_restart_signal = SIGXCPU;
static atomic_int disable_count;
static atomic_int init_called;
static int log_fd = 2;

/* ------------------------------------------------------------------ */
/* Statistics.  FUGC does not export heap statistics, so the heap size */
/* is the resident set size, sampled when a GC cycle is observed.     */

static atomic_size_t bytes_allocd_since_gc;
static atomic_size_t total_bytes_allocd;
static atomic_size_t expl_freed_since_gc;
static atomic_size_t heap_size_estimate;

static size_t resident_bytes(void)
{
    FILE *f = fopen("/proc/self/statm", "r");
    unsigned long size = 0, resident = 0;
    if (f) {
        if (fscanf(f, "%lu %lu", &size, &resident) != 2)
            resident = 0;
        fclose(f);
    }
    return (size_t)resident * (size_t)sysconf(_SC_PAGESIZE);
}

static void count_alloc(size_t n)
{
    atomic_fetch_add_explicit(&bytes_allocd_since_gc, n, memory_order_relaxed);
    atomic_fetch_add_explicit(&total_bytes_allocd, n, memory_order_relaxed);
}

/* ------------------------------------------------------------------ */
/* Global state.                                                      */

/* The client-visible allocation lock (GC_alloc_lock and
   GC_call_with_alloc_lock).  Never held by the library itself, so that
   clients may call GC_REVEAL_POINTER and friends while holding it. */
static pthread_mutex_t alloc_lock = PTHREAD_MUTEX_INITIALIZER;

/* Protects the tables below. */
static pthread_mutex_t state_lock = PTHREAD_MUTEX_INITIALIZER;

static pthread_once_t init_once = PTHREAD_ONCE_INIT;
static zgc_finq *finq;
static zweak_map *finalizers;       /* obj -> struct sentinel */
static zexact_ptrtable *uncollectable_keep;
static zweak_map *uncollectable_set; /* obj -> &uncollectable_marker */
static char uncollectable_marker;
static zexact_ptrtable *hidden;     /* GC_HIDE_POINTER encodings */
static atomic_int hidden_used;
static zweak_map *mark_bits;        /* obj -> struct mark_bit */
static atomic_size_t finalizers_registered;

static void init_state(void)
{
    finq = zgc_finq_new();
    finalizers = zweak_map_new();
    uncollectable_keep = zexact_ptrtable_new();
    uncollectable_set = zweak_map_new();
    hidden = zexact_ptrtable_new_weak();
    mark_bits = zweak_map_new();
    heap_size_estimate = resident_bytes();
}

static inline void ensure_init(void)
{
    pthread_once(&init_once, init_state);
}

static void cycle_hook(void);

/* ------------------------------------------------------------------ */
/* Allocation.                                                        */

/* Fil-C panics on allocations it cannot satisfy; libgc reports them to
   the OOM function, which usually returns NULL.  Do that at least for
   sizes that no machine can provide. */
#define FUGC_MAX_ALLOC ((size_t)1 << 46)

static void *too_big(size_t n)
{
    GC_oom_func f = GC_oom_fn;
    return f ? f(n) : NULL;
}

static void *alloc_normal(size_t n)
{
    if (n > FUGC_MAX_ALLOC)
        return too_big(n);
    cycle_hook();
    void *p = zgc_alloc(n ? n : 1);
    count_alloc(n);
    return p;
}

static void make_uncollectable(void *p)
{
    ensure_init();
    zexact_ptrtable_encode(uncollectable_keep, p);
    zweak_map_set(uncollectable_set, p, &uncollectable_marker);
}

static int is_uncollectable(void *p)
{
    ensure_init();
    return zweak_map_get(uncollectable_set, p) == &uncollectable_marker;
}

static void *alloc_uncollectable(size_t n)
{
    void *p = alloc_normal(n);
    make_uncollectable(p);
    return p;
}

GC_API void *GC_CALL GC_malloc(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_malloc_atomic(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_malloc_ignore_off_page(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_malloc_atomic_ignore_off_page(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_malloc_stubborn(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_malloc_uncollectable(size_t n) { return alloc_uncollectable(n); }
GC_API void *GC_CALL GC_malloc_atomic_uncollectable(size_t n) { return alloc_uncollectable(n); }

GC_API void *GC_CALL GC_memalign(size_t align, size_t n)
{
    cycle_hook();
    if (align <= 16 || n > FUGC_MAX_ALLOC)
        return alloc_normal(n);
    void *p = zgc_aligned_alloc(align, n ? n : 1);
    count_alloc(n);
    return p;
}

GC_API int GC_CALL GC_posix_memalign(void **memptr, size_t align, size_t n)
{
    if (align < sizeof(void *) || (align & (align - 1)) != 0)
        return 22; /* EINVAL */
    *memptr = GC_memalign(align, n);
    return 0;
}

GC_API char *GC_CALL GC_strdup(const char *s)
{
    if (!s)
        return NULL;
    size_t n = strlen(s) + 1;
    char *p = alloc_normal(n);
    memcpy(p, s, n);
    return p;
}

GC_API char *GC_CALL GC_strndup(const char *s, size_t size)
{
    size_t n = strnlen(s, size);
    char *p = alloc_normal(n + 1);
    memcpy(p, s, n);
    p[n] = 0;
    return p;
}

static wchar_t *wcsdup_gc(const wchar_t *s)
{
    size_t n = (wcslen(s) + 1) * sizeof(wchar_t);
    wchar_t *p = alloc_normal(n);
    memcpy(p, s, n);
    return p;
}

static void unregister_finalizer_of(void *p);

GC_API void GC_CALL GC_free(void *p)
{
    if (!p || !zhasvalidcap(p) || p != zgetlower(p))
        return;
    if (atomic_load_explicit(&finalizers_registered, memory_order_relaxed))
        unregister_finalizer_of(p);
    atomic_fetch_add_explicit(&expl_freed_since_gc,
                              (char *)zgetupper(p) - (char *)p,
                              memory_order_relaxed);
    /* Freeing also drops the object from uncollectable_keep. */
    zgc_free(p);
}

GC_API void *GC_CALL GC_realloc(void *p, size_t n)
{
    if (!p)
        return GC_malloc(n);
    if (n == 0) {
        GC_free(p);
        return NULL;
    }
    if (n > FUGC_MAX_ALLOC)
        return too_big(n);
    int uncollectable = is_uncollectable(p);
    cycle_hook();
    void *q = zgc_realloc(p, n);
    count_alloc(n);
    if (uncollectable)
        make_uncollectable(q);
    return q;
}

GC_API void *GC_CALL GC_base(void *p)
{
    if (!p || !zhasvalidcap(p))
        return NULL;
    return zgetlower(p);
}

GC_API int GC_CALL GC_is_heap_ptr(const void *p)
{
    return GC_base((void *)p) != NULL;
}

GC_API size_t GC_CALL GC_size(const void *p)
{
    if (!p || !zhasvalidcap((void *)p))
        return 0;
    return (char *)zgetupper((void *)p) - (char *)zgetlower((void *)p);
}

GC_API void GC_CALL GC_end_stubborn_change(const void *p) { (void)p; }
GC_API void GC_CALL GC_change_stubborn(const void *p) { (void)p; }
GC_API void GC_CALL GC_ptr_store_and_dirty(void *p, const void *q)
{
    *(const void **)p = q;
}
GC_API void GC_CALL GC_debug_ptr_store_and_dirty(void *p, const void *q)
{
    *(const void **)p = q;
}

/* Kinds.  Kind 0 is pointer-free, 1 normal, 2 uncollectable, 3 atomic
   uncollectable, as in libgc; new kinds count up from there. */
#define FUGC_UNCOLLECTABLE 2
#define FUGC_AUNCOLLECTABLE 3
static atomic_uint next_kind = 6;
static atomic_uint next_proc = GC_RESERVED_MARK_PROCS;

GC_API void **GC_CALL GC_new_free_list_inner(void)
{
    return zgc_alloc(FUGC_TINY_FREELISTS * sizeof(void *));
}
GC_API void **GC_CALL GC_new_free_list(void) { return GC_new_free_list_inner(); }

GC_API unsigned GC_CALL GC_new_kind_inner(void **fl, GC_word descr, int adjust,
                                          int clear)
{
    (void)fl;
    (void)descr;
    (void)adjust;
    (void)clear;
    return atomic_fetch_add(&next_kind, 1);
}
GC_API unsigned GC_CALL GC_new_kind(void **fl, GC_word descr, int adjust,
                                    int clear)
{
    return GC_new_kind_inner(fl, descr, adjust, clear);
}

GC_API unsigned GC_CALL GC_new_proc_inner(GC_mark_proc proc)
{
    (void)proc;
    unsigned i = atomic_fetch_add(&next_proc, 1);
    return i % GC_MAX_MARK_PROCS;
}
GC_API unsigned GC_CALL GC_new_proc(GC_mark_proc proc) { return GC_new_proc_inner(proc); }

static GC_disclaim_proc disclaim_procs[64];
static void GC_CALLBACK run_disclaim(void *obj, void *cd);

GC_API void *GC_CALL GC_generic_malloc(size_t n, int k)
{
    if (k == FUGC_UNCOLLECTABLE || k == FUGC_AUNCOLLECTABLE)
        return alloc_uncollectable(n);
    void *p = alloc_normal(n);
    if (k >= 0 && k < 64 && disclaim_procs[k])
        GC_register_finalizer_no_order(p, run_disclaim, (void *)disclaim_procs[k],
                                       NULL, NULL);
    return p;
}
GC_API void *GC_CALL GC_generic_malloc_ignore_off_page(size_t n, int k)
{
    return GC_generic_malloc(n, k);
}
GC_API void *GC_CALL GC_generic_malloc_uncollectable(size_t n, int k)
{
    (void)k;
    return alloc_uncollectable(n);
}
GC_API void *GC_CALL GC_generic_or_special_malloc(size_t n, int k)
{
    return GC_generic_malloc(n, k);
}
GC_API void *GC_CALL GC_debug_generic_or_special_malloc(size_t n, int k,
                                                        GC_EXTRA_PARAMS)
{
    return GC_generic_malloc(n, k);
}
GC_API void *GC_CALL GC_malloc_kind(size_t n, int k) { return GC_generic_malloc(n, k); }
#undef GC_malloc_kind_global
GC_API void *GC_CALL GC_malloc_kind_global(size_t n, int k)
{
    return GC_generic_malloc(n, k);
}

/* A list of separately allocated objects linked through their first
   word, as GC_NEXT expects. */
GC_API void GC_CALL GC_generic_malloc_many(size_t n, int k, void **result)
{
    size_t count = n >= 1024 ? 1 : 1024 / (n ? n : 1);
    if (count > 64)
        count = 64;
    void *head = NULL;
    for (size_t i = 0; i < count; i++) {
        void *p = GC_generic_malloc(n < sizeof(void *) ? sizeof(void *) : n, k);
        *(void **)p = head;
        head = p;
    }
    *result = head;
}

GC_API void *GC_CALL GC_malloc_many(size_t n)
{
    void *result;
    GC_generic_malloc_many(n, GC_I_NORMAL, &result);
    return result;
}

GC_API int GC_CALL GC_get_kind_and_size(const void *p, size_t *psize)
{
    if (psize)
        *psize = GC_size(p);
    return is_uncollectable((void *)p) ? FUGC_UNCOLLECTABLE : GC_I_NORMAL;
}

GC_API size_t GC_CALL GC_get_size_map_at(int i)
{
    return i <= 0 ? 16 : ((size_t)i + 15) & ~(size_t)15;
}

GC_API void GC_CALL GC_incr_bytes_allocd(size_t n) { count_alloc(n); }
GC_API void GC_CALL GC_incr_bytes_freed(size_t n)
{
    atomic_fetch_add(&expl_freed_since_gc, n);
}

/* Typed allocation: FUGC knows where the pointers are already. */
GC_API GC_descr GC_CALL GC_make_descriptor(const GC_word *bm, size_t len)
{
    (void)bm;
    (void)len;
    return 0;
}
GC_API void *GC_CALL GC_malloc_explicitly_typed(size_t n, GC_descr d)
{
    (void)d;
    return alloc_normal(n);
}
GC_API void *GC_CALL GC_malloc_explicitly_typed_ignore_off_page(size_t n,
                                                                GC_descr d)
{
    (void)d;
    return alloc_normal(n);
}
GC_API void *GC_CALL GC_calloc_explicitly_typed(size_t nelements,
                                                size_t element_size, GC_descr d)
{
    (void)d;
    if (element_size && nelements > (size_t)-1 / element_size)
        return too_big((size_t)-1);
    return alloc_normal(nelements * element_size);
}

/* gcj-style objects: the first word is the vtable pointer. */
GC_API void GC_CALL GC_init_gcj_malloc(int mp_index, void *mp)
{
    (void)mp_index;
    (void)mp;
    GC_init();
}
GC_API void *GC_CALL GC_gcj_malloc(size_t n, void *vtable)
{
    void *p = alloc_normal(n < sizeof(void *) ? sizeof(void *) : n);
    *(void **)p = vtable;
    return p;
}
GC_API void *GC_CALL GC_gcj_malloc_ignore_off_page(size_t n, void *vtable)
{
    return GC_gcj_malloc(n, vtable);
}
GC_API void *GC_CALL GC_debug_gcj_malloc(size_t n, void *vtable, GC_EXTRA_PARAMS)
{
    return GC_gcj_malloc(n, vtable);
}

/* Debug allocation: no headers, just the plain allocator. */
GC_API void *GC_CALL GC_debug_malloc(size_t n, GC_EXTRA_PARAMS) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_malloc_atomic(size_t n, GC_EXTRA_PARAMS) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_malloc_ignore_off_page(size_t n, GC_EXTRA_PARAMS) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_malloc_atomic_ignore_off_page(size_t n, GC_EXTRA_PARAMS) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_malloc_stubborn(size_t n, GC_EXTRA_PARAMS) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_malloc_uncollectable(size_t n, GC_EXTRA_PARAMS) { return alloc_uncollectable(n); }
GC_API void *GC_CALL GC_debug_malloc_atomic_uncollectable(size_t n, GC_EXTRA_PARAMS) { return alloc_uncollectable(n); }
GC_API char *GC_CALL GC_debug_strdup(const char *str, GC_EXTRA_PARAMS) { return GC_strdup(str); }
GC_API char *GC_CALL GC_debug_strndup(const char *str, size_t n, GC_EXTRA_PARAMS) { return GC_strndup(str, n); }
GC_API wchar_t *GC_CALL GC_debug_wcsdup(const wchar_t *str, GC_EXTRA_PARAMS) { return wcsdup_gc(str); }
GC_API void GC_CALL GC_debug_free(void *p) { GC_free(p); }
GC_API void *GC_CALL GC_debug_realloc(void *p, size_t n, GC_EXTRA_PARAMS) { return GC_realloc(p, n); }
GC_API void GC_CALL GC_debug_change_stubborn(const void *p) { (void)p; }
GC_API void GC_CALL GC_debug_end_stubborn_change(const void *p) { (void)p; }
GC_API void *GC_CALL GC_debug_malloc_replacement(size_t n) { return alloc_normal(n); }
GC_API void *GC_CALL GC_debug_realloc_replacement(void *p, size_t n) { return GC_realloc(p, n); }
GC_API size_t GC_CALL GC_get_debug_header_size(void) { return 0; }
GC_API void GC_CALL GC_debug_register_displacement(size_t n) { (void)n; }
GC_API void GC_CALL GC_register_displacement(size_t n) { (void)n; }

/* ------------------------------------------------------------------ */
/* Hidden pointers.  gc.h maps GC_HIDE_POINTER/GC_REVEAL_POINTER here  */
/* under Fil-C: ~(uintptr_t)p loses p's capability, but a weak exact  */
/* ptrtable encodes a pointer as its address and gives the capability */
/* back on decode for as long as the object lives.                    */

GC_API GC_hidden_pointer GC_CALL GC_fugc_hide_pointer(const void *p)
{
    if (!p)
        return ~(GC_hidden_pointer)0;
    ensure_init();
    atomic_store_explicit(&hidden_used, 1, memory_order_relaxed);
    return ~(GC_hidden_pointer)zexact_ptrtable_encode(hidden, (void *)p);
}

static void drain_finq(void);

GC_API void *GC_CALL GC_fugc_reveal_pointer(GC_hidden_pointer h)
{
    if (h == ~(GC_hidden_pointer)0)
        return NULL;
    ensure_init();
    void *p = zexact_ptrtable_decode(hidden, (size_t)~h);
    if (zhasvalidcap(p) ||
        !atomic_load_explicit(&finalizers_registered, memory_order_relaxed))
        return p;
    /* FUGC drops weak entries before it revives finalizable objects, but
       libgc keeps hidden pointers to such objects valid until they are
       reclaimed.  If a cycle is running, wait for it to queue what it
       revived, and hide those objects again (drain_finq), then retry. */
    zgc_cycle_number requested = zgc_requested_cycle();
    if (requested > zgc_completed_cycle())
        zgc_wait(requested);
    pthread_mutex_lock(&state_lock);
    drain_finq();
    pthread_mutex_unlock(&state_lock);
    return zexact_ptrtable_decode(hidden, (size_t)~h);
}

/* ------------------------------------------------------------------ */
/* Finalization.                                                      */

struct sentinel {
    void *obj; /* Strong: the sentinel is only reachable through the weak
                  map entry keyed by obj, so this does not keep obj alive,
                  but it does revive obj along with the sentinel. */
    GC_finalization_proc fn;
    void *cd;
    struct sentinel *next; /* pending list */
    zgc_cycle_number dead_cycle; /* when it was found unreachable */
};

static struct sentinel *pending_head, *pending_tail;
static size_t pending_count;
static _Thread_local int running_finalizers;
/* The object whose finalizer is running on this thread, for GC_is_marked. */
static _Thread_local void *finalizing_obj;
static _Thread_local zgc_cycle_number finalizing_dead_cycle;

static void register_finalizer(void *obj, GC_finalization_proc fn, void *cd,
                               GC_finalization_proc *ofn, void **ocd)
{
    ensure_init();
    if (!obj || !zhasvalidcap(obj)) {
        if (ofn)
            *ofn = 0;
        if (ocd)
            *ocd = 0;
        return;
    }
    pthread_mutex_lock(&state_lock);
    struct sentinel *old = zweak_map_get(finalizers, obj);
    if (ofn)
        *ofn = old ? old->fn : 0;
    if (ocd)
        *ocd = old ? old->cd : 0;
    if (old) {
        old->fn = 0;
        old->obj = NULL;
        atomic_fetch_sub(&finalizers_registered, 1);
    }
    if (fn) {
        struct sentinel *s = zgc_finq_alloc(finq, sizeof(struct sentinel));
        s->obj = obj;
        s->fn = fn;
        s->cd = cd;
        zweak_map_set(finalizers, obj, s);
        atomic_fetch_add(&finalizers_registered, 1);
    } else if (old) {
        zweak_map_set(finalizers, obj, NULL);
    }
    pthread_mutex_unlock(&state_lock);
}

static void unregister_finalizer_of(void *p)
{
    pthread_mutex_lock(&state_lock);
    struct sentinel *old = zweak_map_get(finalizers, p);
    if (old) {
        old->fn = 0;
        old->obj = NULL;
        zweak_map_set(finalizers, p, NULL);
        atomic_fetch_sub(&finalizers_registered, 1);
    }
    pthread_mutex_unlock(&state_lock);
}

GC_API void GC_CALL GC_register_finalizer(void *obj, GC_finalization_proc fn,
                                          void *cd, GC_finalization_proc *ofn,
                                          void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_register_finalizer_ignore_self(void *obj,
                                                      GC_finalization_proc fn,
                                                      void *cd,
                                                      GC_finalization_proc *ofn,
                                                      void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_register_finalizer_no_order(void *obj,
                                                   GC_finalization_proc fn,
                                                   void *cd,
                                                   GC_finalization_proc *ofn,
                                                   void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_register_finalizer_unreachable(void *obj,
                                                      GC_finalization_proc fn,
                                                      void *cd,
                                                      GC_finalization_proc *ofn,
                                                      void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_debug_register_finalizer(void *obj,
                                                GC_finalization_proc fn,
                                                void *cd,
                                                GC_finalization_proc *ofn,
                                                void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_debug_register_finalizer_ignore_self(
    void *obj, GC_finalization_proc fn, void *cd, GC_finalization_proc *ofn,
    void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_debug_register_finalizer_no_order(
    void *obj, GC_finalization_proc fn, void *cd, GC_finalization_proc *ofn,
    void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}
GC_API void GC_CALL GC_debug_register_finalizer_unreachable(
    void *obj, GC_finalization_proc fn, void *cd, GC_finalization_proc *ofn,
    void **ocd)
{
    register_finalizer(obj, fn, cd, ofn, ocd);
}

/* Moves sentinels that FUGC queued to the pending list.  state_lock. */
static void drain_finq(void)
{
    struct sentinel *s;
    while ((s = zgc_finq_poll(finq))) {
        if (!s->fn)
            continue; /* unregistered after it was queued */
        if (zweak_map_get(finalizers, s->obj) == s)
            zweak_map_set(finalizers, s->obj, NULL);
        atomic_fetch_sub(&finalizers_registered, 1);
        if (atomic_load_explicit(&hidden_used, memory_order_relaxed))
            zexact_ptrtable_encode(hidden, s->obj);
        s->dead_cycle = zgc_completed_cycle();
        s->next = NULL;
        if (pending_tail)
            pending_tail->next = s;
        else
            pending_head = s;
        pending_tail = s;
        pending_count++;
    }
}

static struct sentinel *pop_pending(void)
{
    pthread_mutex_lock(&state_lock);
    struct sentinel *s = pending_head;
    if (s) {
        pending_head = s->next;
        if (!pending_head)
            pending_tail = NULL;
        pending_count--;
    }
    pthread_mutex_unlock(&state_lock);
    return s;
}

GC_API int GC_CALL GC_invoke_finalizers(void)
{
    int count = 0;
    ensure_init();
    pthread_mutex_lock(&state_lock);
    drain_finq();
    pthread_mutex_unlock(&state_lock);
    running_finalizers++;
    struct sentinel *s;
    while ((s = pop_pending())) {
        GC_finalization_proc fn = s->fn;
        void *obj = s->obj;
        s->fn = 0;
        s->obj = NULL;
        if (fn) {
            if (await_finalize_proc)
                await_finalize_proc(obj);
            void *saved_obj = finalizing_obj;
            zgc_cycle_number saved_cycle = finalizing_dead_cycle;
            finalizing_obj = obj;
            finalizing_dead_cycle = s->dead_cycle;
            fn(obj, s->cd);
            finalizing_obj = saved_obj;
            finalizing_dead_cycle = saved_cycle;
            count++;
        }
    }
    running_finalizers--;
    return count;
}

GC_API int GC_CALL GC_should_invoke_finalizers(void)
{
    ensure_init();
    pthread_mutex_lock(&state_lock);
    drain_finq();
    int result = pending_head != NULL;
    pthread_mutex_unlock(&state_lock);
    return result;
}

/* Runs every registered finalizer, reachable or not (javaxfc.h). */
GC_API void GC_CALL GC_finalize_all(void)
{
    ensure_init();
    for (;;) {
        void *obj = NULL;
        struct sentinel *s = NULL;
        pthread_mutex_lock(&state_lock);
        zweak_map_iter *it = zweak_map_get_iter(finalizers);
        while (zweak_map_iter_next(it)) {
            s = zweak_map_iter_value(it);
            obj = zweak_map_iter_key(it);
            if (s && s->fn)
                break;
            s = NULL;
        }
        if (s) {
            zweak_map_set(finalizers, obj, NULL);
            atomic_fetch_sub(&finalizers_registered, 1);
        }
        pthread_mutex_unlock(&state_lock);
        if (!s)
            break;
        GC_finalization_proc fn = s->fn;
        s->fn = 0;
        s->obj = NULL;
        fn(obj, s->cd);
    }
    GC_invoke_finalizers();
}

/* A disclaim procedure that returns nonzero keeps the object; it is
   asked again the next time the object is found unreachable. */
static void GC_CALLBACK run_disclaim(void *obj, void *cd)
{
    GC_disclaim_proc proc = (GC_disclaim_proc)cd;
    if (proc(obj)) {
        zweak_map_set(mark_bits, obj, NULL);
        register_finalizer(obj, run_disclaim, cd, NULL, NULL);
    }
}

GC_API void GC_CALL GC_register_disclaim_proc(int kind, GC_disclaim_proc proc,
                                              int mark_unconditionally)
{
    (void)mark_unconditionally;
    if (kind >= 0 && kind < 64)
        disclaim_procs[kind] = proc;
}

/* GC_finalized_malloc: the first word holds the closure (with its low
   bit set, as in libgc) and the client gets the address after it. */
static void GC_CALLBACK run_finalizer_closure(void *base, void *cd)
{
    (void)cd;
    const struct GC_finalizer_closure *fc =
        (const struct GC_finalizer_closure *)
            zandptr(((void **)base)[0], ~(unsigned long)1);
    if (fc && fc->proc)
        fc->proc((GC_word *)base + 1, fc->cd);
}

GC_API void GC_CALL GC_init_finalized_malloc(void) { GC_init(); }

GC_API void *GC_CALL GC_finalized_malloc(size_t n,
                                         const struct GC_finalizer_closure *fc)
{
    void **base = alloc_normal(n + sizeof(void *));
    base[0] = zorptr((void *)fc, 1);
    register_finalizer(base, run_finalizer_closure, NULL, NULL, NULL);
    return base + 1;
}

/* Toggle-refs: kept strongly; the callback is never consulted. */
GC_API void GC_CALL GC_set_toggleref_func(GC_toggleref_func f) { toggleref_func = f; }
GC_API GC_toggleref_func GC_CALL GC_get_toggleref_func(void) { return toggleref_func; }
GC_API int GC_CALL GC_toggleref_add(void *obj, int is_strong_ref)
{
    (void)is_strong_ref;
    make_uncollectable(obj);
    return GC_SUCCESS;
}

GC_API void GC_CALL GC_set_await_finalize_proc(GC_await_finalize_proc f) { await_finalize_proc = f; }
GC_API GC_await_finalize_proc GC_CALL GC_get_await_finalize_proc(void) { return await_finalize_proc; }

/* ------------------------------------------------------------------ */
/* Disappearing links.                                                */

struct link_entry {
    GC_word key;    /* address of the link */
    zweak *link;    /* weak: the link's containing object may die */
    zweak *target;
    struct link_entry *next;
};

struct link_table {
    struct link_entry **buckets;
    size_t nbuckets;
    size_t count;
};

static struct link_table short_links, long_links;

static size_t link_hash(struct link_table *t, GC_word key)
{
    return (size_t)((key >> 3) * 0x9E3779B97F4A7C15ull >> 20) & (t->nbuckets - 1);
}

static void link_table_grow(struct link_table *t)
{
    size_t n = t->nbuckets ? t->nbuckets * 2 : 64;
    struct link_entry **b = zgc_alloc(n * sizeof(*b));
    for (size_t i = 0; i < t->nbuckets; i++) {
        struct link_entry *e = t->buckets[i];
        while (e) {
            struct link_entry *next = e->next;
            size_t h = (size_t)((e->key >> 3) * 0x9E3779B97F4A7C15ull >> 20) & (n - 1);
            e->next = b[h];
            b[h] = e;
            e = next;
        }
    }
    t->buckets = b;
    t->nbuckets = n;
}

/* Finds the live entry for link, dropping a stale one (whose link
   object died and whose address was reused) on the way.  state_lock. */
static struct link_entry **link_find(struct link_table *t, void **link)
{
    if (!t->nbuckets)
        return NULL;
    GC_word key = (GC_word)link;
    struct link_entry **pe = &t->buckets[link_hash(t, key)];
    while (*pe) {
        struct link_entry *e = *pe;
        if (e->key == key) {
            if (zweak_get(e->link) == (void *)link)
                return pe;
            *pe = e->next;
            t->count--;
            continue;
        }
        pe = &e->next;
    }
    return NULL;
}

static int link_register(struct link_table *t, void **link, const void *obj)
{
    if (((GC_word)link & (sizeof(void *) - 1)) != 0)
        return GC_UNIMPLEMENTED;
    ensure_init();
    pthread_mutex_lock(&state_lock);
    if (link_find(t, link)) {
        pthread_mutex_unlock(&state_lock);
        return GC_DUPLICATE;
    }
    if (t->count >= t->nbuckets)
        link_table_grow(t);
    struct link_entry *e = zgc_alloc(sizeof(*e));
    e->key = (GC_word)link;
    e->link = zweak_new(link);
    e->target = zweak_new((void *)obj);
    size_t h = link_hash(t, e->key);
    e->next = t->buckets[h];
    t->buckets[h] = e;
    t->count++;
    pthread_mutex_unlock(&state_lock);
    return GC_SUCCESS;
}

static int link_unregister(struct link_table *t, void **link)
{
    int found = 0;
    pthread_mutex_lock(&state_lock);
    struct link_entry **pe = link_find(t, link);
    if (pe) {
        *pe = (*pe)->next;
        t->count--;
        found = 1;
    }
    pthread_mutex_unlock(&state_lock);
    return found;
}

static int link_move(struct link_table *t, void **link, void **new_link)
{
    if (((GC_word)new_link & (sizeof(void *) - 1)) != 0)
        return GC_UNIMPLEMENTED;
    pthread_mutex_lock(&state_lock);
    struct link_entry **pe = link_find(t, link);
    if (!pe) {
        pthread_mutex_unlock(&state_lock);
        return GC_NOT_FOUND;
    }
    if (link == new_link) {
        pthread_mutex_unlock(&state_lock);
        return GC_SUCCESS;
    }
    if (link_find(t, new_link)) {
        pthread_mutex_unlock(&state_lock);
        return GC_DUPLICATE;
    }
    pe = link_find(t, link);
    struct link_entry *e = *pe;
    *pe = e->next;
    e->key = (GC_word)new_link;
    e->link = zweak_new(new_link);
    size_t h = link_hash(t, e->key);
    e->next = t->buckets[h];
    t->buckets[h] = e;
    pthread_mutex_unlock(&state_lock);
    return GC_SUCCESS;
}

/* Clears links whose targets died.  state_lock. */
static void link_sweep(struct link_table *t)
{
    for (size_t i = 0; i < t->nbuckets; i++) {
        struct link_entry **pe = &t->buckets[i];
        while (*pe) {
            struct link_entry *e = *pe;
            void **link = zweak_get(e->link);
            if (!link) {
                *pe = e->next;
                t->count--;
                continue;
            }
            if (!zweak_get(e->target)) {
                *link = NULL;
                *pe = e->next;
                t->count--;
                continue;
            }
            pe = &e->next;
        }
    }
}

GC_API int GC_CALL GC_general_register_disappearing_link(void **link,
                                                         const void *obj)
{
    return link_register(&short_links, link, obj);
}
GC_API int GC_CALL GC_register_disappearing_link(void **link)
{
    return link_register(&short_links, link, GC_base(link));
}
GC_API int GC_CALL GC_unregister_disappearing_link(void **link)
{
    return link_unregister(&short_links, link);
}
GC_API int GC_CALL GC_move_disappearing_link(void **link, void **new_link)
{
    return link_move(&short_links, link, new_link);
}
/* Long links are cleared when the target dies, like short ones: FUGC
   has no notion of objects that are only reachable from finalizers. */
GC_API int GC_CALL GC_register_long_link(void **link, const void *obj)
{
    return link_register(&long_links, link, obj);
}
GC_API int GC_CALL GC_unregister_long_link(void **link)
{
    return link_unregister(&long_links, link);
}
GC_API int GC_CALL GC_move_long_link(void **link, void **new_link)
{
    return link_move(&long_links, link, new_link);
}

/* ------------------------------------------------------------------ */
/* Reacting to completed GC cycles.  FUGC collects on its own thread; */
/* the client sees the effects (cleared links, finalizers, gc_no) the */
/* next time it allocates or calls into the library, as with libgc.   */

static atomic_ullong seen_cycle;

static void process_cycle(zgc_cycle_number c)
{
    GC_start_callback_proc start = start_callback;
    GC_on_collection_event_proc event = on_collection_event;
    if (event)
        event(GC_EVENT_START);
    if (start)
        start();

    pthread_mutex_lock(&state_lock);
    int notify = 0;
    if (atomic_load(&seen_cycle) < c) {
        atomic_store(&seen_cycle, c);
        GC_gc_no = (GC_word)c;
        atomic_store(&bytes_allocd_since_gc, 0);
        atomic_store(&expl_freed_since_gc, 0);
        link_sweep(&short_links);
        link_sweep(&long_links);
        size_t before = pending_count;
        drain_finq();
        notify = pending_count > before || (pending_count && GC_finalize_on_demand);
    }
    pthread_mutex_unlock(&state_lock);
    heap_size_estimate = resident_bytes();

    if (event)
        event(GC_EVENT_END);
    if (notify) {
        if (GC_finalize_on_demand) {
            GC_finalizer_notifier_proc n = GC_finalizer_notifier;
            if (n)
                n();
        } else if (!running_finalizers) {
            GC_invoke_finalizers();
        }
    }
}

static void cycle_hook(void)
{
    zgc_cycle_number c = zgc_completed_cycle();
    if (c != atomic_load_explicit(&seen_cycle, memory_order_relaxed)) {
        ensure_init();
        process_cycle(c);
    }
}

GC_API void GC_CALL GC_gcollect(void)
{
    ensure_init();
    zgc_request_and_wait();
    process_cycle(zgc_completed_cycle());
    if (!GC_finalize_on_demand && !running_finalizers)
        GC_invoke_finalizers();
}

GC_API void GC_CALL GC_gcollect_and_unmap(void)
{
    GC_gcollect();
    zscavenge_synchronously();
}

GC_API int GC_CALL GC_try_to_collect(GC_stop_func f)
{
    (void)f;
    GC_gcollect();
    return 1;
}

GC_API int GC_CALL GC_collect_a_little(void)
{
    zgc_try_request();
    cycle_hook();
    return 0;
}

GC_API void GC_CALL GC_start_incremental_collection(void) { zgc_try_request(); }

/* ------------------------------------------------------------------ */
/* Initialization, settings and statistics.                           */

GC_API void GC_CALL GC_init(void)
{
    ensure_init();
    atomic_store(&init_called, 1);
}
GC_API int GC_CALL GC_is_init_called(void) { return atomic_load(&init_called); }
GC_API void GC_CALL GC_deinit(void) {}

GC_API unsigned GC_CALL GC_get_version(void)
{
    return ((unsigned)GC_VERSION_MAJOR << 16) | (GC_VERSION_MINOR << 8) |
           GC_VERSION_MICRO;
}

GC_API GC_word GC_CALL GC_get_gc_no(void)
{
    cycle_hook();
    return (GC_word)zgc_completed_cycle();
}

GC_API int GC_CALL GC_get_parallel(void) { return GC_parallel; }
GC_API void GC_CALL GC_set_markers_count(unsigned n) { markers_count = (int)n; }
GC_API void GC_CALL GC_start_mark_threads(void) {}

#define SETTER_GETTER(type, name, var)                                        \
    GC_API void GC_CALL GC_set_##name(type v) { var = v; }                    \
    GC_API type GC_CALL GC_get_##name(void) { return var; }

SETTER_GETTER(GC_oom_func, oom_fn, GC_oom_fn)
SETTER_GETTER(GC_on_heap_resize_proc, on_heap_resize, GC_on_heap_resize)
SETTER_GETTER(GC_on_collection_event_proc, on_collection_event, on_collection_event)
SETTER_GETTER(GC_on_thread_event_proc, on_thread_event, on_thread_event)
SETTER_GETTER(int, find_leak, GC_find_leak)
SETTER_GETTER(int, all_interior_pointers, GC_all_interior_pointers)
SETTER_GETTER(int, finalize_on_demand, GC_finalize_on_demand)
SETTER_GETTER(int, java_finalization, GC_java_finalization)
SETTER_GETTER(GC_finalizer_notifier_proc, finalizer_notifier, GC_finalizer_notifier)
SETTER_GETTER(int, dont_expand, GC_dont_expand)
SETTER_GETTER(int, full_freq, GC_full_freq)
SETTER_GETTER(GC_word, non_gc_bytes, GC_non_gc_bytes)
SETTER_GETTER(int, no_dls, GC_no_dls)
SETTER_GETTER(GC_word, free_space_divisor, GC_free_space_divisor)
SETTER_GETTER(GC_word, max_retries, GC_max_retries)
SETTER_GETTER(int, dont_precollect, GC_dont_precollect)
SETTER_GETTER(unsigned long, time_limit, GC_time_limit)
SETTER_GETTER(struct GC_timeval_s, time_limit_tv, time_limit_tv)
SETTER_GETTER(GC_word, allocd_bytes_per_finalizer, allocd_bytes_per_finalizer)
SETTER_GETTER(int, pages_executable, pages_executable)
SETTER_GETTER(size_t, min_bytes_allocd, min_bytes_allocd)
SETTER_GETTER(int, rate, gc_rate)
SETTER_GETTER(int, max_prior_attempts, max_prior_attempts)
SETTER_GETTER(int, manual_vdb_allowed, manual_vdb_allowed)
SETTER_GETTER(int, force_unmap_on_gcollect, force_unmap_on_gcollect)
SETTER_GETTER(GC_start_callback_proc, start_callback, start_callback)
SETTER_GETTER(GC_push_other_roots_proc, push_other_roots, push_other_roots)
SETTER_GETTER(GC_sp_corrector_proc, sp_corrector, sp_corrector)
SETTER_GETTER(GC_warn_proc, warn_proc, warn_proc)
SETTER_GETTER(GC_abort_func, abort_func, GC_on_abort)

GC_API void GC_CALL GC_set_stop_func(GC_stop_func f) { stop_func = f; }
GC_API GC_stop_func GC_CALL GC_get_stop_func(void) { return stop_func; }
GC_API void GC_CALL GC_set_disable_automatic_collection(int v) { GC_dont_gc = v; }
GC_API int GC_CALL GC_get_disable_automatic_collection(void) { return GC_dont_gc; }
GC_API void GC_CALL GC_set_suspend_signal(int sig) { suspend_signal = sig; }
GC_API int GC_CALL GC_get_suspend_signal(void) { return suspend_signal; }
GC_API void GC_CALL GC_set_thr_restart_signal(int sig) { thr_restart_signal = sig; }
GC_API int GC_CALL GC_get_thr_restart_signal(void) { return thr_restart_signal; }
GC_API void GC_CALL GC_set_log_fd(int fd) { log_fd = fd; }
GC_API void GC_CALL GC_set_handle_fork(int v) { (void)v; }
GC_API void GC_CALL GC_atfork_prepare(void) {}
GC_API void GC_CALL GC_atfork_parent(void) {}
GC_API void GC_CALL GC_atfork_child(void) {}
GC_API void GC_CALL GC_start_performance_measurement(void) {}
GC_API unsigned long GC_CALL GC_get_full_gc_total_time(void) { return 0; }

GC_API void GC_CALLBACK GC_ignore_warn_proc(char *msg, GC_word arg)
{
    (void)msg;
    (void)arg;
}

GC_API void GC_CALL GC_abort_on_oom(void)
{
    fprintf(stderr, "GC: out of memory\n");
    abort();
}

/* Heap growth is FUGC's business. */
GC_API int GC_CALL GC_expand_hp(size_t n)
{
    (void)n;
    return 1;
}
GC_API void GC_CALL GC_set_max_heap_size(GC_word n) { (void)n; }

GC_API void GC_CALL GC_disable(void) { atomic_fetch_add(&disable_count, 1); }
GC_API void GC_CALL GC_enable(void) { atomic_fetch_sub(&disable_count, 1); }
GC_API int GC_CALL GC_is_disabled(void) { return atomic_load(&disable_count) > 0; }
GC_API void GC_CALL GC_enable_incremental(void) {}
GC_API int GC_CALL GC_is_incremental_mode(void) { return 0; }
GC_API int GC_CALL GC_incremental_protection_needs(void) { return GC_PROTECTS_NONE; }

static size_t heap_size(void)
{
    size_t h = heap_size_estimate;
    size_t allocd = atomic_load(&bytes_allocd_since_gc);
    return h > allocd ? h : allocd;
}

GC_API size_t GC_CALL GC_get_heap_size(void) { return heap_size(); }
GC_API size_t GC_CALL GC_get_free_bytes(void) { return 0; }
GC_API size_t GC_CALL GC_get_unmapped_bytes(void) { return 0; }
GC_API size_t GC_CALL GC_get_bytes_since_gc(void) { return atomic_load(&bytes_allocd_since_gc); }
GC_API size_t GC_CALL GC_get_expl_freed_bytes_since_gc(void) { return atomic_load(&expl_freed_since_gc); }
GC_API size_t GC_CALL GC_get_total_bytes(void) { return atomic_load(&total_bytes_allocd); }
GC_API size_t GC_CALL GC_get_obtained_from_os_bytes(void) { return heap_size(); }
GC_API size_t GC_CALL GC_get_memory_use(void) { return heap_size(); }

GC_API void GC_CALL GC_get_heap_usage_safe(GC_word *pheap_size,
                                           GC_word *pfree_bytes,
                                           GC_word *punmapped_bytes,
                                           GC_word *pbytes_since_gc,
                                           GC_word *ptotal_bytes)
{
    if (pheap_size)
        *pheap_size = heap_size();
    if (pfree_bytes)
        *pfree_bytes = 0;
    if (punmapped_bytes)
        *punmapped_bytes = 0;
    if (pbytes_since_gc)
        *pbytes_since_gc = atomic_load(&bytes_allocd_since_gc);
    if (ptotal_bytes)
        *ptotal_bytes = atomic_load(&total_bytes_allocd);
}

static size_t fill_prof_stats(struct GC_prof_stats_s *out, size_t size)
{
    struct GC_prof_stats_s s;
    size_t since = atomic_load(&bytes_allocd_since_gc);
    size_t total = atomic_load(&total_bytes_allocd);
    s.heapsize_full = heap_size();
    s.free_bytes_full = 0;
    s.unmapped_bytes = 0;
    s.bytes_allocd_since_gc = since;
    s.allocd_bytes_before_gc = total - since;
    s.non_gc_bytes = GC_non_gc_bytes;
    s.gc_no = (GC_word)zgc_completed_cycle();
    s.markers_m1 = 0;
    s.bytes_reclaimed_since_gc = 0;
    s.reclaimed_bytes_before_gc = 0;
    s.expl_freed_bytes_since_gc = atomic_load(&expl_freed_since_gc);
    s.obtained_from_os_bytes = heap_size();
    if (size > sizeof(s)) {
        memset((char *)out + sizeof(s), 0xff, size - sizeof(s));
        size = sizeof(s);
    }
    memcpy(out, &s, size);
    return size;
}

GC_API size_t GC_CALL GC_get_prof_stats(struct GC_prof_stats_s *s, size_t n)
{
    return fill_prof_stats(s, n);
}
GC_API size_t GC_CALL GC_get_prof_stats_unsafe(struct GC_prof_stats_s *s, size_t n)
{
    return fill_prof_stats(s, n);
}

/* Roots and displacements: FUGC scans globals, stacks and the heap
   precisely, and interior pointers keep their objects alive. */
GC_API void GC_CALL GC_add_roots(void *lo, void *hi) { (void)lo; (void)hi; }
GC_API void GC_CALL GC_remove_roots(void *lo, void *hi) { (void)lo; (void)hi; }
GC_API void GC_CALL GC_clear_roots(void) {}
GC_API void GC_CALL GC_exclude_static_roots(void *lo, void *hi) { (void)lo; (void)hi; }
GC_API void GC_CALL GC_clear_exclusion_table(void) {}
GC_API void GC_CALL GC_register_has_static_roots_callback(GC_has_static_roots_func f) { (void)f; }
GC_API int GC_CALL GC_is_tmp_root(void *p) { (void)p; return 0; }

/* Marking internals.  Mark procedures are never called. */
GC_API struct GC_ms_entry *GC_CALL GC_mark_and_push(void *obj,
                                                    struct GC_ms_entry *msp,
                                                    struct GC_ms_entry *lim,
                                                    void **src)
{
    (void)obj;
    (void)lim;
    (void)src;
    return msp;
}
/* Mark bits only mean something to finalizers and disclaim procedures:
   an object whose finalizer is running counts as marked if the client
   called GC_set_mark_bit on it after the collection that found it
   unreachable began (that is how libgc clients rescue such objects).
   Every other object counts as marked. */
struct mark_bit {
    zgc_cycle_number cycle;
};

GC_API int GC_CALL GC_is_marked(const void *p)
{
    if (!finalizing_obj || p != finalizing_obj)
        return 1;
    struct mark_bit *m = zweak_map_get(mark_bits, (void *)p);
    return m && m->cycle + 1 >= finalizing_dead_cycle;
}
GC_API void GC_CALL GC_clear_mark_bit(const void *p)
{
    ensure_init();
    zweak_map_set(mark_bits, (void *)p, NULL);
}
GC_API void GC_CALL GC_set_mark_bit(const void *p)
{
    ensure_init();
    struct mark_bit *m = zgc_alloc(sizeof(*m));
    m->cycle = zgc_completed_cycle();
    zweak_map_set(mark_bits, (void *)p, m);
}
GC_API void GC_CALL GC_push_all(void *b, void *t) { (void)b; (void)t; }
GC_API void GC_CALL GC_push_all_eager(void *b, void *t) { (void)b; (void)t; }
GC_API void GC_CALL GC_push_conditional(void *b, void *t, int all) { (void)b; (void)t; (void)all; }
GC_API void GC_CALL GC_push_finalizer_structures(void) {}
GC_API void GC_CALL GC_register_describe_type_fn(int k, GC_describe_type_fn f) { (void)k; (void)f; }
GC_API void GC_CALL GC_enumerate_reachable_objects_inner(GC_reachable_object_proc p, void *cd)
{
    (void)p;
    (void)cd;
}
GC_API void *GC_CALL GC_clear_stack(void *p) { return p; }
GC_API void GC_CALL GC_noop1(GC_word x)
{
    static volatile GC_word sink;
    sink = x;
    (void)sink;
}
GC_API void GC_CALL GC_print_free_list(int k, size_t lg) { (void)k; (void)lg; }

/* Pointer checks: Fil-C checks every access anyway. */
GC_API void *GC_CALL GC_same_obj(void *p, void *q) { (void)q; return p; }
GC_API void *GC_CALL GC_is_visible(void *p) { return p; }
GC_API void *GC_CALL GC_is_valid_displacement(void *p) { return p; }
GC_API void *GC_CALL GC_pre_incr(void **p, ptrdiff_t how_much)
{
    *p = (char *)*p + how_much;
    return *p;
}
GC_API void *GC_CALL GC_post_incr(void **p, ptrdiff_t how_much)
{
    void *old = *p;
    *p = (char *)old + how_much;
    return old;
}

/* Diagnostics. */
GC_API void GC_CALL GC_dump_named(const char *name)
{
    fprintf(stderr, "***GC Dump %s (FUGC): cycle %llu, ~%zu bytes resident\n",
            name ? name : "", (unsigned long long)zgc_completed_cycle(),
            heap_size());
}
GC_API void GC_CALL GC_dump(void) { GC_dump_named(NULL); }
GC_API void GC_CALL GC_dump_regions(void) { GC_dump_named("regions"); }
GC_API void GC_CALL GC_dump_finalization(void)
{
    fprintf(stderr, "***Finalization (FUGC): %zu registered, %zu pending\n",
            atomic_load(&finalizers_registered), pending_count);
}

static void vlog(FILE *f, const char *fmt, va_list ap)
{
    vfprintf(f, fmt, ap);
}
GC_API void GC_printf(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vlog(stdout, fmt, ap);
    va_end(ap);
}
GC_API void GC_err_printf(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vlog(stderr, fmt, ap);
    va_end(ap);
}
GC_API void GC_log_printf(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    vlog(stderr, fmt, ap);
    va_end(ap);
}

/* ------------------------------------------------------------------ */
/* Locks, threads and stacks.  FUGC knows every thread already.       */

GC_API void GC_CALL GC_alloc_lock(void) { pthread_mutex_lock(&alloc_lock); }
GC_API void GC_CALL GC_alloc_unlock(void) { pthread_mutex_unlock(&alloc_lock); }

GC_API void *GC_CALL GC_call_with_alloc_lock(GC_fn_type fn, void *cd)
{
    /* Clear dead links first, so that code revealing them under the lock
       sees what libgc would have left there. */
    cycle_hook();
    pthread_mutex_lock(&alloc_lock);
    void *result = fn(cd);
    pthread_mutex_unlock(&alloc_lock);
    return result;
}

GC_API int GC_CALL GC_get_stack_base(struct GC_stack_base *sb)
{
    sb->mem_base = zstack_top();
    return GC_SUCCESS;
}

GC_API void *GC_CALL GC_call_with_stack_base(GC_stack_base_func fn, void *arg)
{
    struct GC_stack_base sb;
    GC_get_stack_base(&sb);
    return fn(&sb, arg);
}

GC_API void *GC_CALL GC_get_my_stackbottom(struct GC_stack_base *sb)
{
    GC_get_stack_base(sb);
    return NULL;
}
GC_API void GC_CALL GC_set_stackbottom(void *gc_thread_handle,
                                       const struct GC_stack_base *sb)
{
    (void)gc_thread_handle;
    (void)sb;
}

static _Thread_local int thread_registered;

GC_API void GC_CALL GC_allow_register_threads(void) { GC_init(); }
GC_API int GC_CALL GC_register_my_thread(const struct GC_stack_base *sb)
{
    (void)sb;
    if (thread_registered)
        return GC_DUPLICATE;
    thread_registered = 1;
    return GC_SUCCESS;
}
GC_API int GC_CALL GC_unregister_my_thread(void)
{
    thread_registered = 0;
    return GC_SUCCESS;
}
GC_API int GC_CALL GC_thread_is_registered(void) { return 1; }
GC_API void GC_CALL GC_register_altstack(void *a, GC_word b, void *c, GC_word d)
{
    (void)a;
    (void)b;
    (void)c;
    (void)d;
}
GC_API void *GC_CALL GC_do_blocking(GC_fn_type fn, void *cd) { return fn(cd); }
GC_API void *GC_CALL GC_call_with_gc_active(GC_fn_type fn, void *cd) { return fn(cd); }
GC_API void GC_CALL GC_stop_world_external(void) {}
GC_API void GC_CALL GC_start_world_external(void) {}
GC_API void GC_CALL GC_suspend_thread(GC_SUSPEND_THREAD_ID t) { (void)t; }
GC_API void GC_CALL GC_resume_thread(GC_SUSPEND_THREAD_ID t) { (void)t; }
GC_API int GC_CALL GC_is_thread_suspended(GC_SUSPEND_THREAD_ID t) { (void)t; return 0; }

GC_API int GC_pthread_create(pthread_t *t, const pthread_attr_t *a,
                             void *(*fn)(void *), void *arg)
{
    return pthread_create(t, a, fn, arg);
}
GC_API int GC_pthread_join(pthread_t t, void **ret) { return pthread_join(t, ret); }
GC_API int GC_pthread_detach(pthread_t t) { return pthread_detach(t); }
GC_API int GC_pthread_cancel(pthread_t t) { return pthread_cancel(t); }
GC_API void GC_pthread_exit(void *ret) { pthread_exit(ret); }
GC_API int GC_pthread_sigmask(int how, const sigset_t *set, sigset_t *old)
{
    return pthread_sigmask(how, set, old);
}
GC_API void *GC_dlopen(const char *path, int mode) { return dlopen(path, mode); }
