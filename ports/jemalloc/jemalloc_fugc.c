/*
 * jemalloc's API on Fil-C's allocator (docs/jemalloc-on-fugc.md).
 *
 * The standard functions (malloc, free, posix_memalign, malloc_usable_size,
 * free_sized, ...) are left to libc, which forwards them to zgc_alloc and
 * friends; defining them here would only interpose identical copies. This
 * file adds the non-standard API: the *allocx family, mallctl and friends,
 * malloc_stats_print, malloc_conf and malloc_message. Every object is a
 * separate GC allocation with its own bounds, and freeing one makes later
 * accesses trap.
 */

#include <errno.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <unistd.h>

#include <stdfil.h>

/* Keep the header's je_* -> public name macros, as jemalloc's sources do. */
#define JEMALLOC_NO_DEMANGLE
#include <jemalloc/jemalloc.h>

#define MINALIGN 16
#define PAGE 4096

/* Applications set options by defining malloc_conf themselves. */
__attribute__((weak)) const char *je_malloc_conf = NULL;
__attribute__((weak)) const char *je_malloc_conf_2_conf_harder = NULL;
void (*je_malloc_message)(void *cbopaque, const char *s) = NULL;

static size_t flags_align(int flags)
{
    int lg = flags & 0x3f;
    return lg ? (size_t)1 << lg : 0;
}

static size_t usable(size_t size)
{
    /* zgc_alloc rounds every size up to its 16-byte minimum alignment. */
    if (!size)
        size = 1;
    return (size + MINALIGN - 1) & ~(size_t)(MINALIGN - 1);
}

/* jemalloc allocates at least one byte for a request of zero. */
void *je_mallocx(size_t size, int flags)
{
    size_t align = flags_align(flags);
    if (!size)
        size = 1;
    /* The memory is always zeroed, so MALLOCX_ZERO needs nothing. Arenas and
       tcaches do not exist; their flags are accepted and ignored. */
    if (align > MINALIGN)
        return zgc_aligned_alloc(align, size);
    return zgc_alloc(size);
}

void *je_rallocx(void *ptr, size_t size, int flags)
{
    size_t align = flags_align(flags);
    if (!size)
        size = 1;
    /* Growth is zero-filled, which covers MALLOCX_ZERO. */
    if (align > MINALIGN)
        return zgc_aligned_realloc(ptr, align, size);
    return zgc_realloc(ptr, size);
}

size_t je_sallocx(const void *ptr, int flags)
{
    (void)flags;
    return (size_t)((const char *)zgetupper((void *)ptr) - (const char *)ptr);
}

/* Objects cannot grow in place. Like jemalloc, report the size it has. */
size_t je_xallocx(void *ptr, size_t size, size_t extra, int flags)
{
    (void)size;
    (void)extra;
    return je_sallocx(ptr, flags);
}

void je_dallocx(void *ptr, int flags)
{
    (void)flags;
    zgc_free(ptr);
}

void je_sdallocx(void *ptr, size_t size, int flags)
{
    (void)size;
    (void)flags;
    zgc_free(ptr);
}

size_t je_nallocx(size_t size, int flags)
{
    (void)flags;
    return usable(size);
}

/* ---- mallctl ---------------------------------------------------------- */

enum kind { K_VOID, K_BOOL, K_UNSIGNED, K_SIZE, K_SSIZE, K_U64, K_STR };

static const size_t kind_size[] = {
    [K_VOID] = 0,
    [K_BOOL] = sizeof(bool),
    [K_UNSIGNED] = sizeof(unsigned),
    [K_SIZE] = sizeof(size_t),
    [K_SSIZE] = sizeof(ssize_t),
    [K_U64] = sizeof(uint64_t),
    [K_STR] = sizeof(const char *),
};

union value {
    bool b;
    unsigned u;
    size_t z;
    ssize_t s;
    uint64_t q;
    const char *str;
};

enum { RO = 0, RW = 1, WO = 2 };

struct node;
typedef int (*handler)(const struct node *n, const size_t *idx, union value *v,
                       const union value *nv);

struct node {
    const char *name; /* '#' stands for a numeric component */
    enum kind kind;
    int access;
    handler fn; /* NULL: constant `init`, writes accepted and ignored */
    union value init;
};

static unsigned narenas = 1;
static unsigned ntcaches;
static uint64_t epoch_value;
static ssize_t dirty_decay_ms = 10000, muzzy_decay_ms = 0;

/* All the stats describe the process's resident memory: this allocator
   keeps no per-size accounting of its own. */
static size_t resident(void)
{
    unsigned long size, rss;
    FILE *f = fopen("/proc/self/statm", "r");
    if (!f)
        return 0;
    if (fscanf(f, "%lu %lu", &size, &rss) != 2)
        rss = 0;
    fclose(f);
    return rss * (size_t)sysconf(_SC_PAGESIZE);
}

/* Like jemalloc, index narenas also means all arenas (the pre-5.0 form). */
static bool arena_ok(size_t i)
{
    return i <= __atomic_load_n(&narenas, __ATOMIC_RELAXED) ||
           i == MALLCTL_ARENAS_ALL || i == MALLCTL_ARENAS_DESTROYED;
}

/* Everything is accounted to arena 0; created arenas stay empty. */
static bool arena_has_memory(size_t i)
{
    return i == 0 || i == MALLCTL_ARENAS_ALL ||
           i == __atomic_load_n(&narenas, __ATOMIC_RELAXED);
}

static int h_epoch(const struct node *n, const size_t *idx, union value *v,
                   const union value *nv)
{
    (void)n;
    (void)idx;
    if (nv)
        __atomic_add_fetch(&epoch_value, 1, __ATOMIC_RELAXED);
    v->q = __atomic_load_n(&epoch_value, __ATOMIC_RELAXED);
    return 0;
}

static int h_resident(const struct node *n, const size_t *idx, union value *v,
                      const union value *nv)
{
    (void)n;
    (void)nv;
    if (idx[0] == (size_t)-1) {
        v->z = resident();
        return 0;
    }
    if (!arena_ok(idx[0]))
        return ENOENT;
    v->z = arena_has_memory(idx[0]) ? resident() : 0;
    return 0;
}

static int h_pactive(const struct node *n, const size_t *idx, union value *v,
                     const union value *nv)
{
    int ret = h_resident(n, idx, v, nv);
    v->z /= PAGE;
    return ret;
}

static int h_arena_zero(const struct node *n, const size_t *idx,
                        union value *v, const union value *nv)
{
    (void)n;
    (void)nv;
    if (!arena_ok(idx[0]))
        return ENOENT;
    memset(v, 0, sizeof *v);
    return 0;
}

static int h_arena_void(const struct node *n, const size_t *idx,
                        union value *v, const union value *nv)
{
    (void)n;
    (void)v;
    (void)nv;
    return arena_ok(idx[0]) ? 0 : EFAULT;
}

static int h_arena_decay(const struct node *n, const size_t *idx,
                         union value *v, const union value *nv)
{
    ssize_t *slot = strstr(n->name, "muzzy") ? &muzzy_decay_ms
                                              : &dirty_decay_ms;
    if (!arena_ok(idx[0]))
        return EFAULT;
    v->s = *slot;
    if (nv)
        *slot = nv->s;
    return 0;
}

static int h_arenas_decay(const struct node *n, const size_t *idx,
                          union value *v, const union value *nv)
{
    size_t none = 0;
    (void)idx;
    return h_arena_decay(n, &none, v, nv);
}

static int h_arena_initialized(const struct node *n, const size_t *idx,
                               union value *v, const union value *nv)
{
    (void)n;
    (void)nv;
    if (!arena_ok(idx[0]))
        return EFAULT;
    v->b = true;
    return 0;
}

static int h_narenas(const struct node *n, const size_t *idx, union value *v,
                     const union value *nv)
{
    (void)n;
    (void)idx;
    (void)nv;
    v->u = __atomic_load_n(&narenas, __ATOMIC_RELAXED);
    return 0;
}

static int h_arenas_create(const struct node *n, const size_t *idx,
                           union value *v, const union value *nv)
{
    (void)n;
    (void)idx;
    (void)nv;
    v->u = __atomic_fetch_add(&narenas, 1, __ATOMIC_RELAXED);
    return 0;
}

static int h_tcache_create(const struct node *n, const size_t *idx,
                           union value *v, const union value *nv)
{
    (void)n;
    (void)idx;
    (void)nv;
    v->u = __atomic_fetch_add(&ntcaches, 1, __ATOMIC_RELAXED);
    return 0;
}

static int h_bin(const struct node *n, const size_t *idx, union value *v,
                 const union value *nv)
{
    /* One small bin (16 bytes), so that bin walks find something valid. */
    (void)nv;
    if (idx[0] != 0)
        return ENOENT;
    if (!strcmp(n->name, "arenas.bin.#.size"))
        v->z = MINALIGN;
    else if (!strcmp(n->name, "arenas.bin.#.nregs"))
        v->u = PAGE / MINALIGN;
    else if (!strcmp(n->name, "arenas.bin.#.slab_size"))
        v->z = PAGE;
    else
        v->u = 0;
    return 0;
}

static int h_arena_bin_zero(const struct node *n, const size_t *idx,
                            union value *v, const union value *nv)
{
    (void)n;
    (void)nv;
    if (!arena_ok(idx[0]) || idx[1] != 0)
        return ENOENT;
    memset(v, 0, sizeof *v);
    return 0;
}

#define B(name, value) { name, K_BOOL, RO, NULL, { .b = value } }
#define S(name, value) { name, K_STR, RO, NULL, { .str = value } }
#define U(name, value) { name, K_UNSIGNED, RO, NULL, { .u = value } }
#define Z(name, value) { name, K_SIZE, RO, NULL, { .z = value } }
#define SS(name, value) { name, K_SSIZE, RO, NULL, { .s = value } }
#define Q(name, value) { name, K_U64, RO, NULL, { .q = value } }
#define H(name, kind, access, fn) { name, kind, access, fn, { .z = 0 } }

static const struct node nodes[] = {
    S("version", JEMALLOC_VERSION),
    H("epoch", K_U64, RW, h_epoch),
    { "background_thread", K_BOOL, RW, NULL, { .b = false } },
    { "max_background_threads", K_SIZE, RW, NULL, { .z = 0 } },

    B("config.cache_oblivious", false),
    B("config.debug", false),
    B("config.fill", false),
    B("config.lazy_lock", false),
    S("config.malloc_conf", ""),
    B("config.opt_safety_checks", false),
    B("config.prof", false),
    B("config.prof_libgcc", false),
    B("config.prof_libunwind", false),
    B("config.stats", true),
    B("config.utrace", false),
    B("config.xmalloc", false),

    B("opt.abort", false),
    B("opt.abort_conf", false),
    B("opt.retain", true),
    S("opt.dss", "disabled"),
    U("opt.narenas", 1),
    S("opt.percpu_arena", "disabled"),
    Z("opt.oversize_threshold", 0),
    B("opt.background_thread", false),
    Z("opt.max_background_threads", 0),
    SS("opt.dirty_decay_ms", 10000),
    SS("opt.muzzy_decay_ms", 0),
    B("opt.stats_print", false),
    S("opt.stats_print_opts", ""),
    S("opt.junk", "false"),
    B("opt.zero", true),
    B("opt.utrace", false),
    B("opt.xmalloc", false),
    B("opt.tcache", false),
    Z("opt.tcache_max", 0),
    S("opt.thp", "disabled"),
    B("opt.prof", false),

    { "thread.arena", K_UNSIGNED, RW, NULL, { .u = 0 } },
    Q("thread.allocated", 0),
    Q("thread.deallocated", 0),
    { "thread.tcache.enabled", K_BOOL, RW, NULL, { .b = false } },
    H("thread.tcache.flush", K_VOID, RO, NULL),
    { "thread.idle", K_VOID, RO, NULL, { .z = 0 } },

    H("tcache.create", K_UNSIGNED, RO, h_tcache_create),
    { "tcache.flush", K_UNSIGNED, WO, NULL, { .u = 0 } },
    { "tcache.destroy", K_UNSIGNED, WO, NULL, { .u = 0 } },

    H("arena.#.initialized", K_BOOL, RO, h_arena_initialized),
    H("arena.#.decay", K_VOID, RO, h_arena_void),
    H("arena.#.purge", K_VOID, RO, h_arena_void),
    H("arena.#.reset", K_VOID, RO, h_arena_void),
    H("arena.#.destroy", K_VOID, RO, h_arena_void),
    H("arena.#.dirty_decay_ms", K_SSIZE, RW, h_arena_decay),
    H("arena.#.muzzy_decay_ms", K_SSIZE, RW, h_arena_decay),

    H("arenas.narenas", K_UNSIGNED, RO, h_narenas),
    H("arenas.dirty_decay_ms", K_SSIZE, RW, h_arenas_decay),
    H("arenas.muzzy_decay_ms", K_SSIZE, RW, h_arenas_decay),
    Z("arenas.quantum", MINALIGN),
    Z("arenas.page", PAGE),
    Z("arenas.tcache_max", 0),
    U("arenas.nbins", 1),
    U("arenas.nhbins", 0),
    U("arenas.nlextents", 0),
    H("arenas.bin.#.size", K_SIZE, RO, h_bin),
    H("arenas.bin.#.nregs", K_UNSIGNED, RO, h_bin),
    H("arenas.bin.#.slab_size", K_SIZE, RO, h_bin),
    H("arenas.bin.#.nshards", K_UNSIGNED, RO, h_bin),
    H("arenas.create", K_UNSIGNED, RO, h_arenas_create),

    H("stats.allocated", K_SIZE, RO, h_resident),
    H("stats.active", K_SIZE, RO, h_resident),
    Z("stats.metadata", 0),
    H("stats.resident", K_SIZE, RO, h_resident),
    H("stats.mapped", K_SIZE, RO, h_resident),
    Z("stats.retained", 0),
    Z("stats.zero_reallocs", 0),

    H("stats.arenas.#.pactive", K_SIZE, RO, h_pactive),
    H("stats.arenas.#.pdirty", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.pmuzzy", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.mapped", K_SIZE, RO, h_resident),
    H("stats.arenas.#.retained", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.resident", K_SIZE, RO, h_resident),
    H("stats.arenas.#.base", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.internal", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.small.allocated", K_SIZE, RO, h_resident),
    H("stats.arenas.#.small.resident", K_SIZE, RO, h_resident),
    H("stats.arenas.#.small.nmalloc", K_U64, RO, h_arena_zero),
    H("stats.arenas.#.small.ndalloc", K_U64, RO, h_arena_zero),
    H("stats.arenas.#.large.allocated", K_SIZE, RO, h_arena_zero),
    H("stats.arenas.#.large.nmalloc", K_U64, RO, h_arena_zero),
    H("stats.arenas.#.large.ndalloc", K_U64, RO, h_arena_zero),
    H("stats.arenas.#.bins.#.curregs", K_SIZE, RO, h_arena_bin_zero),
    H("stats.arenas.#.bins.#.curslabs", K_SIZE, RO, h_arena_bin_zero),
    H("stats.arenas.#.bins.#.nmalloc", K_U64, RO, h_arena_bin_zero),
    H("stats.arenas.#.bins.#.ndalloc", K_U64, RO, h_arena_bin_zero),
    H("stats.arenas.#.bins.#.nslabs", K_U64, RO, h_arena_bin_zero),
};

#define NNODES (sizeof nodes / sizeof nodes[0])
#define MAXDEPTH 8

/* Match `name` against a pattern, collecting its numeric components. */
static bool match(const char *pat, const char *name, size_t *idx,
                  size_t *nidx)
{
    *nidx = 0;
    while (*pat && *name) {
        if (*pat == '#') {
            char *end;
            if (*name < '0' || *name > '9')
                return false;
            errno = 0;
            unsigned long long v = strtoull(name, &end, 10);
            if (errno || *nidx == MAXDEPTH)
                return false;
            idx[(*nidx)++] = (size_t)v;
            name = end;
            pat++;
        } else if (*pat++ != *name++)
            return false;
    }
    return !*pat && !*name;
}

static int ctl(const struct node *n, const size_t *idx, void *oldp,
               size_t *oldlenp, void *newp, size_t newlen)
{
    size_t size = kind_size[n->kind];
    union value v = n->init, nv;
    int ret;

    if (newp) {
        if (n->access == RO)
            return EPERM;
        if (newlen != size)
            return EINVAL;
        memcpy(&nv, newp, size);
    } else if (n->access == WO && n->kind != K_VOID)
        return EINVAL;
    if (oldp && n->access == WO)
        return EPERM;

    if (n->fn) {
        size_t none[MAXDEPTH] = { (size_t)-1 };
        ret = n->fn(n, idx ? idx : none, &v, newp ? &nv : NULL);
        if (ret)
            return ret;
    }

    if (oldp && oldlenp && size) {
        if (*oldlenp != size) {
            size_t copy = *oldlenp < size ? *oldlenp : size;
            memcpy(oldp, &v, copy);
            *oldlenp = copy;
            return EINVAL;
        }
        memcpy(oldp, &v, size);
    }
    return 0;
}

int je_mallctl(const char *name, void *oldp, size_t *oldlenp, void *newp,
               size_t newlen)
{
    size_t idx[MAXDEPTH], nidx;
    for (size_t i = 0; i < NNODES; i++)
        if (match(nodes[i].name, name, idx, &nidx))
            return ctl(&nodes[i], nidx ? idx : NULL, oldp, oldlenp, newp,
                       newlen);
    return ENOENT;
}

static size_t depth(const char *pat)
{
    size_t d = 1;
    for (; *pat; pat++)
        d += *pat == '.';
    return d;
}

/* A MIB is { node, 0, ..., index, ... }: component k holds the value of
   the pattern's k-th component when that is numeric, and 0 otherwise. */
int je_mallctlnametomib(const char *name, size_t *mibp, size_t *miblenp)
{
    size_t idx[MAXDEPTH], nidx;
    for (size_t i = 0; i < NNODES; i++) {
        if (!match(nodes[i].name, name, idx, &nidx))
            continue;
        size_t d = depth(nodes[i].name), k = 0, c = 0;
        if (*miblenp < d)
            return ENOENT;
        mibp[0] = i;
        for (const char *p = nodes[i].name; *p; p++) {
            if (*p == '.') {
                c++;
                if (c < d)
                    mibp[c] = 0;
            } else if (*p == '#')
                mibp[c] = idx[k++];
        }
        *miblenp = d;
        return 0;
    }
    return ENOENT;
}

int je_mallctlbymib(const size_t *mib, size_t miblen, void *oldp,
                    size_t *oldlenp, void *newp, size_t newlen)
{
    size_t idx[MAXDEPTH], nidx = 0, c = 0;
    if (!miblen || mib[0] >= NNODES || miblen != depth(nodes[mib[0]].name))
        return ENOENT;
    for (const char *p = nodes[mib[0]].name; *p; p++) {
        if (*p == '.')
            c++;
        else if (*p == '#')
            idx[nidx++] = mib[c];
    }
    return ctl(&nodes[mib[0]], nidx ? idx : NULL, oldp, oldlenp, newp,
               newlen);
}

/* ---- statistics output ------------------------------------------------ */

static void default_write(void *opaque, const char *s)
{
    (void)opaque;
    if (je_malloc_message)
        je_malloc_message(NULL, s);
    else
        fputs(s, stderr);
}

void je_malloc_stats_print(void (*write_cb)(void *, const char *),
                           void *cbopaque, const char *opts)
{
    char buf[256];
    if (!write_cb)
        write_cb = default_write;
    if (opts && strchr(opts, 'J')) {
        snprintf(buf, sizeof buf,
                 "{\"jemalloc\":{\"version\":\"%s\",\"allocator\":\"Fil-C\","
                 "\"stats\":{\"resident\":%zu}}}\n",
                 JEMALLOC_VERSION, resident());
        write_cb(cbopaque, buf);
        return;
    }
    snprintf(buf, sizeof buf,
             "___ Begin jemalloc statistics ___\n"
             "Version: \"%s\"\n"
             "Allocator: Fil-C's garbage-collected heap (jemalloc API shim)\n"
             "Resident: %zu\n"
             "--- End jemalloc statistics ---\n",
             JEMALLOC_VERSION, resident());
    write_cb(cbopaque, buf);
}
