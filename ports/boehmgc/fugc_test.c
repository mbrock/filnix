/* Tests for the FUGC-backed libgc: the parts that differ from plain
   malloc (finalizers, disappearing links, hidden pointers, uncollectable
   objects) plus a smoke test of the rest of the API. */

#define GC_THREADS 1
#include <gc.h>
#include <gc/gc_mark.h>
#include <gc/gc_typed.h>
#include <gc/gc_inline.h>
#include <gc/gc_disclaim.h>
#include <gc/javaxfc.h>

#include <pthread.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int failures;
#define CHECK(cond)                                                           \
    do {                                                                      \
        if (!(cond)) {                                                        \
            fprintf(stderr, "%s:%d: FAIL: %s\n", __FILE__, __LINE__, #cond);  \
            failures++;                                                       \
        }                                                                     \
    } while (0)

#define NOINLINE __attribute__((noinline))

/* Collect a few times: FUGC is concurrent and a cycle may float garbage
   created while it runs. */
static void collect(void)
{
    for (int i = 0; i < 3; i++)
        GC_gcollect();
}

static int finalized_count;
static void *finalized_cd;
static void GC_CALLBACK count_finalizer(void *obj, void *cd)
{
    CHECK(((int *)obj)[0] == 42); /* the object is still usable */
    finalized_count++;
    finalized_cd = cd;
}

NOINLINE static void make_finalizable(int n)
{
    for (int i = 0; i < n; i++) {
        int *p = GC_MALLOC(64);
        p[0] = 42;
        GC_REGISTER_FINALIZER(p, count_finalizer, (void *)0x1234, 0, 0);
    }
}

static void test_finalizers(void)
{
    finalized_count = 0;
    make_finalizable(100);
    collect();
    GC_invoke_finalizers();
    printf("finalized %d/100\n", finalized_count);
    CHECK(finalized_count >= 90);
    CHECK(finalized_cd == (void *)0x1234);

    /* A live object is not finalized, and unregistering works. */
    finalized_count = 0;
    int *live = GC_MALLOC(64);
    live[0] = 42;
    GC_REGISTER_FINALIZER(live, count_finalizer, 0, 0, 0);
    GC_finalization_proc ofn = 0;
    void *ocd = (void *)1;
    int *cancelled = GC_MALLOC(64);
    GC_REGISTER_FINALIZER(cancelled, count_finalizer, (void *)7, 0, 0);
    GC_REGISTER_FINALIZER(cancelled, 0, 0, &ofn, &ocd);
    CHECK(ofn == count_finalizer);
    CHECK(ocd == (void *)7);
    cancelled = 0;
    collect();
    GC_invoke_finalizers();
    CHECK(finalized_count == 0);
    CHECK(live[0] == 42);
    GC_REGISTER_FINALIZER(live, 0, 0, 0, 0);
}

/* A finalizer that resurrects its object into a global and registers
   itself again (the guardian pattern). */
static void *resurrected;
static int resurrections;
static void GC_CALLBACK resurrect(void *obj, void *cd)
{
    (void)cd;
    resurrected = obj;
    resurrections++;
}
NOINLINE static void make_resurrectable(void)
{
    int *p = GC_MALLOC(32);
    p[0] = 42;
    GC_REGISTER_FINALIZER(p, resurrect, 0, 0, 0);
}
NOINLINE static void reregister(void)
{
    CHECK(resurrected && ((int *)resurrected)[0] == 42);
    GC_REGISTER_FINALIZER(resurrected, resurrect, 0, 0, 0);
    resurrected = 0;
}
static void test_resurrection(void)
{
    make_resurrectable();
    collect();
    GC_invoke_finalizers();
    CHECK(resurrections == 1);
    reregister();
    collect();
    GC_invoke_finalizers();
    CHECK(resurrections == 2);
}

struct holder {
    GC_hidden_pointer hidden; /* weak, as libgc clients write it */
};

static void *GC_CALLBACK reveal_locked(void *h)
{
    struct holder *holder = h;
    return holder->hidden ? GC_REVEAL_POINTER(holder->hidden) : NULL;
}

NOINLINE static struct holder *make_link(int keep, void **kept)
{
    struct holder *h = GC_MALLOC(sizeof *h);
    char *target = GC_MALLOC(16);
    strcpy(target, "target");
    h->hidden = GC_HIDE_POINTER(target);
    CHECK(GC_GENERAL_REGISTER_DISAPPEARING_LINK((void **)&h->hidden, target) ==
          GC_SUCCESS);
    CHECK(GC_GENERAL_REGISTER_DISAPPEARING_LINK((void **)&h->hidden, target) ==
          GC_DUPLICATE);
    if (keep)
        *kept = target;
    return h;
}

static void test_links(void)
{
    void *kept = 0;
    struct holder *dead = make_link(0, 0);
    struct holder *live = make_link(1, &kept);
    collect();
    char *r = GC_call_with_alloc_lock(reveal_locked, live);
    CHECK(r == kept);
    CHECK(r && strcmp(r, "target") == 0);
    CHECK(GC_call_with_alloc_lock(reveal_locked, dead) == NULL);
    CHECK(dead->hidden == 0);

    /* Moving and unregistering. */
    struct holder *other = GC_MALLOC(sizeof *other);
    other->hidden = live->hidden;
    CHECK(GC_move_disappearing_link((void **)&live->hidden,
                                    (void **)&other->hidden) == GC_SUCCESS);
    CHECK(GC_unregister_disappearing_link((void **)&live->hidden) == 0);
    CHECK(GC_unregister_disappearing_link((void **)&other->hidden) == 1);
    CHECK(GC_move_disappearing_link((void **)&live->hidden,
                                    (void **)&other->hidden) == GC_NOT_FOUND);
    CHECK(kept != 0);
}

NOINLINE static GC_hidden_pointer make_uncollectable(void)
{
    char *p = GC_MALLOC_UNCOLLECTABLE(32);
    strcpy(p, "uncollectable");
    return GC_HIDE_POINTER(p);
}

static void test_uncollectable(void)
{
    GC_hidden_pointer h = make_uncollectable();
    collect();
    char *p = GC_REVEAL_POINTER(h);
    CHECK(strcmp(p, "uncollectable") == 0);
    p = GC_REALLOC(p, 4096);
    CHECK(strcmp(p, "uncollectable") == 0);
    GC_FREE(p);
}

static int notified;
static void GC_CALLBACK notifier(void) { notified++; }

static void test_finalize_on_demand(void)
{
    GC_set_finalize_on_demand(1);
    GC_set_finalizer_notifier(notifier);
    finalized_count = 0;
    make_finalizable(10);
    collect();
    CHECK(finalized_count == 0);
    CHECK(notified > 0);
    CHECK(GC_should_invoke_finalizers());
    CHECK(GC_invoke_finalizers() >= 9);
    CHECK(finalized_count >= 9);
    GC_set_finalize_on_demand(0);
    GC_set_finalizer_notifier(0);
}

static int closure_ran;
static void GC_CALLBACK closure_proc(void *obj, void *cd)
{
    CHECK(strcmp(obj, "finalized_malloc") == 0);
    CHECK(cd == (void *)&closure_ran);
    closure_ran++;
}
static const struct GC_finalizer_closure closure = {closure_proc, &closure_ran};
NOINLINE static void make_finalized_malloc(void)
{
    char *p = GC_finalized_malloc(32, &closure);
    strcpy(p, "finalized_malloc");
}
static void test_finalized_malloc(void)
{
    GC_init_finalized_malloc();
    make_finalized_malloc();
    collect();
    GC_invoke_finalizers();
    CHECK(closure_ran == 1);
}

static void *thread_main(void *arg)
{
    void **list = GC_MALLOC(100 * sizeof(void *));
    for (int i = 0; i < 100; i++) {
        list[i] = GC_MALLOC_ATOMIC(100);
        memset(list[i], i, 100);
    }
    GC_gcollect();
    for (int i = 0; i < 100; i++)
        CHECK(((unsigned char *)list[i])[99] == i);
    return arg;
}

static void test_threads(void)
{
    pthread_t t[4];
    for (long i = 0; i < 4; i++)
        CHECK(GC_pthread_create(&t[i], 0, thread_main, (void *)i) == 0);
    for (long i = 0; i < 4; i++) {
        void *r;
        CHECK(GC_pthread_join(t[i], &r) == 0);
        CHECK(r == (void *)i);
    }
}

static void *GC_CALLBACK with_base(struct GC_stack_base *sb, void *arg)
{
    CHECK(sb->mem_base != 0);
    return arg;
}

static void test_misc(void)
{
    char *s = GC_STRDUP("hello");
    CHECK(strcmp(s, "hello") == 0);
    CHECK(GC_size(s) >= 6);
    CHECK(GC_base(s + 3) == s);
    CHECK(GC_is_heap_ptr(s));
    int *a = GC_MALLOC_ATOMIC(10 * sizeof(int));
    for (int i = 0; i < 10; i++)
        CHECK(a[i] == 0);
    a = GC_REALLOC(a, 1000 * sizeof(int));
    CHECK(a[999] == 0);

    GC_word bm[1] = {0};
    GC_set_bit(bm, 0);
    GC_descr d = GC_make_descriptor(bm, 2);
    void **typed = GC_MALLOC_EXPLICITLY_TYPED(2 * sizeof(void *), d);
    typed[0] = s;
    CHECK(GC_calloc_explicitly_typed(4, 16, d) != 0);

    unsigned kind = GC_new_kind(GC_new_free_list(), GC_MAKE_PROC(GC_new_proc(0), 0), 0, 1);
    void **k = GC_generic_malloc(32, (int)kind);
    k[0] = s;
    void *many = GC_malloc_many(32);
    int count = 0;
    for (void *p = many; p; p = GC_NEXT(p))
        count++;
    CHECK(count > 0);

    size_t before = GC_get_gc_no();
    collect();
    CHECK(GC_get_gc_no() > before);
    CHECK(GC_get_heap_size() > 0);
    CHECK(GC_get_total_bytes() > 0);
    CHECK(strcmp(typed[0], "hello") == 0);
    CHECK(strcmp(k[0], "hello") == 0);

    struct GC_stack_base sb;
    CHECK(GC_get_stack_base(&sb) == GC_SUCCESS);
    CHECK(GC_call_with_stack_base(with_base, (void *)5) == (void *)5);
    CHECK(GC_register_my_thread(&sb) == GC_SUCCESS);
    CHECK(GC_register_my_thread(&sb) == GC_DUPLICATE);
    CHECK(GC_unregister_my_thread() == GC_SUCCESS);
    GC_add_roots(a, a + 10);
    GC_enable_incremental();
    GC_disable();
    GC_enable();
    GC_FREE(s);
    GC_FREE(0);
}

int main(void)
{
    GC_INIT();
    test_misc();
    test_finalizers();
    test_resurrection();
    test_links();
    test_uncollectable();
    test_finalize_on_demand();
    test_finalized_malloc();
    test_threads();
    if (failures) {
        printf("%d failures\n", failures);
        return 1;
    }
    printf("all FUGC libgc tests passed\n");
    return 0;
}
