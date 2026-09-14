/* Exercise contended pointer bit locks, including pointer capability reloads. */
#include <glib.h>
#include <glib-object.h>

static gpointer slot;
static int values[2];
static unsigned count;
static GWeakRef weak;
static GObject *object;

static gpointer weak_worker(gpointer unused)
{
    (void)unused;
    for (unsigned i = 0; i < 4000; ++i) {
        GObject *strong = g_weak_ref_get(&weak);
        g_assert_true(strong == object);
        g_object_unref(strong);
    }
    return NULL;
}

static gpointer worker(gpointer unused)
{
    (void)unused;
    for (unsigned i = 0; i < 20000; ++i) {
        gpointer locked;
        g_pointer_bit_lock_and_get(&slot, 0, &locked);
        int *value = (int *)((char *)locked - 1);
        ++*value;
        ++count;
        g_pointer_bit_unlock_and_set(&slot, 0, &values[count % 2], 0);
    }
    return NULL;
}

int main(void)
{
    GThread *threads[4];
    slot = &values[0];
    for (unsigned i = 0; i < G_N_ELEMENTS(threads); ++i)
        threads[i] = g_thread_new("bitlock", worker, NULL);
    for (unsigned i = 0; i < G_N_ELEMENTS(threads); ++i)
        g_thread_join(threads[i]);
    g_assert_cmpuint(count, ==, 80000);
    g_assert_cmpint(values[0] + values[1], ==, 80000);

    /* This path unlocks without replacing the pointer. Contention must not
     * sleep on stale ordinary bytes while the atomic pointer is unlocked. */
    GThread *weak_threads[48];
    object = g_object_new(G_TYPE_OBJECT, NULL);
    g_weak_ref_init(&weak, object);
    for (unsigned i = 0; i < G_N_ELEMENTS(weak_threads); ++i)
        weak_threads[i] = g_thread_new("weak-ref", weak_worker, NULL);
    for (unsigned i = 0; i < G_N_ELEMENTS(weak_threads); ++i)
        g_thread_join(weak_threads[i]);
    g_object_unref(object);
    g_assert_null(g_weak_ref_get(&weak));
    g_weak_ref_clear(&weak);
    return 0;
}
