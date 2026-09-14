/* Exercise contended pointer bit locks, including pointer capability reloads. */
#include <glib.h>

static gpointer slot;
static int values[2];
static unsigned count;

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
    return 0;
}
