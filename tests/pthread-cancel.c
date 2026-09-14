/* Cancellation through a private libc, with the ordinary Fil-C toolchain. */
#include <assert.h>
#include <pthread.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static atomic_int ready;
static atomic_int cleaned;

static void cleanup(void *unused)
{
    (void)unused;
    atomic_fetch_add(&cleaned, 1);
}

static void *worker(void *unused)
{
    (void)unused;
    pthread_cleanup_push(cleanup, NULL);
    atomic_store(&ready, 1);
    for (;;)
        pthread_testcancel();
    pthread_cleanup_pop(1);
    return NULL;
}

int main(int argc, char **argv)
{
    assert(argc == 2);
    FILE *maps = fopen("/proc/self/maps", "r");
    assert(maps);
    char *line = NULL;
    size_t size = 0;
    unsigned found = 0;
    while (getline(&line, &size, maps) >= 0) {
        if (strstr(line, "/lib/libc.so.6666")) {
            assert(strstr(line, argv[1]));
            ++found;
        }
    }
    assert(!ferror(maps));
    fclose(maps);
    free(line);
    assert(found);

    pthread_t thread;
    assert(!pthread_create(&thread, NULL, worker, NULL));
    while (!atomic_load(&ready))
        ;
    assert(!pthread_cancel(thread));
    void *result;
    assert(!pthread_join(thread, &result));
    assert(result == PTHREAD_CANCELED);
    assert(atomic_load(&cleaned) == 1);
    puts("private libc loaded; cancellation and cleanup passed");
    return 0;
}
