#include <assert.h>
#include <dlfcn.h>
#include <pthread.h>
#include <stdlib.h>
#include <stdfil.h>

static void (*encode)(char *, size_t, void *);
static int (*decode)(const char *, void **);

static int successor(int value) { return value + 1; }

static void *worker(void *unused)
{
    (void)unused;
    int values[2] = {0, 42};
    char text[64];
    for (unsigned i = 0; i < 1000; ++i) {
        void *pointer = NULL;
        encode(text, sizeof(text), &values[1]);
        assert(decode(text, &pointer) == 1);
        assert(pointer == &values[1] && *(int *)pointer == 42);
    }
    return NULL;
}

int main(void)
{
    void *a = dlopen("./pointer-a.so", RTLD_NOW | RTLD_LOCAL);
    void *b = dlopen("./pointer-b.so", RTLD_NOW | RTLD_LOCAL);
    assert(a && b && a != b);
    encode = dlsym(a, "encode");
    decode = dlsym(b, "decode");
    assert(encode && decode);

    /* Race first initialization and round-trip interior pointers. */
    pthread_t threads[4];
    for (unsigned i = 0; i < 4; ++i)
        assert(pthread_create(&threads[i], NULL, worker, NULL) == 0);
    for (unsigned i = 0; i < 4; ++i)
        assert(pthread_join(threads[i], NULL) == 0);

    char text[64];
    void *pointer;
    encode(text, sizeof(text), (void *)successor);
    assert(decode(text, &pointer) == 1);
    assert(((int (*)(int))pointer)(41) == 42);
    encode(text, sizeof(text), NULL);
    assert(decode(text, &pointer) == 1 && pointer == NULL);
    assert(decode("pointer:1", &pointer) == 0);
    assert(decode("pointer:", &pointer) == 0);
    assert(decode("pointer:123junk", &pointer) == 0);
    assert(decode("pointer:ffffffffffffffffffffffff", &pointer) == 0);
    pointer = malloc(16);
    encode(text, sizeof(text), pointer);
    free(pointer);
    assert(decode(text, &pointer) == 0);

    dlclose(b);
    dlclose(a);
    return 0;
}
