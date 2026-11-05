// Each mode tries one way to reach a sealed closure's data from outside its
// body. Every one must stop with a Fil-C safety error before printing LEAK.
#include <stdfil.h>
#include <stdio.h>
#include <string.h>

static int secret = 42;

static int body(void)
{
    return *(int*)zcallee_closure_data();
}

static void* get_self(void)
{
    return zclosure_get_data(zcallee());
}

static int peek(void)
{
    return 0;
}

// Reachable by others and calls the body directly. If the body were inlined
// here, its zcallee_closure_data would read whatever closure wraps this.
int helper(void)
{
    return body();
}

int main(int argc, char** argv)
{
    int (*sealed)(void) = zclosure_new_sealed(body, &secret);
    ZASSERT(sealed() == 42);
    const char* mode = argc > 1 ? argv[1] : "";
    if (!strcmp(mode, "get")) {
        printf("LEAK %d\n", *(int*)zclosure_get_data(sealed));
    } else if (!strcmp(mode, "set")) {
        static int forged = 7;
        zclosure_set_data(sealed, &forged);
        printf("LEAK %d\n", sealed());
    } else if (!strcmp(mode, "rebind")) {
        // Running the sealed code on forged data.
        static int forged = 7;
        int (*rebound)(void) = zclosure_new(sealed, &forged);
        printf("LEAK %d\n", rebound());
    } else if (!strcmp(mode, "rebind-sealed")) {
        static int forged = 7;
        int (*rebound)(void) = zclosure_new_sealed(sealed, &forged);
        printf("LEAK %d\n", rebound());
    } else if (!strcmp(mode, "get-self")) {
        // Inside the body, only zcallee_closure_data reads the data.
        void* (*self)(void) = zclosure_new_sealed(get_self, &secret);
        printf("LEAK %p\n", self());
    } else if (!strcmp(mode, "read")) {
        // A function pointer is not readable memory.
        printf("LEAK %d\n", ((volatile int*)(void*)sealed)[8]);
    } else if (!strcmp(mode, "inline")) {
        // Running the sealed body on forged data through a function that
        // calls it.
        static int forged = 7;
        int (*evil)(void) = zclosure_new(helper, &forged);
        printf("LEAK %d\n", evil());
    } else if (!strcmp(mode, "plain")) {
        // Plain functions are not closures at all.
        printf("LEAK %p\n", zclosure_get_data(peek));
    } else {
        return 2;
    }
    return 0;
}
