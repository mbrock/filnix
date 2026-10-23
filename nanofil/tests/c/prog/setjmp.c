// link: lib/setjmp-mask.c
/* Nonlocal returns, mutable locals, independent buffers and GC. */
#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

static jmp_buf a, b;
static int stage;
void mask_set(int blocked);
int mask_is_set(void);

static void nested(int depth, int value)
{
    char *p = malloc(32);
    p[0] = 17;
    if (depth)
        nested(depth - 1, value);
    zgc_request_and_wait();
    if (p[0] != 17)
        abort();
    _longjmp(a, value);
}

static void locals(void)
{
    volatile int changed = 3;
    int stable = 9;
    volatile int addressed = 4;
    volatile int *volatile addr = &addressed;
    char *volatile p = malloc(32);
    p[0] = 21;
    if (_setjmp(a) == 0) {
        changed = 7;
        *addr = 11;
        p = malloc(32);
        p[0] = 42;
        nested(3, 0);
    }
    zgc_request_and_wait();
    printf("locals %d %d %d %d\n", changed, stable, *addr, p[0]);
    if (changed != 7 || stable != 9 || *addr != 11 || p[0] != 42)
        abort();
}

static void buffers(void)
{
    if (setjmp(a) == 0) {
        if (setjmp(b) == 0) {
            stage = 1;
            longjmp(a, 257);
        }
        stage = 3;
        longjmp(a, 1025);
    }
    if (stage == 1) {
        stage = 2;
        zgc_request_and_wait();
        longjmp(b, 513);
    }
    printf("buffers %d\n", stage);
    if (stage != 3)
        abort();
}

static void repeat(void)
{
    volatile int n = 0;
    volatile int result;
    mask_set(1);
    result = sigsetjmp(a, 1);
    if (n++ < 4) {
        if (!mask_is_set())
            abort();
        mask_set(0);
        zgc_request_and_wait();
        siglongjmp(a, 259);
    }
    printf("repeat %d %d\n", n, result);
    if (n != 5 || result != 259)
        abort();
    mask_set(0);
    if (sigsetjmp(a, 0) == 0) {
        mask_set(1);
        siglongjmp(a, 1);
    }
    if (!mask_is_set())
        abort();
    mask_set(0);
}

/* Reexecuting one static site must replace, not retain, its mask policy. */
static void mask_recreate(int first)
{
    volatile int save = first;
    volatile int iteration = 0;
    mask_set(1);
    for (;;) {
        if (sigsetjmp(a, save))
            break;
        if (!iteration++) {
            save = !first;
            mask_set(!first);
        } else {
            mask_set(0);
            zgc_request_and_wait();
            siglongjmp(a, 1);
        }
    }
    printf("mask recreate %d %d\n", first, mask_is_set());
    if (mask_is_set() != !first)
        abort();
    mask_set(0);
}

/* Both user buffers alias the latest execution of one static site. The
   volatile index/pointee deliberately keep their intervening changes;
   the IR test separately asserts compiler temp/phi snapshot values. */
static void loop(void)
{
    static jmp_buf saved[2];
    volatile int i;
    char *volatile p = malloc(16);
    for (i = 0; i < 2; i++) {
        p[0] = i + 30;
        int result = _setjmp(saved[i]);
        if (result) {
            zgc_request_and_wait();
            printf("loop %d %d %d\n", i, result, p[0]);
            if (i != 2 || result != -257 || p[0] != 31)
                abort();
            return;
        }
        zgc_request_and_wait();
    }
    _longjmp(saved[0], -257);
}

int main(void)
{
    locals();
    buffers();
    repeat();
    loop();
    mask_recreate(1);
    mask_recreate(0);
    return 0;
}
