/* An integer ?: converted to a pointer takes the capability of the arm it
   selects, as Fil-C's select does: emacs's pointer_align is
   (void *) ROUNDUP ((uintptr_t) ptr, alignment), and ROUNDUP tests
   whether the alignment is a power of two. nanofil gave the result no
   capability, and emacs's make_pure_string trapped. Each case runs in its
   own child; a cast to a pointer to a VLA keeps its run-time length. */
#include <stdio.h>
#include <stdint.h>
#include <unistd.h>
#include <sys/wait.h>
#define POWER_OF_2(n) (((n) & ((n) - 1)) == 0)
#define ROUNDUP(x, y) (POWER_OF_2 (y) ? ((y) - 1 + (x)) & ~ ((y) - 1) \
                       : ((y) - 1 + (x)) - ((y) - 1 + (x)) % (y))
static long buf[16], other[16];
__attribute__((noinline)) static void *pointer_align(void *p, int a) { return (void *) ROUNDUP ((uintptr_t) p, a); }
__attribute__((noinline)) static char *pick(char *p, char *q, int c) { return (char *)(c ? (uintptr_t)p : (uintptr_t)q); }
__attribute__((noinline)) static char *or0(char *p, int c) { return (char *)(c ? (uintptr_t)p : 0); }
__attribute__((noinline)) static char *nested(char *p, char *q, int c, int d) {
    return (char *)(c ? (d ? (uintptr_t)p : (uintptr_t)q + 1) : 0);
}
static void run(int i) {
    char *b = (char *)buf + 3;
    switch (i) {
    case 0: *(long *)pointer_align(b, 8) = 42; printf("%ld\n", buf[1]); break;
    case 1: *pick(b, (char *)other, 1) = 1; *pick(b, (char *)other, 0) = 2;
            printf("%d %d\n", ((char *)buf)[3], ((char *)other)[0]); break;
    case 2: *or0(b, 1) = 5; printf("%d\n", ((char *)buf)[3]); break;
    case 3: *nested(b, (char *)other, 1, 0) = 6; printf("%d\n", ((char *)other)[1]); break;
    case 4: { int n = 5; int (*v)[n] = (int (*)[n])(n ? (uintptr_t)buf : (uintptr_t)other);
              printf("%zu %d %zu\n", sizeof *v, (int)((char *)(v + 1) - (char *)buf),
                     sizeof *(int (*)[n])(n ? (uintptr_t)buf : (uintptr_t)other)); break; }
    }
}
int main(void) {
    for (int i = 0; i < 5; i++) {
        fflush(stdout);
        if (fork() == 0) { run(i); fflush(stdout); _exit(0); }
        int st; wait(&st); printf("case %d: %s\n", i, WIFSIGNALED(st) ? "signal" : "exit");
    }
    return 0;
}
