/* Fil-C infers pointer-as-int laundering on SSA after the optimizer has
   promoted locals, so a pointer converted to an integer, kept in a
   local integer variable whose address is never taken, and converted
   back keeps its capability: bind's qp_test stores a key as
   uintptr_t pval = (uintptr_t)str and inserts (void *)pval. nanofil
   follows a variable defined once; one defined twice may be a min or
   max clang makes a call (llvm.umin), which has none. What goes through
   memory (an address-taken or volatile local, a global) or a call, or
   merges two pointers, has none, and dereferencing it traps. Each case
   runs in its own child. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>
#include <stdfil.h>
static volatile uintptr_t zero;          /* 0, unknown to the optimizer */
static volatile uintptr_t cell;
static uintptr_t *volatile sink;
__attribute__((noinline)) static uintptr_t opaque(uintptr_t v) { return v + zero; }

/* Keeps the capability. */
__attribute__((noinline)) static char *qp(char *str) {
    uintptr_t pval = (uintptr_t)str;
    return (char *)pval;
}
__attribute__((noinline)) static long *arith(long *p) {
    uintptr_t v = ((uintptr_t)p + 2 * sizeof(long) + 3) & ~(uintptr_t)7;
    return (long *)v;
}
__attribute__((noinline)) static char *branch(char *a, char *b, int c) {
    if (c) { uintptr_t v = (uintptr_t)a; return (char *)v; }
    uintptr_t w;
    w = (uintptr_t)b + 4;
    return (char *)w;
}
__attribute__((noinline)) static char *loop(char *a, int n) {
    char *r = 0;
    for (int i = 0; i < n; i++) {
        uintptr_t v = (uintptr_t)(a + i);
        r = (char *)(v - (v & 1));
    }
    return r;
}
__attribute__((noinline)) static char *copies(char *a) {
    uintptr_t v = (uintptr_t)a;
    intptr_t w = v;
    unsigned long long u = w + 2;
    return (char *)(uintptr_t)u;
}
__attribute__((noinline)) static char *offset(char *buf) {
    size_t off = opaque(3);
    return (char *)((uintptr_t)buf + off);
}
__attribute__((noinline)) static char *scoped(char *a, char *b) {
    uintptr_t v = (uintptr_t)a;
    {
        uintptr_t v = (uintptr_t)b + zero;
        (void)v;
    }
    return (char *)(v + 1);
}

/* Loses it. */
__attribute__((noinline)) static char *addressed(char *a) {
    uintptr_t v = (uintptr_t)a;
    sink = &v;
    *sink = *sink;
    return (char *)v;
}
__attribute__((noinline)) static char *volatile_local(char *a) {
    volatile uintptr_t v = (uintptr_t)a;
    return (char *)v;
}
__attribute__((noinline)) static char *memory(char *a) {
    cell = (uintptr_t)a;
    uintptr_t v = cell;
    return (char *)v;
}
__attribute__((noinline)) static char *called(char *a) {
    uintptr_t v = opaque((uintptr_t)a);
    return (char *)v;
}
__attribute__((noinline)) static char *two(char *a, char *b) {
    uintptr_t v = (uintptr_t)a, w = (uintptr_t)b;
    return (char *)(v + (w & zero));
}
__attribute__((noinline)) static char *two_in_local(char *a, char *b, char *c) {
    uintptr_t t = (uintptr_t)a + ((uintptr_t)b & zero);
    return (char *)((uintptr_t)c + (t & zero));
}
__attribute__((noinline)) static char *accumulated(char *a, char *b, int n) {
    uintptr_t v = (uintptr_t)a;
    for (int i = 0; i < n; i++) v += (uintptr_t)b & zero;
    return (char *)v;
}
__attribute__((noinline)) static char *argument(uintptr_t x) { return (char *)x; }
/* Defined twice: nanofil gives none, as for these Fil-C does. */
__attribute__((noinline)) static char *reassigned(char *a, int c) {
    uintptr_t v = (uintptr_t)a;
    if (c) v = opaque(v);
    return (char *)v;
}
__attribute__((noinline)) static char *param(uintptr_t x, char *a) {
    if (x > (uintptr_t)a) x = (uintptr_t)a;
    return (char *)x;
}
__attribute__((noinline)) static char *other_dest(char *p, uintptr_t lim) {
    uintptr_t x = (uintptr_t)p, m;
    if (x < lim) m = x; else m = lim;
    return (char *)m;
}
/* clang -O1 makes these llvm.umin, umax, smin or usub.sat, calls. */
__attribute__((noinline)) static char *clamp(char *p, size_t n, size_t len) {
    uintptr_t cur = (uintptr_t)p + n, end = (uintptr_t)p + len;
    if (cur > end) cur = end;
    return (char *)cur;
}
__attribute__((noinline)) static char *minimum(char *p, uintptr_t lim) {
    uintptr_t x = (uintptr_t)p;
    return (char *)(x < lim ? x : lim);
}
__attribute__((noinline)) static char *direct_minimum(char *p, uintptr_t lim) {
    return (char *)((uintptr_t)p < lim ? (uintptr_t)p : lim);
}
__attribute__((noinline)) static char *loop_min(char *p, uintptr_t *a, int n) {
    uintptr_t x = (uintptr_t)p;
    for (int i = 0; i < n; i++) if (a[i] < x) x = a[i];
    return (char *)x;
}
__attribute__((noinline)) static char *saturate(char *p, uintptr_t k) {
    uintptr_t x = (uintptr_t)p + 20;
    if (x > k) x -= k; else x = 0;
    return (char *)x;
}
static inline int below(uintptr_t a, uintptr_t b) { return a < b; }
__attribute__((noinline)) static char *inlined_min(char *p, uintptr_t lim) {
    uintptr_t x = (uintptr_t)p;
    return (char *)(below(x, lim) ? x : lim);
}
/* Not a min or max: Fil-C's select keeps the arm's capability. */
__attribute__((noinline)) static char *not_min(char *p, uintptr_t lim) {
    return (char *)((uintptr_t)p > lim ? (uintptr_t)p - 8 : (uintptr_t)p);
}
/* Converting to _Bool compares. */
__attribute__((noinline)) static char *boolean(char *p) {
    _Bool b = (uintptr_t)p;
    return (char *)(uintptr_t)b;
}

static char buf[64], other[64];
static void run(int i) {
    switch (i) {
    case 0: printf("qp %c\n", *qp(buf)); break;
    case 1: { long l[4] = { 1, 2, 3, 4 }; printf("arith %ld\n", *arith(l)); break; }
    case 2: printf("branch %c %c\n", *branch(buf, other, 1), *branch(buf, other, 0)); break;
    case 3: printf("loop %c\n", *loop(buf, 6)); break;
    case 4: printf("copies %c\n", *copies(buf)); break;
    case 5: printf("offset %c\n", *offset(buf)); break;
    case 6: printf("scoped %c\n", *scoped(buf, other)); break;
    case 7: printf("addressed %c\n", *addressed(buf)); break;
    case 8: printf("volatile %c\n", *volatile_local(buf)); break;
    case 9: printf("memory %c\n", *memory(buf)); break;
    case 10: printf("called %c\n", *called(buf)); break;
    case 11: printf("two %c\n", *two(buf, other)); break;
    case 12: printf("two in local %c\n", *two_in_local(buf, other, buf)); break;
    case 13: printf("accumulated %c\n", *accumulated(buf, other, 3)); break;
    case 14: printf("argument %c\n", *argument((uintptr_t)buf)); break;
    case 15: printf("reassigned %c\n", *reassigned(buf, 1)); break;
    case 16: printf("param %c\n", *param((uintptr_t)-1, buf)); break;
    case 17: printf("other dest %c\n", *other_dest(buf, (uintptr_t)-1)); break;
    case 18: printf("clamp %c\n", *clamp(buf, 8, 16)); break;
    case 19: printf("minimum %c\n", *minimum(buf + 4, (uintptr_t)-1)); break;
    case 20: printf("direct minimum %c\n", *direct_minimum(buf + 4, (uintptr_t)-1)); break;
    case 21: { uintptr_t a[2] = { (uintptr_t)-1, (uintptr_t)-2 };
               printf("loop min %c\n", *loop_min(buf, a, 2)); break; }
    case 22: printf("saturate %c\n", *saturate(buf, 10)); break;
    case 23: printf("boolean %d\n", zgetlower(boolean(buf)) != 0); break;
    case 24: printf("not min %c\n", *not_min(buf + 8, 0)); break;
    case 25: printf("inlined min %c\n", *inlined_min(buf, (uintptr_t)-1)); break;
    }
}
int main(void) {
    for (int i = 0; i < 64; i++) { buf[i] = 'a' + i % 26; other[i] = 'A' + i % 26; }
    for (int i = 0; i < 26; i++) {
        fflush(stdout);
        if (fork() == 0) {
            int fd = open("/dev/null", O_WRONLY);
            dup2(fd, 2);
            run(i);
            fflush(stdout);
            _exit(0);
        }
        int st;
        wait(&st);
        printf("case %d: %s\n", i, WIFSIGNALED(st) ? "signal" : WEXITSTATUS(st) ? "trap" : "exit");
    }
    return 0;
}
