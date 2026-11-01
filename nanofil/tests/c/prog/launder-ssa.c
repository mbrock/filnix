/* Where nanofil's laundering keeps more than filcc's: both apply Fil-C's
   rules (one capability source survives integer arithmetic; two merge
   into none; loads, calls and comparisons give none), but nanofil
   reads them on the SSA form of the source program at every level
   (launder.pl), not on what clang -O1 made of it. clang turns these
   selects into llvm.umin, umax or usub.sat, calls that Fil-C gives no
   capability, so filcc traps on each; nanofil keeps, at a phi, the
   capability of the value that arrives, as Fil-C does for a phi that
   stays one. The expected output, in
   launder-ssa.c.nanofil, follows from those rules, not from a run.
   The last cases show what a recovered capability does not change: a
   null one still traps, and the bounds are still checked. Each case
   runs in its own child. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <fcntl.h>
#include <unistd.h>
#include <sys/wait.h>

__attribute__((noinline)) static char *param(uintptr_t x, char *a) {
    if (x > (uintptr_t)a) x = (uintptr_t)a;
    return (char *)x;
}
__attribute__((noinline)) static char *other_dest(char *p, uintptr_t lim) {
    uintptr_t x = (uintptr_t)p, m;
    if (x < lim) m = x; else m = lim;
    return (char *)m;
}
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
/* Each arm brings its own capability. */
__attribute__((noinline)) static char *lesser(char *a, char *b) {
    uintptr_t x = (uintptr_t)a, y = (uintptr_t)b;
    return (char *)(x < y ? x : y);
}
/* A pointer walk in an integer. */
__attribute__((noinline)) static int walk(char *a, int n) {
    int sum = 0;
    for (uintptr_t v = (uintptr_t)a; v < (uintptr_t)a + n; v++) sum += *(char *)v;
    return sum;
}

static char buf[64], other[64];
static void run(int i) {
    switch (i) {
    case 0: printf("param %c\n", *param((uintptr_t)-1, buf)); break;
    case 1: printf("other dest %c\n", *other_dest(buf, (uintptr_t)-1)); break;
    case 2: printf("clamp %c\n", *clamp(buf, 8, 16)); break;
    case 3: printf("minimum %c\n", *minimum(buf + 4, (uintptr_t)-1)); break;
    case 4: printf("direct minimum %c\n", *direct_minimum(buf + 4, (uintptr_t)-1)); break;
    case 5: { uintptr_t a[2] = { (uintptr_t)-1, (uintptr_t)-2 };
              printf("loop min %c\n", *loop_min(buf, a, 2)); break; }
    case 6: printf("saturate %c\n", *saturate(buf, 10)); break;
    case 7: printf("inlined min %c\n", *inlined_min(buf, (uintptr_t)-1)); break;
    case 8: { char *r = lesser(buf, other);
              printf("lesser %d\n", (*r == 'a') + (*r == 'A')); break; }
    case 9: printf("walk %d\n", walk(buf, 5)); break;
    case 10: printf("null arm %c\n", *minimum(buf + 4, 0)); break;
    case 11: printf("past the end %d\n", walk(buf + 60, 8)); break;
    }
}
int main(void) {
    for (int i = 0; i < 64; i++) { buf[i] = 'a' + i % 26; other[i] = 'A' + i % 26; }
    for (int i = 0; i < 12; i++) {
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
