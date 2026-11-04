/* Renewal by the hull of two checks (docs/forward.md) of a read-only
   string: after the call, the write of m[2] is a flag test reading the
   checks of m[0] and m[4], and must trap with the full check's
   "read-only" text. */
// args: 1
#include <stdio.h>
#include <stdlib.h>
static void __attribute__((noinline)) note(int k) { printf("%d\n", k); fflush(stdout); }
static int __attribute__((noinline)) poke(char *m, int k) {
    int t = m[0] + m[4];
    note(t);
    if (k) m[2] = 'x';
    return t;
}
int main(int argc, char **argv) {
    char buf[8] = "hello";
    poke(buf, 1);
    return poke((char *)"hello", argc > 1 ? atoi(argv[1]) : 0) & 1;
}
