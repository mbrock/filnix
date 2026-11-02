// timeout: 120
/* edges.c's matrix with the access in a loop, where --checks=hoist
   tests it against a limit taken before the loop (docs/bounds.md): the
   object's base is the loop's invariant root and the offset is loaded
   in the loop, so no range guard covers it. Every access size against
   objects of the boundary lengths from 0 to 17 bytes, a freed one and
   null, at the offsets near its ends: one digit per offset, 1 when the
   access traps, 2 when it dies otherwise, such as by SIGSEGV from a
   header read at a null lower (writes of 1 and 8 bytes only). Every
   --bounds shape must agree with filcc on each. Each trapping access
   runs in its own child. Hoisting needs -O, which keeps the base in a
   register home. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>

static long sink;

#define READS(T, NAME)                                                 \
    static long NAME(char *base, const long *offs, int k) {           \
        long s = 0;                                                    \
        for (int i = 0; i < k; i++) s += *(T *)(base + offs[i]);       \
        return s;                                                      \
    }
#define WRITES(T, NAME)                                                \
    static void NAME(char *base, const long *offs, int k) {           \
        for (int i = 0; i < k; i++) *(T *)(base + offs[i]) = (T)i;     \
    }
READS(char, read1)
READS(short, read2)
READS(int, read4)
READS(long, read8)
WRITES(char, write1)
WRITES(long, write8)

/* Two iterations: an in-bounds first one when the object has one, so
   the loop really loops, then the offset under test. */
static void access_at(char *base, long first, long off, int size, int write) {
    long offs[2] = { first, off };
    int k = first < 0 ? 1 : 2;
    const long *o = first < 0 ? offs + 1 : offs;
    switch (size * 2 + write) {
    case 2: sink += read1(base, o, k); break;
    case 3: write1(base, o, k); break;
    case 4: sink += read2(base, o, k); break;
    case 8: sink += read4(base, o, k); break;
    case 16: sink += read8(base, o, k); break;
    case 17: write8(base, o, k); break;
    }
}

static int traps(char *base, long off, int n, int size, int write) {
    long first = n >= size ? 0 : -1;
    if (n >= 0 && off >= 0 && off + size <= n) {
        access_at(base, first, off, size, write);
        return 0;
    }
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        access_at(base, first, off, size, write);
        _exit(0);
    }
    int st;
    waitpid(pid, &st, 0);
    if (WIFEXITED(st) && WEXITSTATUS(st) == 0) return 0;
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP ? 1 : 2;
}

int main(void) {
    static const int sizes[] = { 1, 2, 4, 8 };
    static const int lens[] = { -2, -1, 0, 1, 2, 3, 4, 7, 8, 9, 16, 17 };
    for (int l = 0; l < 12; l++) {
        int len = lens[l];
        char *base = len == -2 ? NULL : malloc(len < 0 ? 8 : len);
        if (len == -1) free(base);         /* -1: a freed object, -2: null */
        int n = len < 0 ? 8 : len;
        for (int s = 0; s < 4; s++)
            for (int write = 0; write < 2; write++) {
                if (write && sizes[s] != 1 && sizes[s] != 8) continue;
                printf("len %2d size %d %s ", len, sizes[s], write ? "w" : "r");
                for (long off = -9; off <= n + 2; off++)
                    if (off <= -8 || (off >= -2 && off <= 1) || off >= n - 9)
                        putchar('0' + traps(base, off, len, sizes[s], write));
                putchar('\n');
                fflush(stdout);
            }
    }
    return 0;
}
