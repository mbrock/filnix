// timeout: 120
/* Every access size against objects of the boundary lengths from 0 to
   17 bytes and a freed one, at the offsets near its ends from 9 bytes
   below it to 2 past it: one bit per offset, 1 when the access traps
   (writes of 1 and 8 bytes only). The bounds
   check's shapes (default and --bounds=merged, docs/bounds.md) must
   agree with filcc on each, in particular for an object shorter than
   the access, where a merged comparison without its borrow test would
   pass. Each access runs in its own child. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <sys/wait.h>

static volatile long sink;

static void access_at(char *p, int size, int write) {
    switch (size * 2 + write) {
    case 2: sink = *(volatile char *)p; break;
    case 3: *(volatile char *)p = 1; break;
    case 4: sink = *(volatile short *)p; break;
    case 5: *(volatile short *)p = 1; break;
    case 8: sink = *(volatile int *)p; break;
    case 9: *(volatile int *)p = 1; break;
    case 16: sink = *(volatile long *)p; break;
    case 17: *(volatile long *)p = 1; break;
    }
}

static int traps(char *base, long off, int n, int size, int write) {
    if (n >= 0 && off >= 0 && off + size <= n) {
        /* Within bounds: a trap here stops the whole program, which the
           comparison with filcc reports too, so no child is needed. */
        access_at(base + off, size, write);
        return 0;
    }
    pid_t pid = fork();
    if (pid == 0) {
        freopen("/dev/null", "w", stderr);
        access_at(base + off, size, write);
        _exit(0);
    }
    int st;
    waitpid(pid, &st, 0);
    return !(WIFEXITED(st) && WEXITSTATUS(st) == 0);
}

int main(void) {
    static const int sizes[] = { 1, 2, 4, 8 };
    static const int lens[] = { -1, 0, 1, 2, 3, 4, 7, 8, 9, 16, 17 };
    for (int l = 0; l < 11; l++) {
        int len = lens[l];
        char *base = malloc(len < 0 ? 8 : len);
        if (len < 0) free(base);           /* -1: a freed object */
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
