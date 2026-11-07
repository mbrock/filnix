// Runtime axiom "Address space" (docs/runtime-axioms.md): no object ends
// past 2^48, libpas's address space, so no address inside one wraps and
// two addresses of one object are less than 2^63 apart. Heap objects,
// static and initialized data, and an address-taken local are checked. An allocation of more than
// 2^48 - 1 bytes traps ("attempt to allocate object that is too big"),
// and so may one below that limit that the address space cannot hold
// ("out of memory"): the obvious wrong strengthening, that every
// allocation within the size limit succeeds, is false natively, so the
// runtime's alloc may refuse. Each trap's message is checked, which pins
// the size limit at 2^48 - 1 (interp.pl's alloc_res/6).
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
static volatile unsigned long size;
static char zeroed[1 << 20];
static char initialized[256] = {1};
static void allocate(void) { volatile char *p = malloc(size); (void)p; }
// trapped_with(f, text): f, run in a child, ends in a Fil-C trap
// (SIGTRAP) whose safety error, on the child's stderr, says text.
static int trapped_with(void (*f)(void), const char *text) {
    fflush(stdout);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t c = fork();
    if (c == 0) { close(fd[0]); dup2(fd[1], 2); f(); _exit(0); }
    close(fd[1]);
    char buf[4096];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof buf - 1 && (r = read(fd[0], buf + n, sizeof buf - 1 - n)) > 0) n += r;
    buf[n] = 0;
    close(fd[0]);
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP && strstr(buf, text) != 0;
}
int main(void) {
    int below = 1;
    for (unsigned long n = 1; n <= 1ul << 30; n <<= 3) {
        char *p = malloc(n);
        if ((uintptr_t)p + n > 1ul << 48) below = 0;
        free(p);
    }
    printf("objects end below 2^48: %s\n", below ? "yes" : "no");
    char local[4096];
    char *volatile taken = local;
    int data = (uintptr_t)zeroed + sizeof zeroed <= 1ul << 48 &&
               (uintptr_t)initialized + sizeof initialized <= 1ul << 48 &&
               (uintptr_t)taken + sizeof local <= 1ul << 48;
    printf("data and locals end below 2^48: %s\n", data ? "yes" : "no");
    size = 1ul << 48;
    printf("malloc(2^48) traps as too big: %s\n",
           trapped_with(allocate, "attempt to allocate object that is too big") ? "yes" : "no");
    size = (1ul << 48) - 1;
    printf("malloc(2^48 - 1) traps out of memory: %s\n",
           trapped_with(allocate, "out of memory") ? "yes" : "no");
    return 0;
}
