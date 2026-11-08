// Runtime axiom "Free keeps identities" (docs/runtime-axioms.md): free
// empties an object's bounds in place and reclaims nothing; only the
// collector reclaims, at a safepoint. Right after a free, while no
// collection runs (about 320 KiB with headers, below FUGC's 1 MiB trigger;
// the test checks that none started), thousands of allocations of the
// freed object's size never take its address, the freed pointer's
// capability traps, and another object is untouched.
//
// The obvious wrong strengthening, that free leaves every region as it
// was, is refuted by the trap. The address check is a consequence of the
// axiom, not a sharp test of it: libpas parks deallocations in a log, so
// a runtime whose free handed the slot back might still pass it. After a
// collection the address may recur: the static pointer is redirected to
// the free singleton and the object reclaimed; the capability still traps.
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <stdfil.h>
static long *held;
static void read_held(void) { volatile long x = held[0]; (void)x; }
// trapped(f): f, run in a child whose stderr is closed, ends in a Fil-C
// trap (SIGTRAP), not a normal exit.
static int trapped(void (*f)(void)) {
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); f(); _exit(0); }
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP;
}
int main(void) {
    held = malloc(64);
    long *other = malloc(64);
    for (int i = 0; i < 8; i++) { held[i] = 100 + i; other[i] = 200 + i; }
    volatile uintptr_t address = (uintptr_t)held;
    zgc_cycle_number before = zgc_requested_cycle();
    free(held);
    int taken = 0;
    for (int k = 0; k < 4096; k++) {
        long *q = malloc(64);
        volatile uintptr_t qa = (uintptr_t)q;
        if (qa == address) taken = 1;
        memset(q, 0xa5, 64);
    }
    printf("no collection ran during the allocations: %s\n", zgc_requested_cycle() == before ? "yes" : "no");
    printf("no allocation after a free takes the freed object's address: %s\n", taken ? "no" : "yes");
    printf("the freed pointer's capability traps: %s\n", trapped(read_held) ? "yes" : "no");
    zgc_request_and_wait();
    printf("and still traps after a collection: %s\n", trapped(read_held) ? "yes" : "no");
    int intact = 1;
    for (int i = 0; i < 8; i++) if (other[i] != 200 + i) intact = 0;
    printf("another object reads unchanged: %s\n", intact ? "yes" : "no");
    return 0;
}
