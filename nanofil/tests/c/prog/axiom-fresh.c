// Runtime axiom "Fresh allocation" (docs/runtime-axioms.md): a new
// object reads as zero and is a new identity. Its address may be a
// freed object's: the obvious wrong strengthening, that two objects
// never share an address over time, is false natively. So the probe
// asks only that the old capability still traps after collections and
// many allocations of its size, wherever they landed.
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <stdfil.h>
static long *old;
static void read_old(void) { volatile long x = old[0]; (void)x; }
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
    old = malloc(64);
    for (int i = 0; i < 8; i++) old[i] = 0x5a5a5a5a + i;
    free(old);
    zgc_request_and_wait();
    zgc_request_and_wait();
    int zeroed = 1;
    for (int k = 0; k < 4096; k++) {
        unsigned char *q = malloc(64);
        for (int i = 0; i < 64; i++) if (q[i]) zeroed = 0;
        for (int i = 0; i < 64; i++) q[i] = 0xa5;
        if (k % 1024 == 0) zgc_request_and_wait();
    }
    printf("new objects read zero: %s\n", zeroed ? "yes" : "no");
    printf("the freed object's capability traps: %s\n", trapped(read_old) ? "yes" : "no");
    return 0;
}
