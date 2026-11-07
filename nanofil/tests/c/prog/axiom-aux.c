// Runtime axiom "Aux round-trip" (docs/runtime-axioms.md): a pointer
// store records its capability, and a pointer load returns it, or the
// free singleton's when the collector found the object freed. Either
// way a loaded pointer to a freed object traps, and its address is the
// one stored. The obvious wrong strengthening, that a load returns
// exactly the capability stored, cannot be observed from C; what can
// is that the loaded capability never reads freed memory.
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <stdfil.h>
struct holder { long *p; };
static struct holder *dead, *live;
static void read_dead(void) { volatile long x = dead->p[0]; (void)x; }
static int trapped(void (*f)(void)) {
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); f(); _exit(0); }
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP;
}
int main(void) {
    dead = malloc(sizeof *dead);
    live = malloc(sizeof *live);
    dead->p = malloc(16);
    dead->p[0] = 7;
    live->p = malloc(16);
    live->p[0] = 9;
    uintptr_t a = (uintptr_t)dead->p;
    free(dead->p);
    for (int round = 0; round < 3; round++) {
        for (int k = 0; k < 2000; k++) { long *g = malloc(16); g[0] = k; }
        zgc_request_and_wait();
    }
    printf("a live pointer loads back and reads: %s\n", live->p[0] == 9 ? "yes" : "no");
    printf("a freed pointer loads back at its address: %s\n",
           (uintptr_t)dead->p == a ? "yes" : "no");
    printf("and traps: %s\n", trapped(read_dead) ? "yes" : "no");
    return 0;
}
