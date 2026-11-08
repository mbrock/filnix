// Runtime axiom "Free is checked" (docs/runtime-axioms.md): free frees a
// live heap object through its base, accepts a null pointer, and traps on
// the other pointers below; it never goes on having done something else.
// The obvious wrong strengthening, that free never traps, is false: an
// interior pointer, a second free and a global's address all trap. (Free
// of an escaping local's address returns natively, where the model traps
// `invalid_free`; docs/runtime-axioms.md records it.)
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <signal.h>
#include <sys/wait.h>
#include <stdfil.h>
static long *volatile target;
static long global[4];
static void free_target(void) { free(target); }
static void read_target(void) { volatile long x = target[0]; (void)x; }
static void free_twice(void) { free(target); free(target); }
static void free_after_collection(void) { free(target); zgc_request_and_wait(); free(target); }
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
static const char *yes(int b) { return b ? "yes" : "no"; }
int main(void) {
    target = 0;
    printf("free of null returns: %s\n", yes(!trapped(free_target)));
    long *p = malloc(32);
    target = p;
    printf("free of a live object returns: %s\n", yes(!trapped(free_target)));
    free(p);
    printf("its capability then traps: %s\n", yes(trapped(read_target)));
    target = malloc(32);
    printf("a second free traps: %s\n", yes(trapped(free_twice)));
    target = malloc(32);
    printf("a second free after a collection traps: %s\n", yes(trapped(free_after_collection)));
    target = (long *)malloc(32) + 1;
    printf("free of an interior pointer traps: %s\n", yes(trapped(free_target)));
    target = global;
    printf("free of a global traps: %s\n", yes(trapped(free_target)));
    return 0;
}
