// Runtime axiom "Lifetime" (docs/runtime-axioms.md): bounds change only
// at free, which empties them for every alias at once, and nothing else
// touches an object's header. The probe frees through an alias between
// a checked read and the next read through the other pointer: that read
// must trap. The obvious wrong strengthening, that no free comes
// between a check and its access, would let it read the old bytes.
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
static long *a, *b, *other;
static void read_after_alias_free(void) {
    volatile long x = a[0];
    free(b);
    volatile long y = a[1];
    (void)x; (void)y;
}
static int trapped(void (*f)(void)) {
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); f(); _exit(0); }
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP;
}
int main(void) {
    a = malloc(16);
    a[0] = 1; a[1] = 2;
    b = a;
    other = malloc(16);
    other[0] = 3; other[1] = 4;
    printf("a read after a free through its alias traps: %s\n",
           trapped(read_after_alias_free) ? "yes" : "no");
    free(b);
    printf("freeing one object leaves another intact: %s\n",
           other[0] == 3 && other[1] == 4 ? "yes" : "no");
    return 0;
}
