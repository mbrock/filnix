// Runtime axiom "Safepoints" (docs/runtime-axioms.md): this thread's
// signal handlers run only at safepoints (calls, pollchecks and the
// rest), never inside a straight-line checked region. A timer's handler
// frees the object a loop reads; the loop must keep reading its bytes
// until a safepoint lets the handler run, and then trap at its next
// check. The obvious wrong strengthening, that a handler never frees
// between a check and its access, holds only within one iteration.
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/time.h>
#include <sys/wait.h>
static long *obj;
static void on_alarm(int sig) { (void)sig; free(obj); }
static void loop(void) {
    signal(SIGALRM, on_alarm);
    struct itimerval t = { { 0, 0 }, { 0, 2000 } };
    setitimer(ITIMER_REAL, &t, 0);
    for (long n = 0; n < 4000000000L; n++)
        if (obj[n & 7] != (n & 7) + 100) { printf("garbage\n"); _exit(1); }
    _exit(2);
}
int main(void) {
    obj = malloc(64);
    for (int i = 0; i < 8; i++) obj[i] = i + 100;
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); loop(); }
    int st;
    waitpid(c, &st, 0);
    printf("the loop read only the object's bytes, then trapped: %s\n",
           WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP ? "yes" : "no");
    return 0;
}
