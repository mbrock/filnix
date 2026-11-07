// Shared child isolation for the native contracts in docs/libc-contracts.md.
// A signal alone is insufficient: require a Fil-C diagnostic too.
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>
static int libc_traps(void (*f)(void)) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]);
        dup2(fd[1], 2);
        close(fd[1]);
        f();
        _exit(0);
    }
    close(fd[1]);
    char buf[4096];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof buf - 1 && (r = read(fd[0], buf + n, sizeof buf - 1 - n)) > 0) n += r;
    buf[n] = 0;
    close(fd[0]);
    int st = 0;
    if (child < 0 || waitpid(child, &st, 0) != child) return 0;
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP && strstr(buf, "filc safety error:") != 0;
}
static void answer(const char *claim, int ok) {
    printf("%s: %s\n", claim, ok ? "yes" : "no");
}
