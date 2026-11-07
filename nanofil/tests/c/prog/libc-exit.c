// cflags: -D_GNU_SOURCE -fno-builtin
// exit invokes handlers; _exit does not. Retained callback arguments
// must remain live, and finalize must not invoke the same handler twice.
#include <assert.h>
#include <fcntl.h>
#include "libc-probe.h"
extern int __cxa_atexit(void (*)(void *), void *, void *);
extern void __cxa_finalize(void *);
static int pipe_out;
static void record(void *p) { write(pipe_out, p, 1); }
static void on_exit_probe(void) { write(pipe_out, "E", 1); }
static void read_argument(void *p) { volatile char c = *(char *)p; (void)c; }
static void expired_argument(void) {
    static int tag;
    char *p = malloc(16);
    if (__cxa_atexit(read_argument, p, &tag)) _exit(0);
    free(p);
    __cxa_finalize(&tag);
}
static int stopped(int mode) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]); pipe_out = fd[1];
        dup2(fd[1], 2);
        if (atexit(on_exit_probe)) _exit(99);
        if (mode == 0) exit(23);
        if (mode == 1) _exit(24);
        if (mode == 2) abort();
        __assert_fail("probe", "libc-exit.c", 1, "stopped");
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
    if (mode == 0) return WIFEXITED(st) && WEXITSTATUS(st) == 23 && n == 1 && buf[0] == 'E';
    if (mode == 1) return WIFEXITED(st) && WEXITSTATUS(st) == 24 && n == 0;
    // This pin's abort uses zerror: SIGTRAP, but not a safety error.
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP &&
        strstr(buf, "filc user error: abort(3) called.") &&
        !strstr(buf, "filc safety error:") && buf[0] != 'E';
}
int main(void) {
    int fd[2];
    if (pipe(fd)) return 1;
    pipe_out = fd[1];
    static int dso;
    static char a = 'A', b = 'B';
    int good = __cxa_atexit(record, &a, &dso) == 0 && __cxa_atexit(record, &b, &dso) == 0;
    __cxa_finalize(&dso);
    __cxa_finalize(&dso);
    close(fd[1]);
    char bytes[3] = {0};
    ssize_t n = read(fd[0], bytes, 3);
    close(fd[0]);
    answer("finalize calls matching handlers once in reverse order", good && n == 2 && bytes[0] == 'B' && bytes[1] == 'A');
    answer("exit runs registered handlers", stopped(0));
    answer("underscore-exit skips handlers", stopped(1));
    answer("abort stops without handlers", stopped(2));
    answer("assert failure stops without handlers", stopped(3));
    answer("callback argument must outlive registration", libc_traps(expired_argument));
    return 0;
}
