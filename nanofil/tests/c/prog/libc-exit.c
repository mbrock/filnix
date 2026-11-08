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
static int recursive;
static void oldest(int status, void *arg) {
    int expected = recursive ? -1 : 31;
    write(pipe_out, status == expected && arg == &recursive ? "A" : "X", 1);
}
static void added(void) { write(pipe_out, "C", 1); }
static void newest(void) {
    write(pipe_out, "B", 1);
    if (recursive == 2) _exit(98);
    if (recursive) {
        exit(-1);
        write(pipe_out, "X", 1);
    }
    if (atexit(added)) _exit(98);
}
// Direct handler writes precede the buffered byte flushed by cleanup.
static int dynamic_exit(int reenter) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]); pipe_out = fd[1]; recursive = reenter;
        if (dup2(fd[1], 1) < 0 || setvbuf(stdout, 0, _IOFBF, 4096)) _exit(99);
        if (fputs("Z", stdout) < 0 || on_exit(oldest, &recursive) || atexit(newest)) _exit(99);
        exit(31);
    }
    close(fd[1]);
    char buf[8] = {0};
    size_t n = 0;
    ssize_t r;
    while (n < sizeof buf && (r = read(fd[0], buf + n, sizeof buf - n)) > 0) n += r;
    close(fd[0]);
    int st = 0;
    if (child < 0 || waitpid(child, &st, 0) != child) return 0;
    int status = reenter == 2 ? 98 : reenter ? 255 : 31;
    size_t count = reenter == 2 ? 1 : reenter ? 3 : 4;
    const char *expected = reenter == 2 ? "B" : reenter ? "BAZ" : "BCAZ";
    return WIFEXITED(st) && WEXITSTATUS(st) == status &&
        n == count && memcmp(buf, expected, n) == 0;
}
// A fresh exec reaches main through startup and observes real host
// termination, not just a logical handoff. E is a direct handler write;
// Z remains buffered until soft cleanup, and is absent on hard exit.
static int host_completion(const char *mode, int status, const char *expected) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]);
        if (dup2(fd[1], 1) < 0 || dup2(fd[1], 2) < 0) _exit(99);
        close(fd[1]);
        char *args[] = {"host-completion", (char *)mode, 0};
        char *env[] = {0};
        execve("/proc/self/exe", args, env);
        _exit(99);
    }
    close(fd[1]);
    char buf[4096];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof buf && (r = read(fd[0], buf + n, sizeof buf - n)) > 0) n += r;
    close(fd[0]);
    int st = 0;
    return child > 0 && waitpid(child, &st, 0) == child &&
        WIFEXITED(st) && WEXITSTATUS(st) == status &&
        n == strlen(expected) && memcmp(buf, expected, n) == 0;
}
// The registry, rather than this caller, retains each argument capability.
// Once a callback has consumed its argument, later callbacks need not keep
// that object live. Exercise both sides of the pinned 32-slot block boundary.
static void block_handler(int status, void *arg) {
    if (status != 47) _exit(99);
    unsigned char byte = *(unsigned char *)arg;
    free(arg);
    if (write(pipe_out, &byte, 1) != 1) _exit(99);
}
static int block_exit(int count) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]); pipe_out = fd[1];
        if (dup2(fd[1], 1) < 0 || dup2(fd[1], 2) < 0) _exit(99);
        for (int i = 0; i < count; ++i) {
            unsigned char *arg = malloc(1);
            if (!arg) _exit(99);
            *arg = (unsigned char)(i * 73 + 19);
            if (on_exit(block_handler, arg)) _exit(99);
        }
        exit(47);
    }
    close(fd[1]);
    unsigned char bytes[128];
    size_t n = 0;
    ssize_t r;
    while (n < sizeof bytes && (r = read(fd[0], bytes + n, sizeof bytes - n)) > 0) n += r;
    close(fd[0]);
    int st = 0;
    if (child < 0 || waitpid(child, &st, 0) != child ||
        !WIFEXITED(st) || WEXITSTATUS(st) != 47 || n != (size_t)count) return 0;
    for (int i = 0; i < count; ++i)
        if (bytes[i] != (unsigned char)((count - i - 1) * 73 + 19)) return 0;
    return 1;
}
int main(int argc, char **argv) {
    if (argc == 2) {
        pipe_out = 1;
        if (setvbuf(stdout, 0, _IOFBF, 4096) || atexit(on_exit_probe) || fputs("Z", stdout) < 0)
            _exit(99);
        if (!strcmp(argv[1], "--main")) return -1;
        if (!strcmp(argv[1], "--soft")) exit(258);
        if (!strcmp(argv[1], "--hard")) _Exit(-2);
        if (!strcmp(argv[1], "--underscore")) _exit(513);
        _exit(99);
    }
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
    answer("new handler precedes older handlers and cleanup", dynamic_exit(0));
    answer("recursive exit updates signed status without repeating handler", dynamic_exit(1));
    answer("handler underscore-exit replaces status without cleanup", dynamic_exit(2));
    answer("main return reaches host completion with signed low-byte status", host_completion("--main", 255, "EZ"));
    answer("soft exit reaches host completion after handlers and flush", host_completion("--soft", 2, "EZ"));
    answer("hard exit reaches host completion without handlers or flush", host_completion("--hard", 254, ""));
    answer("underscore-exit reaches host completion with wrapped status", host_completion("--underscore", 1, ""));
    answer("exit registry retains arguments across block boundaries",
           block_exit(31) && block_exit(32) && block_exit(33) && block_exit(65));
    return 0;
}
