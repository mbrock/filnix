// cflags: -D_GNU_SOURCE -fno-builtin
// error(0) returns before a following hard exit; error(nonzero) runs the
// existing exit inventory. Stdout flush and stderr diagnostic are distinct.
#include <error.h>
#include "libc-probe.h"
extern char *program_invocation_name;
static int expected_status;
static void oldest(int status, void *arg) {
    if (status != expected_status || arg != &expected_status) _exit(99);
    write(1, "A", 1);
}
static void newest(void) {
    write(1, "B", 1);
    error(258, 0, "%s:%d", "bad", -3);
    write(1, "X", 1);
}
static int run(int mode) {
    fflush(0);
    int fd[2];
    if (pipe(fd)) return 0;
    pid_t child = fork();
    if (child == 0) {
        close(fd[0]);
        if (dup2(fd[1], 1) < 0 || dup2(fd[1], 2) < 0) _exit(99);
        close(fd[1]);
        program_invocation_name = (char *)"ending";
        if (setvbuf(stdout, 0, _IOFBF, 4096)) _exit(99);
        expected_status = mode == 2 ? 258 : -257;
        if (on_exit(oldest, &expected_status) || fputs("Z", stdout) < 0) _exit(99);
        if (mode == 2) {
            if (atexit(newest)) _exit(99);
            exit(31);
        }
        error(mode == 0 ? 0 : -257, 0, "%s:%d", "bad", -3);
        write(1, "R", 1);
        _exit(7);
    }
    close(fd[1]);
    char bytes[128] = {0};
    size_t n = 0;
    ssize_t r;
    while (n < sizeof bytes && (r = read(fd[0], bytes + n, sizeof bytes - n)) > 0) n += r;
    close(fd[0]);
    int status = 0;
    if (child < 0 || waitpid(child, &status, 0) != child || !WIFEXITED(status)) return 0;
    const char *expected = mode == 0 ? "Zending: bad:-3\nR" :
        mode == 1 ? "Zending: bad:-3\nA" : "BZending: bad:-3\nA";
    int code = mode == 0 ? 7 : mode == 1 ? 255 : 2;
    return WEXITSTATUS(status) == code && n == strlen(expected) && !memcmp(bytes, expected, n);
}
int main(void) {
    answer("error zero returns then hard exit skips handlers", run(0));
    answer("error nonzero exits with signed status and existing handlers", run(1));
    answer("callback error replaces status without repeating active handler", run(2));
    return 0;
}
