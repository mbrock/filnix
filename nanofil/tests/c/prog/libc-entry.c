// cflags: -D_GNU_SOURCE -fno-builtin
// args: plain --name=xyz
// The launcher supplies argv/environment, not just a list of raw
// addresses. Native __libc_start_main precedes Fil-C's entry wrapper.
#include <errno.h>
#include "libc-probe.h"
extern char **environ;
static int copied_inputs(int empty_environment) {
    fflush(0);
    pid_t child = fork();
    if (child == 0) {
        char *args[] = {"entry-copy", empty_environment ? "--copy-empty" : "--copy-bytes",
                        "", "\1\200\377", 0};
        char *env[] = {"NF_COPY=\1\200\377", 0};
        char *empty[] = {0};
        execve("/proc/self/exe", args, empty_environment ? empty : env);
        _exit(99);
    }
    int status;
    return child > 0 && waitpid(child, &status, 0) == child &&
        WIFEXITED(status) && WEXITSTATUS(status) == 0;
}
int main(int argc, char **argv) {
    if (argc == 4 && (!strcmp(argv[1], "--copy-empty") || !strcmp(argv[1], "--copy-bytes"))) {
        const unsigned char *p = (unsigned char *)argv[3];
        int good = argv[4] == 0 && argv[2][0] == 0 &&
            p[0] == 1 && p[1] == 128 && p[2] == 255 && p[3] == 0;
        good = good && (!strcmp(argv[1], "--copy-empty") ? environ[0] == 0 :
            environ[0] && strcmp(environ[0], "NF_COPY=\1\200\377") == 0 && environ[1] == 0);
        for (int i = 0; i < argc; ++i) {
            volatile char *p = argv[i];
            p[strlen(argv[i])] = 0;
        }
        for (char **e = environ; *e; ++e) {
            volatile char *p = *e;
            p[strlen(*e)] = 0;
        }
        return good ? 0 : 1;
    }
    int good = argc == 3 && argv[argc] == 0;
    for (int i = 0; i < argc; ++i) {
        size_t n = strlen(argv[i]);
        char c = argv[i][n];
        argv[i][n] = c;
        good = good && c == 0;
    }
    answer("entry argv carries writable string capabilities", good && strcmp(argv[1], "plain") == 0 && strcmp(argv[2], "--name=xyz") == 0);
    good = environ != 0;
    for (char **p = environ; *p; ++p) {
        size_t n = strlen(*p);
        good = good && (*p)[n] == 0;
    }
    answer("entry environment is sentinel terminated", good);
    answer("entry copies empty strings and high bytes with writable NULs", copied_inputs(0) && copied_inputs(1));
    answer("program names are readable aliases", program_invocation_name && program_invocation_short_name && strlen(program_invocation_name) > 0 && strlen(program_invocation_short_name) > 0 && strstr(program_invocation_name, program_invocation_short_name) != 0);
    int *cell = __errno_location();
    *cell = EDOM;
    answer("errno is a writable thread-local cell", errno == EDOM && __errno_location() == cell);
    answer("initial streams are live", stdout != 0 && stderr != 0 && !ferror(stdout) && fputs("", stderr) >= 0);
    return 0;
}
