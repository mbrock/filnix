// cflags: -D_GNU_SOURCE -fno-builtin
// args: plain --name=xyz
// The launcher supplies argv/environment, not just a list of raw
// addresses. Native __libc_start_main precedes Fil-C's entry wrapper.
#include <errno.h>
#include "libc-probe.h"
extern char **environ;
int main(int argc, char **argv) {
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
    answer("program names are readable aliases", program_invocation_name && program_invocation_short_name && strlen(program_invocation_name) > 0 && strlen(program_invocation_short_name) > 0 && strstr(program_invocation_name, program_invocation_short_name) != 0);
    int *cell = __errno_location();
    *cell = EDOM;
    answer("errno is a writable thread-local cell", errno == EDOM && __errno_location() == cell);
    answer("initial streams are live", stdout != 0 && stderr != 0 && !ferror(stdout) && fputs("", stderr) >= 0);
    return 0;
}
