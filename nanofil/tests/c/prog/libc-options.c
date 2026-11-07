// cflags: -D_GNU_SOURCE -fno-builtin
// getopt_long may permute argv's pointer cells, and optarg aliases an
// argument rather than allocating a copy. Null longindex is allowed.
#include <getopt.h>
#include <fcntl.h>
#include <errno.h>
#include "libc-probe.h"
int main(void) {
    char a0[] = "probe", a1[] = "operand", a2[] = "--name=abc", a3[] = "-v";
    char *av[] = {a0, a1, a2, a3, 0};
    struct option opts[] = {{"name", required_argument, 0, 'n'}, {0, 0, 0, 0}};
    unsetenv("POSIXLY_CORRECT");
    optind = 0; opterr = 0;
    int index = -1;
    int good = getopt_long(4, av, "vn:", opts, &index) == 'n' && index == 0 && optarg == a2 + 7;
    good = good && getopt_long(4, av, "vn:", opts, 0) == 'v';
    good = good && getopt_long(4, av, "vn:", opts, 0) == -1 && optind == 3 && av[3] == a1;
    answer("getopt aliases arguments and permutes cells", good);
    char *bad[] = {a0, "--unknown", 0};
    optind = 0;
    answer("unknown option is a result", getopt_long(2, bad, "", opts, 0) == '?');
    int fd = open("/dev/null", O_RDONLY);
    if (fd < 0) return 1;
    int flags = fcntl(fd, F_GETFD);
    answer("fcntl command selects optional argument", flags >= 0 && fcntl(fd, F_SETFD, flags | FD_CLOEXEC) == 0 && (fcntl(fd, F_GETFD) & FD_CLOEXEC));
    close(fd); errno = 0;
    answer("bad fd is EBADF not panic", fcntl(-1, F_GETFD) == -1 && errno == EBADF);
    return 0;
}
