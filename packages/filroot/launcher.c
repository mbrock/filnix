/* Starts a program of a relocatable Fil-C root.

   Inside the root, every path that was a Nix store path is written as
   /proc/self/fd/987/..., so ELF interpreters, RUNPATHs, shebangs and data
   paths such as glibc's character sets and OpenSSL's directory resolve
   through file descriptor 987. ROOT/DIR/NAME is this launcher: it opens
   ROOT as descriptor 987, which programs inherit, and runs the real program
   ROOT/libexec/filroot/DIR/NAME with the same arguments, argv[0] included.

   ROOT/bin/fil-run PROGRAM ARGS... runs any program, for example one built
   with the root's filcc, with descriptor 987 open.

   This is ordinary static C, not Fil-C, so it runs on any x86-64 Linux. */

#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <limits.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/resource.h>
#include <unistd.h>

#define ROOT_FD 987

static void open_root(const char *root) {
    int fd = open(root, O_PATH | O_DIRECTORY);
    if (fd < 0) {
        fprintf(stderr, "fil: cannot open %s: %s\n", root, strerror(errno));
        exit(127);
    }
    if (fd == ROOT_FD)
        return;
    if (dup2(fd, ROOT_FD) < 0 && errno == EBADF) {
        /* The descriptor limit is too low for ROOT_FD. */
        struct rlimit rl;
        if (getrlimit(RLIMIT_NOFILE, &rl) == 0 && rl.rlim_max > ROOT_FD) {
            rl.rlim_cur = ROOT_FD + 1;
            setrlimit(RLIMIT_NOFILE, &rl);
        }
        if (dup2(fd, ROOT_FD) < 0) {
            fprintf(stderr, "fil: cannot use descriptor %d: %s\n", ROOT_FD, strerror(errno));
            exit(127);
        }
    }
    close(fd);
}

int main(int argc, char **argv) {
    char self[PATH_MAX];
    ssize_t n = readlink("/proc/self/exe", self, sizeof self - 1);
    if (n < 0) {
        perror("fil: /proc/self/exe");
        return 127;
    }
    self[n] = 0;

    /* self is ROOT/DIR/NAME. */
    char *slash = strrchr(self, '/');
    *slash = 0;
    const char *name = slash + 1;
    slash = strrchr(self, '/');
    *slash = 0;
    const char *dir = slash + 1;
    const char *root = *self ? self : "/";
    open_root(root);

    if (strcmp(name, "fil-run") == 0) {
        if (argc < 2) {
            fprintf(stderr, "usage: fil-run PROGRAM [ARGUMENT...]\n");
            return 2;
        }
        execvp(argv[1], argv + 1);
        fprintf(stderr, "fil-run: %s: %s\n", argv[1], strerror(errno));
        return 127;
    }

    char *program;
    if (asprintf(&program, "%s/libexec/filroot/%s/%s", root, dir, name) < 0)
        return 127;
    if (argc == 0) {
        static char *args[2];
        args[0] = (char *)name;
        argv = args;
    }
    execv(program, argv);
    fprintf(stderr, "fil: cannot run %s: %s\n", program, strerror(errno));
    return 127;
}
