/* glibc calls Fil-C has no runtime wrapper for must fail with an error, not
   stop the program (patches/filc-glibc-unsupported-syscalls.patch). */
#define _GNU_SOURCE
#include <errno.h>
#include <sched.h>
#include <spawn.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/pidfd.h>
#include <sys/wait.h>
#include <unistd.h>

extern char **environ;

static void expect(const char *what, int ok)
{
    printf("%s: %s\n", what, ok ? "ok" : "WRONG");
    if (!ok)
        exit(1);
}

int main(void)
{
    /* e2fsck asks for the break at startup; the break never moves. */
    errno = 0;
    expect("sbrk(0) fails with ENOMEM", sbrk(0) == (void *)-1 && errno == ENOMEM);
    errno = 0;
    expect("sbrk(4096) fails with ENOMEM", sbrk(4096) == (void *)-1 && errno == ENOMEM);

    struct sched_attr attr;
    memset(&attr, 0, sizeof attr);
    attr.size = sizeof attr;
    attr.sched_policy = SCHED_OTHER;
    errno = 0;
    expect("sched_setattr fails with ENOSYS",
           sched_setattr(0, &attr, 0) == -1 && errno == ENOSYS);

    int pidfd = -1;
    char *argv[] = { "true", NULL };
    expect("pidfd_spawnp returns ENOSYS",
           pidfd_spawnp(&pidfd, "true", NULL, NULL, argv, environ) == ENOSYS);

    /* The fallback callers take still works. */
    pid_t pid;
    int status;
    expect("posix_spawnp runs true",
           posix_spawnp(&pid, "true", NULL, NULL, argv, environ) == 0
               && waitpid(pid, &status, 0) == pid && WIFEXITED(status)
               && WEXITSTATUS(status) == 0);
    return 0;
}
