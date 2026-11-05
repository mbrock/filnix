/* glibc calls Fil-C has no runtime wrapper for must fail with an error, not
   stop the program (patches/filc-glibc-unsupported-syscalls.patch). */
#define _GNU_SOURCE
#include <errno.h>
#include <sched.h>
#include <spawn.h>
#include <stdint.h>
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

/* What the kernel shows of the break: start_brk in /proc/self/stat, and the
   [heap] mapping, which ends at the page-aligned break once the break has
   moved past start_brk. Independent of sbrk. */
static void kernel_break(uintptr_t *start_brk, uintptr_t *heap_lo, uintptr_t *heap_hi)
{
    char stat[4096], line[512];
    FILE *f = fopen("/proc/self/stat", "r");
    size_t n = fread(stat, 1, sizeof stat - 1, f);
    fclose(f);
    stat[n] = 0;
    char *field = strrchr(stat, ')') + 2; /* field 3 */
    for (int i = 3; i < 47; i++)
        field = strchr(field, ' ') + 1;
    *start_brk = strtoull(field, NULL, 10);
    *heap_lo = *heap_hi = 0;
    f = fopen("/proc/self/maps", "r");
    while (fgets(line, sizeof line, f))
        if (strstr(line, "[heap]"))
            sscanf(line, "%lx-%lx", heap_lo, heap_hi);
    fclose(f);
}

/* sbrk(0) is the kernel's break, as natively. The runtime's native allocator
   may move the break meanwhile, so retry until sbrk(0) agrees before and
   after reading /proc. */
static void expect_sbrk0_is_break(const char *what)
{
    long page = sysconf(_SC_PAGESIZE);
    for (int attempt = 0; attempt < 20; attempt++) {
        errno = 0;
        char *before = sbrk(0);
        int before_errno = errno;
        uintptr_t start_brk, heap_lo, heap_hi;
        kernel_break(&start_brk, &heap_lo, &heap_hi);
        if (sbrk(0) != before)
            continue;
        uintptr_t b = (uintptr_t)before;
        printf("%s: sbrk(0) %#lx, start_brk %#lx, [heap] %#lx-%#lx\n", what,
               (unsigned long)b, (unsigned long)start_brk, (unsigned long)heap_lo,
               (unsigned long)heap_hi);
        expect(what,
               before != (void *)-1 && before_errno == 0 && start_brk != 0
                   && (b == start_brk
                       || (heap_hi != 0 && heap_lo <= start_brk && b > start_brk
                           && heap_hi == ((b + page - 1) & ~(uintptr_t)(page - 1)))));
        return;
    }
    expect("the break settles", 0);
}

int main(void)
{
    /* e2fsck asks for the break at startup. */
    expect_sbrk0_is_break("sbrk(0) is the kernel's break");
    /* Fil-C allocations come from the GC heap; the runtime's native allocator
       may move the break, and sbrk(0) must follow it. */
    for (int i = 0; i < 64; i++) {
        volatile char *p = malloc(1 << 16);
        p[0] = 1;
    }
    expect_sbrk0_is_break("sbrk(0) is the kernel's break after allocating");

    char *brk0 = sbrk(0);
    expect("brk at the break succeeds", brk(brk0) == 0);

    /* Moving the break fails; Fil-C memory comes from the GC heap. */
    errno = 0;
    expect("sbrk(4096) fails with ENOMEM", sbrk(4096) == (void *)-1 && errno == ENOMEM);
    errno = 0;
    expect("brk past the break fails with ENOMEM",
           brk(brk0 + 4096) == -1 && errno == ENOMEM);
    expect_sbrk0_is_break("sbrk(0) is still the kernel's break");

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
