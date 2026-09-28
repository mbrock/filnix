/* Checks for the jemalloc API shim (docs/jemalloc-on-fugc.md). */

#include <assert.h>
#include <errno.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

#include <jemalloc/jemalloc.h>

/* Applications configure jemalloc this way; it must still link. */
const char *malloc_conf = "background_thread:false";

static void expect_trap(void (*fn)(void), const char *what)
{
    fflush(NULL);
    pid_t pid = fork();
    assert(pid >= 0);
    if (!pid) {
        fn();
        _exit(0);
    }
    int status;
    assert(waitpid(pid, &status, 0) == pid);
    if (WIFEXITED(status) && WEXITSTATUS(status) == 0) {
        fprintf(stderr, "FAIL: %s did not trap\n", what);
        exit(1);
    }
    printf("ok: %s traps\n", what);
}

static char *volatile victim;

static void overflow(void)
{
    victim = mallocx(16, 0);
    char *neighbour = mallocx(16, 0);
    strcpy(neighbour, "secret");
    printf("read %c\n", victim[neighbour - victim]);
}

static void use_after_free(void)
{
    victim = mallocx(32, 0);
    dallocx(victim, 0);
    printf("read %c\n", victim[0]);
}

static void use_after_sdallocx(void)
{
    victim = mallocx(100, MALLOCX_ZERO);
    sdallocx(victim, 100, 0);
    victim[1] = 1;
}

static void past_sallocx(void)
{
    victim = mallocx(20, 0);
    victim[sallocx(victim, 0)] = 1;
}

static void out(void *opaque, const char *s)
{
    strncat(opaque, s, 1023 - strlen(opaque));
}

int main(void)
{
    /* Sizes and alignment. */
    for (size_t size = 0; size < 70000; size += size < 300 ? 1 : 997) {
        for (int lg = 0; lg <= 12; lg += 4) {
            int flags = MALLOCX_LG_ALIGN(lg);
            char *p = mallocx(size, flags);
            assert(p);
            assert(((uintptr_t)p & (((uintptr_t)1 << lg) - 1)) == 0);
            assert(sallocx(p, flags) >= size);
            assert(sallocx(p, flags) == nallocx(size, flags));
            assert(malloc_usable_size(p) == sallocx(p, flags));
            for (size_t i = 0; i < size; i++)
                assert(p[i] == 0);
            memset(p, 0xa5, size);
            p = rallocx(p, size * 2 + 1, flags | MALLOCX_ZERO);
            assert(((uintptr_t)p & (((uintptr_t)1 << lg) - 1)) == 0);
            for (size_t i = 0; i < size; i++)
                assert((unsigned char)p[i] == 0xa5);
            for (size_t i = size; i < size * 2 + 1; i++)
                assert(p[i] == 0);
            assert(xallocx(p, size * 4, 0, flags) == sallocx(p, flags));
            if (size & 1)
                sdallocx(p, size * 2 + 1, flags);
            else
                dallocx(p, flags);
        }
    }
    void *a = mallocx(64, MALLOCX_ALIGN(4096) | MALLOCX_TCACHE_NONE |
                              MALLOCX_ARENA(0));
    assert(((uintptr_t)a & 4095) == 0);
    free(a); /* the same heap as malloc */
    a = malloc(10);
    a = rallocx(a, 1000, 0);
    dallocx(a, 0);

    /* mallctl. */
    const char *version;
    size_t len = sizeof version;
    assert(!mallctl("version", &version, &len, NULL, 0));
    assert(!strcmp(version, JEMALLOC_VERSION));
    uint64_t epoch = 1, epoch2;
    len = sizeof epoch;
    assert(!mallctl("epoch", &epoch2, &len, &epoch, sizeof epoch));
    size_t allocated, resident;
    len = sizeof(size_t);
    assert(!mallctl("stats.allocated", &allocated, &len, NULL, 0));
    assert(!mallctl("stats.resident", &resident, &len, NULL, 0));
    assert(allocated > 0 && resident > 0);
    bool b;
    len = sizeof b;
    assert(!mallctl("config.prof", &b, &len, NULL, 0) && !b);
    assert(mallctl("prof.active", &b, &len, NULL, 0) == ENOENT);
    assert(mallctl("no.such.thing", NULL, NULL, NULL, 0) == ENOENT);
    assert(mallctl("config.debug", NULL, NULL, &b, sizeof b) == EPERM);
    unsigned u, narenas;
    len = sizeof u;
    assert(!mallctl("arenas.create", &u, &len, NULL, 0) && u == 1);
    assert(!mallctl("arenas.narenas", &narenas, &len, NULL, 0));
    assert(narenas == 2);
    assert(!mallctl("arena.1.purge", NULL, NULL, NULL, 0));
    assert(!mallctl("arena.4096.purge", NULL, NULL, NULL, 0));
    assert(!mallctl("arena.2.purge", NULL, NULL, NULL, 0)); /* = narenas: all */
    assert(mallctl("arena.7.purge", NULL, NULL, NULL, 0) == EFAULT);
    size_t arena_resident;
    len = sizeof arena_resident;
    assert(!mallctl("stats.arenas.0.resident", &arena_resident, &len, NULL, 0));
    assert(arena_resident > 0);
    assert(!mallctl("stats.arenas.1.small.allocated", &arena_resident, &len,
                    NULL, 0));
    assert(arena_resident == 0);
    len = sizeof u;
    ssize_t decay = 0;
    assert(!mallctl("arena.1.dirty_decay_ms", NULL, NULL, &decay,
                    sizeof decay));
    assert(!mallctl("thread.tcache.flush", NULL, NULL, NULL, 0));
    assert(!mallctl("tcache.create", &u, &len, NULL, 0));
    assert(!mallctl("tcache.destroy", NULL, NULL, &u, sizeof u));
    size_t small = 0;
    len = 2; /* wrong size: partial copy and EINVAL, as in jemalloc */
    assert(mallctl("arenas.page", &small, &len, NULL, 0) == EINVAL);
    assert(len == 2);
    bool bg = false;
    assert(!mallctl("background_thread", NULL, NULL, &bg, sizeof bg));

    size_t mib[8], miblen = 8, size;
    assert(!mallctlnametomib("arenas.bin.0.size", mib, &miblen));
    assert(miblen == 4);
    len = sizeof size;
    assert(!mallctlbymib(mib, miblen, &size, &len, NULL, 0) && size == 16);
    mib[2] = 1;
    assert(mallctlbymib(mib, miblen, &size, &len, NULL, 0) == ENOENT);
    size_t cur, cmib[8], cmiblen = 8;
    assert(!mallctlnametomib("stats.arenas.0.bins.0.curregs", cmib,
                             &cmiblen));
    cmib[2] = MALLCTL_ARENAS_ALL;
    assert(!mallctlbymib(cmib, cmiblen, &cur, &len, NULL, 0) && cur == 0);
    miblen = 2;
    assert(mallctlnametomib("arenas.page", mib, &miblen) == 0);
    miblen = 1;
    assert(mallctlnametomib("arenas.page", mib, &miblen) == ENOENT);

    char text[1024] = "";
    malloc_stats_print(out, text, NULL);
    assert(strstr(text, "Begin jemalloc statistics"));
    text[0] = 0;
    malloc_stats_print(out, text, "J");
    assert(text[0] == '{');

    /* Each object keeps Fil-C's bounds and use-after-free checks. */
    expect_trap(overflow, "reading a neighbouring object");
    expect_trap(use_after_free, "use after dallocx");
    expect_trap(use_after_sdallocx, "use after sdallocx");
    expect_trap(past_sallocx, "writing past sallocx()");

    printf("jemalloc shim: all checks passed\n");
    return 0;
}
