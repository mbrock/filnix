/* Cancellation and signal behavior through the shared Fil-C toolchain. */
#define _GNU_SOURCE 1
#include <assert.h>
#include <errno.h>
#include <pthread.h>
#include <sched.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

enum mode { COOPERATIVE, PENDING, RACING, PAUSED, ASYNC_PAUSED, DISABLED, SIGNAL_ONLY,
            ASYNC_SIGNAL_ONLY };
struct scenario {
    enum mode mode;
    atomic_int ready, proceed, cleaned, cxx_cleaned, tid;
};

static void check_mask(void)
{
    sigset_t set;
    assert(!pthread_sigmask(SIG_SETMASK, NULL, &set));
    assert(sigismember(&set, SIGUSR2) == 1);
    assert(sigismember(&set, 34) == 0);
}

static void cleanup(void *arg)
{
    struct scenario *s = arg;
    check_mask();
#ifdef WITH_CXX_CLEANUP
    assert(atomic_load(&s->cxx_cleaned) == 1);
#endif
    atomic_fetch_add(&s->cleaned, 1);
}

static void signal_handler(int signo) { assert(signo == SIGUSR1); }

static void worker_body(void *arg)
{
    struct scenario *s = arg;
    const int type = (s->mode == ASYNC_PAUSED || s->mode == ASYNC_SIGNAL_ONLY)
        ? PTHREAD_CANCEL_ASYNCHRONOUS : PTHREAD_CANCEL_DEFERRED;
    const int state = s->mode == DISABLED
        ? PTHREAD_CANCEL_DISABLE : PTHREAD_CANCEL_ENABLE;
    atomic_store(&s->tid, (int)syscall(SYS_gettid));
    atomic_store(&s->ready, 1);
    if (s->mode == PENDING)
        while (!atomic_load(&s->proceed))
            ;
    if (s->mode == COOPERATIVE)
        for (;;)
            pthread_testcancel();

    int result = pause();
    assert(result == -1 && errno == EINTR);
    check_mask();
    /* Cancellation cases must unwind instead of returning from pause(). */
    assert(s->mode == DISABLED || s->mode == SIGNAL_ONLY ||
           s->mode == ASYNC_SIGNAL_ONLY);
    assert(!atomic_load(&s->cleaned));
    int previous;
    assert(!pthread_setcanceltype(type, &previous));
    assert(previous == type);
    assert(!pthread_setcancelstate(state, &previous));
    assert(previous == state);
    if (s->mode == DISABLED) {
        assert(!pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL));
        pthread_testcancel();
        assert(!"pending cancellation was lost");
    }
}

#ifdef WITH_CXX_CLEANUP
extern void filc_cancel_cxx_scope(void (*body)(void *), void *arg,
                                  void (*destroy)(void *));
static void cxx_cleanup(void *arg)
{
    struct scenario *s = arg;
    check_mask();
    atomic_fetch_add(&s->cxx_cleaned, 1);
}
#endif

static void *worker(void *arg)
{
    struct scenario *s = arg;
    assert(!pthread_setcanceltype(
        (s->mode == ASYNC_PAUSED || s->mode == ASYNC_SIGNAL_ONLY)
            ? PTHREAD_CANCEL_ASYNCHRONOUS : PTHREAD_CANCEL_DEFERRED, NULL));
    assert(!pthread_setcancelstate(s->mode == DISABLED
        ? PTHREAD_CANCEL_DISABLE : PTHREAD_CANCEL_ENABLE, NULL));
    pthread_cleanup_push(cleanup, s);
#ifdef WITH_CXX_CLEANUP
    filc_cancel_cxx_scope(worker_body, s, cxx_cleanup);
#else
    worker_body(s);
#endif
    pthread_cleanup_pop(0);
    return NULL;
}

/* Observe a real blocked syscall, so the test cannot succeed solely by
 * cancelling before pause(). Fil-C and this experiment are Linux-only. */
static void wait_for_pause(struct scenario *s)
{
    char path[96];
    snprintf(path, sizeof(path), "/proc/self/task/%d/syscall", atomic_load(&s->tid));
    struct timespec started, now;
    assert(!clock_gettime(CLOCK_MONOTONIC, &started));
    for (;;) {
        FILE *file = fopen(path, "r");
        assert(file);
        char line[256];
        assert(fgets(line, sizeof(line), file));
        fclose(file);
        char *end;
        long nr = strtol(line, &end, 10);
        if (end != line && (nr == SYS_rt_sigsuspend || nr == SYS_pause))
            return;
        assert(!clock_gettime(CLOCK_MONOTONIC, &now));
        assert(now.tv_sec - started.tv_sec < 5);
        sched_yield();
    }
}

static void run_case(enum mode mode)
{
    struct scenario s = { .mode = mode };
    pthread_t thread;
    assert(!pthread_create(&thread, NULL, worker, &s));
    while (!atomic_load(&s.ready))
        ;
    if (mode != COOPERATIVE && mode != PENDING && mode != RACING)
        wait_for_pause(&s);
    if (mode == RACING)
        sched_yield();
    if (mode != SIGNAL_ONLY && mode != ASYNC_SIGNAL_ONLY)
        assert(!pthread_cancel(thread));
    if (mode == PENDING)
        atomic_store(&s.proceed, 1);
    if (mode == DISABLED || mode == SIGNAL_ONLY || mode == ASYNC_SIGNAL_ONLY)
        assert(!pthread_kill(thread, SIGUSR1));
    void *result;
    assert(!pthread_join(thread, &result));
    const int cancelled = mode != SIGNAL_ONLY && mode != ASYNC_SIGNAL_ONLY;
    assert(result == (cancelled ? PTHREAD_CANCELED : NULL));
    assert(atomic_load(&s.cleaned) == cancelled);
#ifdef WITH_CXX_CLEANUP
    assert(atomic_load(&s.cxx_cleaned) == 1);
#endif
}

int main(int argc, char **argv)
{
    assert(argc == 2);
    FILE *maps = fopen("/proc/self/maps", "r");
    assert(maps);
    char *line = NULL;
    size_t size = 0;
    unsigned found = 0;
    while (getline(&line, &size, maps) >= 0) {
        if (strstr(line, "/lib/libc.so.6666")) {
            assert(strstr(line, argv[1]));
            ++found;
        }
    }
    assert(!ferror(maps));
    fclose(maps);
    free(line);
    assert(found);

    assert(SIGRTMIN == 37);
    sigset_t set;
    assert(!sigfillset(&set));
    for (int signo = 32; signo < SIGRTMIN; ++signo)
        assert(sigismember(&set, signo) == 0);
    struct sigaction sa = { .sa_handler = signal_handler };
    assert(!sigemptyset(&sa.sa_mask));
    assert(!sigaction(SIGUSR1, &sa, NULL));
    assert(!sigemptyset(&set));
    assert(!sigaddset(&set, SIGUSR2));
    assert(!pthread_sigmask(SIG_BLOCK, &set, NULL));
    for (unsigned i = 0; i < 16; ++i)
        for (enum mode mode = COOPERATIVE; mode <= ASYNC_SIGNAL_ONLY; ++mode)
            run_case(mode);
    puts("Fil-C libc: 128 cancellation/signal cases and cleanup checks passed");
    return 0;
}
