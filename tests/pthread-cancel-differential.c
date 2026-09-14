/* Linux x86-64 pthread cancellation differential probe.
 *
 * Cases:
 *   0: cancel during a non-cancellation-point SA_RESTART signal handler
 *      which interrupted an empty-pipe read; inspect before rescue write.
 *   1: cancellation pending before sem_wait on a semaphore with one token.
 *   2: cancellation pending before close on an open pipe descriptor.
 *   3: cancellation pending before switching to asynchronous cancellation.
 *   4: remotely cancel a thread in read with cancellation disabled.
 *   5: remotely cancel a thread in poll with cancellation disabled.
 *
 * Build from the repository root, with assertions enabled:
 *   cc -O2 -Wall -Wextra -pthread tests/pthread-cancel-differential.c -o probe-glibc
 *   musl-gcc -O2 -Wall -Wextra -static -pthread \
 *     tests/pthread-cancel-differential.c -o probe-musl
 *   cosmocc -O2 -Wall -Wextra -pthread -DSYS_read=0 -DSYS_poll=7 \
 *     -DSYS_ppoll=271 tests/pthread-cancel-differential.c -o probe-cosmo
 * Cosmopolitan's public headers omit these Linux syscall-number macros;
 * the definitions are only for /proc introspection, not issuing syscalls.
 *
 * Run ./probe-glibc CASE or ./probe-musl CASE. Cosmopolitan may require:
 *   ape-x86_64.elf ./probe-cosmo CASE
 * To test an extracted glibc without replacing the system libc:
 *   /path/to/ld-linux-x86-64.so.2 --library-path /path/to/libs ./probe-glibc CASE
 *
 * The handler uses lock-free atomics and calls no cancellation points.
 * /proc/self/task/TID/syscall confirms entry into the intended kernel wait.
 * The bounded observation is not a proof of eventual nontermination; the
 * rescue byte makes a missed wakeup reproducible without hanging the probe.
 * All cases eventually call pthread_testcancel, so canceled=1 by itself is
 * not evidence of timely cancellation. Examine the before-rescue fields and
 * operation_returned, semaphore_count, and fd_open instead.
 * See docs/pthread-cancellation.md for interpretation and recorded results.
 */
#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <semaphore.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <time.h>
#include <unistd.h>

static atomic_int tid, entered, leave_handler, handler_returned, cleaned;
static atomic_int returned, operation_errno;
static int fds[2], which;
static sem_t sem;

static void delay_ms(int ms) {
    struct timespec ts = {ms / 1000, (ms % 1000) * 1000000L};
    while (nanosleep(&ts, &ts) && errno == EINTR) {}
}

static void handler(int sig) {
    (void)sig;
    atomic_store(&entered, 1);
    while (!atomic_load(&leave_handler)) {}
    atomic_store(&handler_returned, 1);
}

static void cleanup(void *arg) {
    (void)arg;
    atomic_store(&cleaned, 1);
}

static void *worker(void *arg) {
    (void)arg;
    pthread_cleanup_push(cleanup, NULL);
    atomic_store(&tid, (int)syscall(SYS_gettid));
    if (which == 0 || which >= 4) {
        if (which >= 4)
            assert(!pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, NULL));
        char c;
        struct pollfd pfd = {.fd = fds[0], .events = POLLIN};
        int r = which == 5 ? poll(&pfd, 1, -1) : read(fds[0], &c, 1);
        atomic_store(&operation_errno, r < 0 ? errno : 0);
        atomic_store(&returned, 1);
        if (which >= 4)
            assert(!pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL));
        pthread_testcancel();
    } else {
        assert(!pthread_cancel(pthread_self()));
        if (which == 1) {
            int r = sem_wait(&sem);
            atomic_store(&operation_errno, r < 0 ? errno : 0);
        } else if (which == 2) {
            int r = close(fds[0]);
            atomic_store(&operation_errno, r < 0 ? errno : 0);
        } else if (which == 3) {
            assert(!pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, NULL));
        }
        atomic_store(&returned, 1);
        if (which == 3)
            assert(!pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, NULL));
        pthread_testcancel();
    }
    pthread_cleanup_pop(0);
    return NULL;
}

static int is_blocked(void) {
    char path[100], line[300];
    snprintf(path, sizeof(path), "/proc/self/task/%d/syscall", atomic_load(&tid));
    FILE *f = fopen(path, "r");
    if (!f) return 0;
    int got = fgets(line, sizeof(line), f) != NULL;
    fclose(f);
    long nr = -1;
    unsigned long fd = 0;
    return got && sscanf(line, "%ld %lx", &nr, &fd) == 2 &&
           (which == 5 ? (nr == SYS_poll || nr == SYS_ppoll) :
            nr == SYS_read && fd == (unsigned long)fds[0]);
}

int main(int argc, char **argv) {
    assert(argc == 2);
    alarm(8);
    assert(atomic_is_lock_free(&entered));
    which = atoi(argv[1]);
    assert(which >= 0 && which <= 5);
    assert(!pipe(fds));
    assert(!sem_init(&sem, 0, 1));
    struct sigaction sa = {.sa_handler = handler, .sa_flags = SA_RESTART};
    assert(!sigemptyset(&sa.sa_mask));
    assert(!sigaction(SIGUSR1, &sa, NULL));
    pthread_t thread;
    assert(!pthread_create(&thread, NULL, worker, NULL));
    if (which == 0 || which >= 4) {
        for (int i = 0; i < 2000 && !is_blocked(); ++i) delay_ms(1);
        assert(is_blocked());
        if (which == 0) {
            assert(!pthread_kill(thread, SIGUSR1));
            for (int i = 0; i < 2000 && !atomic_load(&entered); ++i) delay_ms(1);
            assert(atomic_load(&entered));
        }
        assert(!pthread_cancel(thread));
        delay_ms(100);
        int early = atomic_load(&cleaned);
        atomic_store(&leave_handler, 1);
        delay_ms(200);
        printf("case=%d cleaned_inside_handler=%d handler_returned=%d "
               "cleaned_before_rescue=%d blocked_before_rescue=%d "
               "returned_before_rescue=%d errno=%d\n",
               which, which == 0 ? early : 0, atomic_load(&handler_returned),
               atomic_load(&cleaned), is_blocked(), atomic_load(&returned),
               atomic_load(&operation_errno));
        assert(write(fds[1], "x", 1) == 1);
    }
    void *result;
    assert(!pthread_join(thread, &result));
    int count;
    assert(!sem_getvalue(&sem, &count));
    printf("case=%d canceled=%d cleaned=%d operation_returned=%d "
           "semaphore_count=%d fd_open=%d\n", which, result == PTHREAD_CANCELED,
           atomic_load(&cleaned), atomic_load(&returned), count,
           fcntl(fds[0], F_GETFD) >= 0);
    return 0;
}
