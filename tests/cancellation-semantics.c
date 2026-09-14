/* Behavioral gates for the shared Fil-C cancellation implementation.
   Each case runs in a separate process under the Nix test's timeout. */
#define _GNU_SOURCE 1
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <sched.h>
#include <semaphore.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/epoll.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/un.h>
#include <sys/uio.h>
#include <time.h>
#include <unistd.h>

enum scenario {
    READ_PENDING, READ_BLOCKED, READ_DISABLED, READ_NESTED, POLL_BLOCKED,
    CLOSE_PENDING, COND_PENDING, COND_BLOCKED, SEM_PENDING, SEM_BLOCKED,
    JOIN_BLOCKED, EXIT_CLEANUP, COND_SIGNAL,
    WRITE_BLOCKED, WRITE_PARTIAL, READV_PENDING, WRITEV_BLOCKED,
    ACCEPT_BLOCKED, ACCEPT_PENDING, RECVMSG_BLOCKED, RECVMSG_PENDING,
    EPOLL_BLOCKED, EPOLL_PENDING, SLEEP_BLOCKED, OPEN_FIFO_BLOCKED, OPEN_PENDING,
    PREAD_PENDING, PWRITE_PENDING,
};
struct context {
    enum scenario scenario;
    atomic_int ready, proceed, tid, cleanups, destroyed, handler, release_handler, cxx_destroyed;
    int pipefd[2];
    pthread_mutex_t mutex;
    pthread_cond_t cond;
    sem_t sem;
    pthread_t target;
    pthread_key_t key;
    int predicate, extra, peer, epfd, capacity;
    char *buffer;
    atomic_long transferred;
};
static struct context *signal_context;

static void wait_flag(atomic_int *p)
{
    while (!atomic_load_explicit(p, memory_order_acquire))
        sched_yield();
}

/* Wait for the requested kernel wait, not just a thread's readiness flag. */
static void wait_syscall(struct context *c, long wanted)
{
    wait_flag(&c->ready);
    char path[96];
    snprintf(path, sizeof(path), "/proc/self/task/%d/syscall", atomic_load(&c->tid));
    for (;;) {
        FILE *f = fopen(path, "r");
        assert(f);
        char line[256];
        assert(fgets(line, sizeof(line), f));
        fclose(f);
        char *end;
        long nr = strtol(line, &end, 10);
        if (end != line && nr == wanted)
            return;
        sched_yield();
    }
}

static void check_exit_state(void)
{
    int old;
    assert(!pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, &old));
    assert(old == PTHREAD_CANCEL_DISABLE);
    assert(!pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, &old));
    assert(old == PTHREAD_CANCEL_DEFERRED);
    /* Type remains a real public setting while cancellation is disabled.
       EXITING must suppress delivery without falsifying setter results. */
    assert(!pthread_setcanceltype(PTHREAD_CANCEL_ASYNCHRONOUS, &old));
    assert(old == PTHREAD_CANCEL_DEFERRED);
    assert(!pthread_setcanceltype(PTHREAD_CANCEL_DEFERRED, &old));
    assert(old == PTHREAD_CANCEL_ASYNCHRONOUS);
    /* A repeated self request and a cancellation point must not reenter cleanup. */
    assert(!pthread_cancel(pthread_self()));
    pthread_testcancel();
}

static void tsd_destroy(void *p)
{
    struct context *c = p;
    check_exit_state();
    assert(atomic_load(&c->cleanups) == 2);
    atomic_fetch_add(&c->destroyed, 1);
}

static void outer_cleanup(void *p)
{
    struct context *c = p;
    check_exit_state();
    assert(atomic_fetch_add(&c->cleanups, 1) == 1);
}

static void inner_cleanup(void *p)
{
    struct context *c = p;
    check_exit_state();
#ifdef WITH_CXX_CLEANUP
    assert(atomic_load(&c->cxx_destroyed) == 1);
#endif
    assert(atomic_fetch_add(&c->cleanups, 1) == 0);
    if (c->scenario == COND_PENDING || c->scenario == COND_BLOCKED ||
        c->scenario == COND_SIGNAL) {
        /* An ERRORCHECK mutex proves the cleanup runs while this thread owns it. */
        assert(pthread_mutex_lock(&c->mutex) == EDEADLK);
        assert(!pthread_mutex_unlock(&c->mutex));
    }
}

static void handler(int signo)
{
    assert(signo == SIGUSR1);
    atomic_store(&signal_context->handler, 1);
    /* No cancellation point: the interrupted read must still wake afterward. */
    while (!atomic_load(&signal_context->release_handler))
        ;
}

static void *target(void *p)
{
    struct context *c = p;
    wait_flag(&c->proceed);
    return c;
}

static void worker_body(void *p)
{
    struct context *c = p;
    atomic_store(&c->tid, (int)syscall(SYS_gettid));
    atomic_store(&c->ready, 1);
    if (c->scenario == READ_PENDING || c->scenario == CLOSE_PENDING ||
        c->scenario == COND_PENDING || c->scenario == SEM_PENDING ||
        c->scenario == READV_PENDING || c->scenario == ACCEPT_PENDING ||
        c->scenario == RECVMSG_PENDING || c->scenario == EPOLL_PENDING ||
        c->scenario == OPEN_PENDING || c->scenario == PREAD_PENDING ||
        c->scenario == PWRITE_PENDING)
        wait_flag(&c->proceed);
    switch (c->scenario) {
    case READ_PENDING: case READ_BLOCKED: case READ_NESTED: {
        char byte;
        (void)read(c->pipefd[0], &byte, 1);
        break;
    }
    case READ_DISABLED: {
        char byte;
        assert(read(c->pipefd[0], &byte, 1) == 1 && byte == 'x');
        assert(!pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, NULL));
        pthread_testcancel();
        break;
    }
    case POLL_BLOCKED: {
        struct pollfd fd = { .fd = c->pipefd[0], .events = POLLIN };
        (void)poll(&fd, 1, -1);
        break;
    }
    case CLOSE_PENDING:
        (void)close(c->pipefd[0]);
        break;
    case COND_PENDING: case COND_BLOCKED: case COND_SIGNAL:
        while (!c->predicate)
            assert(!pthread_cond_wait(&c->cond, &c->mutex));
        if (c->scenario == COND_SIGNAL)
            pthread_exit(c); /* Completion may win a racing cancellation. */
        break;
    case SEM_PENDING: case SEM_BLOCKED:
        (void)sem_wait(&c->sem);
        break;
    case JOIN_BLOCKED:
        (void)pthread_join(c->target, NULL);
        break;
    case EXIT_CLEANUP:
        pthread_exit(c);
    case WRITE_BLOCKED:
        (void)write(c->pipefd[1], "x", 1);
        break;
    case WRITE_PARTIAL: {
        ssize_t count = write(c->pipefd[1], c->buffer, c->capacity * 2);
        assert(count > 0 && count <= c->capacity);
        atomic_store(&c->transferred, count);
        /* A partial transfer must return before a racing deferred request acts. */
        pthread_testcancel();
        break;
    }
    case READV_PENDING: {
        char byte;
        struct iovec iov = { &byte, 1 };
        (void)readv(c->pipefd[0], &iov, 1);
        break;
    }
    case WRITEV_BLOCKED: {
        struct iovec iov = { "x", 1 };
        (void)writev(c->pipefd[1], &iov, 1);
        break;
    }
    case ACCEPT_BLOCKED: case ACCEPT_PENDING:
        (void)accept(c->extra, NULL, NULL);
        break;
    case RECVMSG_BLOCKED: case RECVMSG_PENDING: {
        char byte, control[CMSG_SPACE(sizeof(int))];
        struct iovec iov = { &byte, 1 };
        struct msghdr msg = { .msg_iov = &iov, .msg_iovlen = 1,
            .msg_control = control, .msg_controllen = sizeof(control) };
        (void)recvmsg(c->extra, &msg, 0);
        break;
    }
    case EPOLL_BLOCKED: case EPOLL_PENDING: {
        struct epoll_event event;
        (void)epoll_wait(c->epfd, &event, 1, -1);
        break;
    }
    case SLEEP_BLOCKED: {
        struct timespec delay = { .tv_sec = 100 };
        (void)nanosleep(&delay, NULL);
        break;
    }
    case OPEN_FIFO_BLOCKED:
        (void)open("cancel-fifo", O_RDONLY);
        break;
    case OPEN_PENDING:
        (void)open("cancel-file", O_CREAT | O_WRONLY | O_EXCL, 0600);
        break;
    case PREAD_PENDING: {
        char byte;
        (void)pread(c->extra, &byte, 1, 0);
        break;
    }
    case PWRITE_PENDING:
        (void)pwrite(c->extra, "y", 1, 0);
        break;
    }
    assert(!"cancellation point unexpectedly returned");
}

#ifdef WITH_CXX_CLEANUP
extern void filc_cancel_cxx_scope(void (*body)(void *), void *arg, void (*destroy)(void *));
static void cxx_cleanup(void *p)
{
    struct context *c = p;
    check_exit_state();
    assert(!atomic_load(&c->cleanups));
    assert(atomic_fetch_add(&c->cxx_destroyed, 1) == 0);
}
#endif

static void *worker(void *p)
{
    struct context *c = p;
    assert(!pthread_setspecific(c->key, c));
    if (c->scenario == READ_DISABLED)
        assert(!pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, NULL));
    if (c->scenario == COND_PENDING || c->scenario == COND_BLOCKED ||
        c->scenario == COND_SIGNAL)
        assert(!pthread_mutex_lock(&c->mutex));
    pthread_cleanup_push(outer_cleanup, c);
    pthread_cleanup_push(inner_cleanup, c);
#ifdef WITH_CXX_CLEANUP
    filc_cancel_cxx_scope(worker_body, c, cxx_cleanup);
#else
    worker_body(c);
#endif
    pthread_cleanup_pop(0);
    pthread_cleanup_pop(0);
    return NULL;
}

static void *other_waiter(void *p)
{
    struct context *c = p;
    assert(!pthread_mutex_lock(&c->mutex));
    atomic_store(&c->handler, 1);
    while (!c->predicate)
        assert(!pthread_cond_wait(&c->cond, &c->mutex));
    assert(!pthread_mutex_unlock(&c->mutex));
    return c;
}

static void run(enum scenario scenario)
{
    struct context c = { .scenario = scenario };
    assert(!pipe(c.pipefd));
    pthread_mutexattr_t attr;
    assert(!pthread_mutexattr_init(&attr));
    assert(!pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_ERRORCHECK));
    assert(!pthread_mutex_init(&c.mutex, &attr));
    assert(!pthread_mutexattr_destroy(&attr));
    assert(!pthread_cond_init(&c.cond, NULL));
    assert(!sem_init(&c.sem, 0, scenario == SEM_PENDING));
    assert(!pthread_key_create(&c.key, tsd_destroy));
    if (scenario == READ_PENDING || scenario == READV_PENDING || scenario == EPOLL_PENDING)
        assert(write(c.pipefd[1], "x", 1) == 1);
    if (scenario == WRITE_BLOCKED || scenario == WRITE_PARTIAL || scenario == WRITEV_BLOCKED) {
        c.capacity = fcntl(c.pipefd[1], F_GETPIPE_SZ);
        assert(c.capacity > 0);
        c.buffer = malloc(c.capacity * 2);
        assert(c.buffer);
        memset(c.buffer, 'x', c.capacity * 2);
        if (scenario != WRITE_PARTIAL)
            assert(write(c.pipefd[1], c.buffer, c.capacity) == c.capacity);
    }
    if (scenario == ACCEPT_BLOCKED || scenario == ACCEPT_PENDING) {
        c.extra = socket(AF_UNIX, SOCK_STREAM, 0);
        assert(c.extra >= 0);
        struct sockaddr_un addr = { .sun_family = AF_UNIX, .sun_path = "cancel-socket" };
        assert(!bind(c.extra, (struct sockaddr *)&addr, sizeof(addr)));
        assert(!listen(c.extra, 1));
        if (scenario == ACCEPT_PENDING) {
            c.peer = socket(AF_UNIX, SOCK_STREAM, 0);
            assert(c.peer >= 0);
            assert(!connect(c.peer, (struct sockaddr *)&addr, sizeof(addr)));
        }
    }
    if (scenario == RECVMSG_BLOCKED || scenario == RECVMSG_PENDING) {
        int pair[2];
        assert(!socketpair(AF_UNIX, SOCK_STREAM, 0, pair));
        c.extra = pair[0];
        c.peer = pair[1];
        if (scenario == RECVMSG_PENDING) {
            char control[CMSG_SPACE(sizeof(int))] = { 0 };
            struct iovec iov = { "x", 1 };
            struct msghdr msg = { .msg_iov = &iov, .msg_iovlen = 1,
                .msg_control = control, .msg_controllen = sizeof(control) };
            struct cmsghdr *cm = CMSG_FIRSTHDR(&msg);
            cm->cmsg_level = SOL_SOCKET;
            cm->cmsg_type = SCM_RIGHTS;
            cm->cmsg_len = CMSG_LEN(sizeof(int));
            memcpy(CMSG_DATA(cm), &c.pipefd[0], sizeof(int));
            assert(sendmsg(c.peer, &msg, 0) == 1);
        }
    }
    if (scenario == EPOLL_BLOCKED || scenario == EPOLL_PENDING) {
        c.epfd = epoll_create1(0);
        assert(c.epfd >= 0);
        struct epoll_event event = { .events = EPOLLIN, .data.ptr = &c };
        assert(!epoll_ctl(c.epfd, EPOLL_CTL_ADD, c.pipefd[0], &event));
    }
    if (scenario == OPEN_FIFO_BLOCKED)
        assert(!mkfifo("cancel-fifo", 0600));
    if (scenario == PREAD_PENDING || scenario == PWRITE_PENDING) {
        c.extra = open("cancel-file", O_CREAT | O_RDWR | O_EXCL, 0600);
        assert(c.extra >= 0);
        assert(write(c.extra, "x", 1) == 1);
    }
    if (scenario == JOIN_BLOCKED)
        assert(!pthread_create(&c.target, NULL, target, &c));
    if (scenario == READ_NESTED) {
        signal_context = &c;
        struct sigaction sa = { .sa_handler = handler, .sa_flags = SA_RESTART };
        assert(!sigemptyset(&sa.sa_mask));
        assert(!sigaction(SIGUSR1, &sa, NULL));
    }
    pthread_t thread, other;
    assert(!pthread_create(&thread, NULL, worker, &c));
    wait_flag(&c.ready);
    if (scenario == READ_BLOCKED || scenario == READ_DISABLED || scenario == READ_NESTED)
        wait_syscall(&c, SYS_read);
    if (scenario == POLL_BLOCKED)
        wait_syscall(&c, SYS_poll);
    if (scenario == COND_BLOCKED || scenario == SEM_BLOCKED ||
        scenario == JOIN_BLOCKED || scenario == COND_SIGNAL)
        wait_syscall(&c, SYS_futex);
    if (scenario == WRITE_BLOCKED || scenario == WRITE_PARTIAL)
        wait_syscall(&c, SYS_write);
    if (scenario == WRITEV_BLOCKED)
        wait_syscall(&c, SYS_writev);
    if (scenario == ACCEPT_BLOCKED)
        wait_syscall(&c, SYS_accept4);
    if (scenario == RECVMSG_BLOCKED)
        wait_syscall(&c, SYS_recvmsg);
    if (scenario == EPOLL_BLOCKED)
        wait_syscall(&c, SYS_epoll_wait);
    if (scenario == SLEEP_BLOCKED)
        wait_syscall(&c, SYS_clock_nanosleep);
    if (scenario == OPEN_FIFO_BLOCKED)
        wait_syscall(&c, SYS_openat);
    if (scenario == COND_SIGNAL) {
        assert(!pthread_create(&other, NULL, other_waiter, &c));
        wait_flag(&c.handler);
        /* Acquiring the mutex proves the other waiter has released it in wait. */
        assert(!pthread_mutex_lock(&c.mutex));
        assert(!pthread_mutex_unlock(&c.mutex));
    }
    if (scenario == READ_NESTED) {
        assert(!pthread_kill(thread, SIGUSR1));
        wait_flag(&c.handler);
    }
    if (scenario == WRITE_PARTIAL) {
        int bytes;
        do {
            assert(!ioctl(c.pipefd[0], FIONREAD, &bytes));
            sched_yield();
        } while (bytes != c.capacity);
    }
    if (scenario == COND_SIGNAL)
        assert(!pthread_mutex_lock(&c.mutex));
    if (scenario != EXIT_CLEANUP)
        assert(!pthread_cancel(thread));
    if (scenario == COND_SIGNAL) {
        c.predicate = 1;
        assert(!pthread_cond_signal(&c.cond));
        assert(!pthread_mutex_unlock(&c.mutex));
    }
    if (scenario == READ_PENDING || scenario == CLOSE_PENDING ||
        scenario == COND_PENDING || scenario == SEM_PENDING ||
        scenario == READV_PENDING || scenario == ACCEPT_PENDING ||
        scenario == RECVMSG_PENDING || scenario == EPOLL_PENDING ||
        scenario == OPEN_PENDING || scenario == PREAD_PENDING ||
        scenario == PWRITE_PENDING)
        atomic_store(&c.proceed, 1);
    if (scenario == READ_DISABLED)
        assert(write(c.pipefd[1], "x", 1) == 1);
    if (scenario == READ_NESTED) {
        /* Instruction-by-instruction notification placement is covered by the
           native gate test; here exercise actual Fil-C callback nesting. */
        struct timespec delay = { .tv_nsec = 10000000 };
        assert(!nanosleep(&delay, NULL));
        atomic_store(&c.release_handler, 1);
    }
    void *result;
    assert(!pthread_join(thread, &result));
    if (scenario == COND_SIGNAL)
        assert(result == &c || result == PTHREAD_CANCELED);
    else
        assert(result == (scenario == EXIT_CLEANUP ? (void *)&c : PTHREAD_CANCELED));
    assert(atomic_load(&c.cleanups) == 2 && atomic_load(&c.destroyed) == 1);
    if (scenario == READ_PENDING || scenario == READV_PENDING) {
        char byte;
        assert(read(c.pipefd[0], &byte, 1) == 1 && byte == 'x');
    }
    if (scenario == CLOSE_PENDING)
        assert(fcntl(c.pipefd[0], F_GETFD) != -1);
    if (scenario == SEM_PENDING) {
        int value;
        assert(!sem_getvalue(&c.sem, &value) && value == 1);
    }
    if (scenario == JOIN_BLOCKED) {
        atomic_store(&c.proceed, 1);
        assert(!pthread_join(c.target, &result) && result == &c);
    }
    if (scenario == COND_SIGNAL) {
        /* If the first waiter completed normally, it may have consumed the
           signal. If it cancelled, the sole remaining waiter must receive it. */
        if (result != PTHREAD_CANCELED) {
            assert(!pthread_mutex_lock(&c.mutex));
            assert(!pthread_cond_signal(&c.cond));
            assert(!pthread_mutex_unlock(&c.mutex));
        }
        assert(!pthread_join(other, &result) && result == &c);
    }
    if (scenario == WRITE_PARTIAL) {
        long count = atomic_load(&c.transferred);
        assert(count > 0);
        assert(read(c.pipefd[0], c.buffer, c.capacity * 2) == count);
    }
    if (scenario == WRITE_BLOCKED || scenario == WRITE_PARTIAL || scenario == WRITEV_BLOCKED)
        free(c.buffer);
    if (scenario == ACCEPT_BLOCKED || scenario == ACCEPT_PENDING) {
        if (scenario == ACCEPT_PENDING) {
            int accepted = accept(c.extra, NULL, NULL);
            assert(accepted >= 0);
            assert(!close(accepted));
            assert(!close(c.peer));
        }
        assert(!close(c.extra));
        assert(!unlink("cancel-socket"));
    }
    if (scenario == RECVMSG_BLOCKED || scenario == RECVMSG_PENDING) {
        if (scenario == RECVMSG_PENDING) {
            char byte, control[CMSG_SPACE(sizeof(int))];
            struct iovec iov = { &byte, 1 };
            struct msghdr msg = { .msg_iov = &iov, .msg_iovlen = 1,
                .msg_control = control, .msg_controllen = sizeof(control) };
            assert(recvmsg(c.extra, &msg, 0) == 1 && byte == 'x');
            struct cmsghdr *cm = CMSG_FIRSTHDR(&msg);
            assert(cm && cm->cmsg_level == SOL_SOCKET && cm->cmsg_type == SCM_RIGHTS);
            assert(cm->cmsg_len == CMSG_LEN(sizeof(int)));
            int received;
            memcpy(&received, CMSG_DATA(cm), sizeof(int));
            assert(fcntl(received, F_GETFD) >= 0);
            assert(!close(received));
        }
        assert(!close(c.extra));
        assert(!close(c.peer));
    }
    if (scenario == EPOLL_BLOCKED || scenario == EPOLL_PENDING) {
        if (scenario == EPOLL_PENDING) {
            struct epoll_event event;
            assert(epoll_wait(c.epfd, &event, 1, 0) == 1);
            assert(event.data.ptr == &c);
            /* Exercise the returned pointer's capability, not just its address. */
            assert(((struct context *)event.data.ptr)->scenario == EPOLL_PENDING);
        }
        assert(!close(c.epfd));
    }
    if (scenario == OPEN_FIFO_BLOCKED)
        assert(!unlink("cancel-fifo"));
    if (scenario == OPEN_PENDING) {
        assert(access("cancel-file", F_OK) == -1 && errno == ENOENT);
    }
    if (scenario == PREAD_PENDING || scenario == PWRITE_PENDING) {
        char byte;
        assert(pread(c.extra, &byte, 1, 0) == 1 && byte == 'x');
        assert(!close(c.extra));
        assert(!unlink("cancel-file"));
    }
    assert(!pthread_cond_destroy(&c.cond));
    assert(!pthread_mutex_destroy(&c.mutex));
    assert(!sem_destroy(&c.sem));
    assert(!pthread_key_delete(c.key));
    assert(!close(c.pipefd[0]));
    assert(!close(c.pipefd[1]));
}

int main(int argc, char **argv)
{
    assert(argc == 2);
    unsigned scenario = strtoul(argv[1], NULL, 10);
    assert(scenario <= PWRITE_PENDING);
    for (unsigned i = 0; i < 20; ++i)
        run(scenario);
    printf("scenario %u: 20 passes\n", scenario);
}
