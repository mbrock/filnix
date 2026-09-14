/* Exercise the actual native cancellation gate before integrating user-libc
   unwinding. This test reports gate outcomes; it does not claim to implement
   pthread_cancel. Build with -I/path/to/libpas/src/libpas and that tree's
   filc_cancel_syscall.S. Run each case in a fresh process under a timeout.

   0 pending read, 1 blocked read, 2 nested handler, 3 disabled read,
   4 partial write, 5 successful read with cancellation during result handling,
   6 pending close, 7 completed close, 8 exiting read, 9 interrupted poll. */
#define _GNU_SOURCE
#include <assert.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/syscall.h>
#include <sys/mman.h>
#include <sys/ptrace.h>
#include <sys/user.h>
#include <sys/wait.h>
#include <time.h>
#include <ucontext.h>
#include <unistd.h>
#include "filc_cancel_syscall.h"

static unsigned control;
static _Thread_local const unsigned* active_control;
static atomic_int tid, entered_handler, release_handler, left_handler;
static atomic_int got_result, release_result, finished;
static atomic_int notification_seen;
static int fds[2], which, cancel_signal, replacement = -1;
static filc_cancel_syscall_result outcome;
static char bytes[1024 * 1024];

static void cancel_handler(int sig, siginfo_t* info, void* context)
{
    (void)info;
    ucontext_t* uc = context;
    if (!active_control)
        return;
    atomic_store(&notification_seen, 1);
    unsigned value = __atomic_load_n(active_control, __ATOMIC_ACQUIRE);
    if ((value & (FILC_CANCEL_DISABLED | FILC_CANCEL_PENDING | FILC_CANCEL_EXITING))
        != FILC_CANCEL_PENDING)
        return;
    uintptr_t pc = uc->uc_mcontext.gregs[REG_RIP];
    sigaddset(&uc->uc_sigmask, sig);
    if (pc >= (uintptr_t)filc_cancel_syscall_begin
        && pc < (uintptr_t)filc_cancel_syscall_end) {
        uc->uc_mcontext.gregs[REG_RIP] = (uintptr_t)filc_cancel_syscall_abort;
        return;
    }
    /* Keep the notification blocked in this context but pending for the
       outer signal return. The production runtime must preserve this across
       its own native-to-Fil-C callback and mask restoration. */
    syscall(SYS_tgkill, getpid(), syscall(SYS_gettid), sig);
}

static void app_handler(int sig)
{
    (void)sig;
    atomic_store(&entered_handler, 1);
    while (!atomic_load(&release_handler)) {}
    atomic_store(&left_handler, 1);
}

static void delay(void)
{
    struct timespec ts = {0, 1000000};
    while (nanosleep(&ts, &ts) && errno == EINTR) {}
}

static void wait_flag(atomic_int* flag)
{
    for (int n = 0; n < 3000 && !atomic_load(flag); ++n)
        delay();
    assert(atomic_load(flag));
}

static int blocked(void)
{
    char path[128], line[256];
    snprintf(path, sizeof(path), "/proc/self/task/%d/syscall", atomic_load(&tid));
    FILE* f = fopen(path, "r");
    if (!f) return 0;
    int got = fgets(line, sizeof(line), f) != NULL;
    fclose(f);
    long nr = -1;
    unsigned long fd = 0;
    return got && sscanf(line, "%ld %lx", &nr, &fd) == 2
        && (which == 9 ? nr == SYS_poll :
            nr == (which == 4 ? SYS_write : SYS_read)
            && fd == (unsigned long)fds[which == 4]);
}

static void wait_blocked(void)
{
    for (int n = 0; n < 3000 && !blocked(); ++n)
        delay();
    assert(blocked());
}

static void notify_cancel(pthread_t worker)
{
    unsigned previous = __atomic_fetch_or(&control, FILC_CANCEL_PENDING, __ATOMIC_RELEASE);
    if (!(previous & (FILC_CANCEL_DISABLED | FILC_CANCEL_EXITING)))
        assert(!pthread_kill(worker, cancel_signal));
}

static void* worker(void* ignored)
{
    (void)ignored;
    atomic_store(&tid, (int)syscall(SYS_gettid));
    active_control = &control;
    if (which == 6 || which == 7) {
        outcome = filc_cancel_syscall(&control, SYS_close, fds[0], 0, 0, 0, 0, 0);
    } else if (which == 9) {
        struct pollfd pfd = {.fd = fds[0], .events = POLLIN};
        outcome = filc_cancel_syscall(&control, SYS_poll, (long)&pfd, 1, -1, 0, 0, 0);
    } else {
        outcome = filc_cancel_syscall(&control, which == 4 ? SYS_write : SYS_read,
            fds[which == 4], (long)bytes, which == 4 ? sizeof(bytes) : 1, 0, 0, 0);
    }
    if (which == 5 || which == 7) {
        atomic_store(&got_result, 1);
        while (!atomic_load(&release_result)) {}
    }
    /* Only ordinary read/write/poll EINTR is classified here. Close is
       explicitly excluded, and a successful result is never reconsidered. */
    if (which != 6 && which != 7 && outcome.value == -EINTR
        && (__atomic_load_n(&control, __ATOMIC_ACQUIRE) & 25) == 8)
        outcome.canceled = 1;
    active_control = NULL;
    atomic_store(&finished, 1);
    return NULL;
}

/* Stop at each actual instruction, then inject cancellation. This tests the
   final-check-to-syscall window without adding an instrumentation call to it.
   A queued byte makes stepping over the syscall deterministic; injection at
   the first post-syscall instruction must preserve that consumed byte. */
static void instruction_window(unsigned long offset)
{
    unsigned* state = mmap(NULL, 4096, PROT_READ | PROT_WRITE,
        MAP_SHARED | MAP_ANONYMOUS, -1, 0);
    assert(state != MAP_FAILED);
    *state = 0;
    assert(write(fds[1], "x", 1) == 1);
    pid_t child = fork();
    assert(child >= 0);
    if (!child) {
        active_control = state;
        assert(!ptrace(PTRACE_TRACEME, 0, NULL, NULL));
        raise(SIGSTOP);
        char byte;
        filc_cancel_syscall_result result = filc_cancel_syscall(
            state, SYS_read, fds[0], (long)&byte, 1, 0, 0, 0);
        unsigned long end = filc_cancel_syscall_end - filc_cancel_syscall_begin;
        assert(result.canceled == (long)(offset < end));
        if (offset >= end) assert(result.value == 1 && byte == 'x');
        _exit(0);
    }
    int status;
    assert(waitpid(child, &status, 0) == child && WIFSTOPPED(status));
    uintptr_t target = (uintptr_t)filc_cancel_syscall_begin + offset;
    unsigned steps;
    for (steps = 0; steps < 100000; ++steps) {
        struct user_regs_struct regs;
        assert(!ptrace(PTRACE_GETREGS, child, NULL, &regs));
        if (regs.rip == target) break;
        assert(!ptrace(PTRACE_SINGLESTEP, child, NULL, NULL));
        assert(waitpid(child, &status, 0) == child && WIFSTOPPED(status));
        assert(WSTOPSIG(status) == SIGTRAP);
    }
    assert(steps < 100000);
    __atomic_store_n(state, FILC_CANCEL_PENDING, __ATOMIC_RELEASE);
    assert(!ptrace(PTRACE_CONT, child, NULL, (void*)(long)cancel_signal));
    assert(waitpid(child, &status, 0) == child);
    assert(WIFEXITED(status) && WEXITSTATUS(status) == 0);
    printf("instruction-offset=%lu steps=%u passed\n", offset, steps);
    assert(!munmap(state, 4096));
}

int main(int argc, char** argv)
{
    assert(argc == 2 || argc == 3);
    which = atoi(argv[1]);
    assert(which >= 0 && which <= 10);
    alarm(10);
    assert(atomic_is_lock_free(&finished));
    assert(__atomic_always_lock_free(sizeof(control), &control));
    cancel_signal = SIGRTMIN;
    struct sigaction sa = {.sa_sigaction = cancel_handler, .sa_flags = SA_SIGINFO | SA_RESTART};
    sigemptyset(&sa.sa_mask);
    assert(!sigaction(cancel_signal, &sa, NULL));
    struct sigaction app = {.sa_handler = app_handler, .sa_flags = SA_RESTART};
    sigemptyset(&app.sa_mask);
    assert(!sigaction(SIGUSR1, &app, NULL));
    assert(!pipe(fds));
    if (which == 10) {
        assert(argc == 3);
        instruction_window(strtoul(argv[2], NULL, 0));
        return 0;
    }
    if (which == 0 || which == 6) control = FILC_CANCEL_PENDING;
    if (which == 3) control = FILC_CANCEL_DISABLED;
    if (which == 8) control = FILC_CANCEL_EXITING | FILC_CANCEL_PENDING;
    if (which == 5) assert(write(fds[1], "x", 1) == 1);
    pthread_t thread;
    assert(!pthread_create(&thread, NULL, worker, NULL));
    if (which == 5 || which == 7) {
        wait_flag(&got_result);
        if (which == 7) {
            assert(fcntl(fds[0], F_GETFD) == -1 && errno == EBADF);
            replacement = open("/dev/null", O_RDONLY);
            assert(replacement == fds[0]);
        }
        notify_cancel(thread);
        wait_flag(&notification_seen);
        atomic_store(&release_result, 1);
    } else if (which != 0 && which != 6) {
        wait_blocked();
        if (which == 2) {
            assert(!pthread_kill(thread, SIGUSR1));
            wait_flag(&entered_handler);
        }
        notify_cancel(thread);
        if (which == 2) {
            wait_flag(&notification_seen);
            assert(!atomic_load(&finished));
            atomic_store(&release_handler, 1);
        }
        if (which == 3 || which == 8) {
            for (int i = 0; i < 30; ++i) delay();
            assert(!atomic_load(&finished));
            assert(write(fds[1], "x", 1) == 1);
        }
    }
    wait_flag(&finished);
    assert(!pthread_join(thread, NULL));
    if (which == 0 || which == 1 || which == 2 || which == 6 || which == 9)
        assert(outcome.canceled);
    else
        assert(!outcome.canceled);
    if (which == 2) assert(atomic_load(&left_handler));
    if (which == 3 || which == 5 || which == 8) assert(outcome.value == 1);
    if (which == 6) assert(fcntl(fds[0], F_GETFD) >= 0);
    if (which == 7) assert(outcome.value == 0 && fcntl(replacement, F_GETFD) >= 0);
    if (which == 4) {
        assert(outcome.value > 0 && (unsigned long)outcome.value < sizeof(bytes));
        assert(!close(fds[1]));
        long total = 0, n;
        while ((n = read(fds[0], bytes, sizeof(bytes))) > 0) total += n;
        assert(n == 0 && total == outcome.value);
    }
    printf("case=%d canceled=%ld result=%ld passed\n", which, outcome.canceled, outcome.value);
    return 0;
}
