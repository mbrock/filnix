/* Exercises a broad set of libpizlo's zsys functions through glibc and prints
   only deterministic results, so runs against two libpizlo builds can be
   compared with diff. check.sh runs it against the stock and split builds. */

#include <dirent.h>
#include <errno.h>
#include <fcntl.h>
#include <poll.h>
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/epoll.h>
#include <sys/eventfd.h>
#include <sys/mman.h>
#include <sys/random.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/time.h>
#include <sys/wait.h>
#include <time.h>
#include <unistd.h>

static volatile sig_atomic_t got_signal;
static void on_usr1(int sig) { got_signal = sig; }

static void* thread_main(void* arg)
{
    int* value = arg;
    *value *= 2;
    return value;
}

int main(void)
{
    char path[] = "/tmp/filc-smoke-XXXXXX";
    int fd = mkstemp(path);
    printf("write: %zd\n", write(fd, "hello, libpizlo\n", 16));
    printf("lseek: %ld\n", (long)lseek(fd, 0, SEEK_SET));
    char buf[64] = { 0 };
    printf("read: %zd %s", read(fd, buf, sizeof(buf) - 1), buf);
    struct stat st;
    printf("fstat: %d size=%lld\n", fstat(fd, &st), (long long)st.st_size);
    struct timeval times[2] = { { 1000, 0 }, { 2000, 0 } };
    printf("utimes: %d\n", utimes(path, times));
    printf("stat: %d mtime=%lld\n", stat(path, &st), (long long)st.st_mtime);
    close(fd);
    printf("open missing: %d errno=%d\n", open("/nonexistent/x", O_RDONLY), errno);

    int pipefd[2];
    printf("pipe: %d\n", pipe(pipefd));
    pid_t child = fork();
    if (!child) {
        write(pipefd[1], "child", 5);
        _exit(7);
    }
    int status;
    waitpid(child, &status, 0);
    memset(buf, 0, sizeof(buf));
    read(pipefd[0], buf, 5);
    printf("fork+wait: exit=%d pipe=%s\n", WEXITSTATUS(status), buf);

    pthread_t thread;
    int value = 21;
    void* result;
    pthread_create(&thread, NULL, thread_main, &value);
    pthread_join(thread, &result);
    printf("pthread: %d same=%d\n", value, result == &value);

    char* map = mmap(NULL, 8192, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    map[8191] = 'x';
    printf("mmap: %c madvise=%d munmap=%d\n", map[8191], madvise(map, 8192, MADV_DONTNEED), munmap(map, 8192));

    int sv[2];
    printf("socketpair: %d\n", socketpair(AF_UNIX, SOCK_STREAM, 0, sv));
    send(sv[0], "ping", 4, 0);
    struct pollfd pfd = { .fd = sv[1], .events = POLLIN };
    printf("poll: %d revents=%d\n", poll(&pfd, 1, 1000), pfd.revents);
    int ep = epoll_create1(0);
    struct epoll_event ev = { .events = EPOLLIN, .data.ptr = &value }, out;
    epoll_ctl(ep, EPOLL_CTL_ADD, sv[1], &ev);
    int n = epoll_wait(ep, &out, 1, 1000);
    printf("epoll: %d ptr_ok=%d\n", n, out.data.ptr == &value && *(int*)out.data.ptr == 42);
    memset(buf, 0, sizeof(buf));
    printf("recv: %zd %s\n", recv(sv[1], buf, sizeof(buf), 0), buf);

    int efd = eventfd(3, 0);
    unsigned long long counter;
    printf("eventfd: %zd %llu\n", read(efd, &counter, sizeof(counter)), counter);

    signal(SIGUSR1, on_usr1);
    raise(SIGUSR1);
    printf("signal: %d\n", got_signal);

    unsigned char random_bytes[16];
    printf("getrandom: %zd\n", getrandom(random_bytes, sizeof(random_bytes), 0));
    struct timespec ts;
    printf("clock_gettime: %d\n", clock_gettime(CLOCK_MONOTONIC, &ts));
    struct timespec nap = { 0, 1000000 };
    printf("nanosleep: %d\n", nanosleep(&nap, NULL));

    DIR* dir = opendir("/");
    int entries = 0;
    while (readdir(dir))
        entries++;
    closedir(dir);
    printf("readdir: %d\n", entries > 2);
    printf("unlink: %d\n", unlink(path));
    printf("float: %.3f\n", 3.14159);
    return 0;
}
