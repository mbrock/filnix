// glibc's socket functions under _GNU_SOURCE take transparent unions
// (__SOCKADDR_ARG, __CONST_SOCKADDR_ARG): any sockaddr pointer passes.
// An AF_UNIX server and a forked client, and an AF_INET bind.
#define _GNU_SOURCE
#include <arpa/inet.h>
#include <netinet/in.h>
#include <stdio.h>
#include <string.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <unistd.h>

int main(void) {
    struct sockaddr_un addr = { .sun_family = AF_UNIX };
    strcpy(addr.sun_path, "sock");
    int s = socket(AF_UNIX, SOCK_STREAM, 0);
    if (bind(s, &addr, sizeof addr) || listen(s, 1)) { perror("bind"); return 1; }
    pid_t pid = fork();
    if (pid == 0) {
        int c = socket(AF_UNIX, SOCK_STREAM, 0);
        if (connect(c, (const struct sockaddr_un *)&addr, sizeof addr)) _exit(2);
        const char msg[] = "hello over a socket";
        write(c, msg, sizeof msg);
        close(c);
        _exit(0);
    }
    struct sockaddr_un peer;
    socklen_t len = sizeof peer;
    int a = accept(s, &peer, &len);
    char buf[64] = { 0 };
    ssize_t n = read(a, buf, sizeof buf);
    int status;
    waitpid(pid, &status, 0);
    printf("%zd %s %d %d\n", n, buf, peer.sun_family, WEXITSTATUS(status));
    struct sockaddr_un name;
    len = sizeof name;
    getsockname(s, &name, &len);
    printf("%s %d\n", name.sun_path, len > 2);
    close(a);
    close(s);
    unlink("sock");

    struct sockaddr_in in = { .sin_family = AF_INET, .sin_addr.s_addr = htonl(INADDR_LOOPBACK) };
    int t = socket(AF_INET, SOCK_DGRAM, 0);
    printf("%d ", bind(t, (struct sockaddr *)&in, sizeof in));
    struct sockaddr_in6 got;
    len = sizeof got;
    printf("%d %d %u\n", getsockname(t, &got, &len), ((struct sockaddr_in *)&got)->sin_family,
           (unsigned)len);
    close(t);
    return 0;
}
