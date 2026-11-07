// Runtime axiom "Retention under concurrent free" (docs/runtime-axioms.md):
// memory is not reclaimed while this thread may still reach it. Another
// thread frees the object a loop reads, then allocates, fills and
// collects to tempt the allocator into reusing its memory. The loop must
// read the object's bytes or trap, never other values. The obvious
// wrong strengthening, that no free comes between a check and its
// access, is false under threads: here it may, and retention is what
// keeps the access safe.
#include <pthread.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <stdfil.h>
static long *obj;
static void *freer(void *arg) {
    (void)arg;
    usleep(2000);
    free(obj);
    for (int k = 0; k < 2000; k++) memset(malloc(64), 0xff, 64);
    zgc_request_and_wait();
    return 0;
}
static void loop(void) {
    pthread_t t;
    pthread_create(&t, 0, freer, 0);
    for (long n = 0; n < 4000000000L; n++)
        if (obj[n & 7] != (n & 7) + 100) { printf("garbage\n"); _exit(1); }
    _exit(2);
}
int main(void) {
    obj = malloc(64);
    for (int i = 0; i < 8; i++) obj[i] = i + 100;
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); loop(); }
    int st;
    waitpid(c, &st, 0);
    printf("the loop read only retained bytes, then trapped: %s\n",
           WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP ? "yes" : "no");
    return 0;
}
