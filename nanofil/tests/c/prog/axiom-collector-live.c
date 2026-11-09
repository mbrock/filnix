// Runtime axiom "Collector live" (docs/runtime-axioms.md): at a
// safepoint the collector changes no object's region. Fil-C's runtime
// frees nothing by itself; a program with one thread and no signal
// handler keeps every object across polls and collections, live with
// the same bounds, and a freed one stays freed. Objects held by a
// local, through another object and by a global, of 16 bytes, 1008
// bytes and 1 MiB, cross many pollchecks (loops and calls) and forced
// collections; afterwards each still reads its last byte, still traps
// one past it, and the freed one still traps. Fil-C rounds an object's
// bounds up to 16 bytes, so every size here is a multiple of 16.
//
// The axiom keeps the regions of objects nothing names, which natively
// the collector does reclaim: the stronger reading, that no address is
// ever reused, is false (axiom-identity.c stops its claim at the first
// collection for that reason), and only how a held capability reads or
// traps is observable. A free at a safepoint by a signal handler the
// program installed, as in axiom-safepoint.c, is the program's code,
// not the collector's.
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <stdfil.h>
struct holder { char *p; long n; };
static const long sizes[3] = { 16, 1008, 1 << 20 };
static struct holder *held;
static char *global_obj[3];
static char *gone;
static char *probe;
static long probe_at;
static void read_probe(void) { volatile char x = probe[probe_at]; (void)x; }
static int trapped(char *p, long at) {
    probe = p;
    probe_at = at;
    fflush(stdout);
    pid_t c = fork();
    if (c == 0) { dup2(open("/dev/null", O_WRONLY), 2); read_probe(); _exit(0); }
    int st;
    waitpid(c, &st, 0);
    return WIFSIGNALED(st) && WTERMSIG(st) == SIGTRAP;
}
static char *make(long n, int tag) {
    char *p = malloc(n);
    memset(p, tag, n);
    return p;
}
static long churn(long k) {
    char *g = malloc(64);
    g[0] = (char)k;
    return g[0];
}
static int intact(char *p, long n, int tag) {
    return p[0] == tag && p[n - 1] == tag && !trapped(p, n - 1) && trapped(p, n);
}
int main(void) {
    char *local_obj[3];
    held = malloc(3 * sizeof *held);
    for (int i = 0; i < 3; i++) {
        local_obj[i] = make(sizes[i], 'a' + i);
        held[i].p = make(sizes[i], 'd' + i);
        held[i].n = sizes[i];
        global_obj[i] = make(sizes[i], 'g' + i);
    }
    char *in_register = make(32, 'r');
    gone = make(48, 'x');
    free(gone);
    long sum = 0;
    for (int round = 0; round < 6; round++) {
        for (long k = 0; k < 20000; k++) sum += churn(k) + in_register[k % 32];
        zgc_request_and_wait();
    }
    int ok = 1;
    for (int i = 0; i < 3; i++) ok &= intact(local_obj[i], sizes[i], 'a' + i);
    printf("objects held by a frame keep their bounds: %s\n", ok ? "yes" : "no");
    ok = 1;
    for (int i = 0; i < 3; i++) ok &= intact(held[i].p, held[i].n, 'd' + i);
    printf("objects held through an object keep their bounds: %s\n", ok ? "yes" : "no");
    ok = 1;
    for (int i = 0; i < 3; i++) ok &= intact(global_obj[i], sizes[i], 'g' + i);
    printf("objects held by a global keep their bounds: %s\n", ok ? "yes" : "no");
    printf("an object held in a register keeps its bounds: %s\n",
           intact(in_register, 32, 'r') && sum != 0 ? "yes" : "no");
    printf("a freed object stays freed: %s\n", trapped(gone, 0) ? "yes" : "no");
    return 0;
}
