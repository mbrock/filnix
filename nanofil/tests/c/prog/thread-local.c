/* Thread-local variables against clang's. Eight threads each count,
   build linked lists and update arrays in thread-locals that nanofil
   defines (here) and that clang defines (lib/thread-local.c), each
   module reaching the other's through its getter. Every thread must
   see its own instances, freshly initialized: the counts, list lengths
   and initializers come out the same in every thread, the sums are the
   thread's own, the addresses differ between threads, and main's own
   instances are untouched. The lists hold the only pointers to
   their nodes, so a collection (forced every few hundred rounds) that
   did not see a thread's thread-locals would free nodes still in use.
   Taking a thread-local's address in a static initializer is refused
   (C11 6.6p9), as clang refuses it. */
// link: lib/thread-local.c
#include <pthread.h>
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include "lib/thread-local.h"

_Thread_local long nf_count;
__thread struct node *nf_list;
_Thread_local int nf_init = 100;
_Thread_local char nf_name[16] = "nanofil";
static _Thread_local struct { int a[3]; const char *s; void *self; } nf_local = { { 7, 8, 9 }, "local" };

static int static_local(void)
{
    static _Thread_local int calls = 10;
    return calls++;
}

struct result { long counts, nf_sum, nf_len, check, init, pairs, statics; int distinct; };

static long *addresses[THREADS], *clang_addresses[THREADS];
static pthread_barrier_t barrier;

static void *work(void *arg)
{
    int id = (int)(long)arg;
    struct result *r = calloc(1, sizeof *r);
    r->init = nf_init + cl_init + nf_local.a[1] + (long)strlen(nf_name) + (long)strlen(nf_local.s);
    nf_local.self = &nf_local;
    nf_init += id;            /* other threads must not see these */
    cl_init += id;
    nf_name[0] = 'N';
    for (int i = 0; i < ROUNDS; i++) {
        struct node *n = malloc(sizeof *n);
        n->value = id * 100000 + i;
        n->next = nf_list;
        nf_list = n;
        nf_count++;
        r->counts += clang_round(id, i, &nf_count);
        if (i % 500 == 0)
            zgc_request_and_wait();
    }
    long sum = 0, len = 0;
    for (struct node *n = nf_list; n; n = n->next) {
        sum += n->value;
        len++;
    }
    r->nf_sum = sum;
    r->nf_len = len;
    r->check = clang_check(id);
    for (int k = 0; k < 4; k++)
        r->pairs += cl_pairs.a[k];
    r->pairs -= id * ROUNDS;
    for (int k = 0; k < 5; k++)
        r->statics += static_local() + clang_static_local();
    addresses[id] = &nf_count;
    clang_addresses[id] = clang_counter_address();
    /* Every thread is still alive here, so its addresses are distinct. */
    pthread_barrier_wait(&barrier);
    r->distinct = nf_local.self == &nf_local;
    for (int k = 0; k < THREADS; k++)
        if (k != id && (addresses[k] == &nf_count || clang_addresses[k] == &cl_count))
            r->distinct = 0;
    pthread_barrier_wait(&barrier);
    return r;
}

int main(void)
{
    pthread_t threads[THREADS];
    pthread_barrier_init(&barrier, 0, THREADS);
    nf_count = 1000;              /* main's own instances */
    cl_count = 2000;
    for (long id = 0; id < THREADS; id++)
        pthread_create(&threads[id], 0, work, (void *)id);
    for (int id = 0; id < THREADS; id++) {
        struct result *r;
        pthread_join(threads[id], (void **)&r);
        printf("thread: counts %ld nf %ld/%ld check %ld init %ld pairs %ld statics %ld distinct %d\n",
               r->counts, r->nf_sum, r->nf_len, r->check, r->init, r->pairs, r->statics, r->distinct);
    }
    printf("main: %ld %ld %d %d %s %d %d\n", nf_count, cl_count, nf_init, cl_init, nf_name,
           static_local(), clang_static_local());
    return 0;
}
