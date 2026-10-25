/* Concurrent-GC fixture: no fabricated state or allocation metadata.
   65536 exceeds FILC_MAX_BYTES_BETWEEN_POLLCHECKS (10000 at af813053).
   Dirty/reused aux allocation takes ensure_aux_ptr_slow_large's exit;
   size alone does not guarantee it (a zero_mode allocation skips it).
   FUGC_SCRIBBLE=1 and suspended scavenging make reuse observable. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

void large_store(void);
long c_is_marking(void);
static long **destination;
struct node { struct node *next; };
static struct node *volatile mark_work;

void *c_large(void)
{
    destination = malloc(65536);
    return destination;
}

void *c_value(long value)
{
    long *p = malloc(sizeof(*p));
    *p = value;
    return p;
}

void c_collect(void)
{
    zgc_request_and_wait();
    zgc_request_and_wait();
    /* A request is asynchronous. Wait for a real concurrent marking
       phase, not a guessed delay. The native probe only reads the same
       published state that nanofil's lower-barrier fast path reads.
       If a whole cycle ran between observations, request another. */
    for (;;) {
        zgc_cycle_number cycle = zgc_request_fresh();
        do {
            if (c_is_marking())
                return;
        } while (zgc_completed_cycle() < cycle);
    }
}

int main(void)
{
    zscavenger_suspend();
    /* Give each requested cycle real tracing work. With only the tiny
       source alive, marking can finish inside ensure-aux before its
       caller reaches the lower barrier. A chain cannot be traced in
       parallel; keep it rooted for the duration of the test. */
    for (int i = 0; i < 65536; ++i) {
        struct node *p = malloc(sizeof(*p));
        p->next = mark_work;
        mark_work = p;
    }
    for (int i = 0; i < 20; ++i) {
        large_store();
        zgc_request_and_wait();
        zgc_request_and_wait();
        if (**destination != 80)
            abort();
        destination = NULL;
    }
    puts("large store = 20 x 80");
    return 0;
}
