/* Pointer phis on polled back edges, in a function with local objects
   (stack-aux roots), under collection: with -O, phis of different blocks
   share shadow slots and roots (docs/perf.md item 9), and fewer shadow
   roots move the stack-aux roots after them. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

struct node {
    struct node *next;
    long v;
};

static void bump(long *cell, long by)
{
    *cell += by;
}

static long walk(int n)
{
    long acc[4] = { 0, 0, 0, 0 };
    long seen = 0;
    struct node *a = 0, *b = 0, *c = 0;
    for (int i = 0; i < n; i++) {
        struct node *x = malloc(sizeof *x);
        x->v = i;
        x->next = a;
        struct node *t = a;
        a = b;
        b = c;
        c = x;
        if (t)
            acc[i & 3] += t->v;
        if ((i & 63) == 0)
            zgc_request_and_wait();
    }
    for (struct node *p = a, *q = b; p || q;) {
        if (p) {
            bump(&seen, p->v);
            p = p->next;
        }
        if (q) {
            bump(&seen, 2 * q->v);
            q = q->next;
        }
        if ((seen & 255) == 0)
            zgc_request_and_wait();
    }
    for (struct node *r = c; r; r = r->next)
        seen += 3 * r->v;
    return seen + acc[0] + 3 * acc[1] + 5 * acc[2] + 7 * acc[3];
}

int main(void)
{
    printf("%ld %ld %ld\n", walk(0), walk(10), walk(1000));
    return 0;
}
