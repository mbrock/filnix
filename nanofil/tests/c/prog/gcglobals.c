// Heap objects reachable only from globals (a list head, a pointer
// array, a static local) must survive forced collections, and pointer
// stores into globals must keep the store barrier. Run with
// FUGC_SCRIBBLE=1 FUGC_VERIFY=1 too.
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
struct node { long v; struct node *next; };
struct node *head;
static struct node *slots[64];
static struct node *keep(struct node *n) { static struct node *last; struct node *o = last; last = n; return o; }
static struct node *mk(long v, struct node *next) {
    struct node *n = malloc(sizeof *n);
    n->v = v; n->next = next; return n;
}
int main(void) {
    for (long i = 0; i < 20000; i++) {
        head = mk(i, head);
        slots[i % 64] = mk(-i, slots[(i + 1) % 64]);
        keep(mk(i * 2, 0));
        free(malloc(48));
        if (i % 5000 == 0) { zgc_request_and_wait(); zgc_request_fresh(); }
    }
    zgc_request_and_wait();
    zgc_request_and_wait();
    long sum = 0, len = 0;
    for (struct node *p = head; p; p = p->next) { sum += p->v; len++; }
    long s2 = 0;
    for (int k = 0; k < 64; k++) s2 += slots[k] ? slots[k]->v : 0;
    struct node *l = keep(0);
    printf("len %ld sum %ld slots %ld last %ld\n", len, sum, s2, l->v);
    return 0;
}
