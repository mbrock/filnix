// Runtime axiom "Rooting" (docs/runtime-axioms.md): the collector sees
// the values in a frame and every pointer stored in a reachable object,
// so it never reclaims what the program can still name. Objects held
// only by a local, and one held only through another object, survive
// forced collections and heavy allocation of their size; the gc-stress
// steps run this with FUGC_SCRIBBLE=1, which overwrites reclaimed
// memory. gcglobals.c probes the same for globals.
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdfil.h>
struct node { long v[4]; struct node *next; };
static struct node *make(long v, struct node *next) {
    struct node *n = malloc(sizeof *n);
    for (int i = 0; i < 4; i++) n->v[i] = v + i;
    n->next = next;
    return n;
}
int main(void) {
    struct node *local = make(100, make(200, 0));
    for (int round = 0; round < 6; round++) {
        for (int k = 0; k < 4000; k++) memset(malloc(sizeof(struct node)), 0xff, sizeof(struct node));
        zgc_request_and_wait();
    }
    int intact = 1;
    for (int i = 0; i < 4; i++)
        if (local->v[i] != 100 + i || local->next->v[i] != 200 + i) intact = 0;
    printf("objects reachable from a frame survive collection: %s\n", intact ? "yes" : "no");
    return 0;
}
