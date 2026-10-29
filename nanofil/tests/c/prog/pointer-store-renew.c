/* Check renewal (docs/m7.md, round 4) of a pointer store under
   collection: under -O --checks=renew, h->next's read and pointer store
   in the loop renew the read before the loop, after a malloc and a
   forced collection each iteration. The Nix check runs it with
   FUGC_SCRIBBLE=1 FUGC_VERIFY=1, so a pointer store that skipped
   ensure-aux or lost h's rooting would show. */
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>
struct N { struct N *next; long v; };
static long __attribute__((noinline)) build(struct N *h, int n) {
    long seen = h->next != 0;
    for (int i = 0; i < n; i++) {
        struct N *x = malloc(sizeof *x);
        x->v = i;
        x->next = 0;
        if (i % 16 == 0) zgc_request_and_wait();
        x->next = h->next;
        h->next = x;
    }
    return seen;
}
int main(void) {
    struct N *h = calloc(1, sizeof *h);
    long seen = build(h, 200);
    zgc_request_and_wait();
    long sum = 0, len = 0;
    for (struct N *p = h->next; p; p = p->next) { sum += p->v; len++; }
    printf("%ld %ld %ld\n", seen, len, sum);
    return 0;
}
