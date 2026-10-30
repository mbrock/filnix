/* A copy of more than 40 bytes checks both whole ranges before it
   writes anything, as filcc's does: this destination is 8 bytes short,
   so the copy traps with nothing written, and its reason is filcc's. */
// trap-reason
#include <stdio.h>
#include <stdlib.h>

struct big { int *p; long n[5]; const char *s; };   /* 56 bytes */

static int x = 42;

int main(void) {
    struct big a = { &x, { 1, 2, 3, 4, 5 }, "a" };
    long *room = calloc(6, sizeof(long));
    struct big *d = (struct big *)room;
    printf("before %ld\n", room[1]);
    fflush(stdout);
    *d = a;
    printf("after %ld\n", room[1]);
    return 0;
}
