/* Under -fcommon a tentative definition of an external object (C11
   6.9.2p2) is a common symbol, which clang gives Fil-C as a weak
   definition: two units may both define `int shared;`, and the link
   keeps one object. One initialized elsewhere (counted) wins over the
   tentative one; a static tentative definition stays each unit's own.
   Older packages rely on this (GCC 10 and clang 11 made -fno-common
   the default). */
// cflags: -fcommon
// nanofil-link: lib/common.c
#include <stdio.h>

int shared;
int counted;
struct rec { long n; int *p; } rec;
static int own = 1;

void bump(void);
int lib_own(void);

int main(void) {
    static int x = 40;
    shared = 2;
    rec.p = &x;
    bump();
    printf("%d %d %ld %d\n", shared, counted, rec.n, *rec.p);
    printf("%d %d\n", own, lib_own());
    return 0;
}
