/* A const, not volatile, arithmetic object defined with a constant
   initializer is a constant where its definition is visible, as clang
   folds it (C11 6.6p10): in static initializers (weston's barycentric
   table from block-scope consts), case labels, enumerators, static
   assertions and array sizes, which then declare ordinary arrays, so
   one can be initialized and its sizeof is a constant. A narrowing
   initializer folds converted; a float constant folds too. */
#include <stdint.h>
#include <stdio.h>
static const int K = 7;
static const int L = K + 1;
static const char C = 300;
static const double D = 2.5;
static int tab[] = { K, L, C };
static double dv = D * 2;
enum { E = K * 10 };
_Static_assert(L == 8, "L");
static int which(int k)
{
    switch (k) {
    case K: return 1;
    case L: return 2;
    }
    return 0;
}
int main(void)
{
    const uint32_t x = 0xff0000, y = 0x00ff00;
    static const uint32_t bary[][2] = { { x, y }, { y, x | 1 } };
    int arr[K] = { 1, 2 };
    const int n = 3;
    char buf[n * 2];
    printf("%d %d %d %g %d\n", tab[0], tab[1], tab[2], dv, E);
    printf("%x %x %d %d %zu %zu\n", bary[0][0], bary[1][1], arr[1], which(8), sizeof arr, sizeof buf);
    return 0;
}
