/* The declarators of one member declaration share its type (C11
   6.7.2.3p5): `struct { ... } found, saved_found;` declares one struct, so
   gnupg's hd->saved_found = hd->found assigns; tagged structs and enums
   alike. A variable named function_name does not hide __func__. */
#include <stdio.h>
struct h { struct { int k; long o; } found, saved; struct t { int x; } a, b; enum { EA, EB } e1, e2; };
int main(void) {
    int function_name = 3;
    struct h v = { {1, 2}, {0, 0}, {5}, {0}, EB, EA };
    v.saved = v.found; v.b = v.a; v.e2 = v.e1;
    printf("%d %ld %d %d %s %d\n", v.saved.k, v.saved.o, v.b.x, v.e2, __func__, function_name);
    return 0;
}
