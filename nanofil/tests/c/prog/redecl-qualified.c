/* Redeclarations that agree, qualifiers included (C11 6.2.7p2-3,
   6.7.3p10), whatever order the sizes and prototypes arrive in. A
   parameter's own qualifiers do not count (6.7.6.3p15). The mismatched
   forms are in tests/c/reject/redecl-*.c. */
#include <stdio.h>

extern const char *const names[];
const char *const names[] = { "a", "b" };
extern volatile int ticks;
volatile int ticks = 3;
extern int *restrict cursor;
int *restrict cursor;
int scale(const int k);
int scale(int k) { return k * 2; }
int total(const char *s, ...);
int use(void) { extern const int limit; return limit; }
extern const int limit;
const int limit = 7;
typedef const int cint;
extern cint shared;
const int shared = 11;

int main(void) {
    int x = 4;
    cursor = &x;
    printf("%s %s %d %d %d %d %d\n", names[0], names[1], ticks, *cursor,
           scale(5), use(), shared);
    return 0;
}
