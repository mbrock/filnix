// run: $lua_frontend 3
#include <math.h>
static char output[] = {"lua" ".out"};
static double infinity = HUGE_VAL;
int lua_frontend(int x) {
    typedef int *intptr;
    int *p = (__extension__ (intptr)(&x));
    int n = (__extension__ ({ int y = *p + 1; y; }));
    return n + sizeof output + output[3] + (infinity > 1.0e300);
}
