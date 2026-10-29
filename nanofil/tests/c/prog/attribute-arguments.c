/* Only an attribute's name counts, never an identifier among its
   arguments: cleanup functions named weak, destructor and aligned are
   functions, not the weak, destructor and aligned attributes (c_types
   attr_entry/3). Before, nanofil refused the char below as aligned. */
#include <stdio.h>

static void weak(int *p) { printf("weak %d\n", *p); }
static void destructor(int *p) { printf("destructor %d\n", *p); }
static void aligned(char *p) { printf("aligned %d\n", *p); }
static void mode(long *p) { printf("mode %ld %zu\n", *p, sizeof *p); }

int main(void)
{
    __attribute__((cleanup(weak))) int x = 1;
    __attribute__((cleanup(destructor))) int y = 2;
    __attribute__((cleanup(aligned))) char z = 3;
    __attribute__((cleanup(mode), unused)) long m = 4;
    printf("%zu %zu %d\n", _Alignof(__typeof__(z)), sizeof m, x + y + z);
    return 0;
}
