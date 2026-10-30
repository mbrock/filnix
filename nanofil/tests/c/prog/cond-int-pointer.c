/* A ?: with a pointer arm and an integer arm that is not a null
   pointer constant violates C11 6.5.15p3, but clang and GCC only warn
   and give the pointer type, converting the integer as a cast does.
   Ruby's error.c has RBOOL(FIXNUM_P(num) ? num == e : rb_equal(num, e))
   with VALUE a pointer under Fil-C. An integer made a pointer has no
   capability, so it can be compared but not dereferenced. */
// cflags: -Wno-conditional-type-mismatch
#include <stdio.h>

struct s { int v; };
static struct s g = {5};

static struct s *pick(int c, int k) { return c ? k == 3 : &g; }
static long back(int c, struct s *p) { return (long)(c ? p : 7); }
static char *gnu(long x, char *p) { return x ?: p; }

int main(void) {
    printf("%d %d\n", pick(1, 3) == (struct s *)1, pick(0, 3)->v);
    printf("%ld %d\n", back(0, &g), back(1, &g) == (long)&g);
    printf("%zu\n", sizeof(1 ? (unsigned char)2 : (char *)0 + 1));
    char buf[] = "gnu";
    printf("%s %d\n", gnu(0, buf), gnu(9, buf) == (char *)9);
    return 0;
}
