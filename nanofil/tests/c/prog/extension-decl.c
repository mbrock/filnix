/* __extension__ before a block-scope declaration or static assertion
   (binutils' __extension__ typedef, ruby's __extension__ static_assert),
   and clang's nullability on a pointer typedef in specifier position
   (zix's ZixMallocFunc _Null_unspecified malloc), mean nothing. */
#include <stdio.h>
#include <assert.h>
int f(unsigned x) {
  __extension__ typedef unsigned long long ull;
  static_assert(sizeof(int) == 4, "int");
  _Static_assert(1, "x");
  int * _Nullable p = 0; int * _Nonnull q = (int *)&x; int * _Null_unspecified r = q;
  ull y = x; (void)p; (void)r;
  return (int)y + *q;
}

typedef void *(*MallocFunc)(unsigned long);
struct A { MallocFunc _Null_unspecified malloc; MallocFunc _Nonnull other; };
int g(struct A *a) { return a->malloc != 0; }
static void *mk(unsigned long n) { (void)n; return 0; }
int main(void)
{
    struct A a = { mk, mk };
    printf("%d %d\n", f(3), g(&a) + (a.other == mk));
    return 0;
}
