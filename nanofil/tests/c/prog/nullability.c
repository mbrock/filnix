/* clang's nullability qualifiers, _Nullable, _Nonnull and
   _Null_unspecified, which zix's headers put on pointers; they do not
   change the type. */
#include <stdio.h>
#include <stddef.h>

typedef struct A A;
typedef void *_Nullable (*MallocFunc)(A *_Nullable a, size_t n);

static void *my(A *_Nullable a, size_t n) { return a ? NULL : (void *)(n * 2); }

int main(void)
{
    MallocFunc m = my;
    int x = 5;
    int *_Nonnull p = &x;
    int *_Null_unspecified const *q = &p;
    printf("%ld %d %d\n", (long)m(NULL, 21), *p, **q);
    return 0;
}
