/* An aligned typedef's alignment carries through _Alignas(type-name),
   to a member and an object, and to a parameter of that type, as
   clang lays them out. */
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#define MIS(x, n) ((int)((uintptr_t)(x) % (n)))
typedef int i32 __attribute__((aligned(32)));
struct T { char c; _Alignas(i32) char d; };
static int param(i32 p, char c)
{
    return MIS(&p, 32) + c;
}
int main(void)
{
    char pad = 1;
    _Alignas(i32) char ac = 2;
    printf("T %zu %zu %zu\n", sizeof(struct T), _Alignof(struct T), offsetof(struct T, d));
    printf("ac %d %d\n", MIS(&ac, 32), pad + ac);
    printf("param %d\n", param(5, 0));
    return 0;
}
