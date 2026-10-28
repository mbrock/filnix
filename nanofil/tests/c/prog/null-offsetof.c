/* Integer casts of addresses built from an integer constant fold, as
   clang and GCC fold them (C11 6.6p10): offsetof's old spelling
   (size_t)&((T *)0)->m in static initializers and case labels, a
   gperf string pool's (int)(size_t)&((struct pool *)0)->str, element
   addresses, pointer arithmetic, and a non-zero base. */
#include <stddef.h>
#include <stdio.h>
#define OLD_OFFSETOF(T, m) ((size_t)&((T *)0)->m)
struct inner { short a; long b[3]; };
struct s { char c; int x; struct inner in; };
struct pool { char str0[sizeof "alpha"]; char str1[sizeof "beta"]; char str2[sizeof "gamma"]; };
static const struct pool pool_contents = { "alpha", "beta", "gamma" };
#define POOL ((const char *)&pool_contents)
static const struct { int name; int value; } words[] = {
    { (int)(size_t)&((struct pool *)0)->str0, 1 },
    { (int)(size_t)&((struct pool *)0)->str1, 2 },
    { (int)(size_t)&((struct pool *)0)->str2, 3 },
};
static const size_t offs[] = {
    OLD_OFFSETOF(struct s, x), OLD_OFFSETOF(struct s, in.b[2]),
    (size_t)&((struct s *)16)->in, (size_t)((char *)0 + 12), (size_t)((int *)8 - 1),
    (size_t)&((char *)0)[5], (size_t)(void *)&((struct inner *)0)->b,
};
static int which(size_t off)
{
    switch (off) {
    case OLD_OFFSETOF(struct s, x): return 1;
    case OLD_OFFSETOF(struct s, in): return 2;
    case (size_t)&((struct s *)0)->in.b[1]: return 3;
    }
    return 0;
}
int main(void)
{
    for (unsigned i = 0; i < sizeof offs / sizeof offs[0]; i++)
        printf("%zu ", offs[i]);
    printf("\n");
    for (unsigned i = 0; i < 3; i++)
        printf("%s=%d ", POOL + words[i].name, words[i].value);
    printf("\n%d %d %d %d\n", which(offsetof(struct s, x)), which(offsetof(struct s, in)),
           which(offsetof(struct s, in.b[1])), which(3));
    return 0;
}
