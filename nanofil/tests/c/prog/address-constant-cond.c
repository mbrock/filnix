/* A conditional with an integer constant condition is the address
   constant of the arm it chooses, as clang accepts it in a static
   initializer (C11 6.6p10): nettle's curve tables pick a function by
   `USE_REDC ? redc : modp`. Arms are functions, arrays plus an offset,
   members, a null pointer and a nested conditional. */
#include <stdio.h>

static int redc(int x) { return x * 2; }
static int modp(int x) { return x + 100; }
static const int tab[4] = { 10, 20, 30, 40 };
static struct { int a, b; } pair = { 5, 6 };

#define USE_REDC 0
#define WIDE 1

struct curve {
    int (*reduce)(int);
    int (*other)(int);
    const int *limb;
    const int *none;
    int *member;
};

static const struct curve curves[2] = {
    { USE_REDC ? redc : modp, WIDE ? redc : modp, WIDE ? tab + 2 : tab, 0 ? tab : 0,
      &pair.b },
    { 1 ? (0 ? modp : redc) : modp, modp, !WIDE ? tab : &tab[3], WIDE - 1 ? tab : 0,
      sizeof(int) == 4 ? &pair.a : &pair.b },
};

int main(void)
{
    for (int i = 0; i < 2; i++) {
        const struct curve *c = &curves[i];
        printf("%d %d %d %d %d\n", c->reduce(3), c->other(4), *c->limb,
               c->none == 0, *c->member);
    }
    return 0;
}
