/* GCC's alias attribute, as dash's bgcmd uses it. Inside this
   translation unit an alias is its target: calls reach it and its
   address is the target's. clang (lib/alias.c) calls the exported
   aliases through their own names. An alias may take its type from
   typeof, as libapparmor's __old_change_hat does. */
// link: lib/alias.c
#include <stdio.h>

int fgcmd(int argc, char **argv) { return argc * 10 + (argv[0][0] - 'a'); }
int bgcmd(int, char **) __attribute__((__alias__("fgcmd")));
static long twice(long x) { return 2 * x; }
static long dbl(long) __attribute__((alias("twice")));
void hello(void) { puts("hello"); }
extern void hi(void) __attribute__((alias("hello")));
struct pair { long a, b, c; };
struct pair mk(long x) { struct pair p = { x, x + 1, x + 2 }; return p; }
struct pair mk2(long) __attribute__((alias("mk")));
extern typeof((fgcmd)) old_fgcmd __attribute__((alias("fgcmd")));
typeof(hello) hi2 __attribute__((alias("hello")));
extern typeof(mk) mk3 __attribute__((weak, alias("mk")));

int from_clang(void);

int main(void)
{
    char *argv[] = { "bb", 0 };
    printf("%d %ld\n", bgcmd(2, argv), dbl(21));
    printf("%d %d\n", &bgcmd == &fgcmd, dbl == twice);
    int (*f)(int, char **) = bgcmd;
    printf("%d\n", f(3, argv));
    hi();
    struct pair p = mk2(5);
    printf("%ld %ld %ld\n", p.a, p.b, p.c);
    hi2();
    printf("%d %ld\n", old_fgcmd(5, argv), mk3(8).b);
    printf("%d\n", from_clang());
    return 0;
}
