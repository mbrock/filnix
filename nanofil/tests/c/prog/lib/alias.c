#include <stdio.h>
int bgcmd(int, char **);
void hi(void);
struct pair { long a, b, c; };
struct pair mk2(long);
int from_clang(void)
{
    char *argv[] = { "cc", 0 };
    hi();
    struct pair p = mk2(7);
    int (*volatile g)(int, char **) = bgcmd;
    return bgcmd(4, argv) + g(1, argv) + (int)p.c;
}
