/* GNU's obsolete designator syntax, `member: value`, as parted's
   label tables write it (clang accepts it with -Wgnu-designator). */
#include <stdio.h>
#include <stddef.h>

struct ops {
    int (*open)(int);
    const char *name;
    struct { int x, y; } pt;
    int last;
};

static int op(int x) { return x + 1; }

static struct ops o = { open: op, name: "pc98", pt: { y: 4, x: 3 }, last: 9 };

int main(void)
{
    struct ops q = { name: "x", last: 2 };
    int c = 1;
    struct ops r = { open: c ? op : NULL, last: c ? 7 : 8 };
    printf("%d %s %d %d %d\n", o.open(1), o.name, o.pt.x, o.pt.y, o.last);
    printf("%s %d %d %d %d\n", q.name, q.last, q.open == NULL, r.open(2), r.last);
    return 0;
}
