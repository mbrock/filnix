// Identifiers spelled "none", which nanofil's parse tree once also used
// for "no name": a global, a parameter that shadows it, a local, struct
// and enum tags, and a member next to an anonymous one (also designated).
#include <stdio.h>

int none = 40;

struct none { int x; struct none *next; };

struct holder {
    struct { int a; int b; };
    int none;
};

static int bump(int none) { return none + 1; }
static int sum(struct none *none) { return none->x + none->next->x; }
static int count(void)
{
    enum none { A = 2, B };     /* tags share a namespace: a new scope */
    enum none e = B;
    return A * 10 + e;
}

int main(void)
{
    struct none first = { 5, 0 };
    struct none second = { 6, &first };
    struct holder h = { .none = 7 };
    struct holder g = { { 1, 2 }, 3 };
    h.a = 8;
    printf("global %d param %d\n", none, bump(100));
    printf("tag %d enum %d\n", sum(&second), count());
    printf("member %d %d %d / %d %d %d\n", h.a, h.b, h.none, g.a, g.b, g.none);
    {
        int none = 9;
        printf("local %d\n", none + bump(none));
    }
    printf("global again %d\n", none);
    return none - 40;
}
