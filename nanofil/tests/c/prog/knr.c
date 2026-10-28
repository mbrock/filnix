// link: lib/knr.c
// signatures
/* K&R definitions (C11 6.9.1p6): parameters declared in any order, with
   several declarators, register, arrays, structs, and types default
   promotion changes, which arrive promoted and are converted to the
   declared type (sizeof sees the declared one); one after a prototype,
   which keeps the prototype's char. The companion calls them through
   declarations without prototypes, passing promoted arguments. */
#include <stdio.h>
int proto(char c);
int proto(c) char c; { return c * 3; }
double scale(f, s) float f; short s; { return f * s; }
long mix(p, n, d, c, u)
    register unsigned char u; char *p; double d; int n; char c;
{
    return *p + n + (long)d + c + u;
}
int add(a, b) int a, b; { return a + b; }
struct pt { int x, y; };
int sum_pt(s) struct pt s; { return s.x + s.y; }
int deref(a) int a[]; { return a[1]; }
int bump(a) char a; { a++; return a + (int)sizeof a; }
int callers(void);
int main(void)
{
    char buf[] = "A";
    int arr[] = { 1, 2 };
    struct pt q = { 3, 4 };
    printf("%d %g %ld %d %d %d %d %d\n", proto(5), scale(1.5f, 4), mix(buf, 2, 3.75, 4, 250),
           add(6, 7), sum_pt(q), deref(arr), bump(127), callers());
    return 0;
}
