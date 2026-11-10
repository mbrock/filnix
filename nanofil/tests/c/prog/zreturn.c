/* Fil-C's zargs and zreturn, as glibc's syscall stubs use them: a void
   function of no parameters forwards its caller's arguments to another
   function through zcall and returns what it returned, and a variadic
   one reads its own arguments as one snapshot. The words zreturn
   returns keep their capabilities. */
#include <stdfil.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

long add3(long a, long b, long c) { return 100 * a + 10 * b + c; }
char *pick(char *s, long i) { return s + i; }

void fwd_add3(void) { zreturn(zcall(add3, zargs())); }
void fwd_pick(void) { zreturn(zcall(pick, zargs())); }
int vfwd(long a, ...) { return *(int *) zcall(add3, zargs()); }
void two_words(void)
{
    char **box = malloc(2 * sizeof *box);
    box[0] = strdup("boxed");
    box[1] = (char *) 7;
    zreturn(box);
}
void early(int n)
{
    if (n > 0)
        return;
    zreturn(zcall(add3, zargs()));
}

struct pair { char *s; long n; };

int main(void)
{
    long (*f)(long, long, long) = (void *) fwd_add3;
    char *(*g)(char *, long) = (void *) fwd_pick;
    struct pair (*h)(void) = (void *) two_words;
    /* Through a volatile pointer: clang, seeing no va_start, drops the
       variadic arguments of a direct call. */
    int (*volatile vf)(long, ...) = vfwd;
    printf("%ld %s %d\n", f(1, 2, 3), g("abcdef", 2), vf(4, 5L, 6L));
    struct pair p = h();
    printf("%s %ld %zu\n", p.s, p.n, strlen(p.s));
    early(1);
    printf("%ld\n", ((long (*)(long, long, long)) (void *) early)(0, 1, 2));
    return 0;
}
