// nanofil-link: lib/static-thunks.c
/* Two objects each define a static variadic function named say and call
   it with the same signature. Each call goes through a call thunk named
   for say and that signature; a static callee's thunk is local to its
   object, as clang's is, so neither object's calls reach the other's
   say (abi-findings.md, "Symbols the linker merges"). */
#include <stdarg.h>
#include <stdio.h>
static int say(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    int n = printf("main: ");
    n += vprintf(fmt, ap);
    va_end(ap);
    return n;
}
int other(int);
int main(void)
{
    say("%d\n", 1);
    other(2);
    say("%d\n", 3);
    return 0;
}
