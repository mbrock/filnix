#include <stdarg.h>
#include <stdio.h>
static const char *prefix = "other: ";
static int say(const char *fmt, ...)
{
    va_list ap;
    va_start(ap, fmt);
    int n = printf("%s", prefix);
    n += vprintf(fmt, ap);
    va_end(ap);
    return n;
}
int other(int x) { return say("%d\n", x); }
