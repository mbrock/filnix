// error: va_start outside a variadic function
#include <stdarg.h>
int sum(int n) { va_list ap; va_start(ap, n); return n; }
