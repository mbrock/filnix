/* Fil-C: the same layout in a thread-local initializer. */
#include <stdio.h>
int anchor = 5;
struct __attribute__((packed)) P { char c; int *p; };
_Thread_local struct P t = { 1, &anchor };
int main(void) { printf("%d\n", *t.p); return 0; }
