/* Fil-C: after TLS initialization, inspect the capability of the aligned word
 * at offset 0, which the initializer never wrote a pointer to. */
#include <stdfil.h>
#include <stdio.h>
int anchor = 5;
struct __attribute__((packed)) P { char c; int *p; };
_Thread_local struct P t = { 1, &anchor };
int main(void)
{
    void *volatile *word = (void *volatile *)&t;
    void *w = *word;
    printf("word0 has valid cap: %d\n", (int)zhasvalidcap(w));
    zprintf("word0: %P\n", w);
    return 0;
}
