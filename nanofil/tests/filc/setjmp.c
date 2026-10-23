#include <setjmp.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdfil.h>

int nloop(void);
int nbad(void *);
void nforward(void);
static jmp_buf a, b;

void *pick(int i) { return i ? b : a; }
void collect(void) { zgc_request_and_wait(); }
void jump_a(void) { _longjmp(a, 257); }

int main(int argc, char **argv)
{
    switch (atoi(argv[1])) {
    case 0: printf("%d\n", nloop()); break;
    case 1: nbad((void *)0); break;
    case 2: nbad("readonly buffer"); break;
    case 3: nbad((char *)malloc(32) + 1); break;
    case 4:
        if (_setjmp(a) == 0)
            nforward();
        puts("forward");
        break;
    }
    return 0;
}
