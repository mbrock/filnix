#include <stdio.h>

/* Recursion: each call is a call in the IR, and a frame in the assembly. */
static long fib(int n) {
    return n < 2 ? n : fib(n - 1) + fib(n - 2);
}

int main(void) {
    for (int i = 0; i < 10; i++)
        printf("fib(%d) = %ld\n", i, fib(i));
    return 0;
}
