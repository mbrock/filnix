/* clang's optnone compiles a function without optimization and changes
   nothing it means (ghostscript's ttinterp.c and sjpege.c). */
#include <stdio.h>
__attribute__((optnone)) static int sq(int x) { return x * x; }
__attribute__((__optnone__, noinline)) int add(int a, int b) { return a + b; }
int main(void) { printf("%d %d\n", sq(7), add(2, 3)); return 0; }
