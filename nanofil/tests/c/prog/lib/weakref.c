/* Companion of ../weakref.c, built by clang into both programs. */
int target(int x) { return x * 10; }
int other(int x) { return x + 100; }
int apply(int (*f)(int), int x) { return f(x); }
