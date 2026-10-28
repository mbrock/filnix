/* clang's side of tests/c/prog/object-alignment.c. */
#include <stdint.h>
int misaligned(const void *p, unsigned n) { return (int)((uintptr_t)p % n); }
