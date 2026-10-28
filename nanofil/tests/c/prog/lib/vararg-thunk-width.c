/* The clang side of vararg-thunk-width.c: the 64-bit call. */
#include <inttypes.h>
#include <stdint.h>
#include <stdio.h>
void c_print64(char *out, uint64_t v) { snprintf(out, 40, "%016" PRIx64, v); }
