/* A 2-byte read of a freed object through a pointer 2^63 - 1 past its
   lower, moved there by integer arithmetic that keeps the capability.
   filcc traps (free object). --bounds=sign passes the check, since
   (ptr - lower) | (upper - 2 - ptr) is then 2^63 - 1, and the
   non-canonical address faults in hardware instead (SIGSEGV); every
   other shape must trap as filcc does (tests/bounds_smt.py, docs/bounds.md). */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(void) {
    char *p = malloc(16);
    volatile uintptr_t off = ((uintptr_t)1 << 63) - 1;
    free(p);
    short *q = (short *)(p + off);
    puts("reading");
    fflush(stdout);
    return *(volatile short *)q;
}
