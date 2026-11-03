/* Shared check parts (docs/perf.md item 17): three checks of one
   16-byte object in one block, of 1, 2 and 8 bytes. Under -O
   --share=upper the second and third reuse the upper the first loaded,
   adjusted to their size. With k = 9 the third reads [9, 17), one byte
   past the end, and must trap out of bounds as filcc -O2's does.
   Its functions are external, since nanofil -O inlines small static
   functions whatever their attributes. tests/share-trap.sh compares. */
// args: 9
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
long __attribute__((noinline)) mix(unsigned char *b, int k) {
    long t = b[0];
    t += *(unsigned short *)(b + 2);
    t += *(long *)(b + k);
    return t;
}
int main(int argc, char **argv) {
    unsigned char *b = malloc(16);
    memset(b, 1, 16);
    printf("%ld\n", mix(b, 8));
    fflush(stdout);
    printf("%ld\n", mix(b, atoi(argv[1])));
    return 0;
}
