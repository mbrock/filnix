// A libc function writing past a nanofil-allocated buffer must trap.
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
int main(int argc, char **argv) {
    char *small = malloc(4);
    printf("before\n");
    fflush(stdout);
    strcpy(small, "this is much longer than sixteen bytes");
    printf("after %s\n", small);
    return 0;
}
