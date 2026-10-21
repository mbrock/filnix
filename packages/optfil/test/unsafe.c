/* unsafe oob|uaf: makes the memory error named by its argument, which
   Fil-C must stop before it happens. */
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

int main(int argc, char **argv) {
    int *a = malloc(4 * sizeof *a);
    volatile int i = 4;
    if (argc > 1 && strcmp(argv[1], "uaf") == 0) {
        free(a);
        i = 0;
    }
    a[i] = 42;
    printf("wrote a[%d] = %d\n", i, a[i]);
    return 0;
}
