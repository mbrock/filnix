#include <stdio.h>
#include <stdlib.h>

long rept_sum(void);
long rept_oob(void);

int main(void)
{
    long r = rept_sum();
    /* TABLE = {1, 2, 30, 30, 1, 2, 30, 30} = 126, plus 3 * 1000. */
    if (r != 3126) {
        printf("FAIL: rept_sum got %ld, want 3126\n", r);
        return 1;
    }
    printf("rept ok\n");
    fflush(stdout);
    rept_oob();
    printf("FAIL: rept_oob did not trap\n");
    return 1;
}
