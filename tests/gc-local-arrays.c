#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Two random-accessed local pointer arrays, built at -O0 so that they have
   no lifetime markers. Both used to share one frame slot for their stack
   aux, so the objects held only by objs were collected while in use. */
int main(int argc, char **argv)
{
    int *objs[10];
    int *other[10];
    for (int t = 0; t < 10; t++) {
        objs[t] = malloc(20000);
        objs[t][2] = t;
        other[t] = 0;
    }
    for (int round = 0; round < 50; round++) {
        for (int i = 0; i < 20000; i++)
            memset(malloc(1000), 1, 1000);
        for (int t = 0; t < 10; t++)
            if (objs[t][2] != t) {
                printf("round %d objs[%d] = %d\n", round, t, objs[t][2]);
                return 1;
            }
    }
    printf("ok %p\n", (void *)other[argc % 10]);
    return 0;
}
