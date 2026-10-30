// trap-reason
/* __builtin_frame_address at a nonzero level is a run-time error under
   filcc, reached only when it runs. Level 0 is refused (reject/). */
#include <stdio.h>
int main(int argc, char **argv) {
    printf("start\n"); fflush(stdout);
    if (argc > 5) return 0;
    void *p = __builtin_frame_address(1);
    printf("%d\n", p != 0);
    return 0;
}
