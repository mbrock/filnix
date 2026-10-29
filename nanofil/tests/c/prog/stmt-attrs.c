// A GNU attribute may begin a statement: libevent, unbound and
// util-linux put `__attribute__((fallthrough));` right after a case
// label, where only a statement may follow.
#include <stdio.h>

static int classify(int k) {
    int n = 0;
    switch (k) {
    case 1:
        if (k) {
            n += 1;
        }
        __attribute__((fallthrough));
    case 2:
        __attribute__((fallthrough));
    case 3:
        n += 2;
        break;
    default:
        n = -1;
    }
    return n;
}

int main(void) {
    for (int k = 0; k < 5; k++)
        printf("%d:%d ", k, classify(k));
    printf("\n");
    return 0;
}
