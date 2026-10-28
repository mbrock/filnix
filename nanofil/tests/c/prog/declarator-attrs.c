// GNU attributes may begin a declarator after the comma of a declarator
// list, before its '*' (x264's `char *tok, UNUSED *saveptr=NULL, *init;`),
// in a block, at file scope and in a member declaration.
#include <stdio.h>
#include <string.h>

#define UNUSED __attribute__((unused))

static int g0, UNUSED *g1 = &g0, UNUSED g2 = 7;

struct pair {
    int n, UNUSED *p;
};

int main(void) {
    char buf[] = "ab,c,,def";
    int count = 0;
    if (buf[0]) {
        char *tok, UNUSED *saveptr = NULL, *init;
        for (init = buf; (tok = strtok_r(init, ",", &saveptr)); init = NULL)
            count += printf("[%s]", tok);
        printf("\n");
    }
    struct pair s = {3, &g0};
    *s.p = 5;
    printf("%d %d %d %d\n", count, g0, *g1 + g2, s.n);
    return 0;
}
