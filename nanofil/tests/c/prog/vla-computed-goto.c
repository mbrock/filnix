// GNU goto * among labels inside a variable length array's scope, as
// alsa-lib's pcm_route.c threads its sample conversion: each goto * is
// checked from the scopes open where it is, so jumps that stay inside
// the VLA's scope, and one that leaves it, are accepted, as clang
// accepts them (reject/vla-computed-goto.c enters the scope).
#include <stdio.h>

static int route(int n) {
    static void *const lab[2] = { &&even, &&odd };
    void *out = &&done;
    int a[n];
    int s = 0, i = 0;
    for (; i < n; i++) {
        a[i] = i * 3;
        goto *lab[i & 1];
    even:
        s += a[i];
        continue;
    odd:
        s += 10 * a[i];
        if (s > 400)
            goto *out;
    }
    return s;
done:
    return -s - i;
}

int main(void) {
    printf("%d %d %d\n", route(1), route(5), route(20));
    return 0;
}
