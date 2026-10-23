// run: $value 5
// run: $void_result 7
// run: $nested 3
// run: $shadow 4
// run: $macro_assert 9
// run: $jumps 6
// run: $inner_switch 5
// run: $label_value 8
// run: $types 2
#include <assert.h>

int value(int x) { return 2 + ({ int y = x * 3; y + 1; }); }
int void_result(int x) {
    ({ x++; });
    ({ int y = 2; x += y; ; });
    ({});
    return (({ if (x) x++; }), x);
}
int nested(int x) { return ({ int y = ({ x + 2; }); y * 3; }); }
int shadow(int x) { int y = ({ int x = 12; x + 1; }); return x + y; }
int macro_assert(int x) { assert(x > 0); return x; }
int jumps(int x) {
    int n = 0;
    for (int i = 0; i < x; i++) {
        ({ if (i == 1) continue; if (i == 4) break; n += i; });
    }
    ({ goto inside; n = 100; inside: n++; });
    ({ ({ goto out; }); });
    n = 200;
out:
    return n;
}
int inner_switch(int x) {
    return ({ int n = 0; switch (x) { case 5: n = 12; break; default: n = 4; } n; });
}
int label_value(int x) { return ({ goto done; x = 100; done: x + 2; }); }
int types(int x) {
    int a[2] = { x, 7 };
    int *p = ({ a; });
    return *p + sizeof(({ short y = 1; y; })) + (({ (void)0; }), 3);
}
