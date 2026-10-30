/* GNU vector operators apply element by element: arithmetic wraps to
   the element type, a comparison gives -1 or 0 per element, a scalar
   operand is repeated, a cast to a vector of the same size keeps the
   bytes, and a vector is subscripted, initialized, passed to and
   returned from a static function, and stored in arrays and structs. */
#include <stdio.h>
typedef int v4si __attribute__((vector_size(16)));
typedef unsigned char v16qu __attribute__((vector_size(16)));
typedef signed char v16qs __attribute__((vector_size(16)));
typedef long long v2di __attribute__((vector_size(16)));
typedef long long v2di_u __attribute__((vector_size(16), aligned(1)));
typedef float v4sf __attribute__((vector_size(16)));
typedef double v2df __attribute__((vector_size(16)));
struct S { char c; v4si v; v2di_u u; };
static v4si add(v4si a, v4si b) { return a + b; }
static void pr(const char *n, v4si v) { printf("%s %d %d %d %d\n", n, v[0], v[1], v[2], v[3]); }
int main(void) {
    v4si a = {1, 2, 3, -4}, b = {10, 20, 30, 40};
    pr("add", add(a, b));
    pr("mul", a * 3);
    pr("div", b / a);
    pr("mod", b % 7);
    pr("shr", b >> 1);
    pr("shl", a << (v4si){1, 2, 3, 4});
    pr("cmp", a < b);
    pr("eq", a == (v4si){1, 0, 3, 0});
    pr("neg", -a);
    pr("not", ~a);
    pr("and", a & b);
    v16qu q = (v16qu)(a + b);
    printf("%d %d %d\n", q[0], q[4], q[12]);
    v16qu w = q + (unsigned char)250;
    printf("wrap %d %d\n", w[0], w[1]);
    v16qs s = (v16qs)q;
    v16qs sc = s > (signed char)0;
    printf("scmp %d %d\n", sc[0], sc[12]);
    v2di d = (v2di)a;
    printf("%llx %llx\n", (unsigned long long)d[0], (unsigned long long)d[1]);
    v4sf f = {1.5f, 2.5f, -3.0f, 0.25f};
    f = f * f + 1.0f;
    printf("%g %g %g %g\n", f[0], f[1], f[2], f[3]);
    v4si fc = f > 2.0f;
    pr("fcmp", fc);
    v2df g = {0.5, -2.0};
    g /= 2;
    printf("%g %g\n", g[0], g[1]);
    a[2] = 99;
    a += b;
    pr("idx", a);
    int i = 3;
    a[i] -= 1000;
    pr("var", a);
    v4si arr[2] = {{1, 2, 3, 4}, {5, 6, 7, 8}};
    pr("arr", arr[1] - arr[0]);
    struct S st = {1, {7, 8, 9, 10}, {11, 12}};
    st.v *= 2;
    pr("st", st.v);
    printf("%zu %zu %zu %lld\n", sizeof st, _Alignof(v2di_u), sizeof(v16qu), st.u[1]);
    return 0;
}
