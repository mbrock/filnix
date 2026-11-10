/* _Complex float and double, as glibc's libm uses them: __real__ and
   __imag__ (lvalues too), imaginary constants, conversions to and from
   real types, ==, !=, + - * / with a real operand, ~ (GNU conj) and
   compound assignment, against clang. A complex is laid out and passed
   as a struct of its two parts, which lib/complex.c checks across the
   call boundary, _Complex long double arguments included. A real
   operand stays real (Annex G.5.1): z + 2 keeps z's -0 imaginary part,
   and a real converted to complex gets +0. */
// link: lib/complex.c
#include <stdio.h>
#include <string.h>

_Complex double cl_rot(_Complex double z);
_Complex float cl_halve(_Complex float z);
long double cl_im(_Complex long double z);
struct holder { char tag; _Complex float f; _Complex double d; };
double cl_sum(struct holder h);
double cl_calls(void);

_Complex double nf_conj(_Complex double z) { return ~z; }
_Complex float nf_scale(_Complex float z, float k) { return k * z; }
long double nf_ldre(_Complex long double z) { return __real__ z; }

static void show(const char *what, _Complex double z)
{
    printf("%s %a %a\n", what, __real__ z, __imag__ z);
}

static _Complex double pick(int c, _Complex double a, double b) { return c ? a : b; }

int main(void)
{
    volatile double nz = -0.0, nan = __builtin_nan("");
    _Complex double z = 1.5 - 2.0i, w;
    __real__ w = 0.25; __imag__ w = nz;
    show("add", w + 2);
    show("sub", 2 - w);
    show("mul", w * 4);
    show("div", z / 0.5);
    show("neg", -w);
    show("conj", ~w);
    show("real", (_Complex double) nz);
    show("float", (_Complex float) (1.0 / 3.0 + 1.0i / 3.0));
    printf("to real %a %a %d %d\n", (double) z, (float) z, (int) z, (_Bool) (0.0 + 1.0i));
    _Complex double n = nan;
    printf("eq %d %d %d %d %d %d\n", z == z, z != z, n == n, n != n, z == 1.5, 1.5 != z);
    z += 1.0i; z -= 0.5; z *= 2; z /= 4;
    show("compound", z);
    _Complex double arr[3] = { 1, 2.0i, 0 }, *p = arr;
    __imag__ p[2] = 7; __real__ *(p + 2) = -1;
    show("array", arr[0] + arr[1] + arr[2]);
    struct holder h; memset(&h, 0, sizeof h);
    h.tag = 1; h.f = 2.0f + 3.0if; h.d = 4.0 + 5.0i;
    printf("struct %zu %zu %g\n", sizeof h, __builtin_offsetof(struct holder, d), cl_sum(h));
    show("rot", cl_rot(z));
    _Complex float hf = cl_halve(3.0f + 5.0if);
    printf("halve %a %a %zu\n", __real__ hf, __imag__ hf, sizeof hf);
    printf("ld %Lg %g\n", cl_im(1.0L - 6.5iL), cl_calls());
    printf("call part %a\n", __real__ cl_rot(2.0i));
    show("pick", pick(0, z, 9.5) + pick(1, z, 9.5));
    return 0;
}
