/* __builtin_ia32_rdtsc and __builtin_ia32_cvtpd2ps, as glibc's
   fast-jitter.h and sincosf_poly.h use them: the counter is edx:eax as
   one 64-bit value, so a later reading is no smaller and the high half
   is not lost; CVTPD2PS rounds each double to nearest float and zeroes
   the upper two elements. */
#include <stdio.h>

typedef double v2df __attribute__((vector_size(16)));
typedef float v4sf __attribute__((vector_size(16)));

int main(void)
{
    unsigned long long t0 = __builtin_ia32_rdtsc(), t1 = __builtin_ia32_rdtsc();
    printf("%d %d %d\n", t1 >= t0, (t0 >> 32) != 0, sizeof __builtin_ia32_rdtsc() == 8);
    v2df d = { 1.0 / 3.0, -2.5e40 };
    v4sf f = __builtin_ia32_cvtpd2ps(d);
    v2df e = { 0x1.000001p0, 0x1.0000018p0 };
    v4sf g = __builtin_ia32_cvtpd2ps(e);
    printf("%a %a %a %a\n", f[0], f[1], f[2], f[3]);
    printf("%a %a %a %a\n", g[0], g[1], g[2], g[3]);
    return 0;
}
