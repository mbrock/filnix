// trap-reason
// vectors
/* fftw's simd-avx2.h loads through asm("vmovapd %1, %0" : "=x"(v) :
   "m"(x[0])): a vector output is a value to clang, so filcc compiles
   the memory operand's address to its run-time "pointer argument"
   error, as for an integer output. */
#include <immintrin.h>
#include <stdio.h>
__attribute__((target("avx"))) static __m128d ld(const double *x) {
    __m128d var;
    __asm__("vmovapd %1, %0\n" : "=x"(var) : "m"(x[0]));
    return var;
}
int main(void) {
    double d[2] __attribute__((aligned(16))) = {1, 2};
    puts("before");
    fflush(stdout);
    printf("%g\n", _mm_cvtsd_f64(ld(d)));
    return 0;
}
