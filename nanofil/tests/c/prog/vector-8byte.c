// trap-reason
// vectors
/* 8-byte vectors (fftw's single-precision SIMD: xmmintrin.h's
   _mm_loadl_pi, _mm_loadh_pi, _mm_storel_pi and _mm_storeh_pi read and
   write a packed struct of one) are checked as one 8-byte access at the
   vector's alignment, capped at 8: through the packed struct that is 1,
   so +4 runs, while a plain v2f pointer at +4 traps, as in filcc. */
#include <xmmintrin.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/wait.h>

typedef float v2f __attribute__((vector_size(8)));
typedef int v2i __attribute__((vector_size(8)));
typedef short v4h __attribute__((vector_size(8)));
struct holder { char c; v2i v; };
static volatile int off4 = 4, off8 = 8, off12 = 12, off13 = 13, offm4 = -4;
static void (*volatile release)(void *) = free;

static void showps(__m128 v) {
    float f[4];
    _mm_storeu_ps(f, v);
    printf("%g %g %g %g\n", f[0], f[1], f[2], f[3]);
}

static void values(void) {
    float src[6] = {1, 2, 3, 4, 5, 6}, dst[6] = {0};
    __m128 a = _mm_setr_ps(10, 20, 30, 40);
    showps(_mm_loadl_pi(a, (const __m64 *)(src + 1)));
    showps(_mm_loadh_pi(a, (const __m64 *)(src + 3)));
    _mm_storel_pi((__m64 *)(dst + 1), a);
    _mm_storeh_pi((__m64 *)(dst + 4), a);
    printf("%g %g %g %g %g %g\n", dst[0], dst[1], dst[2], dst[3], dst[4], dst[5]);
    v2i x = {3, -7}, y = {10, 20};
    v2i z = x * y + (x >> 1);
    v4h h = {1, -2, 300, -32768};
    h = h + h;
    v2f fv = {1.5f, -0.25f};
    fv = fv * fv - (v2f){1, 1};
    printf("%d %d %d %d %d %d %g %g\n", z[0], z[1], h[0], h[1], h[2], h[3], fv[0], fv[1]);
    v2i s = __builtin_shufflevector(x, y, 3, 0);
    typedef int v4i __attribute__((vector_size(16)));
    v4i w = __builtin_shufflevector(x, y, 0, 1, 2, 3);
    v2i back = __builtin_shufflevector(w, w, 2, 1);
    printf("%d %d %d %d %d %d\n", s[0], s[1], w[3], back[0], back[1], (int)sizeof(struct holder));
    struct holder hd;
    memset(&hd, 0, sizeof hd);
    hd.v = x;
    v2i r = hd.v;
    printf("%d %d\n", r[0], r[1]);
}

static void run(int i) {
    char *b = malloc(16);
    memset(b, 7, 16);
    __m128 a = _mm_set1_ps(1);
    switch (i) {
    case 0: a = _mm_loadl_pi(a, (const __m64 *)(b + off4)); break;   /* packed: runs */
    case 1: { v2f v = *(v2f *)(b + off4); a[0] = v[0]; break; }      /* alignment 8 */
    case 2: a = _mm_loadl_pi(a, (const __m64 *)(b + off12)); break;  /* 4 bytes short */
    case 3: _mm_storeh_pi((__m64 *)(b + off13), a); break;
    case 4: a = _mm_loadh_pi(a, (const __m64 *)(b + offm4)); break;
    case 5: release(b); _mm_storel_pi((__m64 *)b, a); break;
    case 6: { v2i v = {1, 2}; *(v2i *)(b + off12) = v; break; }      /* 8-aligned, 4 short */
    case 7: { v2i v = *(v2i *)(b + off8); a[0] = (float)v[1]; break; } /* the last 8 bytes */
    case 8: _mm_storel_pi((__m64 *)(b + off12), a); printf("%d\n", b[12]); break;
    }
    printf("%g\n", a[0]);
    fflush(stdout);
}

int main(void) {
    values();
    fflush(stdout);
    for (int i = 0; i <= 8; i++) {
        printf("case %d\n", i);
        fflush(stdout);
        pid_t p = fork();
        if (p == 0) { run(i); _exit(0); }
        int st;
        waitpid(p, &st, 0);
        printf("signaled %d\n", WIFSIGNALED(st));
    }
    return 0;
}
