/* Idioms of ordinary Linux userland that nanofil builds (dash, jq, GNU
   sed): dash's INTOFF compiler barrier, jq's typeof-based MIN and MAX
   in statement expressions, and jq's __builtin_isnan and
   __builtin_flt_rounds, dash's SHELL_ALIGN (sizeof a union type that
   the type name defines) and stackblock() + n (GNU void pointer
   arithmetic), and gnulib's max_align_t unions (alignment attributes
   no stronger than the member's own alignment), and gnulib's
   _GL_UNUSED_LABEL (a label's attributes). */
#include <stddef.h>
#include <stdio.h>
#include <math.h>
#include <fenv.h>

#define barrier() ({ __asm__ __volatile__ ("": : :"memory"); })
#define MIN(a, b) ({ __typeof__(a) _a = (a); __typeof__(b) _b = (b); _a < _b ? _a : _b; })
#define MAX(a, b) ({ typeof(a) _a = (a); typeof(b) _b = (b); _a > _b ? _a : _b; })

static volatile int suppressint;
#define SHELL_SIZE (sizeof(union {int i; char *cp; double d; }) - 1)
#define SHELL_ALIGN(nbytes) (((nbytes) + SHELL_SIZE) & ~SHELL_SIZE)
static char stack[64] = "abcdefghijklmnop";
#define stackblock() ((void *)stack)

int main(int argc, char **argv)
{
    (void)argv;
    suppressint++;
    barrier();
    __asm__ volatile ("" ::: "memory");
    asm("");
    suppressint--;
    long len = 40 + argc;
    unsigned bufsize = 7;
    printf("%ld %ld %d\n", MIN(len, bufsize - 1), MAX(len, 3), (int)(MIN(2.5, argc) * 10));
    printf("%d\n", MAX((char)-1, 1));
    if (argc > 9) goto done_early;
 done_early: __attribute__((__unused__));
 unused_label: __attribute__((__unused__));
    char *p = stackblock() + 3;
    void *q = stackblock();
    q += 5; q++;
    printf("%zu %zu %c %c %ld\n", SHELL_ALIGN((size_t)13), SHELL_SIZE, *p,
           *(char *)q, (long)((void *)p - stackblock()));
    double vals[] = { 0.0, -1.5, NAN, INFINITY, -NAN };
    for (unsigned i = 0; i < sizeof vals / sizeof vals[0]; i++)
        printf("%d %d %d\n", __builtin_isnan(vals[i]) != 0,
               __builtin_isnan((float)vals[i]) != 0, isnan(vals[i]) != 0);
    /* glibc's math.h classification macros. */
    double more[] = { 0.0, -0.0, 1.0, -2.5, 1e-310, -1e-310, 1e308, NAN, -NAN,
                      INFINITY, -INFINITY, 2.2250738585072014e-308 };
    for (unsigned i = 0; i < sizeof more / sizeof more[0]; i++) {
        double d = more[i];
        float f = (float)d;
        printf("%d %d %d %d %d | %d %d %d %d %d\n",
               isinf(d), isfinite(d), isnormal(d), signbit(d) != 0, fpclassify(d),
               isinf(f), isfinite(f), isnormal(f), signbit(f) != 0, fpclassify(f));
    }
    int modes[] = { FE_TONEAREST, FE_UPWARD, FE_DOWNWARD, FE_TOWARDZERO, FE_TONEAREST };
    for (unsigned i = 0; i < 5; i++) {
        fesetround(modes[i]);
        printf("%d ", __builtin_flt_rounds());
    }
    printf("%d\n", suppressint);
    struct al { char c; long double d __attribute__((__aligned__(__alignof__(long double))));
                _Alignas(int) int i; long long l __attribute__((aligned(4))); };
    union { max_align_t a; char c[1000]; } space;
    printf("%zu %zu %zu %zu %zu %zu\n", sizeof(max_align_t), _Alignof(max_align_t),
           sizeof(struct al), offsetof(struct al, l), sizeof space, _Alignof(union { max_align_t a; }));
    printf("%zu\n", __builtin_offsetof(struct { char c; _Alignas(long) long x; }, x));
    /* gnulib's signed-nan.h: long double sign bits and constants. */
    long double lds[] = { 1.0L, -2.5L, -0.0L, 0.0L, __builtin_huge_vall(), -__builtin_infl(),
                          -__builtin_nanl(""), __builtin_nanl("") };
    for (unsigned i = 0; i < sizeof lds / sizeof lds[0]; i++)
        printf("%d%d%d ", __builtin_signbitl(lds[i]) != 0, signbit(lds[i]) != 0,
               __builtin_signbitl((double)lds[i] * 2) != 0);
    printf("%d %d %d\n", __builtin_signbitl(-3), __builtin_signbitf(-0.0), __builtin_signbitf(-1e-60));
    /* gnulib's countof tests: sizeof of a compound literal, unevaluated. */
    printf("%zu %zu\n", sizeof (int[]) { suppressint++, 2, 3 }, sizeof (char[]){"abc"});
    return 0;
}
