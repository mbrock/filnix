/* __builtin_types_compatible_p and __builtin_choose_expr, as systemd,
   util-linux, git and tor use them (ARRAY_SIZE's array check, typed
   swaps), with clang's answers for enums, which are compatible with
   their underlying type but not with each other, typedefs, character
   and long types, arrays and pointers; _Generic on an enum; and the
   hints __builtin_assume, __builtin_prefetch and _mm_pause's builtin,
   which change no result. */
#include <stdio.h>
enum E { X }; enum F { Y = -1 }; enum G { Z };
typedef enum { A1, A2 } Anon;
typedef int I;
#define IS_ARRAY(a) (!__builtin_types_compatible_p(__typeof__(a), __typeof__(&(a)[0])))
#define SAME(x, y) __builtin_types_compatible_p(__typeof__(x), __typeof__(y))
_Static_assert(__builtin_types_compatible_p(I, int), "typedef");
static int calls;
static int bump(void) { return ++calls; }
int main(void)
{
    int a[3] = { 1, 2, 3 }, *p = a;
    enum E e = X; enum G g = Z; Anon an = A2; unsigned u = 0;
    long l = 0; long long ll = 0;
    printf("%d %d %d %d %d %d\n", __builtin_types_compatible_p(enum E, unsigned),
           __builtin_types_compatible_p(enum E, int), __builtin_types_compatible_p(enum F, int),
           __builtin_types_compatible_p(enum E, enum G), __builtin_types_compatible_p(char, signed char),
           __builtin_types_compatible_p(const int, int));
    printf("%d %d %d %d %d\n", __builtin_types_compatible_p(int[], int[3]),
           __builtin_types_compatible_p(int *, const int *), __builtin_types_compatible_p(long, long long),
           __builtin_types_compatible_p(int (*)(), int (*)(int)), __builtin_types_compatible_p(I, int));
    printf("arrays %d %d same %d %d %d %d %d\n", IS_ARRAY(a), IS_ARRAY(p), SAME(e, g), SAME(e, u),
           SAME(an, u), SAME(l, ll), SAME(e, e));
    printf("generic %d %d %d\n", _Generic(e, enum G: 1, default: 0), _Generic(e, unsigned: 1, default: 0),
           _Generic(an, Anon: 1, default: 0));
    int r = __builtin_choose_expr(SAME(a[0], int), a[1], (void)0);
    printf("choose %d %zu %zu\n", r, sizeof(__builtin_choose_expr(0, 1, 'c')),
           sizeof(__builtin_choose_expr(1, l, 'c')));
    __builtin_assume(bump() > 0);
    __builtin_prefetch(p + 1000, 0, 3);
    __builtin_prefetch(&a[bump()]);
#ifdef __x86_64__
    __builtin_ia32_pause();
#endif
    printf("hints calls %d\n", calls);
    return 0;
}
