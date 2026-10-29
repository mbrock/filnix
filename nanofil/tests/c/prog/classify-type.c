/* GCC's __builtin_classify_type, an unevaluated integer constant
   expression (c_types type_class_number/2). filnix's cmocka shim for
   tpm2-tss picks a pointer or an integer member with
   __builtin_choose_expr(__builtin_classify_type(v) == 5, ...). */
#include <stdio.h>
#include <stdint.h>
enum E { A1 }; struct S { int a; }; union U { int a; long b; };
union V { const void *ptr; uintmax_t uint_val; };
int arr[3]; int fn(void) { return 0; }
#define P(e) printf("%s %d\n", #e, __builtin_classify_type(e))
#define VAL(v) __builtin_choose_expr(__builtin_classify_type(v) == 5, \
    ((union V){.ptr = (const void *)(uintptr_t)(v)}), ((union V){.uint_val = (uintmax_t)(v)}))
_Static_assert(__builtin_classify_type(arr) == 5, "arrays decay");
static int table[__builtin_classify_type(1.0)];
int main(void) {
    char c = 0; _Bool b = 0; enum E e = A1; struct S s = {0}; union U u = {0};
    long double ld = 0; float f = 0; int *p = &s.a; unsigned long ul = 0; int i = 0;
    P(c); P(b); P(e); P(A1); P(s); P(u); P(ld); P(f); P(p); P(ul); P(arr); P(fn);
    P("str"); P((void)0); P(i++); P(1.0); P((char)1); P(&s); P(0);
    union V x = VAL(p), y = VAL(42);
    printf("i=%d %d %d %ju %zu\n", i, x.ptr == p, *(const int *)x.ptr, y.uint_val, sizeof table);
    return 0;
}
