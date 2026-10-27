/* Probes of what Fil-C does with C's undefined behaviour; see
   ../docs/ub.md. Build at -O0 and -O2 with filcc and run one case:

     $FILCC -O2 -w ub.c -o ub && ./ub CASE; echo "exit $?"

   Operands come from volatiles so that clang cannot fold them. */
#include <limits.h>
#include <stdio.h>
#include <string.h>

static int g[4] = {1, 2, 3, 4};

__attribute__((noinline)) int inc_gt(int x) { return x + 1 > x; }
__attribute__((noinline)) int shl(int x, int n) { return x << n; }
__attribute__((noinline)) int shl_then_check(int n) {
  int r = 1 << n;
  if (n >= 32)
    return -1;
  return r;
}
__attribute__((noinline)) int div_then_check(int x, int d) {
  int q = x / d;
  if (d == 0)
    return -1;
  return q;
}
__attribute__((noinline)) int tbaa(int *i, float *f) {
  *i = 1;
  *f = 2.0f;
  return *i;
}
__attribute__((noinline)) int uninit(int c) {
  int x;
  if (c)
    x = 5;
  return x;
}
__attribute__((noinline)) int fp2i(double d) { return (int)d; }
__attribute__((noinline)) int unreach_ret(int x) {
  if (x)
    __builtin_unreachable();
  return 7;
}
__attribute__((noinline)) int unreach_idx(int i) {
  if (i >= 4)
    __builtin_unreachable();
  return g[i];
}
__attribute__((noinline)) int wrap_idx(int i) {
  int j = i + 1;
  if (j > i)
    return g[j & 3];
  return g[j];
}
__attribute__((noinline)) int null_then_check(int *p) {
  int v = *p;
  if (!p)
    return -1;
  return v;
}

int main(int argc, char **argv) {
  volatile int big = INT_MAX, min = INT_MIN, zero = 0, m1 = -1, one = 1,
               n32 = 32, n40 = 40, ten = 10;
  volatile double huge = 1e20;
  const char *t = argc > 1 ? argv[1] : "";
  if (!strcmp(t, "inc")) printf("%d\n", inc_gt(big));
  else if (!strcmp(t, "neg")) printf("%d\n", -min);
  else if (!strcmp(t, "shl")) printf("%d\n", shl(1, n32));
  else if (!strcmp(t, "shl-check")) printf("%d\n", shl_then_check(n40));
  else if (!strcmp(t, "div0")) printf("%d\n", 7 / zero);
  else if (!strcmp(t, "div-check")) printf("%d\n", div_then_check(5, zero));
  else if (!strcmp(t, "min-1")) printf("%d\n", min / m1);
  else if (!strcmp(t, "tbaa")) {
    long w = 0;
    printf("%d\n", tbaa((int *)&w, (float *)&w));
  } else if (!strcmp(t, "uninit")) printf("%d\n", uninit(zero));
  else if (!strcmp(t, "fp")) printf("%d\n", fp2i(huge));
  else if (!strcmp(t, "unreach")) printf("%d\n", unreach_ret(one));
  else if (!strcmp(t, "unreach-idx")) printf("%d\n", unreach_idx(ten));
  else if (!strcmp(t, "wrap-idx")) printf("%d\n", wrap_idx(big));
  else if (!strcmp(t, "null")) printf("%d\n", null_then_check(0));
  else {
    fprintf(stderr, "unknown case %s\n", t);
    return 2;
  }
  return 0;
}
