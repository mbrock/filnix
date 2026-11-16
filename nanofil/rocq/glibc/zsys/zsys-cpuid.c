// Native counterexample probe for os_cpuid_contract and os_xgetbv_contract
// (rocq/glibc/zsys/OsCpuid.v), built by filcc and compared with
// zsys-cpuid.c.expected. Every line holds on any x86-64 machine that meets
// the contracts, whatever its CPUID answers:
//   writes      zcpuid writes its four results and nothing beside them: the
//               bytes around each 4-byte slot keep their values, the results
//               are those of the CPUID instruction, errno untouched
//   count       zcpuid(leaf) is zcpuid_count(leaf, 0), and a subleaf is
//               passed on (leaf 4's subleaves 0 and 1 are both read)
//   order       the four stores go eax, ebx, ecx, edx: four equal pointers
//               leave edx, so the contract speaks of ecx only when the edx
//               span lies elsewhere
//   caps        a write over half of a pointer slot keeps its capability
//   osxsave     when leaf 1 reports OSXSAVE (ecx bit 27), zxgetbv returns
//               (0: its child did not die); on a machine without the bit the
//               probe does not call zxgetbv and prints the same line
//   xgetbv      zxgetbv writes nothing: a stack array, heap object and
//               global unchanged, errno untouched
//   null        a null result pointer, in the first or the last place: panic
//   readonly    a read-only result pointer: panic
//   oob         a result pointer with three bytes left in its object: panic
//   freed       a freed result pointer: panic
//   div0        glibc's handle_amd divides by a CPUID byte that may be 0
//               ((ecx >> 6) & 0x3fffc00) / (ecx & 0xff) with ecx = 0xf000);
//               Fil-C's division by zero gives 0 and does not trap (0)
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <cpuid.h>
#include <stdfil.h>

static char gcanary[8] = "global!";
static const unsigned ro[4] = {1, 2, 3, 4};

static void null_first(int u) {
  unsigned b, c, d;
  zcpuid(0, NULL, &b, &c, &d);
}
static void null_last(int u) {
  unsigned a, b, c;
  zcpuid_count(0, 0, &a, &b, &c, NULL);
}
static void readonly(int u) {
  unsigned a, b, d;
  zcpuid(0, &a, &b, (unsigned *)&ro[2], &d);
}
static void oob(int u) {
  char *buf = malloc(16);
  unsigned a, c, d;
  zcpuid(0, &a, (unsigned *)(buf + zlength(buf) - 3), &c, &d);
}
static void freed(int u) {
  unsigned *p = malloc(4);
  unsigned a, b, c;
  free(p);
  zcpuid(0, &a, &b, &c, p);
}
static void xgetbv(int u) { zxgetbv(); }
static void div0(int u) {
  volatile unsigned ecx = 0xf000;
  volatile unsigned q = ((ecx >> 6) & 0x3fffc00) / (ecx & 0xff);
  if (q != 0)
    abort();
}

int main(void) {
  errno = 1234;
  // Four 4-byte slots, each between two guard words.
  unsigned r[12];
  for (int i = 0; i < 12; i++)
    r[i] = 0xa5a5a5a5u;
  zcpuid(0, &r[1], &r[4], &r[7], &r[10]);
  unsigned a, b, c, d;
  __cpuid(0, a, b, c, d);
  int guards = 1;
  for (int i = 0; i < 12; i++)
    if (i % 3 != 1)
      guards &= r[i] == 0xa5a5a5a5u;
  printf("writes %d %d %d\n", guards, r[1] == a && r[4] == b && r[7] == c && r[10] == d, errno == 1234);

  unsigned x[4], y[4], z[4];
  zcpuid(4, &x[0], &x[1], &x[2], &x[3]);
  zcpuid_count(4, 0, &y[0], &y[1], &y[2], &y[3]);
  zcpuid_count(4, 1, &z[0], &z[1], &z[2], &z[3]);
  __cpuid_count(4, 1, a, b, c, d);
  printf("count %d %d\n", !memcmp(x, y, sizeof x), z[0] == a && z[1] == b && z[2] == c && z[3] == d);

  unsigned same = 0;
  zcpuid(0, &same, &same, &same, &same);
  printf("order %d\n", same == r[10]);

  char *obj = malloc(16);
  char **slot = malloc(sizeof(char *));
  *slot = obj;
  unsigned t[3];
  zcpuid(0, (unsigned *)slot, &t[0], &t[1], &t[2]);
  printf("caps %d\n", zgetlower(*slot) == (void *)obj && zgetupper(*slot) == (void *)(obj + 16));

  unsigned l1[4];
  zcpuid(1, &l1[0], &l1[1], &l1[2], &l1[3]);
  int osxsave = (l1[2] >> 27) & 1;
  if (osxsave)
    dies("osxsave", xgetbv, 0);
  else
    printf("osxsave 0\n");

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  if (osxsave)
    zxgetbv();
  printf("xgetbv %d %d %d %d\n", !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"),
         !strcmp(gcanary, "global!"), errno == 1234);

  dies("null", null_first, 0);
  dies("null", null_last, 0);
  dies("readonly", readonly, 0);
  dies("oob", oob, 0);
  dies("freed", freed, 0);
  dies("div0", div0, 0);
  return 0;
}
