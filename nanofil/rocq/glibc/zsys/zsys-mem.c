// Native counterexample probe for the registry's void_only zmemmove and
// zmemset (rocq/glibc/zsys/OsRegistry.v, ExternalCalls.v's memmove_contract and
// memset_contract), built by filcc and compared with zsys-mem.c.expected:
//   move        16 bytes heap to heap: copied, the bytes after untouched
//   overlap     an overlapping move within one object: as memmove
//   ptr-move    a whole 8-byte pointer slot copies its capability
//   ptr-part    4 bytes of a pointer slot: the destination slot loses its
//               capability (the contract's copy_slots empties it)
//   set         8 bytes of 'x': set, the bytes after untouched
//   ptr-set     a set over a pointer slot clears its capability
//   void-ret    called through a pointer to a function returning void *,
//               both return a null pointer with no capability, not the
//               destination: hence void_only
//   unchanged   a stack array, heap object and global outside the ranges
//   oob-move    a count one past the destination: panic
//   oob-src     a count one past the source: panic
//   ro-set      a read-only destination: panic
//   null-set    a null destination with count 1: panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <stdfil.h>

static char gcanary[8] = "global!";
static const char ro[16] = "read-only";

static void oob_move(int u) {
  char *d = malloc(16), *s = malloc(32);
  zmemmove(d, s, 17);
}
static void oob_src(int u) {
  char *d = malloc(32), *s = malloc(16);
  zmemmove(d, s, 17);
}
static void ro_set(int u) { zmemset((void *)ro, 'x', 1); }
static void null_set(int u) { zmemset(NULL, 'x', 1); }

int main(void) {
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");

  char *d = malloc(32), *s = malloc(32);
  memset(d, 'd', 32);
  for (int i = 0; i < 32; i++)
    s[i] = (char)('a' + i % 26);
  zmemmove(d, s, 16);
  int after = 1;
  for (int i = 16; i < 32; i++)
    after &= d[i] == 'd';
  printf("move %d %d\n", !memcmp(d, s, 16), after);

  char o[16] = "0123456789abcdef";
  zmemmove(o + 2, o, 10);
  printf("overlap %d\n", !memcmp(o, "010123456789cdef", 16));

  void **ps = malloc(16), **pd = malloc(16);
  ps[0] = hcanary;
  ps[1] = 0;
  pd[0] = 0;
  zmemmove(pd, ps, 8);
  printf("ptr-move %d %d\n", pd[0] == (void *)hcanary, zhasvalidcap(pd[0]));

  void **pp = malloc(16);
  pp[0] = hcanary;
  zmemmove(pp, ps, 4);
  printf("ptr-part %d\n", zhasvalidcap(pp[0]));

  memset(d, 'd', 32);
  zmemset(d, 'x', 8);
  after = 1;
  for (int i = 8; i < 32; i++)
    after &= d[i] == 'd';
  printf("set %d %d\n", !memcmp(d, "xxxxxxxx", 8), after);

  void **pz = malloc(16);
  pz[0] = hcanary;
  zmemset(pz, 0, 8);
  printf("ptr-set %d %d\n", pz[0] == NULL, zhasvalidcap(pz[0]));

  volatile void *mm = (void *)zmemmove, *ms = (void *)zmemset;
  void *r1 = ((void *(*)(void *, void *, unsigned long))mm)(d, s, 4);
  void *r2 = ((void *(*)(void *, unsigned, unsigned long))ms)(d, 'y', 4);
  printf("void-ret %d %d %d %d %d\n", r1 == NULL, zhasvalidcap(r1), r2 == NULL, zhasvalidcap(r2),
         !memcmp(d, "yyyy", 4));

  printf("unchanged %d %d %d\n", !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"),
         !strcmp(gcanary, "global!"));

  dies("oob-move", oob_move, 0);
  dies("oob-src", oob_src, 0);
  dies("ro-set", ro_set, 0);
  dies("null-set", null_set, 0);
  return 0;
}
