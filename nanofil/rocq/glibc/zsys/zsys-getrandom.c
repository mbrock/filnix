// Native counterexample probe for os_getrandom_contract
// (rocq/glibc/zsys/OsGetrandom.v), built by filcc and compared with
// zsys-getrandom.c.expected:
//   key        8 bytes into a heap buffer, as __ptmalloc_init asks: a
//              count from 0 to 8, errno untouched, the bytes either side
//              of the 8 unchanged
//   odd        a buffer at an odd address: a count from 0 to 8
//   zero       a zero-length request: 0
//   einval     invalid flags: (long)-1, errno EINVAL, and a stack array,
//              heap object and global unchanged
//   short      7 bytes available for 8: panic
//   readonly   a read-only global of 8 bytes: panic
//   null       a null pointer for 8 bytes: panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <stdfil.h>
#include <sys/random.h>

static char gcanary[8] = "global!";
static const char rokey[8] = {1};

static void short_buf(int f) { zsys_getrandom((char *)malloc(16) + 9, 8, f); }
static void readonly(int f) { zsys_getrandom((void *)rokey, 8, f); }
static void null_buf(int f) { zsys_getrandom(NULL, 8, f); }

int main(void) {
  char *h = malloc(8 + 32);
  memset(h, 'z', 8 + 32);
  errno = 1234;
  long r = zsys_getrandom(h + 16, 8, GRND_NONBLOCK);
  int edges = 1;
  for (int i = 0; i < 16; i++)
    edges &= h[i] == 'z' && h[16 + 8 + i] == 'z';
  printf("key %d %d %d\n", r >= 0 && r <= 8, errno == 1234, edges);

  char *u = malloc(16);
  r = zsys_getrandom(u + 1, 8, GRND_NONBLOCK);
  printf("odd %d\n", r >= 0 && r <= 8);

  char z[1];
  printf("zero %ld\n", zsys_getrandom(z, 0, 0));

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  char buf[8];
  errno = 0;
  r = zsys_getrandom(buf, 8, 0x40000000);
  printf("einval %ld %d %d %d %d\n", r, errno == EINVAL, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  dies("short", short_buf, GRND_NONBLOCK);
  dies("readonly", readonly, GRND_NONBLOCK);
  dies("null", null_buf, GRND_NONBLOCK);
  return 0;
}
