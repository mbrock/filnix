// Native counterexample probe for os_clock_gettime_contract
// (rocq/glibc/zsys/OsClockGettime.v), built by filcc and compared with
// zsys-clock.c.expected:
//   size       sizeof(struct timespec) is 16 (timespec_size)
//   mono       CLOCK_MONOTONIC into a heap buffer, as __ptmalloc_init asks:
//              0, errno untouched, the bytes either side of the 16 unchanged
//   odd        a buffer at an odd address: 0 (no alignment is asked)
//   einval     an invalid clock: (int)-1, errno EINVAL, and a stack array,
//              heap object and global unchanged
//   short      15 bytes available: panic
//   readonly   a read-only global of 16 bytes: panic
//   null       a null pointer: panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <stdfil.h>
#include <time.h>

static char gcanary[8] = "global!";
static const char rots[16] = {1};

static void short_buf(int c) { zsys_clock_gettime(c, (char *)malloc(16) + 1); }
static void readonly(int c) { zsys_clock_gettime(c, (void *)rots); }
static void null_buf(int c) { zsys_clock_gettime(c, NULL); }

int main(void) {
  printf("size %zu\n", sizeof(struct timespec));

  char *h = malloc(16 + 32);
  memset(h, 'z', 16 + 32);
  errno = 1234;
  int r = zsys_clock_gettime(CLOCK_MONOTONIC, h + 16);
  int edges = 1;
  for (int i = 0; i < 16; i++)
    edges &= h[i] == 'z' && h[16 + 16 + i] == 'z';
  printf("mono %d %d %d\n", r, errno == 1234, edges);

  char *u = malloc(32);
  r = zsys_clock_gettime(CLOCK_MONOTONIC, u + 1);
  printf("odd %d\n", r);

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  struct timespec ts;
  errno = 0;
  r = zsys_clock_gettime(12345, &ts);
  printf("einval %d %d %d %d %d\n", r, errno == EINVAL, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  dies("short", short_buf, CLOCK_MONOTONIC);
  dies("readonly", readonly, CLOCK_MONOTONIC);
  dies("null", null_buf, CLOCK_MONOTONIC);
  return 0;
}
