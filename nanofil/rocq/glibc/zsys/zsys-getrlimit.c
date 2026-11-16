// Native counterexample probe for os_getrlimit_contract
// (rocq/glibc/zsys/OsGetrlimit.v), built by filcc and compared with
// zsys-getrlimit.c.expected:
//   size       sizeof(struct rlimit) is 16 (rlimit_size)
//   stack      RLIMIT_STACK into a heap buffer: 0, errno untouched, the
//              bytes either side of the 16 unchanged
//   odd        a buffer at an odd address: 0 (no alignment is asked)
//   einval     an invalid resource: (int)-1, errno EINVAL, and a stack
//              array, heap object and global unchanged
//   short      15 bytes available: panic
//   readonly   a read-only global of 16 bytes: panic
//   null       a null pointer: panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <stdfil.h>
#include <sys/resource.h>

static char gcanary[8] = "global!";
static const char rolim[16] = {1};

static void short_buf(int r) { zsys_getrlimit(r, (char *)malloc(16) + 1); }
static void readonly(int r) { zsys_getrlimit(r, (void *)rolim); }
static void null_buf(int r) { zsys_getrlimit(r, NULL); }

int main(void) {
  printf("size %zu\n", sizeof(struct rlimit));

  char *h = malloc(16 + 32);
  memset(h, 'z', 16 + 32);
  errno = 1234;
  int r = zsys_getrlimit(RLIMIT_STACK, h + 16);
  int edges = 1;
  for (int i = 0; i < 16; i++)
    edges &= h[i] == 'z' && h[16 + 16 + i] == 'z';
  printf("stack %d %d %d\n", r, errno == 1234, edges);

  char *u = malloc(32);
  r = zsys_getrlimit(RLIMIT_STACK, u + 1);
  printf("odd %d\n", r);

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  struct rlimit lim;
  errno = 0;
  r = zsys_getrlimit(12345, &lim);
  printf("einval %d %d %d %d %d\n", r, errno == EINVAL, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  dies("short", short_buf, RLIMIT_STACK);
  dies("readonly", readonly, RLIMIT_STACK);
  dies("null", null_buf, RLIMIT_STACK);
  return 0;
}
