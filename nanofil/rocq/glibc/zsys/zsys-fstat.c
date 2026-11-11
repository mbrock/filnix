// Native counterexample probe for os_fstat_contract (rocq/glibc/zsys/OsFstat.v),
// built by filcc and compared with zsys-fstat.c.expected:
//   size       sizeof(struct stat) is 144 (stat_size)
//   pipe       a heap struct stat of a pipe: 0, S_ISFIFO, errno untouched,
//              and the bytes either side of the 144 unchanged
//   stack      a stack struct stat inside a larger stack object: 0, the
//              neighbours unchanged
//   odd        a struct stat at an odd address (offset 1 of 160 bytes):
//              0, the bytes either side unchanged (no alignment is asked)
//   ebadf      a closed descriptor: (int)-1, errno EBADF, and a stack array,
//              heap object and global unchanged
//   ptrslot    a pointer stored in the 144 bytes before a successful call:
//              the kernel rewrites its address bytes but its aux capability
//              stays (the contract hands the block back with whatever is
//              there, bytes and aux both)
//   short      143 bytes available (malloc rounds to 16, so offset 1 of 144):
//              panic
//   readonly   a read-only global of 144 bytes: panic
//   null       a null pointer: panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <stdfil.h>
#include <sys/stat.h>

static char gcanary[8] = "global!";
static const char rostat[144] = {1};

static void short_buf(int fd) { zsys_fstat(fd, (char *)malloc(144) + 1); }
static void readonly(int fd) { zsys_fstat(fd, (void *)rostat); }
static void null_buf(int fd) { zsys_fstat(fd, NULL); }

int main(void) {
  int p[2];
  printf("size %zu\n", sizeof(struct stat));

  // pipe
  pipe(p);
  char *h = malloc(144 + 32);
  memset(h, 'z', 144 + 32);
  errno = 1234;
  int r = zsys_fstat(p[0], h + 16);
  struct stat st;
  memcpy(&st, h + 16, sizeof st);
  int edges = 1;
  for (int i = 0; i < 16; i++)
    edges &= h[i] == 'z' && h[16 + 144 + i] == 'z';
  printf("pipe %d %d %d %d\n", r, S_ISFIFO(st.st_mode), errno == 1234, edges);

  // stack
  struct {
    char before[8];
    struct stat st;
    char after[8];
  } s;
  memset(&s, 'y', sizeof s);
  r = zsys_fstat(p[1], &s.st);
  printf("stack %d %d %d %d\n", r, S_ISFIFO(s.st.st_mode), !memcmp(s.before, "yyyyyyyy", 8),
         !memcmp(s.after, "yyyyyyyy", 8));

  // odd
  char *u = malloc(160);
  memset(u, 'u', 160);
  r = zsys_fstat(p[0], u + 1);
  memcpy(&st, u + 1, sizeof st);
  printf("odd %d %d %d %d\n", r, ((unsigned long)(u + 1)) % 2, S_ISFIFO(st.st_mode),
         u[0] == 'u' && u[145] == 'u');

  // ebadf
  close(p[1]);
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  errno = 0;
  r = zsys_fstat(p[1], &st);
  printf("ebadf %d %d %d %d %d\n", r, errno == EBADF, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  // ptrslot
  void **slots = malloc(144);
  memset(slots, 0, 144);
  slots[0] = hcanary;
  int before = zhasvalidcap(slots[0]);
  r = zsys_fstat(p[0], slots);
  printf("ptrslot %d %d %d\n", r, before, zhasvalidcap(slots[0]));
  close(p[0]);

  pipe(p);
  dies("short", short_buf, p[0]);
  dies("readonly", readonly, p[0]);
  dies("null", null_buf, p[0]);
  return 0;
}
