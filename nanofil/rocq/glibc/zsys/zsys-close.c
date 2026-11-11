// Native counterexample probe for os_close_contract (rocq/glibc/zsys/OsClose.v),
// built by filcc and compared with zsys-close.c.expected:
//   ok        closing an open pipe end: 0, errno untouched, the descriptor gone
//   ebadf     closing it again: -1 (as int; 4294967295 read as a long through a
//             pointer, the zero-extended W value), errno EBADF, a stack
//             array, heap object and global unchanged
//   negative  closing -1: -1, errno EBADF (no holder, no panic)
//   arity     a call through a pointer with no argument: panic (ArgumentSize)
//   logfd     under FILC_LOG_TO_FILE, closing libpizlo's log descriptor: 0,
//             and it stays open (no check_fd: the call admits every fd)
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"

static char gcanary[8] = "global!";

static void arity(int fd) {
  volatile void *f = (void *)zsys_close;
  ((int (*)(void))f)();
}

int main(int argc, char **argv) {
  if (argc > 1) {
    int lf = log_fd();
    if (lf < 0)
      return 3;
    int r = zsys_close(lf);
    // fcntl(lf) would trip zsys_fcntl's own check_fd: look in /proc instead.
    return r == 0 && log_fd() == lf ? 0 : 4;
  }
  int p[2];
  pipe(p);
  errno = 1234;
  int r = zsys_close(p[1]);
  printf("ok %d %d %d\n", r, errno == 1234, fcntl(p[1], F_GETFD) < 0);

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  errno = 0;
  r = zsys_close(p[1]);
  int bad = errno == EBADF;
  errno = 0;
  volatile void *f = (void *)zsys_close;
  long wide = ((long (*)(int))f)(p[1]);
  printf("ebadf %d %d %ld %d %d %d %d\n", r, bad, wide, errno == EBADF, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  errno = 0;
  r = zsys_close(-1);
  printf("negative %d %d\n", r, errno == EBADF);

  dies("arity", arity, 0);
  // Expected to stay alive: prints 0.
  logged("logfd", "logfd");
  return 0;
}
