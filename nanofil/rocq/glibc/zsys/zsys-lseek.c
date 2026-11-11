// Native counterexample probe for os_lseek_contract (rocq/glibc/zsys/OsLseek.v),
// built by filcc and compared with zsys-lseek.c.expected:
//   set/cur/end  SEEK_SET 5, SEEK_CUR +3, SEEK_END on a 10-byte file: 5 8 10,
//                errno untouched
//   big          SEEK_SET 2^40: returns 2^40
//   near-max     SEEK_SET 2^62 and LONG_MAX, SEEK_END + 2^62: each either
//                returns its offset or fails with -1 EINVAL (filesystem
//                limits differ), never a value outside the contract's range
//   espipe       a pipe: -1, errno ESPIPE
//   einval       whence 99, and a negative offset: -1, errno EINVAL, the file
//                position unchanged
//   ebadf        a closed descriptor: -1, errno EBADF, a stack array, heap
//                object and global unchanged
//   arity        a call through a pointer with one argument: panic (ArgumentSize)
//   logfd        under FILC_LOG_TO_FILE, lseek of libpizlo's log descriptor:
//                check_fd's assertion kills the process (the precondition's
//                ow_log_fd clause)
//   otherfd      under FILC_LOG_TO_FILE, lseek of another descriptor: no death
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"

static char gcanary[8] = "global!";

static void arity(int fd) {
  volatile void *f = (void *)zsys_lseek;
  ((long (*)(int))f)(fd);
}

int main(int argc, char **argv) {
  if (argc > 1) {
    int lf = log_fd();
    if (lf < 0)
      return 3;
    if (!strcmp(argv[1], "logfd"))
      zsys_lseek(lf, 0, SEEK_SET);
    else
      zsys_lseek(0, 0, SEEK_CUR);
    return 0;
  }
  char tmpl[] = "/tmp/zsys-lseek-XXXXXX";
  int fd = mkstemp(tmpl);
  unlink(tmpl);
  write(fd, "0123456789", 10);
  errno = 1234;
  long a = zsys_lseek(fd, 5, SEEK_SET);
  long b = zsys_lseek(fd, 3, SEEK_CUR);
  long c = zsys_lseek(fd, 0, SEEK_END);
  printf("set/cur/end %ld %ld %ld %d\n", a, b, c, errno == 1234);

  long big = zsys_lseek(fd, 1L << 40, SEEK_SET);
  printf("big %d\n", big == 1L << 40);
  long big62[3] = {1L << 62, 0x7fffffffffffffffL, 10 + (1L << 62)};
  long got62[3];
  int e62[3];
  errno = 0;
  got62[0] = zsys_lseek(fd, 1L << 62, SEEK_SET);
  e62[0] = errno;
  errno = 0;
  got62[1] = zsys_lseek(fd, 0x7fffffffffffffffL, SEEK_SET);
  e62[1] = errno;
  errno = 0;
  got62[2] = zsys_lseek(fd, 1L << 62, SEEK_END);
  e62[2] = errno;
  int ok62 = 1;
  for (int i = 0; i < 3; i++)
    ok62 &= got62[i] == big62[i] || (got62[i] == -1 && e62[i] == EINVAL);
  printf("near-max %d\n", ok62);
  zsys_lseek(fd, 4, SEEK_SET);

  int p[2];
  pipe(p);
  errno = 0;
  long r = zsys_lseek(p[0], 0, SEEK_CUR);
  printf("espipe %ld %d\n", r, errno == ESPIPE);

  errno = 0;
  r = zsys_lseek(fd, 0, 99);
  int e1 = errno == EINVAL;
  errno = 0;
  long r2 = zsys_lseek(fd, -20, SEEK_SET);
  printf("einval %ld %d %ld %d %ld\n", r, e1, r2, errno == EINVAL, zsys_lseek(fd, 0, SEEK_CUR));

  close(p[1]);
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  errno = 0;
  r = zsys_lseek(p[1], 0, SEEK_SET);
  printf("ebadf %ld %d %d %d %d\n", r, errno == EBADF, !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  dies("arity", arity, fd);
  logged("logfd", "logfd");
  logged("otherfd", "otherfd");
  return 0;
}
