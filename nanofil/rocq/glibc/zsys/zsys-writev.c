// Native counterexample probe for os_writev_contract (rocq/glibc/zsys/OsWritev.v)
// and OsWrite.v's zero-length read check, built by filcc and compared with
// zsys-writev.c.expected. Each line checks one clause against libpizlo at the pin:
//   full        stack, heap and read-only entries: returns the total, the reader
//               gets the entries' bytes in order
//   nullzero    an entry {NULL, 0} in the middle passes its (skipped) read check
//   empty       iovcnt 0 with a null array: returns 0, nothing written
//   write0      zsys_write(fd, NULL, 0): returns 0 (filc_check_read skips size 0)
//   partial     a nonblocking pipe with less room: 0 < k < total, prefix gathered
//   ebadf       a closed descriptor: -1, errno EBADF, entries, the array, a
//               stack array, a heap object and a global all unchanged
//   einval      iovcnt 2000 (> IOV_MAX): -1, errno EINVAL, nothing written
//   oob-entry   an entry one byte past its object: panic, nothing written
//   oob-array   iovcnt one past the array: panic, nothing written
//   negative    iovcnt -1: filc_mul_size overflows, panic, nothing written
//   misaligned  the array at an address that is 4 mod 8: panic, nothing written
//   ro-array    a read-only (const global) iovec array: accepted, bytes gathered
//   freed       an entry whose buffer was freed: panic, nothing written
//   logfd       under FILC_LOG_TO_FILE, writev to libpizlo's log descriptor:
//               check_fd's assertion kills the process
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <sys/uio.h>

// Run fn(wfd) in a child; print whether it died (not a clean exit 0) and how
// many bytes reached the pipe.
static void dies_w(const char *name, void (*fn)(int)) {
  int p[2];
  pipe_nb(p);
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    close(p[0]);
    fn(p[1]);
    _exit(0);
  }
  close(p[1]);
  int status = 0;
  waitpid(pid, &status, 0);
  char got[64];
  long n = drain(p[0], got, sizeof got);
  printf("%s %d %ld\n", name, !(WIFEXITED(status) && WEXITSTATUS(status) == 0), n);
  close(p[0]);
}

static void oob_entry(int fd) {
  char *h = malloc(16);
  memset(h, 'x', 16);
  struct iovec v[2] = {{h, 8}, {h + 8, 9}};
  zsys_writev(fd, v, 2);
}

static void oob_array(int fd) {
  struct iovec *v = malloc(2 * sizeof *v);
  v[0].iov_base = "ab"; v[0].iov_len = 2;
  v[1].iov_base = "cd"; v[1].iov_len = 2;
  zsys_writev(fd, v, 3);
}

static void negative(int fd) {
  struct iovec v[1] = {{"ab", 2}};
  zsys_writev(fd, v, -1);
}

static void misaligned(int fd) {
  char *raw = malloc(64);
  memset(raw, 0, 64);
  // 16 bytes from offset 4: a null base and length 0, so only the
  // pointer load's alignment check can refuse it.
  zsys_writev(fd, raw + 4, 1);
}

static void freed_entry(int fd) {
  char *h = malloc(16);
  memset(h, 'f', 16);
  free(h);
  struct iovec v[1] = {{h, 16}};
  zsys_writev(fd, v, 1);
}

static char rodata0[] = "ro-";
static char rodata1[] = "array";
static const struct iovec roiov[2] = {{rodata0, 3}, {rodata1, 5}};

static char big[20000];
static char sink[70000];
static char gcanary[8] = "global!";

int main(int argc, char **argv) {
  if (argc > 1) {
    int lf = log_fd();
    if (lf < 0)
      return 3;
    struct iovec v[1] = {{"x", 1}};
    zsys_writev(lf, v, 1);
    return 0;
  }
  int p[2];
  char got[64];
  char sbuf[6] = "stack";
  char *hbuf = malloc(5);
  memcpy(hbuf, "heap!", 5);
  static const char ro[] = "ro";

  // full
  pipe_nb(p);
  struct iovec v[3] = {{sbuf, 5}, {hbuf, 5}, {(void *)ro, 2}};
  long r = zsys_writev(p[1], v, 3);
  long n = drain(p[0], got, sizeof got);
  printf("full %ld %ld %d\n", r, n, n == 12 && !memcmp(got, "stackheap!ro", 12));
  close(p[0]); close(p[1]);

  // nullzero
  pipe_nb(p);
  struct iovec vz[3] = {{sbuf, 5}, {NULL, 0}, {hbuf, 5}};
  r = zsys_writev(p[1], vz, 3);
  n = drain(p[0], got, sizeof got);
  printf("nullzero %ld %ld %d\n", r, n, n == 10 && !memcmp(got, "stackheap!", 10));
  close(p[0]); close(p[1]);

  // empty
  pipe_nb(p);
  r = zsys_writev(p[1], NULL, 0);
  n = drain(p[0], got, sizeof got);
  printf("empty %ld %ld\n", r, n);

  // write0
  r = zsys_write(p[1], NULL, 0);
  n = drain(p[0], got, sizeof got);
  printf("write0 %ld %ld\n", r, n);
  close(p[0]); close(p[1]);

  // partial
  for (int i = 0; i < (int)sizeof big; i++)
    big[i] = (char)(i * 7 + 1);
  pipe_nb(p);
  while (write(p[1], sink, 4096) > 0)
    ;
  long freed = read(p[0], sink, 8192);
  struct iovec vb[2] = {{big, 10000}, {big + 10000, 10000}};
  r = zsys_writev(p[1], vb, 2);
  n = drain(p[0], sink, sizeof sink);
  int prefix = r > 0 && n >= r && !memcmp(sink + n - r, big, r);
  printf("partial %d %d %d\n", freed > 0, r > 0 && r < (long)sizeof big, prefix);
  close(p[0]); close(p[1]);

  // ebadf
  pipe_nb(p);
  close(p[1]);
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  errno = 0;
  r = zsys_writev(p[1], v, 3);
  printf("ebadf %ld %d %d %d %d %d %d\n", r, errno == EBADF,
         v[0].iov_base == sbuf && v[0].iov_len == 5 && v[2].iov_base == ro,
         !memcmp(sbuf, "stack", 6) && !memcmp(hbuf, "heap!", 5),
         !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));
  close(p[0]);

  // einval
  pipe_nb(p);
  struct iovec *many = malloc(2000 * sizeof *many);
  for (int i = 0; i < 2000; i++) {
    many[i].iov_base = sbuf;
    many[i].iov_len = 1;
  }
  errno = 0;
  r = zsys_writev(p[1], many, 2000);
  int inval = errno == EINVAL;
  n = drain(p[0], got, sizeof got);
  printf("einval %ld %d %ld\n", r, inval, n);
  close(p[0]); close(p[1]);

  dies_w("oob-entry", oob_entry);
  dies_w("oob-array", oob_array);
  dies_w("negative", negative);
  dies_w("misaligned", misaligned);

  pipe_nb(p);
  r = zsys_writev(p[1], roiov, 2);
  n = drain(p[0], got, sizeof got);
  printf("ro-array %ld %ld %d\n", r, n, n == 8 && !memcmp(got, "ro-array", 8));
  close(p[0]); close(p[1]);

  dies_w("freed", freed_entry);
  logged("logfd", "logfd");
  return 0;
}
