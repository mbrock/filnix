// Native counterexample probe for os_ioctl_contract (rocq/glibc/zsys/OsIoctl.v),
// built by filcc and compared with zsys-ioctl.c.expected. TCGETS2 is
// __isatty_nostatus's request; a pty master is a tty, a pipe is not.
//   tty         a 48-byte heap termios2 on a tty: 0, the 44 bytes changed, the
//               last 4 untouched, errno untouched
//   big         a 256-byte object: 0, and bytes 44..256 untouched (the runtime
//               copies back at most min(avail, 128), and only what changed)
//   enotty      a pipe: -1, errno ENOTTY (errno is clobbered, finding 2), the
//               buffer, a stack array, a heap object and a global unchanged
//   tcgets      TCGETS (36 bytes) on a tty from a stack buffer: 0
//   nullfault   a null argument on a tty takes the integer path: -1, errno
//               EFAULT, no panic
//   short-pipe  40 bytes available on a pipe: -1 ENOTTY, no panic (the kernel
//               never touches it; the contract still refuses it)
//   short-tty   40 bytes available on a tty: the kernel faults on the guarded
//               copy and the runtime panics
//   ro-tty      a read-only global on a tty: the copy-back's write check panics
//   ro-pipe     the same on a pipe: -1 ENOTTY, no panic (nothing to copy back)
//   request     the request number is 0x802C542A, 2150388778 in OsIoctl.v
//   intarg      TCXONC (0x540A) with the integer TCOON (1) on a tty: the
//               integer path, 0, no panic; a small integer (0x1000) for
//               TCGETS2 on a tty: -1 EFAULT, and on a pipe -1 ENOTTY
//   inbounds    an in-bounds pointer below 2^32 is impossible natively: every
//               object's address is at least 2^32 (printed as a check)
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"

#define TCGETS2_REQ 0x802C542A
#define TCGETS_REQ 0x5401

static int tty;
static char gcanary[8] = "global!";
static const char rotermios[64] = {1};

static int all(const char *p, long n, char c) {
  for (long i = 0; i < n; i++)
    if (p[i] != c)
      return 0;
  return 1;
}

static void short_buf(int fd) { zsys_ioctl(fd, TCGETS2_REQ, (char *)malloc(48) + 8); }
static void ro_buf(int fd) { zsys_ioctl(fd, TCGETS2_REQ, (void *)rotermios); }

int main(void) {
  tty = posix_openpt(O_RDWR | O_NOCTTY);
  int p[2];
  pipe(p);

  // tty
  char *h = malloc(48);
  memset(h, 0x5a, 48);
  errno = 1234;
  int r = zsys_ioctl(tty, TCGETS2_REQ, h);
  printf("tty %d %d %d %d\n", r, !all(h, 44, 0x5a), all(h + 44, 4, 0x5a), errno == 1234);

  // big
  char *b = malloc(256);
  memset(b, (char)0xaa, 256);
  r = zsys_ioctl(tty, TCGETS2_REQ, b);
  printf("big %d %d %d\n", r, !all(b, 44, (char)0xaa), all(b + 44, 256 - 44, (char)0xaa));

  // enotty
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  memset(h, 0x5a, 48);
  errno = 0;
  r = zsys_ioctl(p[0], TCGETS2_REQ, h);
  printf("enotty %d %d %d %d %d %d\n", r, errno == ENOTTY, all(h, 48, 0x5a), !strcmp(canary, "canary!"),
         !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));

  // tcgets
  char sbuf[40];
  memset(sbuf, 0x5a, sizeof sbuf);
  r = zsys_ioctl(tty, TCGETS_REQ, sbuf);
  printf("tcgets %d %d\n", r, all(sbuf + 36, 4, 0x5a));

  // nullfault
  errno = 0;
  r = zsys_ioctl(tty, TCGETS2_REQ, NULL);
  printf("nullfault %d %d\n", r, errno == EFAULT);

  // short-pipe
  errno = 0;
  r = zsys_ioctl(p[0], TCGETS2_REQ, (char *)malloc(48) + 8);
  printf("short-pipe %d %d\n", r, errno == ENOTTY);

  dies("short-tty", short_buf, tty);
  dies("ro-tty", ro_buf, tty);
  dies("ro-pipe", ro_buf, p[0]);

  printf("request %d %d\n", TCGETS2_REQ == 2150388778u, TCGETS_REQ == 21505);

  errno = 0;
  r = zsys_ioctl(tty, 0x540A, (void *)1L);
  int e0 = errno;
  errno = 0;
  int rf = zsys_ioctl(tty, TCGETS2_REQ, (void *)0x1000L);
  int ef = errno == EFAULT;
  errno = 0;
  int rp = zsys_ioctl(p[0], TCGETS2_REQ, (void *)0x1000L);
  printf("intarg %d %d %d %d %d %d\n", r, e0 == 0, rf, ef, rp, errno == ENOTTY);

  printf("inbounds %d %d %d\n", (unsigned long)h >= 1ul << 32, (unsigned long)gcanary >= 1ul << 32,
         (unsigned long)canary >= 1ul << 32);
  return 0;
}
