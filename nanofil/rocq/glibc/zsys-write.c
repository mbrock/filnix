// Native counterexample probe for os_write_contract (rocq/glibc/zsys/OsWrite.v,
// docs/glibc-ir.md), built by filcc and run natively by rocq/glibc/probe.sh,
// which compares its output with zsys-write.c.expected. Each case checks
// one clause of the trusted contract against libpizlo at the pin:
//   full      a readable buffer: returns n, the reader gets exactly those bytes
//   readonly  a string literal's read-only capability is readable
//   empty     size 0: returns 0, nothing written
//   partial   a nonblocking pipe with less room than n: returns k with
//             0 < k < n, and the reader gets exactly the buffer's first k bytes
//   ebadf     a closed descriptor: -1, errno EBADF, and the buffer, a stack
//             array, a heap object and a global all unchanged
//   eagain    a full nonblocking pipe: -1, errno EAGAIN, nothing written
//   oob       size one past the buffer's object: a Fil-C panic before any
//             byte is written (the capability check, outside the premise)
// Finite evidence, not a proof that every native call satisfies the contract.
#include <errno.h>
#include <fcntl.h>
#include <pizlonated_syscalls.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>
#include <unistd.h>

static int pipe_nb(int fds[2]) {
  if (pipe(fds))
    return -1;
  return fcntl(fds[1], F_SETFL, O_NONBLOCK);
}

// Read everything in the pipe's read end without blocking.
static long drain(int fd, char *out, long cap) {
  int fl = fcntl(fd, F_GETFL);
  fcntl(fd, F_SETFL, fl | O_NONBLOCK);
  long got = 0;
  for (;;) {
    long r = read(fd, out + got, cap - got);
    if (r <= 0)
      break;
    got += r;
  }
  fcntl(fd, F_SETFL, fl);
  return got;
}

static char big[20000];
static char gcanary[8] = "global!";
static char sink[70000];

int main(void) {
  int p[2];
  char buf[13] = "hello, glibc";
  char canary[8] = "canary!";

  // full
  pipe_nb(p);
  long r = zsys_write(p[1], buf, 12);
  char got[64];
  long n = drain(p[0], got, sizeof got);
  printf("full %ld %ld %d\n", r, n, n == 12 && !memcmp(got, buf, 12));
  close(p[0]); close(p[1]);

  // readonly
  pipe_nb(p);
  static const char lit[] = "literal";
  r = zsys_write(p[1], lit, 7);
  n = drain(p[0], got, sizeof got);
  printf("readonly %ld %ld %d\n", r, n, n == 7 && !memcmp(got, lit, 7));
  close(p[0]); close(p[1]);

  // empty
  pipe_nb(p);
  r = zsys_write(p[1], buf, 0);
  n = drain(p[0], got, sizeof got);
  printf("empty %ld %ld\n", r, n);
  close(p[0]); close(p[1]);

  // partial: fill the pipe, free some room, write more than fits.
  for (int i = 0; i < (int)sizeof big; i++)
    big[i] = (char)(i * 7 + 1);
  pipe_nb(p);
  while (write(p[1], sink, 4096) > 0)
    ;
  long freed = read(p[0], sink, 8192);
  r = zsys_write(p[1], big, sizeof big);
  // The pipe holds the old fill, then the k new bytes; read it all.
  n = drain(p[0], sink, sizeof sink);
  int prefix = r > 0 && n >= r && !memcmp(sink + n - r, big, r);
  printf("partial %d %d %d\n", freed > 0, r > 0 && r < (long)sizeof big, prefix);
  close(p[0]); close(p[1]);

  // ebadf: a closed descriptor.
  pipe_nb(p);
  close(p[1]);
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  errno = 0;
  r = zsys_write(p[1], buf, 12);
  printf("ebadf %ld %d %d %d %d %d\n", r, errno == EBADF, !strcmp(buf, "hello, glibc"),
         !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"),
         !strcmp(gcanary, "global!"));
  close(p[0]);

  // eagain: a full nonblocking pipe.
  pipe_nb(p);
  long filled = 0, w;
  while ((w = write(p[1], sink, 4096)) > 0)
    filled += w;
  errno = 0;
  r = zsys_write(p[1], buf, 12);
  int again = errno == EAGAIN;
  n = drain(p[0], sink, sizeof sink);
  printf("eagain %ld %d %d\n", r, again, n == filled);
  close(p[0]); close(p[1]);

  // oob: one byte past the object. The child must die before writing.
  pipe_nb(p);
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    close(p[0]);
    char *h = malloc(16);
    memset(h, 'x', 16);
    zsys_write(p[1], h, 17);
    _exit(0);
  }
  close(p[1]);
  int status = 0;
  waitpid(pid, &status, 0);
  n = drain(p[0], got, sizeof got);
  printf("oob %d %ld\n", !(WIFEXITED(status) && WEXITSTATUS(status) == 0), n);
  close(p[0]);
  return 0;
}
