// Native counterexample probe for os_exit_contract (rocq/glibc/zsys/OsExit.v),
// built by filcc and compared with zsys-exit.c.expected. Each case runs in a
// forked child and prints how it ended and what reached a pipe:
//   soft-263    zsys_exit_soft(263): exits with status 7 (exit_status)
//   hard-neg    zsys_exit_hard(-1): exits with status 255
//   soft-hook   a user atexit handler is not run by zsys_exit_soft: user
//               glibc's handlers are its own Fil-C memory (exit() runs them
//               first, as plain-exit shows)
//   plain-exit  user glibc's exit(0) runs the handler
//   soft-stdio  an unflushed user FILE buffer is lost by zsys_exit_soft
//   hard-stdio  and by zsys_exit_hard
//   no-return   code after the call is never reached (the child would write
//               "R" to the pipe)
//   arity       a call through a pointer with no argument: panic (ArgumentSize),
//               not an exit
// The exits take no pointer and set no errno: there is no errno case.
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"

static int wfd;

static void hook(void) { write(wfd, "H", 1); }

// Run fn in a child with the pipe's write end in wfd; print name, how the
// child ended (exit status, or -1 for a signal) and the bytes it wrote.
static void ends(const char *name, void (*fn)(void)) {
  int p[2];
  pipe_nb(p);
  fflush(stdout);
  pid_t pid = fork();
  if (pid == 0) {
    close(p[0]);
    wfd = p[1];
    fn();
    write(wfd, "R", 1);
    _exit(100);
  }
  close(p[1]);
  int status = 0;
  waitpid(pid, &status, 0);
  char got[64];
  long n = drain(p[0], got, sizeof got - 1);
  got[n < 0 ? 0 : n] = 0;
  printf("%s %d \"%s\"\n", name, WIFEXITED(status) ? WEXITSTATUS(status) : -1, got);
  close(p[0]);
}

static void soft263(void) { zsys_exit_soft(263); }
static void hardneg(void) { zsys_exit_hard(-1); }
static void softhook(void) { atexit(hook); zsys_exit_soft(0); }
static void plainexit(void) { atexit(hook); exit(0); }
static void softstdio(void) {
  FILE *f = fdopen(wfd, "w");
  setvbuf(f, NULL, _IOFBF, 4096);
  fputs("buffered", f);
  zsys_exit_soft(0);
}
static void hardstdio(void) {
  FILE *f = fdopen(wfd, "w");
  setvbuf(f, NULL, _IOFBF, 4096);
  fputs("buffered", f);
  zsys_exit_hard(0);
}
static void noreturn(void) { zsys_exit_hard(3); }
static void arity(void) {
  volatile void *f = (void *)zsys_exit_hard;
  ((void (*)(void))f)();
}

int main(void) {
  ends("soft-263", soft263);
  ends("hard-neg", hardneg);
  ends("soft-hook", softhook);
  ends("plain-exit", plainexit);
  ends("soft-stdio", softstdio);
  ends("hard-stdio", hardstdio);
  ends("no-return", noreturn);
  ends("arity", arity);
  return 0;
}
