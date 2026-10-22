/* After siglongjmp restores a mask saved while cancellation was enabled, a
   redundant pthread_setcancelstate(DISABLE) must block the runtime's private
   cancellation signal (kernel signal 34, the runtime's native SIGRTMIN) again, or a late cancellation notification
   interrupts disabled blocking calls. Public masks hide the signal, so read
   the native mask from /proc. */
#include <pthread.h>
#include <setjmp.h>
#include <signal.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>
#include <sys/syscall.h>

static int private_blocked(void) {
  char path[64], line[256];
  snprintf(path, sizeof path, "/proc/self/task/%ld/status", (long)syscall(SYS_gettid));
  FILE *f = fopen(path, "r");
  unsigned long long blk = 0;
  while (fgets(line, sizeof line, f))
    if (!strncmp(line, "SigBlk:", 7)) blk = strtoull(line + 7, 0, 16);
  fclose(f);
  return (blk >> (34 - 1)) & 1; /* the runtime's native SIGRTMIN */
}

int main(void) {
  sigjmp_buf env;
  int old;
  if (private_blocked()) { puts("FAIL: blocked while enabled"); return 1; }
  if (!sigsetjmp(env, 1)) {
    pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, &old);
    if (!private_blocked()) { puts("FAIL: not blocked after disable"); return 1; }
    siglongjmp(env, 1);
  }
  int stale = !private_blocked();
  pthread_setcancelstate(PTHREAD_CANCEL_DISABLE, &old);
  int ok = private_blocked();
  printf("after siglongjmp: %s; after redundant disable: %s -> %s\n",
         stale ? "unblocked" : "blocked", ok ? "blocked" : "unblocked", ok ? "OK" : "FAIL");
  /* Enabled no-op setters (stdio) must still leave cancellation working. */
  pthread_setcancelstate(PTHREAD_CANCEL_ENABLE, &old);
  for (int i = 0; i < 1000; i++) fprintf(stderr, "%s", "");
  return !ok;
}
