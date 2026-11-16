// Native counterexample probe for the startup contracts of
// rocq/glibc/zsys/OsStartCalls.v, built by filcc and compared with
// zsys-start.c.expected:
//   setcookie  zthread_set_self_cookie(p) makes zthread_self_cookie() return
//              p, with its capability (a read through it works), errno and
//              a stack array, heap object and global untouched
//   nullcookie a null cookie is accepted and read back as null (no check)
//   restore    setting the original cookie back restores it
//   id         zthread_self_id() is nonzero, the same on two calls, errno
//              untouched; another thread's is different
//   self       zthread_self() is nonnull, the same on two calls, errno
//              untouched, and a byte read through it panics (no data access)
//   sigmask    zmake_setjmp_save_sigmask(0) and (1) return, errno untouched
//   errno2     a second zregister_sys_errno_handler: panic
//   dlerror2   a second zregister_sys_dlerror_handler: panic
//   ctors2     a second zrun_deferred_global_ctors: panic
// Finite evidence, not a proof that every native call satisfies the contract.
// The first registrations and the first constructor run happen in startup
// before main, so this probe can only observe the second.
#include "zsys-common.h"
#include <pthread.h>
#include <stdfil.h>

static char gcanary[8] = "global!";
static unsigned other_id;

static void *other(void *arg) {
  other_id = zthread_self_id();
  return arg;
}

static void self_read(int unused) {
  volatile char x = *(char *)zthread_self();
  (void)x;
}
static void handler(int e) { (void)e; }
static void dl_handler(const char *s) { (void)s; }
static void errno2(int unused) { zregister_sys_errno_handler(handler); }
static void dlerror2(int unused) { zregister_sys_dlerror_handler(dl_handler); }
static void ctors2(int unused) { zrun_deferred_global_ctors(); }

int main(void) {
  void *orig = zthread_self_cookie();
  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  char *mine = malloc(16);
  strcpy(mine, "cookie");
  errno = 1234;
  zthread_set_self_cookie(mine);
  char *got = zthread_self_cookie();
  printf("setcookie %d %d %d %d %d %d\n", got == mine, !strcmp(got, "cookie"), errno == 1234,
         !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"), !strcmp(gcanary, "global!"));
  zthread_set_self_cookie(NULL);
  printf("nullcookie %d\n", zthread_self_cookie() == NULL);
  zthread_set_self_cookie(orig);
  printf("restore %d\n", zthread_self_cookie() == orig);

  errno = 1234;
  unsigned id = zthread_self_id(), id2 = zthread_self_id();
  pthread_t t;
  pthread_create(&t, NULL, other, NULL);
  pthread_join(t, NULL);
  printf("id %d %d %d %d\n", id != 0, id == id2, errno == 1234, other_id != id);

  errno = 1234;
  void *s = zthread_self(), *s2 = zthread_self();
  printf("self %d %d %d\n", s != NULL, s == s2, errno == 1234);
  dies("selfread", self_read, 0);

  errno = 1234;
  zmake_setjmp_save_sigmask(0);
  zmake_setjmp_save_sigmask(1);
  printf("sigmask %d\n", errno == 1234);

  dies("errno2", errno2, 0);
  dies("dlerror2", dlerror2, 0);
  dies("ctors2", ctors2, 0);
  return 0;
}
