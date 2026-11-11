// Native counterexample probe for os_self_contract (rocq/glibc/zsys/OsThread.v),
// built by filcc and compared with zsys-thread.c.expected:
//   cookie     nonnull, the thread's pthread_self(), the same on every call,
//              errno untouched
//   size       its object is at least 2464 + 8 bytes (struct pthread's highest
//              offset user glibc reads through it, ledger finding 5)
//   unchanged  the call writes nothing: a stack array, heap object and global
//              unchanged, and the cookie's first 2472 bytes too
//   other      another thread's cookie is its own, not the main thread's
//   oob        a read one past the cookie's object: panic
//   arity      extra arguments are ignored (the call takes none): no panic
// Finite evidence, not a proof that every native call satisfies the contract.
#include "zsys-common.h"
#include <pthread.h>
#include <stdfil.h>

static char gcanary[8] = "global!";
static void *other_cookie;

static void *other(void *arg) {
  other_cookie = zthread_self_cookie();
  return arg;
}

static void oob(int unused) {
  char *c = zthread_self_cookie();
  volatile char x = c[zlength(c)];
  (void)x;
}

int main(void) {
  errno = 1234;
  void *c = zthread_self_cookie();
  void *c2 = zthread_self_cookie();
  printf("cookie %d %d %d %d\n", c != NULL, c == (void *)pthread_self(), c == c2, errno == 1234);
  printf("size %d\n", zlength((char *)c) >= 2464 + 8);

  char canary[8] = "canary!";
  char *hcanary = malloc(8);
  strcpy(hcanary, "a heap!");
  char *snap = malloc(2472);
  memcpy(snap, c, 2472);
  zthread_self_cookie();
  printf("unchanged %d %d %d %d\n", !strcmp(canary, "canary!"), !strcmp(hcanary, "a heap!"),
         !strcmp(gcanary, "global!"), !memcmp(snap, c, 2472));

  pthread_t t;
  pthread_create(&t, NULL, other, NULL);
  pthread_join(t, NULL);
  printf("other %d %d\n", other_cookie != NULL, other_cookie != c);

  dies("oob", oob, 0);
  volatile void *f = (void *)zthread_self_cookie;
  void *c3 = ((void *(*)(int, int))f)(1, 2);
  printf("arity %d\n", c3 == c);
  return 0;
}
