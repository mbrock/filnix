/* A callee that owns memory across calls, in the shape of gnulib's
   quotearg: fill keeps one buffer in its own static slot, grows it by
   free and malloc when a request does not fit, fills it with memset,
   and lends it to its caller until the next call. use calls it three
   times, reading each result before the next call; the second call
   reuses the buffer and the third grows it. */
#include <stdlib.h>
#include <string.h>

static char *slot;
static unsigned long slot_size;

char *fill(int c, unsigned long n) {
  if (slot_size <= n) {
    free(slot);
    slot = malloc(n + 1);
    slot_size = n + 1;
  }
  memset(slot, c, n);
  slot[n] = 0;
  return slot;
}

int use(void) {
  char *a = fill('a', 8);
  int x = a[7];
  char *b = fill('b', 3);
  int y = b[0];
  char *c = fill('c', 16);
  return x + y + c[15];
}
