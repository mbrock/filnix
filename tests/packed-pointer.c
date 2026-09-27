// A constant initializer with a pointer at a misaligned offset, as in
// ALSA's packed snd_seq_ev_ext, used to trip an assertion in
// FilPizlonator.  The pointer is stored without a capability, like any
// misaligned pointer store; the rest of the object stays usable.
#include <stdio.h>

struct ext {
  unsigned len;
  void *ptr;
} __attribute__((packed));

static char buf[4] = "abc";
static const struct ext constant = {sizeof buf, buf};
static struct ext mutable = {7, buf};

int main(void) {
  if (constant.len != 4 || mutable.len != 7)
    return 1;
  puts("ok");
  return 0;
}
