// A closed program with no input and no libc call: the first program
// Panics.v proves never panics (rocq/theories/Sum.v). The loop reads a
// read-only global array through checked loads.
// run: $sum

static const long xs[4] = {1, 2, 3, 4};

long sum(void) {
  long s = 0;
  for (int i = 0; i < 4; i++)
    s += xs[i];
  return s;
}
