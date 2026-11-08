// A loop whose trip count is the input: the sum of n longs read in turn
// from a read-only global array of four, for every int n. The index is
// i % 4, which is in bounds because i never goes negative, so the proof
// (rocq/theories/Cycle.v) needs an assertion about i at the loop's head
// rather than a list of runs.
// run: $cycle 6
// run: $cycle -1
// run: $cycle 0

static const long xs[4] = {1, 2, 3, 4};

long cycle(int n) {
  long s = 0;
  for (int i = 0; i < n; i++)
    s += xs[i % 4];
  return s;
}
