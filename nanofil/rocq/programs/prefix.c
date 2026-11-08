// A closed program with an integer input: the sum of the first n longs
// of a read-only global array, for every int n. The loop's index is
// checked against both n and the array's length, so no n reaches past
// the array (rocq/theories/Prefix.v).
// run: $prefix 2
// run: $prefix -1
// run: $prefix 9

static const long xs[4] = {1, 2, 3, 4};

long prefix(int n) {
  long s = 0;
  for (int i = 0; i < n && i < 4; i++)
    s += xs[i];
  return s;
}
