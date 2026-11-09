// A program with a heap object: a buffer of four longs from alloca,
// which Fil-C allocates in the collected heap, filled and then read in
// turn as in cycle.c, for every int n. Two proofs: rocq/theories/Buffer.v
// by an assertion at each point, and rocq/theories/BufferLogic.v through
// the Iris program logic.
// run: $buffer 6
// run: $buffer -1
// run: $buffer 0

long buffer(int n) {
  long *p = __builtin_alloca(4 * sizeof(long));
  for (int i = 0; i < 4; i++)
    p[i] = i + 1;
  long s = 0;
  for (int i = 0; i < n; i++)
    s += p[i % 4];
  return s;
}
