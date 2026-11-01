# One branch for both bounds (`--bounds=merged`)

D. J. Bernstein suggested (November 2026) replacing Fil-C's two bounds
branches, `ptr < lower` and `ptr > upper - size`, with one unsigned
comparison of `ptr - lower` against `upper - lower`, and storing the
length instead of `upper` in the object header to save the subtraction.
Fil-C's runtime header names the same tradeoff
(`filc_runtime.h`, `struct filc_object`): size "would mean one branch
for checking lower and upper bounds … but at the cost of that branch
having a data dependency … experience shows that more branches with
fewer dependencies is faster. We should test if size is better than
upper at some point!" nanofil can test the check's shape without
touching the toolchain, so it does, as an opt-in mode.

## The check

nanofil's default check, with the pointer in `%rax` and its lower in
`%rcx` (filc_amd64.pl, `access_check//2`):

```
test %rcx,%rcx ; jz fail            null lower
cmp  %rcx,%rax ; jb fail            ptr < lower
mov  -16(%rcx),%rdx                 upper
sub  $Size,%rdx ; [jb fail]         upper - Size (the borrow test is dropped for Size =< 16 under local selection)
cmp  %rdx,%rax ; ja fail            ptr > upper - Size
```

With `--bounds=merged` (`merged_bounds//2`):

```
test %rcx,%rcx ; jz fail            null lower: -16(0) would fault
mov  %rax,%rsi ; sub %rcx,%rsi      T = ptr - lower
mov  -16(%rcx),%rdx
sub  %rcx,%rdx                      upper - lower
sub  $(Size-1),%rdx                 M; borrows when the object is shorter than Size - 1
cmovb %rdx,%rsi                     on a borrow T = M, so the test fails
cmp  %rdx,%rsi ; jae fail           T >= M
```

The valid `T` are exactly `0 =< T < M`. A pointer below lower makes `T`
at least 2^64 - 2^48, above any `M` (addresses have 48 bits). The
`cmovb` is not optional. Without it, `M` wraps to nearly 2^64 whenever
`upper - lower < Size - 1`, and the comparison passes:

- an object shorter than the access, such as `malloc(1)` read as 8
  bytes;
- every freed object, read with 2 bytes or more: `free` sets
  `upper = lower` (`free_impl`), so its length is 0. Fil-C's FREE flag
  is tested only for writes; reads of a freed object are refused by the
  bounds alone, so dropping the borrow would let use-after-free reads
  through.

[tests/c/bounds/edges.c](../tests/c/bounds/edges.c) reads 1, 2, 4 and 8
bytes (and writes 1 and 8) at the offsets near both ends of objects of
the boundary lengths from 0 to 17 bytes and of a freed one, and
compares the trap pattern with filcc's. It fails
when the `cmovb` is removed (the freed object's rows differ first).

## Results

Benchmark gate (docs/perf.md), AMD Ryzen 9 7950X3D, 7 trials, time
ratio to filcc -O2. `O-lenproxy` drops `sub %rcx,%rdx`, as a header
holding the length instead of `upper` would: a timing proxy for that
ABI change, built only for this measurement because it is unsound with
the real header (the gate's workloads never trap, so it runs them
correctly).

| Workload | `-O` | `-O --bounds=merged` | length ABI proxy |
|---|--:|--:|--:|
| zlib -6 text | 2.10 | 2.19 | 2.14 |
| zlib -d text | 1.66 | 1.71 | 1.65 |
| bzip2 -9 text | 1.63 | 1.71 | 1.66 |
| bzip2 -d text | 2.24 | 2.29 | 2.25 |
| lz4 -1 random | 2.21 | 2.28 | 2.18 |
| lz4 -9 text | 2.10 | 2.18 | 2.17 |
| lz4 -d text | 2.66 | 2.66 | 2.62 |
| lua int | 1.50 | 1.58 | 1.53 |
| lua tab | 1.40 | 1.47 | 1.44 |
| lua str | 1.40 | 1.41 | 1.39 |
| sqlite | 1.83 | 1.86 | 1.85 |
| geomean | 1.84 | 1.90 | 1.86 |

The merged check runs 3% more instructions and is about 3% slower; no
workload gets faster. Storing the length recovers about two thirds of
that and still loses to the two-branch check. `.text` grows 0.7 to
1.2% (three instructions per check). On this machine Fil-C's
experience holds: the bounds branches are almost never taken and
predict well, so removing one buys little, while the merged form
lengthens the check's dependency chain (load, two subtractions,
`cmovb`, compare) before its only branch can resolve. A real ABI
change (runtime, FilPizlonator and every library) is not worth making
for this. Other microarchitectures, or code where branch-predictor
capacity rather than latency is the limit, could differ; the mode stays
to measure them (`O-merged` in nanofil/bench).
