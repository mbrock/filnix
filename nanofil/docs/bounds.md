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

## The OR of two differences (`--bounds=sign`, `--bounds=or`)

Bernstein's later form: `(ptr - lower) | (upper - Size - ptr)` is
non-negative exactly when both differences are, and then branch on the
sign. With `-lower` and `upper - Size` already in registers it is four
instructions and one branch (`lea`, `sub`, `or`, `js`). It also handles
a freed object (`upper = lower` makes the second term negative) and an
object shorter than the access, without the `cmovb`.

nanofil has nothing in registers across accesses yet, so it recomputes
both terms at each check (`or_bounds//1`):

```
test %rcx,%rcx ; jz fail            null lower
mov  %rax,%rsi ; sub %rcx,%rsi      ptr - lower
mov  -16(%rcx),%rdx
sub  %rax,%rdx ; sub $Size,%rdx     upper - ptr - Size
or   %rsi,%rdx
js fail                             --bounds=sign
shr $56,%rdx ; jnz fail             --bounds=or
```

**The sign test is not exact.** `ptr` is any 64-bit value: integer
arithmetic moves a pointer anywhere and keeps its capability. When
`upper - lower` is less than `Size - 1` (a freed object, or one shorter
than the access) and `ptr - lower` lies within `Size` of 2^63, both
terms come out with the sign bit clear and the check passes. Example:
a freed 16-byte object, `ptr = lower + 2^63 - 1`, a 2-byte read. That
pointer is non-canonical, so the read faults in hardware (SIGSEGV)
rather than reaching memory. Memory stays safe, but the trap is no
longer Fil-C's. [tests/c/prog/bounds-far-freed.c](../tests/c/prog/bounds-far-freed.c)
is that program: filcc and every other shape stop with "cannot read
pointer to free object", and `--bounds=sign` exits with SIGSEGV.
1-byte accesses are exact under the sign test.

`--bounds=or` tests bits 56 and up instead of bit 63. That is exact
while objects stay below 2^56 bytes, which is the user space of
five-level paging. Each term of an in-bounds access is below 2^56. An
out-of-bounds term is either at least 2^56 or negative, and a negative
one is at most -(2^56 + Size), which sets the top bits.

### Proof: [tests/bounds_smt.py](../tests/bounds_smt.py)

The script takes the lines `bounds_check//4` emits for each shape
(split, merged, or, sign), both immediate selections (stack, local) and
sizes 1, 2, 3, 4, 8, 16, 17, 32, 4096 and 2^31 - 1. It runs them with
x86-64 semantics (flags included) and asks Z3 whether

    passes <=> lower != 0 and lower =< ptr and ptr + Size =< upper

can fail for any 64-bit `ptr`, `lower` and `upper`. Header reads are
also checked: no shape may read the header of a null lower. The proof
assumes what the runtime guarantees for a nonnull lower:

- `16 =< lower`, since the header sits below it;
- `lower =< upper`;
- `upper < 2^47` (four-level paging) or `2^56` (five-level), checked
  separately.

Results (about 40 s; a Nix check step):

- **split, merged and or are equivalent** in every case, including the
  borrow test that local selection drops for `Size =< 16`. That drop is
  sound only because of `16 =< lower`.
- **sign differs for every size from 2 up.** For each case the script
  prints a counterexample, then proves the weaker property: every
  pointer it wrongly passes satisfies `2^56 =< ptr < 2^64 - 2^56`, so it
  is non-canonical under either paging mode.
- **Planted bugs are caught.** Without the `cmovb`, merged fails with a
  freed object (`upper = lower`, 2-byte read). With `shr $47` instead of
  56, or fails at 56 bits on an object larger than 2^47.

### Results

Same gate as above, re-measured together (7950X3D, 7 trials, time ratio
to filcc -O2, instruction ratio in parentheses):

| Workload | `-O` | merged | sign | or |
|---|--:|--:|--:|--:|
| zlib -6 text | 2.08 | 2.18 | 2.19 | 2.22 |
| zlib -d text | 1.63 | 1.68 | 1.68 | 1.75 |
| bzip2 -9 text | 1.61 | 1.69 | 1.67 | 1.75 |
| bzip2 -d text | 2.25 | 2.29 | 2.27 | 2.32 |
| lz4 -1 random | 2.12 | 2.04 | 2.05 | 2.05 |
| lz4 -9 text | 2.02 | 2.22 | 2.18 | 2.20 |
| lz4 -d text | 2.52 | 2.39 | 2.56 | 2.44 |
| lua int | 1.57 | 1.68 | 1.66 | 1.77 |
| lua tab | 1.45 | 1.54 | 1.54 | 1.66 |
| lua str | 1.37 | 1.39 | 1.37 | 1.39 |
| sqlite | 1.82 | 1.86 | 1.85 | 1.89 |
| geomean | 1.83 (2.81) | 1.88 (2.89) | 1.88 (2.87) | 1.92 (2.93) |

- **sign matches merged** and is 3% behind the two-branch check. Its
  bytes equal split's (35 per check; sqlite's `.text` is 10,297,708
  bytes against 10,296,236).
- **The exact or is 5% behind.** The `shr` sits on the only branch's
  dependency chain.

Recomputed at every access, the OR is nine instructions with a longer
dependency chain, not four. The case for it is a loop that keeps
`-lower` and `upper - Size` in registers across iterations, the
hoisting docs/m7.md bounds. Until nanofil does that, split stays the
default.
