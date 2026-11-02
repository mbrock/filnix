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

## Hoisting the invariant parts (`--checks=hoist`)

Filip Pizlo's answer to the OR form: check-heavy code needs a pipeline
built for codegenning checks, and there may be up to 10% to gain. The
question for nanofil: when a loop checks the same capability on every
iteration, can the parts that do not change (the null test, the load of
upper, `upper - Size`) be computed once before the loop, so that the
check in the loop shrinks to the short form? It can, soundly, but under
the trap rule the short form needs the free flag test, and with it the
gain is gone. Without it, an unsound timing proxy gains about 1%.

### The obligation and why a flag test stays

A check in a loop of P, whose lower is that of a root P0 defined before
the loop, needs at the access `lower != 0`, `lower =< P` and
`P + Size =< upper`. The lower is P0's whatever P's address (a flight
keeps its lower donor's lower), so it is the same on every iteration.
The upper is not: `free` sets `upper = lower` (docs/perf.md item 6),
and a call, a signal handler at a poll or another thread may free the
object between the snapshot and the access. Two designs keep the trap
behaviour:

1. **Reload the upper after every safepoint** that can free: every
   call, allocation, pointer store (ensure-aux may exit), getter, and
   the slow path of every poll, which every loop's back edge has. The
   check in the loop is then the short form alone.
2. **Test the free flag at the access**, as renewal does (docs/m7.md,
   round 4). By round 4's lifetime lemma an object's upper changes only
   when it is freed, and free sets the FREE flag. So the snapshot's
   bounds and a clear flag together are exactly the full check, across
   any calls and polls.

nanofil implements the second, which needs no new kill list, no
emitter refresh and no native proof that every safepoint refreshes,
and measures the first as an unsound proxy that drops the flag test.

### The terms

Two checked-stage ops (ir.pl):

| Op | Class | Args | Meaning |
| --- | --- | --- | --- |
| `limit(Size)` | `l` | `[p]` P0 | an opaque snapshot of P0's capability and bounds for Size-byte accesses; never traps, reaches no safepoint |
| `check_limit(0, Size, Rights, Align)` | `a` | `[p, l]` P, U | exactly `check(0, Size, Rights, Align)` of P, followed by its access |

The validator accepts `check_limit` when U has one definition, a
`limit(Size)` of a single-definition P0, and P reaches P0 through
single-definition flights' lower donors (`lower_chain/3`), whatever
their addresses; the function has no setjmp; and its access follows.
By round 4's dominance argument P and P0 then hold, at the access, the
values the limit and P's flights saw. A limit is read only as a
`check_limit`'s second argument (`limit_reads/2`), so its encoding is
the backend's. A `check_limit` proves what a check proves: later
accesses may reuse it (rounds 1–3) and renew it (round 4). In the
interpreter a limit is `limit(Cap, Size)`, and `check_limit` is its
check when the limit is of P's capability and size, otherwise
`unchecked(limit)`.

The pass (`check_reuse:hoist_checks/2`) runs after renewal. Each full
check left in a natural loop, at offset 0 and followed by a renewable
access, whose pointer's lower chain reaches a root defined outside the
loop, reads a limit of that root and size placed where range guards
place theirs (`guard_places/4`: the end of the loop header's immediate
dominator, or a common dominator of several loops). `hoist_refines/2`
accepts only fresh limits at block ends and checks replaced in place.

### What it emits

The limit (`limit_value//3`), with the lower in `%rcx`, into `%rdx`:

| Shape | lower L not 0 | L = 0 |
|---|---|---|
| split | `upper - Size + 1`, or 0 if that borrows | 0 |
| merged | `upper - L - Size + 1`, or 0 if that borrows | 0 |
| or, sign | `upper - Size` | -1 |

The check in the loop (`limit_check//3`), after P's flight load into
`%rax:%rcx` and the limit into `%rdx`:

```
split    cmp %rcx,%rax ; jb F ; cmp %rdx,%rax ; jae F
merged   mov %rax,%rsi ; sub %rcx,%rsi ; cmp %rdx,%rsi ; jae F
or       mov %rax,%rsi ; sub %rcx,%rsi ; sub %rax,%rdx ; or %rsi,%rdx ; shr $56,%rdx ; jnz F
sign     as or, with js F instead of shr and jnz
then     testb $4,-2(%rcx) ; jnz F           ($6 for a write: also read-only)
```

The sentinels fold the null test into the bounds: no pointer lies in
`[0, 0)`, and with -1, `p | ~p` has every bit set. The flags byte is
read only once the bounds passed, so never at a null lower. Every
failure goes to the full check's label with `%rax:%rcx` = P, so the
report is the full check's. Against the full check (eight instructions,
`test`, `jz`, `cmp`, `jb`, `mov`, `sub`, `cmp`, `ja`), a hoisted read
is seven with split (the limit's move, four, the flag test's two), so
it saves one instruction; a write saves three, since the full write
check tests the flags too. The OR form is three more than split even
with its terms hoisted.

### Proof: [tests/hoist_smt.py](../tests/hoist_smt.py)

The sibling of bounds_smt.py. It takes `limit_value//3`'s and
`limit_check//3`'s lines from the compiler for every shape, both rights
and sizes 1 to 2^31 - 1, runs the first with lower L and upper U0 and
the second later with any 64-bit ptr, the same L, the limit, and flags
byte F, and asks Z3 whether

    passes <=> L != 0 and L =< ptr and ptr + Size =< U
               and, for a write, the object is not read-only

can fail, where U is the upper at the access. The assumptions are the
contract's, explicit:

- the check's lower is the limit's (the lower chain);
- U = U0 unless the object was freed since; then U = L and F has FREE
  (4), and FREE is set exactly when the object is freed (the lifetime
  lemma); a free racing the access is outside the model, as for every
  check;
- READONLY (2) in F is the object's read-only flag;
- for a nonnull L, `16 =< L =< U0 < 2^47` (and separately `2^56`);
  only an object can be freed.

Neither part may read a header at a null lower, and the limit must
reach its end. Results (about 60 s, a Nix check step): split, merged
and or are equivalent in every case; sign again passes only
non-canonical pointers (`2^56 =< ptr < 2^64 - 2^56`).

### Tests, and the mistakes they catch

| Planted mistake | Caught by |
| --- | --- |
| split limit without its clamp | hoist_smt (sizes 32 and up) |
| or limit with 0 for a null lower | hoist_smt; hoist-edges.c (`-O --bounds=or`, the null row dies by SIGSEGV) |
| no flag test | hoist_smt; renew-trap.sh (`hoist-free.c`) |
| the read mask for a write | hoist_smt; renew-trap.sh (`hoist-readonly.c`) |
| split `ja` for `jae` | hoist_smt; hoist-edges.c |
| merged limit without `- lower` | hoist_smt; hoist-edges.c |
| validator ignores the lower chain, the size, or the offset | unit `limit_validation` (and `limit_semantics`) |
| validator lets a limit be read as a number or by a phi | unit `limit_validation` |
| interpreter ignores the limit's capability | unit `limit_semantics` |
| liveness drops the limit | progtest under `--checks=hoist -O` (spurious traps) |

- **Unit:** `limit_validation` (variable offsets, two flights, another
  pointer's address with the root's lower; rejected: another root or
  lower donor, a limit of another size either way, an offset, not a
  limit, the limit, root or a flight defined twice, a setjmp, a limit
  read by an add or a phi, no access, a limit that does not dominate),
  `limit_semantics` (in bounds, one byte past, a free in between, null,
  a write to read-only data, a limit of another object or size) and
  `hoist_pass` (a loop's read of `p + j`, `j` loaded in the loop,
  across a call that frees; the store after it renews the hoisted
  proof; one limit; `hoist_refines/2` refuses a moved check and another
  limit).
- **Native:** [tests/c/bounds/hoist-edges.c](../tests/c/bounds/hoist-edges.c)
  is edges.c's matrix with each access in a loop whose offset is loaded
  in the loop, plus a null row, recording a Fil-C trap and any other
  death apart; under `-O --checks=hoist` every shape must match filcc.
  `hoist-free.c` (freed by a call in the loop), `hoist-past.c` (an index
  one element past the end) and `hoist-readonly.c` (a write to
  read-only data) compare the whole stderr with reference checks, in
  every shape. check.nix runs difftest, run-c and progtest under hoist
  with and without `-O`, and the corpus under `-O`.

`--checks=hoist` leaves every other mode's output unchanged: the
snapshot gate is identical, and `-O` (renew) output is identical on
tests/c and tests/c/prog.

### Results

Benchmark gate, 7950X3D, 7 trials, time ratio to filcc -O2 with the
instruction ratio in parentheses. All modes of a table are one run.

| Workload | `-O` | hoist, split | hoist, merged | hoist, or | `-O --bounds=merged` | `-O --bounds=or` |
|---|--:|--:|--:|--:|--:|--:|
| zlib -6 text | 2.09 (3.50) | 2.11 (3.47) | 2.17 (3.50) | 2.24 (3.63) | 2.19 (3.61) | 2.23 (3.67) |
| zlib -d text | 1.78 (3.03) | 1.78 (3.03) | 1.82 (3.09) | 1.88 (3.21) | 1.83 (3.10) | 1.91 (3.21) |
| bzip2 -9 text | 1.63 (2.17) | 1.67 (2.16) | 1.68 (2.15) | 1.82 (2.32) | 1.70 (2.27) | 1.78 (2.33) |
| bzip2 -d text | 2.27 (2.75) | 2.27 (2.72) | 2.30 (2.78) | 2.35 (2.84) | 2.31 (2.84) | 2.34 (2.87) |
| lz4 -1 random | 2.12 (10.14) | 2.14 (10.09) | 2.10 (10.33) | 2.09 (10.34) | 2.23 (10.34) | 2.19 (10.33) |
| lz4 -9 text | 2.05 (2.68) | 2.12 (2.74) | 2.15 (2.77) | 2.23 (2.83) | 2.12 (2.78) | 2.14 (2.78) |
| lz4 -d text | 2.64 (5.52) | 2.62 (5.52) | 2.64 (5.62) | 2.67 (5.63) | 2.65 (5.62) | 2.66 (5.63) |
| lua int | 1.53 (1.82) | 1.64 (1.80) | 1.60 (1.85) | 1.70 (1.91) | 1.62 (1.89) | 1.67 (1.92) |
| lua tab | 1.48 (1.73) | 1.49 (1.72) | 1.58 (1.79) | 1.73 (1.84) | 1.56 (1.80) | 1.64 (1.84) |
| lua str | 1.41 (1.51) | 1.41 (1.51) | 1.43 (1.54) | 1.43 (1.55) | 1.42 (1.54) | 1.44 (1.55) |
| sqlite | 1.84 (1.89) | 1.90 (1.92) | 1.93 (1.97) | 1.96 (1.99) | 1.87 (1.95) | 1.90 (1.97) |
| geomean | 1.86 (2.81) | 1.89 (2.81) | 1.91 (2.86) | 1.98 (2.93) | 1.92 (2.89) | 1.96 (2.93) |

The proxy for design 1 drops the flag test from hoisted reads: what
reloading the upper after every safepoint would run if the reloads cost
nothing and every loop qualified (a loop with a call would need a
reload after it). It is unsound for a program that reads a freed
object, which no gate workload does, and was built only for this
measurement. A second run:

| Workload | `-O` | hoist, split | proxy, split | proxy, or |
|---|--:|--:|--:|--:|
| zlib -6 text | 2.08 (3.50) | 2.11 (3.47) | 2.06 (3.39) | 2.21 (3.56) |
| zlib -d text | 1.63 (3.03) | 1.63 (3.03) | 1.62 (3.03) | 1.73 (3.21) |
| bzip2 -9 text | 1.63 (2.17) | 1.68 (2.16) | 1.57 (2.05) | 1.74 (2.21) |
| bzip2 -d text | 2.24 (2.75) | 2.24 (2.72) | 2.22 (2.68) | 2.30 (2.80) |
| lz4 -1 random | 2.03 (10.28) | 2.05 (10.28) | 2.03 (10.28) | 2.03 (10.46) |
| lz4 -9 text | 2.02 (2.68) | 2.26 (2.74) | 2.06 (2.67) | 2.28 (2.76) |
| lz4 -d text | 2.53 (5.52) | 2.38 (5.52) | 2.37 (5.52) | 2.52 (5.63) |
| lua int | 1.57 (1.82) | 1.82 (1.80) | 1.56 (1.78) | 1.74 (1.89) |
| lua tab | 1.46 (1.73) | 1.46 (1.72) | 1.46 (1.72) | 1.66 (1.83) |
| lua str | 1.40 (1.50) | 1.40 (1.51) | 1.40 (1.51) | 1.42 (1.55) |
| sqlite | 1.85 (1.89) | 1.91 (1.92) | 1.90 (1.91) | 1.95 (1.99) |
| geomean | 1.83 (2.81) | 1.88 (2.81) | 1.81 (2.78) | 1.94 (2.90) |

The flag test is two instructions per hoisted read, so the instruction
difference between hoist and the proxy counts them: about 245M hoisted
reads in bzip2 -9, 95M in lz4 -9, 70M in zlib -6, 50M in SQLite, 30M in
bzip2 -d, 15M in Lua int.

- **Sound hoisting does not beat `-O`.** Instructions are the same
  (bzip2 -9 −0.6%, zlib -6 −1%, SQLite +1.3%), and time is 1–3% worse
  in the geomean. A hoisted read saves one instruction.
- **The flag test is costly where it runs.** Lua int is 7–16% slower
  with it and as fast as `-O` without it; perf shows cycles +13% with
  fewer instructions and `ls_bad_status2.stli_other` (loads stalled by
  a store-to-load interlock) doubling, 10M to 19.5M. Renewal reads the
  same byte; why it stalls here was not pinned down.
- **Without the flag test it gains about 1%** in the geomean, the upper
  bound for design 1: bzip2 -9 −4% (−5.4% instructions), zlib -6 −1%,
  and SQLite +3%. In SQLite, functions with short loops called often
  (`sqlite3GetVarint`, `sqlite3VdbeRecordCompareWithSkip`) pay for a
  limit, and the register it holds, on every call.
- **Hoisting does not rescue the OR form.** Hoisted OR is 5–7% behind
  hoisted split in both runs, and behind the unhoisted OR form too.
  Even with both terms invariant, the check is the subtraction from
  `ptr`, the OR, the shift and the branch on one dependency chain,
  where split's two compares are independent and predict well.

So split stays the default, unhoisted, and `--checks=hoist` stays
opt-in for measurement (`O-hoist`, `O-hoist-merged` and `O-hoist-or` in
nanofil/bench). Design 1 is bounded by about 1% on this gate before
paying for its reloads, which needs a reviewed contract: limits that
the validator kills at every call, allocation, pointer store and getter
but carries across polls, an emitter that recomputes every live limit
after `filc_pollcheck_slow`, and native tests where a signal handler
frees the object at a poll. Not proposed at this yield.
