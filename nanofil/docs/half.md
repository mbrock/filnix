# Half checks: one bound where the other is known

Status: **opt-in** (`--checks=half`, November 2026). It is candidate 2 of
perf.md item 16's ranking. The `-O` default stays `renew`; see
[Measured](#measured) and [Default](#default).

An access check tests three things: the capability is not null, the
address is at or above lower, and the access ends at or below upper. When
an earlier check of the same object has passed at another range, some of
that is already known. filcc's forward pass then emits a check of only the
unknown bound. perf.md item 16 counts 207M of these lower-only runs on
filcc's side. On nanofil the same situation, its "partial" class, is 285M
executed checks: 217M at constant offsets and 67M at variable ones.

This contract does the same without moving any check. A check whose
object was checked before tests only the bound that earlier check does
not establish. It still traps at the same access with the same text.

## The facts

Let C1 be a passed heap check of P1 over [Lo1, Hi1) with proof Q1. Let C
be a later check of P over [Lo, Hi), with P = P1 + D modulo 2^64 and P1's
capability. When C1 ran:

- P1's capability was not null, and its lower was L.
- lower ≤ P1 + Lo1 and P1 + Lo1 + (Hi1 − Lo1) ≤ U0, the upper then.

Both facts last as long as the object does. A capability's lower never
changes for one SSA value. An object's upper changes only when it is
freed, which sets upper = lower and the FREE flag (docs/m7.md, round 4's
lifetime lemma). So with E = D + Lo − Lo1 and F = D + Hi − Hi1:

| Bound tested | Known | Needs |
|---|---|---|
| `upper` | not null; P + Lo is E bytes above P1 + Lo1, so it is at or above lower | E ≥ 0 |
| `lower` | not null; P + Hi is −F bytes below P1 + Hi1, so it is at or below U0, which is still the upper unless the object was freed | F ≤ 0, and the FREE flag is tested |

Wraparound: D is exact only modulo 2^64. It is reduced to the signed
range, and E and F must lie within ±2^62 (`near_offset/1`). Then for
`upper`, P1 + Lo1 + E cannot pass 2^64, since P1 + Lo1 is a user address
below 2^56. For `lower`, the access may lie below address 0 when the
object is low: P + Lo = P1 + Lo1 + E taken as an integer lies in
(−2^63, 2^56). Compared unsigned, such an address would be above lower,
so the lower test compares signed, and Hi − Lo ≤ 2^62 keeps P + Lo above
−2^63. A previous review of the scheduler found the same mistake there:
an offset that wraps modulo 2^64 was counted as a large positive one.

## The term

One new op, approved for this work as a grammar change:

| Op | Class | Args | Meaning |
|---|---|---|---|
| `half_check(Bound, Lo, Hi, Rights, Align)` | `a` | `[a, p]`: Q1, P | checked stage: exactly `check(Lo, Hi, Rights, Align)` of P; natively it tests only Bound, `upper` or `lower` |

Its result is P, proven, like a check's. It is followed by its access. It
is `evidence_preserving/1`. After its access it adds the full fact
`live(Q, P, Lo, Hi, Rights, Align)`, because it proves the whole range.
So rounds 1–3 may reuse it, and a renew, another half check or
candidate 1's hull rule may read it as they read a check. Q1 is
justification only: the emitter and liveness never read it.

## Validator rule (ir.pl, independent of the pass)

`let(tmp(Q), a, half_check(Bound, Lo, Hi, Rights, Align), [Q1, P])` is
accepted iff all of these hold:

1. Q1 is in renew's source table (`stage_sources/3`). That means Q1 has
   one definition, a heap `check`, `check_ahead`, `renew_if`,
   `check_limit` or `half_check` of P1, and P1 has one definition. The
   table is empty in a function with a setjmp.
2. `pointer_distance(Once, P, P1, D0)`: P and P1 reach one
   single-definition base through single-definition `add`, `sub` and
   `copy` flights whose lower donor is their address operand, at exact
   offsets. So P has P1's capability, and P's address is P1's plus D0
   modulo 2^64.
3. `half_known(Bound, Lo, Hi, D0, Lo1, Hi1)`: with D the signed reduction
   of D0, E and F as above, near_offset(E), near_offset(F),
   Hi − Lo ≤ 2^62, and E ≥ 0 for `upper` or F ≤ 0 for `lower`.
4. The next instruction is an access it covers (`proof_use/6`), as for a
   check.

Strict SSA's `definitions_dominate` makes Q1's definition dominate the
half check. With rule 2 that is round 4's argument (m7.md, the addendum's
lemma): at the half check, P1 and Q1 hold the values C1 checked, and P
is computed from the same base value. There is no dataflow and no kill
list. Nothing between C1 and C can falsify the facts except a free, and
each bound's test accounts for that:
- `upper`: a free sets upper = lower ≤ P + Lo < P + Hi, so the upper
  test itself fails.
- `lower`: the FREE flag is tested.

## Interpreter rule (interp.pl)

`half_check` with operands `[ptr(_, Cap1), ptr(A, Cap)]` and Cap1 ≠ Cap is
`unchecked(alias)`. Otherwise it runs the check's whole `access_res/7` on
P, and separately the native one-sided test (`half_passes/8`):
- `upper`: B + Size ≤ upper.
- `lower`: B taken signed ≥ lower, and the object not freed.
- Then, for both, not read-only for a write, and aligned.

When the two agree, the result is the check's: P, or its trap. When they
disagree, the bound the validator took as known was false, and the
result is `unchecked(half)`. A capability that is not an object's is
`unchecked(half)` too, since no half check may read its header. So a
validator or pass mistake shows in difftest as a changed outcome.

## Emitter rule (filc_amd64.pl)

`fused(half_check(Bound, 0, Size, Rights, Align), Access)`: the flight
load of P, `half_bounds//5`, the check's `align_check`, then the access.
- `upper`: split's upper test (`movq -16(%rcx), %rdx; subq $Size, %rdx;
  jb; cmpq %rdx, %rax; ja`, with local selection's borrow rule), then
  `write_check` for a write.
- `lower`: `cmpq %rcx, %rax; jl`, then `testb $4` or `$6, -2(%rcx); jnz`,
  renewal's flags test.

Every failure goes to the check's own fail label `k(Size, Write, Align)`
with %rax:%rcx = P and the check's origin. `filc_optimized_access_check_fail`
works out its message from the pointer's state and the origin's size, not
from which test fired. So a half check that traps prints exactly the full
check's text. `single_proofs` and the in-block proofs map Q to P, as for a
check, so a reused access or renew of Q reloads P. The lines are the same
under every `--bounds` shape. Compared with split's full check, a read
saves 4 instructions (`upper`: the null and lower tests) or 5 (`lower`:
the null test and the upper's load, adjustment and compare, for one flags
test). A write saves 4 or 7.

`tests/half_smt.py` proves, with Z3 over 64-bit bit-vectors, for both
bounds, both selections, reads and writes, and sizes from 1 to 2^31 − 1:
the emitted lines pass exactly when Fil-C's full check passes at the
access, given the facts above. It reads them from the compiler, not from
a transcription. Its assumptions are those of hoist_smt.py, plus the
earlier check's success and the bounds on E and F.

## The pass (half_check.pl)

`half_checks/2` runs after renewal. For each heap check left in a
reachable block, it looks for a source, any heap proof of the forms in
rule 1, whose pointer reaches one of the check's exact single-definition
bases. The source must be earlier in the block or in a dominating block,
shallowest dominator depth first. It takes the first source with a known
bound: `lower` when F ≤ 0 (for a write that test also covers free), else
`upper` when E ≥ 0. As renewal does, it calls the validator's
`pointer_distance/4` so as to make only what the validator accepts.
`half_refines/2` accepts only checks replaced in place by half checks of
the same pointer, range, rights and alignment. Then `valid_module/1`
decides. The pass's side rule (`known_bound/6`) is written separately from
the validator's `half_known/6`.

## Observation contract

Unchanged from the reference. Every check stays at its index, with its
origin, pointer, range, rights and alignment. A half check traps exactly
when its check would, on the same state, and the report is the same:
- the same fail call;
- the runtime's message, which depends only on that state and the
  origin;
- the same block count.

No check moves, widens or is added. A free by another thread that races
with the access may go unseen, as with every check and its access. The
same holds for the window in which free_impl has written upper but not
yet FREE (m7.md, round 4).

## Measured

On swa (Ryzen 9 7950X3D) at 65872a9 plus this change. Executed checks
come from `bench/profile/checks.py` (callgrind, perf.md item 16's
counting). A half check with a lower test and no upper test is a
lower-only run there, which is not counted as a check, as for filcc. Each
cell is checks M, then check instructions M and program instructions G.
Outputs are byte-identical to filcc's.

| Workload | `-O` | `-O --checks=half` | program instructions |
|---|--:|--:|--:|
| zlib -6 | 241.0 (1299; 6.86G) | 193.8 (1122; 6.63G) | −3.4% |
| zlib -d | 17.6 (131; 0.57G) | 16.5 (105; 0.54G) | −5.3% |
| bzip2 -9 | 512.8 (2909; 10.13G) | 503.0 (2728; 9.89G) | −2.4% |
| bzip2 -d | 118.1 (660; 3.92G) | 118.1 (594; 3.83G) | −2.3% |
| lz4 -1, -d | 3.2, 3.8 | unchanged | 0 |
| lz4 -9 | 155.8 (1062; 7.31G) | 152.4 (1046; 7.30G) | −0.1% |
| Lua int | 68.1 (484; 2.09G) | 54.0 (396; 1.99G) | −4.8% |
| Lua tab | 60.2 (425; 1.63G) | 48.1 (353; 1.53G) | −6.1% |
| Lua str | 85.6 (627; 3.22G) | 69.2 (547; 3.12G) | −3.1% |
| SQLite | 557.9 (3725; 16.65G) | 480.9 (3107; 15.80G) | −5.1% |
| **all** | **1824 (11372; 52.9G)** | **1643 (10048; 51.2G)** | **−1.75G** |

So 181M checks leave the count, 1.32G check instructions go, and
program instructions fall by 1.75G, against item 16's estimate of about
1.1G. The other 0.43G is outside the check runs that checks.py counts
(flight loads and frame traffic, inferred, not split here). Null tests fall from 1.44G to 1.01G
executed. bzip2 -d's count does not move, because its partial checks
became upper-only half checks, which still count as checks.

Time: `run.py --modes ref,O,O-half`, 7 trials on cpu 6, which run.py
found quiet (load 1.2). The ratio is time against filcc -O2, with the
trial range:

| Workload | `-O` | `-O --checks=half` |
|---|--:|--:|
| geomean | 1.83 (2.81) | 1.80 (2.73) |
| bzip2 -9 | 1.61 (1.61..1.62) | 1.53 (1.53..1.57) |
| SQLite | 1.81 (1.81..1.82) | 1.78 (1.76..1.81) |
| lz4 -d | 2.49 (2.36..2.55) | 2.39 (2.34..2.52) |
| zlib -6 | 2.08 (2.05..2.09) | 2.06 (2.02..2.08) |
| Lua int | 1.57 (1.57..1.68) | 1.58 (1.57..1.65) |
| others | within 0.02 | within 0.02 |

No workload is slower beyond its trials' range.

## Review (November 2026)

A reviewing subagent attacked the validator, interpreter, emitter, pass
and Z3 model. It found no blocker: no input on which a half check passes
or traps differently from its check, or reports differently. Its one
should-fix, now fixed: the pass walked the dominator tree for every
source and check, so a function of 1500 sequential `if` arms took 369 s
under half against 8.0 s under renew. It now uses `dom_intervals/3`'s
preorder intervals, as the validator does, and takes 9.1 s, with output
byte-identical on all 195 `tests/c/prog` programs.

Found sound:
- D, E and F modulo 2^64, and the signed lower test near 0 and 2^63.
- Another lower donor.
- Dominance in loops and irreducible CFGs.
- A half check citing its own proof, and setjmp.
- `check_limit`, `renew_if` and half checks as sources, and sources
  with Lo1 < 0.
- A free before either bound, special and function objects (upper =
  lower, so no source check passes on them), read-only data, and local
  selection's borrow rule.
- Integer and pointer cas after a half check.
- The report, which the runtime derives from state.
- That half_smt.py's assumptions are exactly what half_known/6
  establishes.

Accepted, as in m7.md: the race of an unsynchronized free with the
access.

## Default

Recommended, not yet made. Half checks win in instructions everywhere
and in time on the geomean, no workload loses, and the review has no
open blocker. Making `-O` select `--checks=half` is the user's decision.
The snapshot pins `--checks=reference`, so it would stay byte-identical.

## Tests and plants

- `tests/unit.pl`:
  - `half_validation`. Accepted: `upper` of a + 8 and `lower` of a − 8
    after a call, for reads and writes; `lower` of a + (2^64 − 8) and of
    a + (2^63 − 4) + (2^63 − 4), both a − 8; either bound at distance 0;
    a variable offset through a shared base (a + n + 8 after a + n); a
    half check's proof reused, renewed and read by another half check.
    Rejected: the wrong side for each of those, another lower donor, a
    renew's proof, Q1 defined twice, a setjmp, no access after it, Q1
    not dominating, a + n after a (no constant distance), and E below
    −2^62.
  - `half_semantics`: in bounds by either bound; past the end and below
    the start, which trap like the check; a free in between, which traps
    `out_of_bounds` for both bounds; a write to read-only data, which
    traps `readonly` for both; p − 2^40, whose address wraps past 0 and
    still traps; forged wrong sides, which are `unchecked(half)`; another
    object, which is `unchecked(alias)`.
  - `half_pass`: a loop with a call reads p + 24 (`upper` from p's
    check) and writes p + 16 (`lower` from p + 24's). The original,
    checked, renewed and half modules agree. There are fewer null tests,
    and `jl` appears in the code. half_refines refuses a changed range and
    a deleted check, and a check on one arm leaves the join's check alone.
- `tests/half_smt.py`: the emitted lines against Fil-C's condition.
- `tests/c/prog/half-*.c` with `tests/renew-trap.sh`: nanofil `-O` with
  reference checks and with `--checks=half` must agree on stdout, exit
  status and the whole stderr (addresses masked), and the half build must
  have fewer null tests than renewal alone. `half-past` (upper, past the
  end), `half-below` (lower, below the start), `half-wrap` (lower, 2^50
  bytes below, wrapping past 0), `half-free` (lower after a free in the
  loop), `half-free-upper` (upper after a free), `half-readonly` and
  `half-readonly-lower` (a write to read-only data). progtest also runs
  them against filcc. half-below compares with filcc `-O0`: at `-O1` and
  `-O2`, filcc's own lower-only check of p[-2] reaches the fail function
  with a pointer whose state it finds valid, and filcc panics ("Should
  not be reached") instead of reporting.
- nix/check.nix runs difftest, ABI+GC and progtest under half with and
  without `-O`, and the corpus under `-O`. The hello, zlib, bzip2, lz4,
  Lua and SQLite checks build a half variant that must match filcc.

Plants, each caught and then restored:

| Planted mistake | Caught by |
|---|---|
| validator: `upper` ignores E, or `lower` ignores F | unit (`half_validation`, `half_semantics`) |
| validator: D not reduced modulo 2^64 | unit (two adds of 2^63 − 4) |
| validator: neither reduced nor near_offset | unit |
| validator: no near_offset | unit (E below −2^62) |
| validator: any pointer at distance 0 | unit (another lower donor) |
| validator: a half check is not a source | unit |
| interpreter: no one-sided test (the check's result always) | unit (`half_semantics`) |
| interpreter: the lower test unsigned | unit (p − 2^40) |
| interpreter: `lower` ignores free | unit |
| pass: ignores dominance | unit (`half_pass`, validator rejects) |
| pass: sides swapped | unit (validator rejects) |
| emitter: the lower test unsigned (`jb`) | half_smt.py, renew-trap (`half-wrap`) |
| emitter: `lower` without the free flag | half_smt.py, renew-trap (`half-free`) |
| emitter: `lower` tests FREE only for a write | renew-trap (`half-readonly-lower`) |
| emitter: `upper` without the read-only test | renew-trap (`half-readonly`) |
| emitter: `upper` without its own upper test | renew-trap (`half-past`, `half-free-upper`) |
| emitter: half_check missing from `inst_check_kind` | renew-trap (link error) |
| emitter: half proofs not in `single_proofs` | unit (a renew of a half check's proof) |
| emitter: half proofs not in the block's proofs | unit (a reuse with Q defined twice) |
