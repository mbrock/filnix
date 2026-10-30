# Full-width vector access checks (V1): contract (reviewed, implemented)

The frontend lowers GCC/clang vector types to scalar IR, in 8-byte
chunks (element-sized for float elements). filcc checks a 16-, 32- or
64-byte vector access as one access, with its alignment requirement
capped at 8: a misaligned `_mm_load_si128` reports "alignment requirement
of 8 bytes not met", and `_mm_storeu_si128` one byte short reports
"cannot write 16 bytes when upper - ptr = 15" with nothing written. To
keep that observation, nanofil needs one check of the full width before
any chunk is accessed. This is a check-shape change, so it comes as a
contract and an Oracle review before code, like B1 and M7's rounds.

## The terms

Unchecked IR gains one statement:

| Term | Meaning |
| --- | --- |
| `access(K, Addr, Size, Align)` | traps exactly as a K access of Size bytes at Addr with alignment Align would, and accesses nothing |

- K is `read` or `write`.
- Addr is a pointer operand: class `p` in a Fil-C module, the address
  class in a plain one.
- Size is a constant 16, 32 or 64; Align a constant 1, 2, 4 or 8.

The frontend emits it immediately before the chunked loads or stores it
covers, which are ordinary `l` (or `s`/`d`) accesses at Addr, Addr+8,
and so on.

Checked IR gains one statement:

| Term | Meaning |
| --- | --- |
| `touch(tmp(Q))` | consumes the proof Q and does nothing else |

pizlonate turns `access(K, A, Size, Align)` into

    let(tmp(Q), a, check(0, Size, K, Align), [A]),
    touch(tmp(Q))

so the invariant that each check is immediately followed by its one use
(docs/pizlonation.md) is unchanged. Validator rules:
- `touch(tmp(Q))` is accepted only as the instruction right after the
  `check`, `renew` or `renew_if` that defines Q, handled in those three
  clauses directly (it has no raw-access shape for `covered_access`),
  and never reads a reused proof;
- it is rejected anywhere else, including after `check_local` or
  `check_function`, and in unchecked IR; `checked_inst(touch(_))` holds;
- `access` (and an unfused `touch`, so emission names the problem) is
  in `filc_amd64:unchecked_access`; `access` is in `ir:unchecked_access`,
  so a Fil-C checked module that still has one is rejected: a pizlonate
  that forgot the term fails closed instead of compiling the full-width
  check to nothing (pizlonate passes unknown instructions through).

The chunk accesses after it are pizlonated as they are today: each gets
its own check. On one thread nothing between the full check and a chunk
can make a chunk check fail: pizlonate polls only on back edges, no pass
inserts calls, integer stores never ensure aux, and signals wait for
safepoints. So the reference path's single-threaded observation is
filcc's: the full-width trap, before any chunk, or none.

**A tolerated race.** Another thread's `free` (or `munmap`) landing
between the full check and chunk k makes chunk k's check trap after
chunks 0..k−1 are written. filcc cannot produce that: its one check
passed, and `free` only sets `upper = lower` and the free flag, leaving
the payload for exactly such races (filc_runtime.h 169–177, filc_runtime.c
3172–3194), so its single vector access completes without a trap. This
*adds* a trap after partial effects, which M7's contract ("no trap is
added or moved earlier") does not cover, so it is tolerated on its own
terms: the trap is a correct Fil-C trap on a freed object, the program
races on the object's lifetime, and filcc shows the same partial-then-
trap behaviour for any access it splits, such as a struct copy. It is
observable in two ways: a `munmap` of a `MAP_SHARED` mapping can leave a
torn record in the file (chunks 0..k−1 written, then the range remapped,
filc_runtime.c 9948–9976), and a thread that passed its own check before
the free can read the partial payload. The alternative is to have the
chunks read Q: reuse already rewires them when the chunk address is
`A + const` of single-definition temps, so under `renew` (the `-O`
default) and `guard` the race is already gone for well-shaped chunks,
and the same rewiring could run for `access` pairs on the reference
path. V1 keeps the reference path's per-chunk checks.

An alternative is to drop `touch` and let the first chunk access consume
the full-width check (a 16-byte check covers an 8-byte raw access at
offset 0). It needs no new term, but pizlonate would have to pair
`access` with the next instruction, which then depends on the
frontend's emission order. `touch` keeps the pairing local.

## Semantics

- **Interpreter, Fil-C mode, unchecked stage:** `access_res(Mem, A, Cap,
  Size, K, Align, Res)`, the relation every scalar access uses; a trap
  stops the run with its reason, ok continues with memory unchanged.
- **Interpreter, checked stage:** the check runs as any check; `touch`
  continues.
- **Interpreter, plain mode:** a no-op. C's semantics are the chunked
  accesses' (an out-of-bounds chunk is ub there as it is without the
  term).
- **Emission:** `fused(check(0, Size, K, Align), touch(P))` is the
  check's lines (`flight_load`, `access_check(k(Size, Write, Align))`)
  and nothing after them: `proven_access`, `access_pointer/3` at offset
  0, and a `raw_access//4` clause that emits nothing. filc_amd64 has no
  `inst` clause for `access`. `borrow_check` keeps its borrow test for
  32 and 64 bytes (it drops it only at 16 or less), and the fused,
  renewed and guarded forms already accept any Align in {1,2,4,8}. The failure reporter is the shared one for
  `k(Size, Write, Align)`, so the reason text is the check's: "cannot
  read 16 bytes when upper - ptr = 15", the read-only, freed, null,
  below-start and alignment forms. Its origin is the access's.
- **Plain backend:** `amd64.pl` emits nothing for `access`.
- **Align** is filcc's: `MinAlign(ABI, instruction alignment)`, capped
  at 8 (FilPizlonator.cpp 4198, 4251–4261). The frontend passes
  `min(ABI, access align, 8)`, so 1 for `_mm_loadu_si128`. Size is the
  store size (16 for a `float3` ext-vector), not the bytes the chunks
  cover.
- **Reasons.** nanofil's check origin is `long(Size), byte([Align, 0,
  Write])`, filcc's Size, Alignment, AlignmentOffset, NeedsWrite, and
  both report through `filc_optimized_access_check_fail`, which derives
  the text (null, free, ptr < lower, ptr >= upper, size > upper − ptr,
  read-only, alignment) from the pointer and the origin. So the texts
  match; a vector at exactly `upper` reports the ptr >= upper text.

## Trap order and text

The full-width check comes first, so a vector access that would run past
the end traps before any chunk is written, with filcc's size in the
reason. A constant offset is not folded into the base; that matches
nanofil's scalar accesses, not filcc at `-O1` (which reports "cannot
write 33 bytes when upper - ptr = 32" for b+17 on a 32-byte object, as it
reports "25 bytes" for a long at b+25). That difference is pre-existing
and out of scope here.

## Pointer slots

A vector store is a run of integer (or float) chunk stores. In Fil-C an
integer or float store writes only the payload and leaves an existing
capability in the aux word alone (`storeValueRecurseAfterCheck`,
docs/abi-findings.md); the interpreter does the same (`width_word`,
`stored_aux(none, ...)`), and so does the emitter. So a vector store
over pointer slots keeps their capabilities, as filcc's does, and a
vector load of pointer slots reads their address words only.

## Middle end

`access` has no result and must not be removed or reordered:
- simplify removes only pure `let`s, so it stays;
- no pass moves memory accesses today; `access` must stay in program
  order with the chunks after it, as `fence` and `asm_fixed` do;
- `escape:inst_event`: an access to an alloc's address is an escape
  (`esc(access)`), so promotion and local storage leave the object
  alone in V1. Promoting it would need the static bounds to discharge
  the trap, which is later work;
- `access` needs clauses in `cfg:inst_uses` (no fallback),
  `simplify:inst_subst` and `operand_temp`, `copy:inst_reps`,
  `escape:inst_event`, `ir:valid_inst` and `unchecked_access`, interp
  `inst_result`, pizlonate, `amd64` `inst//2` and
  `filc_amd64:unchecked_access`. `promote:inst_renamed`,
  `inline:renamed_temps`, `filc_abi:lower_inst` and local_storage's
  default are already right; it defines nothing.
- `touch` needs clauses in `ir` (`checked_inst`, the check, renew and
  renew_if clauses, the catch-all's rejection, `evidence_preserving`),
  `cfg:inst_uses` (fail-open otherwise: `live_inst` unwraps the fused
  pair, and without the use P's slot could be shared before the
  check's `flight_load`), `filc_amd64` (above), `check_reuse` (below)
  and interp `inst_result`.
- Float chunks already escape (`load_width` has no `s` or `d`), so the
  cost of `esc(access)` falls on integer vector locals. Later,
  local_storage could lower a constant-offset `access` to `check_local`
  and `touch`.

## Reuse, renew and guard

The M7 passes match a check followed by a scalar access, so they need
these clauses for `touch`; without them it is opaque, which would be
sound but would wipe every fact in the block (`state_none`), slowing
the `-O` default (renew) around every vector access:
- `ir:evidence_preserving(touch(_))` and
  `check_reuse:transparent(touch(_))`: it accesses nothing and cannot
  exit.
- **As a source.** In `reused_insts`, a check followed by `touch` keeps
  both and adds the check's fact, [0, Size) of A with K's rights and
  Align. Reuse relates a chunk address `flight(add, [address(A),
  const(8)], lower(A))` to A when both have one definition
  (`flight_offset`, `base_of`, `related`), so under `--checks=reuse`,
  `renew` and `guard` a chunk at A+8, A+16, ... reads Q at its offset
  and its own check goes. Renew relates only equal offsets
  (`same_pointer`), so only the chunk at offset 0 can be renewed from
  the full check.
- **As a target.** V1 does not reuse, renew or guard the full-width
  check itself; it stays a full check. (Reuse would delete the pair when
  a live fact covers [0, Size); renew would need `renewable_access(touch
  ...)`. Both are later work, and `subsumes` already keeps a 16-byte
  fact from standing for a 32-byte check.)

## Known differences from filcc

- **Split access under a racing free (accepted by the orchestrator,
  October 2026).** A `free` or `munmap` by another thread between the
  full-width check and chunk k traps at chunk k's check after chunks
  0..k−1 are written; filcc's single vector access completes without a
  trap. This is the same as filcc's own behaviour for any access it
  splits, such as a struct copy. It is observable only under a race on
  the object's lifetime: as a torn record in a `MAP_SHARED` file, or as
  a partial payload read by a thread that passed its own check before
  the free. Under `-O` (renew) and `--checks=guard`, reuse rewires
  well-shaped chunks to the full check, which removes it; the reference
  path keeps a check per chunk.
- **Constant offsets are not folded into the base.** filcc at `-O1`
  reports `b+17` on a 32-byte object as "cannot write 33 bytes when
  upper - ptr = 32"; nanofil reports the vector's own size, as it does
  for scalar accesses. Pre-existing, not specific to vectors.

## Tests and plants (planned)

- **Unit, validator:** accepts every K, Size and Align and rejects
  others (Size 8 or 24, Align 16, a non-constant); rejects `touch` in
  unchecked IR, with no check before it, after `check_local` or
  `check_function`, or as a second use; rejects `access` in a Fil-C
  checked module.
- **Unit, nothing written before the trap:** the interpreter runs an
  `access` of 16 bytes one byte short of an object's end, followed by
  two chunk stores, on the unchecked and the pizlonated module, to
  `stop(trap(_), s(Mem, _))`, and the object's bytes are unchanged.
  (Its reasons are coarse, so the texts are native tests.)
- **Unit, frontend order:** C to IR puts `access` before the first chunk
  of every vector load and store (with the frontend thread).
- **Unit, pizlonate:** the output has the check and `touch` right before
  the first chunk's check; with `--checks=reuse`, through
  `checks_module` and `valid_module`, the chunk at offset 8 reads Q at
  offset 8 and has no check of its own (asserting the rewiring
  happened).
- **Unit, liveness:** `inst_uses(touch(tmp(x)), [x])`, and P is live
  into a fused check and `touch` when nothing after uses it.
- **Unit, passes:** copy, promote, inline, simplify and local_storage
  keep every `access`; an `access` on an alloc keeps the alloc
  (`esc(access)`).
- **Native, against filcc** (the frontend's prog tests): every measured
  reason for loads and stores; a fork whose child does a 16-byte store
  one byte short of the end of a `MAP_SHARED` page and whose parent
  checks that the child died of a Fil-C panic and the page is unchanged;
  a vector at exactly the end (ptr >= upper); a vector store that
  writes a different in-bounds address over pointer slots, followed by a
  dereference, compared with filcc. Under `FUGC_SCRIBBLE`/`FUGC_VERIFY`,
  and with `--checks=reference`, `reuse`, `renew` and `guard`.
- **Plants**, each to be caught:
  1. pizlonate leaves `access` in place (validator);
  2. the check after the first chunk (the partial-write unit test);
  3. Size from the chunk (native text);
  4. Align not capped (native alignment case);
  5. a stray `touch` accepted in the catch-all (validator unit);
  6. no `cfg:inst_uses(touch)` (the liveness unit test);
  7. no `escape` clause (unit);
  8. `touch` not evidence-preserving, or not transparent (the reuse
     unit test, through validation, asserting the rewiring);
  9. the interpreter's `access` writing memory (the partial-write test);
  10. a pass dropping `access` (passes unit).

## Review

Oracle reviewed the first draft: the term pair is the right shape and
`touch` beats having the first chunk consume the check, but it found
that `touch` was invisible to M7 (opaque, wiping facts), that a missing
pizlonate clause failed open through a filc_amd64 `inst` clause, that
the planned partial-write test could not fail, that "the chunk checks
cannot fail" is false under a racing free, and that renew relates only
equal offsets. All are folded in above. Its second round found the
blockers resolved, corrected the race paragraph (an added trap, not the
converse of M7's lost one, and observable through `munmap` and other
threads' reads) and replaced two vacuous tests; folded in too.

## As built

The IR side follows the contract. `ir:proof_use/6` is the one place a
check, renew or renew_if accepts what follows it: a covered heap raw
access or a `touch` of its own proof. `check_reuse` keeps a check and
its `touch` and adds their fact, so under `--checks=reuse`, `renew` (the
`-O` default) and `guard` the chunks read the full-width proof at their
offsets with no checks of their own; the full-width check is never a
reuse or renew target in V1.

Tests (`tests/unit.pl`):
- `vector_access_validation`: every K, Size and Align; bad ones refused;
  pizlonate's check and `touch`; `access` in checked IR, a second
  `touch`, a `touch` after an access, of another live proof, after a
  check of another proof, or after a local check, refused; `inst_uses`
  of both; `access` does nothing in a plain module.
- `vector_access_no_partial_write`: a 16-byte store whose first chunk is
  in bounds and second is not leaves memory exactly as the `access`
  alone does, unchecked and pizlonated.
- `vector_access_reuse`: through `reuse_refines` and `valid_module`, the
  chunks read the full-width proof at offsets 0 and 8.
- `vector_access_kept`: `-O` with inlining and simplify keeps `access`
  and its object on the heap, while a dead `let` goes.

Natively, the frontend's `tests/c/prog/vector-access.c` matches filcc
under `--checks=reference`, `reuse`, `renew` and `guard`, with and
without `-O`, and with `--registers=temps`, under
`FUGC_SCRIBBLE`/`FUGC_VERIFY`: every reason for loads and stores, ptr >=
upper, pointer slots keeping their capabilities, and `MAP_SHARED` pages
unchanged after the trap. Its freed cases call `free` through an opaque
pointer: clang `-O1` folds a direct free then access into "cannot access
pointer to free object", for scalars too (pre-existing, like offset
folding).

Plants (unit = the unit tests; native = vector-access.c, plain and `-O`):

| Plant | Caught by |
| --- | --- |
| 1. pizlonate leaves `access` in place | unit, native |
| 2. pizlonate drops the full-width check | unit (partial write), native |
| 3. Size taken from the chunk | unit, native |
| 4. Align dropped to 1 | unit, native |
| 5. a stray `touch` accepted | unit |
| 5b. a `touch` of another proof accepted | unit |
| 6. no `cfg:inst_uses(touch)` | unit, native |
| 7. no escape clause | unit, native `-O` |
| 8. `touch` not evidence-preserving | unit (reuse), native `-O` |
| 8b. check+touch not a reuse source | unit (reuse) |
| 9. the interpreter's `access` a no-op in Fil-C | unit (partial write) |
| 10. simplify drops `access` | unit (kept) |
| 11. reuse lets a narrower fact cover a wider check | existing reuse and renew unit tests, native `-O` |
| 12. the interpreter's `access` ignores K and Align | unit (misaligned and read-only cases) |
| 14. `copy:inst_reps` does not substitute in `access` | unit (kept), native `-O` |
| 17. no plain-backend clause | unit (plain module emitted) |
| 18. `valid_inst(access)` takes any address class | unit (an `l` address refused) |

Oracle reviewed the implementation and found no blocker; 12–18 are its
plants, and its should-fixes (the tests above, the escape clause's
place) are folded in. Equivalent mutants that pass: simplify not
substituting into `access`, or not counting its operand (simplify turns
a numbered duplicate into a copy, which the copy propagation it runs
afterwards rewrites everywhere, and its use counts serve only boolean
rewrites); `transparent(touch)` and the `unchecked_access` entries in
filc_amd64, which valid IR never reaches (the reuse clause consumes check
and `touch` together; the validator runs first). The frontend accepts
only 16-byte vectors today, so the 32- and 64-byte sizes are covered by
unit tests, not natively.
