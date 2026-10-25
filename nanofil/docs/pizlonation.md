# Pizlonation: Fil-C's checks in the IR

Until October 2026 the Fil-C access check existed twice and unconnected:
`filc_amd64.pl` emitted it inside every `load(T)` and `store` at a p
address, and `interp.pl` gave that same load and store a trapping
meaning. Now the check is a term of the IR. `src/pizlonate.pl` (named
after Fil-C's LLVM pass, FilPizlonator) turns the unchecked IR that the
frontend and middle end write into the checked IR the Fil-C backend
compiles, and `ir.pl` states the rules that make a check cover an
access.

## The checked stage

```prolog
let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P])  % P any p value
let(tmp(D), K, raw_load(T, Off), [tmp(Q)])         % raw load
raw_store(W, Off, V, tmp(Q))                       % raw store
let(tmp(F), f, check_function, [P])                % proven function target
raw_call(Res, tmp(F), Args)                        % call that target
goto(poll(L)), branch(V, poll(L1), L2)             % pollcheck on the edge
```

- A check traps unless P's capability permits Rights (`read` or `write`)
  on `[P+Lo, P+Hi)` and `P+Lo` is Align-aligned. Its result, of class
  `a`, is P: a *proven address*. Class `a` lives only in a register: it
  is never a parameter, phi, call argument or result, never in memory.
- A raw access reads a proven address. Which check covers it is
  structural: its address operand's definition. The validator requires
  `Lo =< Off`, `Off + Size =< Hi`, the access's alignment
  (`access_size_align/3`) dividing Align and `Off - Lo`, and write rights
  for a store.
- In the interpreter a raw access that its capability does not allow
  gives the outcome `unchecked(Why)`: neither ub (which would allow any
  outcome) nor a trap. Only a broken pass produces it, so a missing or
  too weak check shows up as a mismatch.
- `poll(L)` is a pollcheck on the edge, after the phis' copies, then L.
  Every cycle of the CFG must have a poll edge. Calls do not count: the
  callee need not poll.
- The stage is told by vocabulary (`ir:module_stage/2`): a module with
  any check, raw access or poll edge is checked, and then may contain no
  `load(T)` or `store` at a p address.
- `raw_load(T, Off)` reuses the load-type vocabulary of `load(T)` rather
  than a separate width and extension; retiring `load(T)`'s mixed form would
  change both at once.
- A function check requires a function capability and the exact callable
  address (the object's aux pointer), not merely an aligned address or
  an address within an object. It produces class `f`, distinct from a
  memory proof. Like class `a`, it is only a check result, never a
  parameter, phi, argument, stored value or call result. Its only use is
  the immediately following `raw_call`.
- `raw_call` discharges **target validity**, not signature compatibility.
  It still dispatches through the fast or generic convention, checks
  argument and result sizes, and propagates exceptions. An invalid raw
  target gives `unchecked(not_a_function)`; an ABI failure or a callee's
  trap remains a trap, even if that trap is itself `not_a_function`.
  The interpreter's `function_check_res/3` states the target rule once
  for ordinary indirect calls, checks and raw calls. External symbols
  remain explicitly uninterpretable, not assumed callable.
- Checked modules cannot contain ordinary indirect `call` instructions.
  Direct `call(..., global(F), ...)` remains; the external thunk's
  getter and function check are still ABI machinery in the backend.

Every module, in either stage, also obeys a new rule: each use of a
temporary in a reachable block is dominated by one of its definitions
(`definitions_dominate/3`). All 308 frontend modules of the snapshot
corpus, with and without `-O`, were already strict SSA; two hand-written
fixtures (`copy.ir`'s `redefined`, `memory.ir`'s `twice`) define a
temporary twice in a dominating position, which the rule allows.

## Why a proof dies at a safepoint, and what one is

A check reads the object's header; `free` sets `upper = lower` and the
FREE flag (`free_impl`, filc_runtime.c:3172). So a check is good until
something may free the object: on this thread, a call, a signal handler
at a pollcheck, or the runtime when the thread exits; other threads'
frees are the race Fil-C tolerates (the object keeps what accesses need,
filc_runtime.h:175). Memory is not reclaimed while a frame slot holds
the base pointer's lower: frames are marked with plain `marker.mark`
(filc_runtime_inlines.h:459), not `fugc_mark_or_free_flight`, which
redirects heap references to freed objects (fugc.h:162-170).

Safepoints: every call (including `free`, external and indirect calls),
pollchecks, `alloc` (`filc_allocate` exits for large sizes), setjmp,
va_arg and a symbol's getter (conservatively), and a pointer store
itself: `filc_object_ensure_aux_ptr_outline` can exit, zeroing a large
aux between `filc_exit` and `filc_enter` (filc_runtime.c:2575-2590), and
`filc_exit` runs deferred signal handlers and the collector's handshake
(filc_runtime.c:1231-1266). `filc_store_barrier_for_lower_slow` does not
exit. The stack-overflow check and the check-failure blocks never
return.

A pointer store is therefore check, ensure-aux (may exit), store, with
no recheck; the backend reloads the pointer from its rooted slot after
ensure-aux. That is sound for the reasons above and is what
FilPizlonator does too (EnsureAuxPtr erases only later accesses' facts,
FilPizlonator.cpp:5821-5827).

For now each check is followed immediately by its only use, so no
safepoint can come between them; the IR says so (`checked_insts/3`) and
the backend fuses the pair (`fused_blocks/4`) into one instruction at one
index, so local labels and frame slots number instructions as before
and the assembly is byte-identical.

## Gates

- `tests/snapshot.sh`: every output identical. `cc-ir` prints the
  unchecked IR; `cc` and `compile` (filc) pizlonate, validate the
  result, and emit.
- `difftest` on a filc module also runs the pizlonated module on every
  run line and requires the same outcome, traps and their reasons
  included (`mode_pizlonation_agrees/4` in main.pl). Planting an
  over-broad check (twice the access size) made three runs of
  `tests/filc/basic.ir` fail it.
- `tests/unit.pl`: `pizlonate_states_every_check` deletes a check and
  sees `unchecked(out_of_bounds)` where the original trapped, and the
  validator reject the mutant; `checked_ir_rules` rejects a too weak
  check, a call between a check and its access, and a loop without a
  poll; `definitions_dominate_uses` rejects a use before its definition.

## Review

The design was reviewed by Oracle (October 2026) before adoption.
Its findings and what became of them:

1. Mode and stage were inferred from contents, so a p-free loop going to
   the Fil-C backend (promote can remove every p) would get poll edges
   in a plain module. Resolved: pizlonate runs whenever the Fil-C
   backend runs, poll edges are allowed in any module, and the backend
   itself rejects a cycle without a poll.
2. The validator must not accept what the backend cannot compile: a
   check with other instructions before its use (and P redefined in
   between) or an alignment `access_check//2` cannot test. Resolved: a
   check is immediately followed by its one use; the backend throws on
   `Lo =/= 0`, an offset access, or an alignment other than 1 or 8.
3. Dominance was unmeasured. Measured (above), and stated as "some
   definition dominates", skipping unreachable blocks and phi operands
   from unreachable predecessors.
4. `ub(unchecked(_))` would have meant "anything goes", the opposite of
   a pass bug. Resolved: the outcome `unchecked(Why)`.
5. `poll(L)` is unwrapped in one place, `cfg:edge_label/2`, which
   `ir.pl`, `interp.pl` and the backend read.
6. Fresh check temporaries are named `chkN`, which the IR text prints
   and reads.
7. Fusion happens before layout, so class-a temporaries get no slots
   and no setjmp payload words.

Oracle confirmed: the safepoint list is complete, nothing between a
check and its access but a pointer store's ensure-aux reaches one, and
the check and raw access share `cap_access_res/7`, so trap reasons and
their order are those of `access_check//2`.

### Function-target checks

The next increment was also reviewed before adoption. The review
approved `check_function`/`raw_call` with immediate consumption and
required that both proof classes be isolated from ordinary values and
both call forms' arguments/results. It also identified the backend's
failure-block selector: that now reads the explicit function-check term,
not the former bare indirect call.

Fusion keeps two views: `fused(check_function, call(Res, P, Args))` for
emission, and the original `call(Res, P, Args)` for layout/liveness.
Thus P, every argument and every result share the original closed
instruction interval; no `f` slot is allocated. Emission preserves the
origin store, return-buffer reservation, flight load, function check,
aux store and dispatch order. An ordinary indirect call is rejected,
not silently checked by the emitter. A check of a constant pointer is
also supported, even though the frontend's indirect calls use temps.

Tests cover exact function addresses (including offsets 1 and 8), null
and forged capabilities, target-vs-callee traps, argument/return-size
failures, external symbols, proof escape and immediate consumption.
Deleting a check and rewiring its raw call to the original pointer
exposes `unchecked(not_a_function)`; valid targets still run. The
tuple fixture covers indirect buffered returns through fast and generic
dispatch, with the second pointer result used through a phi and a
tuple-result name colliding with the first candidate proof name.
The new transformation test failed before implementation. Scratch
mutations also fail the tests: reporting a raw-target failure as a trap,
allowing `f` to be read as an integer, and accepting an aligned but
noncanonical function address. The snapshot's 1014 outputs, including
the extended fixtures, are identical to the preceding compiler's.

Additional native validation used mixed XMM/GPR arguments and stack
spills, buffered pointer-bearing returns, pointer results, forced GC
inside and after indirect callees, and an indirect returns-twice call
whose own indirect call longjmps. Both optimization levels returned
`64 29 64 29 37` under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`, matching filcc;
the old and new assembly was byte-identical, including frame and
setjmp payload layouts. This is a representation change, not a
check-elimination or rooting change.

## Cost

`valid_module` now computes dominators, and `cc` validates twice (the
frontend's module and the pizlonated one). On SWI this is about +10% on
c-testsuite 00200. On Trealla it is about +30% time and +1 GB peak memory
(00200, `cc`: 9.3 s, 2.66 GB before; about 12-13 s, 3.6 GB after; `-O
cc` 3.7 to 4.7 GB), nearly all in `cfg.pl`'s dominator computation.

## Deferred

- Explicit aux and barrier operations; until then `raw_load(p, _)` and
  `raw_store(p, ...)` keep them inside, and `raw_store(p, ...)` is itself
  a safepoint.
- Address/lower decomposition, frame construction and fast/generic ABI
  lowering before AMD64 emission. Explicit check terms alone do not
  complete that separation; the roadmap is in [campaign.md](campaign.md).
- Merging and removing checks, and removing redundant pollchecks. This
  needs a model of `free` in the interpreter first (today regions never
  die in filc mode, so a check that spans a call cannot fail there) and
  FilPizlonator's split between stable facts (bounds, rights,
  alignment) and volatile ones (not freed, aux pointer). Moving a check
  earlier is a refinement only when every access it covers is sure to
  execute and no safepoint comes between. Hoisting out of loops is
  mostly impossible, since every loop polls.
- Class-a values across instructions, and `Lo =/= 0` in the backend.
