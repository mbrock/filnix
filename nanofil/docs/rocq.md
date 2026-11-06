# Campaign 1, first milestone: the core model in Rocq

November 2026. This note reports on Campaign 1 of [formal.md](formal.md),
which builds on [campaign.md](campaign.md): what exists, the decisions
taken, what the transcription clarified, and what is left. The
development is in [rocq/](../rocq/) and is checked by
`nix build .#checks.x86_64-linux.nanofil-rocq`.

## What exists

A Rocq 9.1 development, built with the Rocq and stdlib of the flake's
pinned nixpkgs. It contains no `Admitted`, no `Axiom` and no `Parameter`,
and the Nix check fails if any appears. Each file is a transcription of
the interpreter and cites the predicate it copies.

| File | Transcribes | Contents |
| --- | --- | --- |
| `Term.v` | ground Prolog terms | names (temporaries, labels, symbols) as terms compared by `==` |
| `Syntax.v` | ir.pl's header tables | classes, ops, values, instructions, jumps, blocks, functions, data, modules; `op_arg_classes/4`, `evidence_preserving/1`, `ahead_transparent/1`, `local_objects/2` |
| `Values.v` | interp.pl's values | `cap` (`none`, `obj`, `ro`, `fn`, `ext`), `ptr`, `word`; `word_at_class/3` |
| `Memory.v` | interp.pl's Memory section | regions, `mem`, `cap_access_res/7`, `free_res/4`, bytes and aux, `fresh` |
| `Ops.v` | `alu/4`, `additive_res/4`, `kind_res/8` | integer ops, `check` and the reuse vocabulary, raw loads, pointer-load and pointer-store protocols |
| `Semantics.v` | `run/5`'s blocks, instructions, jumps, calls | the configuration, `step`, `step_rel`, `reachable` |
| `Run.v` | `initial_memory/4`, `alloc_base/6` | module preparation, the interpreter's allocator as one fresh choice, a driver |
| `Transport.v` | — | decoding a printed checked module, encoding outcomes, `judge` |
| `Extract.v`, `extraction/main.ml` | — | OCaml extraction, and a reader of Prolog terms |

Covered: filc mode, the checked stage, classes `w`, `l`, `p`, `a` and
`f`; `check`, `check_ahead` (with the doomed state of
[schedule.md](schedule.md)), `renew`, `renew_hull`, `half_check`,
`span_test` with `renew_if`, `limit` with `check_limit`, `check_local`
and named locals, `check_function` with `raw_call` (including the
generic entry's argument and result conversions), `raw_load`,
`raw_load_pointer`, `raw_store`, `raw_store_pointer` with their effect
lists, `flight`, poll edges, direct `call`, and libc `free`. A function
that uses anything else decodes to `IOutside`. It keeps its address and
its `fn` capability, but running or calling it is stuck, and the
comparison reports such a run as `outside`.

Not yet done: the validator `valid` and its gate against
`ir:valid_module/1`. This is the larger half of Campaign 1.

## The gate

`nanofil outcomes FILE` (main.pl, a new command) prints the checked
module that `difftest` would compare, then `interp:run/5`'s outcome on
each run line, as terms. [rocq/agree.sh](../rocq/agree.sh) pipes that
output into the extracted model. The model decodes the module, runs
every line, and prints `agree`, `disagree`, `outside` or `stuck_both`
for each; the script fails on any disagreement.

The Nix check runs `rocq/tests/*.ir` once with the reference checks.
It then runs `tests/filc/*.ir` and `tests/c/*.c` with and without `-O`,
under each of the twelve `--checks` modes.

| Corpus | Lines that agree | Outside the subset | Disagree |
| --- | --- | --- | --- |
| filc fixtures and C tests, without `-O` (each `--checks` mode) | 447 | 41 | 0 |
| the same with `-O` | 449 | 39 | 0 |
| `rocq/tests/reuse.ir` (`renew_if`, `renew_hull`, each with and without a free) | 4 | 0 | 0 |

The lines outside the subset are floats, `long double`, variadics and
float structs.

The gate can fail. I planted three bugs, each found by the gate and then
reverted:

- A freed renewal returned `unchecked(span)` instead of the check's
  trap. Two lines of `reuse.ir` disagreed.
- The null test came after the bounds test. `forged` and `nullread`
  in basic.ir disagreed.
- `sar` was computed as `shr`. `immediate_shiftw` disagreed.

Gaps in coverage: pizlonate's output never contains `renew_if` or
`renew_hull` in the corpus. `reuse.ir` covers them by hand, so it runs
only with the reference checks, because the check passes take only
pizlonate's output. A `--checks=schedule` run over it is rejected by
the validator, which is the expected result for input outside a pass's
precondition, not a finding.

## Decisions

These are formal.md's early decisions as they turned out in the code:

- **Small-step with an explicit configuration.** A configuration is the
  running frame, the suspended callers (each with how it reads its
  callee's result), memory and fuel. A frame is either about to enter a
  block (`Enter l from`) or partway through one (`Exec l insts jump`).
  Entering a block costs one unit of fuel, as `block_outcome/7` does,
  so the model's `OutOfFuel` comes at the same point as the
  interpreter's. `step` is a function returning `Next`, `Done`, `Fresh`
  or `Stuck`; `step_rel` is the relation built on it.
- **Values are a sum over classes.** `WInt`, `WPtr` and `WLimit`
  (the opaque snapshot from `limit`). Classes are checked by the
  operations that read a word, not by its type.
- **Fresh allocation is nondeterministic.** Next is not part of the
  memory. `alloc` and `local_alloc` step to `Fresh q k`, and `step_rel`
  takes any base `fresh` for q: positive, aligned, the identity of no
  region (live or freed), overlapping no region's current bounds, and
  zero with no stored capability. The interpreter's monotone Next is
  `Run.v`'s `interp_alloc`, used only by the extracted driver.
- **Externals are stuck.** A call to a symbol the module does not
  define is stuck, except `void free(p)`, which the interpreter models.
  So is an access through an `ext` capability. The same holds for every
  place where the interpreter throws: a temporary read before it is
  assigned, an unregistered capability base.
- **Transport is part of the model's trusted base for the gate.**
  Prolog prints canonical terms; the model decodes them itself. A
  decoding error would show as a disagreement or as `bad_line`, never as
  a silent agreement, because `judge` compares the model's encoded
  outcome with the interpreter's term by `==`.

## What the transcription made clearer

- **The interpreter's run state mixes two things.** Its `hidden(doomed)`
  and `hidden(va_snapshot)` are keys in the environment of temporaries.
  In the model the doomed state is a field of the frame, which makes
  `check_ahead`'s contract visible: once doomed, a run ends at the first
  instruction that is not `ahead_transparent/1`, at a return, at
  `unreachable` or at a poll edge, unless an access in between fails.
- **An integer at class `p` is a real case.** `class_arg/2` accepts a
  plain integer for a `p` argument, so the model's words must allow it.
  `free_res/4` treats it as a pointer with no capability, and
  `generic_word` reads its address. This is a defaulty case at the
  interface, and Campaign 3's well-classedness invariant will have to
  exclude it or state it.
- **`ub` cannot occur in the core subset.** Fil-C's total division
  makes integer arithmetic defined everywhere, so the only sources of
  `ub(Why)` are float conversions and plain mode.
- **Phis read the entry environment.** `phis_env/6` binds every phi
  from the environment as it was on entry, which the model states by
  passing the old environment explicitly.
- **`renew_res/4` asks only about `obj`.** It answers "freed, so it
  traps" for an `obj(Base)` capability only. A renewal of read-only
  object that fails for another reason is `unchecked(span)`, even if
  the object was freed. `object_free_res` does free a read-only heap
  object, and the variadic snapshot (`args_snapshot`) is one. A renew
  through a freed snapshot would therefore be reported as a broken pass
  instead of the reference check's `trap(out_of_bounds)`. This is
  outside the core subset (`va_arg`), so it has no fixture yet; it is
  the first candidate for one when variadics come in, and Campaign 3's
  renew lemma must state which objects can be freed.

## Disagreements

None so far. No fixture was needed, and the Prolog has not yet been
contradicted. Making the comparison work needed two changes on the
OCaml side, neither of them semantic: a gas limit in the driver that
was too small for loops (now 2^60 steps, so the run's own fuel always
ends a run first), and atoms containing UTF-8 bytes in a reader.

## Next

1. `valid : module -> bool`, transcribing `ir:valid_module/1` for the
   checked stage: coverage, evidence persistence and each reuse rule's
   side conditions. Then the gate against the validator over the
   snapshot corpus, with and without `-O` and under every `--checks`
   mode.
2. A larger corpus for the outcome gate: `gen.pl` modules pizlonated,
   and the Lua test suite once its functions fit the subset.
3. The Campaign 2 `Module Type Runtime`: `fresh` and the lifetime facts
   of `Memory.v` are the first candidates to move into it.

Inquiries touched: none closed. The integer-at-`p` case is a small
input to the integer-to-pointer inquiry.
