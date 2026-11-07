# Campaign 1: the core model in Rocq

November 2026. This note reports on Campaign 1 of [formal.md](formal.md),
which builds on [campaign.md](campaign.md): what exists, the decisions
taken, what the transcription clarified, and what is left. The
development is in `nanofil/rocq/` and is checked by
`nix build .#checks.x86_64-linux.nanofil-rocq`.

## What exists

A Rocq 9.1 development, built with the Rocq and stdlib of the flake's
pinned nixpkgs. It contains no `Admitted`, and no `Axiom` or `Parameter`
outside `Runtime.v`'s module type, which the interpreter's instance
discharges; the Nix check fails otherwise, and `Print Assumptions` of
`judge` is closed. Each file is a transcription of
the interpreter and cites the predicate it copies.

| File | Transcribes | Contents |
| --- | --- | --- |
| `Term.v` | ground Prolog terms | names (temporaries, labels, symbols) as terms compared by `==`, and `term_eqb_eq`, that `==` is equality; `char_code/2` |
| `Maps.v` | library(assoc) | name maps: a hash of the name, then an association list per hash, so a lookup's answer never depends on the hash |
| `Ieee.v` | ieee.pl | binary32, binary64 and x87 extended as bit patterns: `decode/4`, `round_ratio/5`, `ieee_binary/5`, `ieee_convert/4`, `ieee_compare/5`, `ieee_from_int/3`, `ieee_to_int/3` |
| `Syntax.v` | ir.pl's header tables | classes, ops, values, instructions, jumps, blocks, functions, data, modules; `op_arg_classes/4`, `evidence_preserving/1`, `ahead_transparent/1`, `local_objects/2` |
| `Values.v` | interp.pl's values | `cap` (`none`, `obj`, `ro`, `fn`, `ext`), `ptr`, `word`; `word_at_class/3` |
| `Memory.v` | interp.pl's Memory section | regions, `mem`, `cap_access_res/7`, `free_res/4`, bytes and aux, `fresh` |
| `Runtime.v` | `alloc_base/6`, `free_res/4`; [runtime-axioms.md](runtime-axioms.md) | Campaign 2's `Module Type Runtime`, seven axioms and two readiness obligations, and `InterpRuntime`, which proves them |
| `Ops.v` | `alu/4`, `additive_res/4`, `kind_res/8` | integer and float ops, `check` and the reuse vocabulary, raw loads and stores, pointer-load and pointer-store protocols, `va_arg` |
| `Semantics.v` | `run/5`'s blocks, instructions, jumps, calls | the configuration, `step`, `step_rel`, `reachable`; the variadic entry snapshot |
| `Run.v` | `initial_memory/4` | module preparation, and `Driver`, a run over any `Runtime`'s allocations and free |
| `Machine.v` | — (Campaign 3) | the machine of a `Runtime`: steps, the runtime's allocations, its actions at safepoints; `ready` kept by every step; each step a `step_rel` step or a safepoint action |
| `Cfg.v` | cfg.pl | `func_cfg/2`, `cfg_idoms/2` (Cooper, Harvey and Kennedy), `dom_children/3`, `dom_intervals/3`, `dominates_by_interval/3` |
| `Validate.v` | ir.pl's `valid_module/1` | `valid_func`, `valid_data`, `valid_alias`, `valid_items`, `valid`: uses, ops, instructions, dominance, locals, the evidence pass, the reuse rules, `polls_every_cycle`, data linkage and items, aliases |
| `Coverage.v` | — (Campaign 3) | the coverage lemma: a raw access that `covered_access/6` puts inside a passed check gives no `unchecked` |
| `Transport.v` | — | decoding a printed checked module, encoding outcomes, `judge`, `judge_valid` |
| `Extract.v`, `extraction/main.ml` | — | OCaml extraction, and a reader of Prolog terms |

Covered: filc mode, the checked stage, classes `w`, `l`, `p`, `a` and
`f`, and the float classes `s`, `d` and `x` with their arithmetic,
comparisons and conversions; `check`, `check_ahead` (with the doomed state of
[schedule.md](schedule.md)), `renew`, `renew_hull`, `half_check`,
`span_test` with `renew_if`, `limit` with `check_limit`, `check_local`
and named locals, `check_function` with `raw_call` (including the
generic entry's argument and result conversions), `raw_load`,
`raw_load_pointer`, `raw_store`, `raw_store_pointer` with their effect
lists, `flight`, poll edges, direct `call`, libc `free`, and variadic
functions (`va_args`, `va_arg`, the entry snapshot and the extra
arguments of a call through the generic entry). What is left out is
vectors, `store`, `cas` and atomics, `setjmp`, `asm_fixed` and `touch`.
A function that uses anything else decodes to `IOutside`. It keeps its address,
its `fn` capability and its term (so the validator can read its
signature and its calls), but running or calling it is stuck, and the
comparison reports such a run as `outside`.

The validator covers every item of a Fil-C module: functions in the
subset, data objects and aliases. `valid` is `None` for a module with a
function outside the subset. The `context(Name, Records)` items are not transcribed:
they are provenance's records, which `valid_contexts/1` checks and
`run/5` never reads, and the module the gates compare has none.

## Routine smoke check and opt-in campaign

Rocq is experimental work, not a reason to turn every edit into a long
release qualification. `checks.x86_64-linux.nanofil-rocq` is the quick
push check, targeted at 1–2 minutes: build/extract/link the model, run
`web/rocq/tests/parse.sh` on every theory, then compare outcomes and base
validator verdicts on `rocq/tests/*.ir`, `tests/filc/basic.ir`,
`tests/c/ldouble.c` and `tests/c/prog/alias.c`, with reference checks.
`NANOFIL_MUTANTS=0` selects `mutants.pl --base`: it generates no mutations,
only the unchanged items' whole-module verdicts. This is a smoke check,
not rejection coverage or a soundness proof.
In particular, `dominance.ir`'s one-sweep-idom and always-true-dominance
plants, and `interval.ir`'s same-index plant, are detected by their
mutant verdicts, not their unchanged base verdicts. They are covered only by the full campaign, not the routine
no-mutants smoke check. This tradeoff is deliberate; a dominance or
other soundness-relevant change calls for the opt-in evidence.

The fleet's default `--roots auto`, ship's evidence verifier and CI share
the change selector in `scripts/nanofil-fleet required-roots`. Model,
compiler/validator and gate-input changes need the quick root; unrelated
web styling, rendering and documentation edits skip it. Parser/grammar
changes still need parse.sh. Plain ship runs the relevant quick check;
exact-head ship reuses its receipt instead of rerunning it.

The complete outcome and mutation matrix described below is now
`checks.x86_64-linux.nanofil-rocq-full`. Run it deliberately before a
release or for a soundness-relevant change:

```sh
scripts/nanofil-fleet run --rev HEAD --shards 6 --roots auto,nanofil-rocq-full
```

Even `--roots all` excludes it. CI runs quick checks on relevant pushes
and pull requests; its manual `full` input selects the campaign. No
nightly campaign is enabled. `scripts/release --fleet-results FILE`
requires exact-head full-campaign evidence, not a quick receipt.

All jobs retain timestamped progress and budget warnings. Quick Rocq
warns at 120 seconds and fails at 300; the full fleet root warns at 600
and fails at 1800. A corpus file warns at 60 seconds and fails at 300.
Timeouts fail, never omit coverage. Independent outcome modes run in
parallel, as the validator modes already did. Lua's whole-module mutant
generation/judging uses independent item-index partitions after the
program cases finish; every changed module is still judged whole, and
inserted-item mutants occur only in partition zero. The union is checked
against the serial stream. Model inputs exclude fixtures/harnesses/docs;
the check excludes unrelated web/docs inputs. Outputs retain full logs
per mode/program, with file/mode/seconds progress visible through the fleet.

## The full outcome gate

`nanofil outcomes FILE` (main.pl, a new command) prints the checked
module that `difftest` would compare, then `interp:run/5`'s outcome on
each run line, as terms. [rocq/agree.sh](../rocq/agree.sh) pipes that
output into the extracted model. The model decodes the module, runs
every line, and prints `agree`, `disagree`, `outside` or `stuck_both`
for each; the script fails on any disagreement.

The full Nix campaign runs `rocq/tests/*.ir` once with the reference checks.
It then runs `tests/filc/*.ir`, `tests/c/*.c` and forty generated Fil-C
modules (`tests/gen.pl SEED 10 filc`, seeds 1 to 40) with and without
`-O`, under each of the twelve `--checks` modes. All forty generated
modules are Fil-C ones, and 1,291 of their 2,400 runs trap.

| Corpus | Lines that agree | Outside the subset | Disagree |
| --- | --- | --- | --- |
| filc fixtures and C tests, with and without `-O` (each `--checks` mode) | 488 | 0 | 0 |
| the gen modules, with and without `-O` (each mode) | 2,400 | 0 | 0 |
| Lua's own functions (`rocq/lua.sh`, with and without `-O`, each mode) | 27 | 0 | 0 |
| `rocq/tests/reuse.ir` (`renew_if`, `renew_hull`, each with and without a free) | 4 | 0 | 0 |
| `rocq/tests/snapshot.ir` (the variadic snapshot read, written, empty, freed) | 5 | 0 | 0 |
| `rocq/tests/floats.ir` (ties to even, a float read through the generic entry) | 3 | 0 | 0 |

Before floats and variadics came in, 41 lines without `-O` were
outside: floats, `long double`, variadics and float structs. None is
now.

The gate can fail. I planted three bugs in the integer model, and later
five in floats and variadics, each found by the gate and then
reverted:

- A freed renewal returned `unchecked(span)` instead of the check's
  trap. Two lines of `reuse.ir` disagreed.
- The null test came after the bounds test. `forged` and `nullread`
  in basic.ir disagreed.
- `sar` was computed as `shr`. `immediate_shiftw` disagreed.
- A `long double` `va_arg` cell aligned to 8, not 16: `variadic` in
  ldouble.c disagreed.
- The va_list cursor advanced by 8, not by the cell: the same.
- The snapshot's capability was `obj`, not `ro`: `snapshot_write`
  returned instead of trapping `readonly`.
- A variadic callee reached through the generic entry lost its extra
  arguments: `variadic_fixed_pointers` disagreed.
- Rounding broke ties upward, not to even: no corpus line noticed, so
  `rocq/tests/floats.ir` adds two ties, which then disagreed.

One planted bug is still not caught: `generic_word` keeping all 64 bits
of an integer word read as `s` or `d`, instead of its low bits. The
receiving function reads its parameter at its class, which takes the
low bits again (`value_x/5` calls `word_at_class/3`), and so does a
caller reading a result. The difference could show only through a
variadic callee with an `s` or `d` parameter reached through the
generic entry, whose snapshot stores the parameter word as passed; no
fixture has one yet.

The Lua test suite itself cannot run in the interpreter: Lua's
functions take a `lua_State` and call libc (allocation, strings,
`setjmp` for errors), which the interpreter does not model, and Lua's
tests run natively in `nix/lua.nix`. What the gate takes instead is
Lua's source in two ways. Lowered file by file, every one of Lua's
1,096 functions but one decodes into the subset; the one is
`luaD_rawrunprotected`, which calls `_setjmp`. And
[rocq/tests/lua.c](../rocq/tests/lua.c) includes lctype.c, lobject.c
and lstring.c, as Lua's onelua.c does, and runs the functions of theirs
that need neither a state nor libc on the path taken: integer and float
arithmetic (`luaO_rawarith`), integer numerals (`luaO_str2num`), the
string hash, UTF-8 escapes and `luaO_ceillog2`.
[rocq/lua.sh](../rocq/lua.sh) preprocesses it against the Lua source
`nix/lua.nix` builds, with the same flags.

Every reuse form is reached by the check passes over the corpus, but
the C tests reach `renew_hull` (6 times) and `renew_if` (9) rarely,
and seldom on a run that traps. So the `filc` mode of tests/gen.pl also draws a
memory loop whose shapes are the ones the passes
need: an access at a fixed offset in a loop with a call (the guard
pass makes it `span_test` and `renew_if`), an access at an offset that
grows with the trip count (the hoist pass makes it `limit` and
`check_limit`), and after the loop two loads 8 bytes apart, a call and
a load between them (the hull pass makes it `renew_hull`). The call is
sometimes libc `free` of the slot, so a later renewal traps on a freed
object, and offsets run past the slot. Over the forty modules the
passes now emit 179 `renew_if`, 179 `limit` with 358 `check_limit`,
222 `renew_hull` and 412 `check_ahead`; before, none of the first
three. Plain modules draw nothing new, so their corpus (nix/check.nix
compares seed 1 byte for byte) is unchanged.

Four bugs planted in these forms are each caught by the gen modules
alone: a failed guard's `renew_if` answering `unchecked(span)` (96
disagreements), a passed guard skipping the flag test (41, only after
the free inside the loop came in), `check_limit` skipping its access
test (269), and `renew_hull` skipping its access test (96).

`reuse.ir`, `snapshot.ir` and `floats.ir` are hand-written checked IR,
so they run only with the reference checks: the check passes take only
pizlonate's output, and a `--checks=schedule` run over `reuse.ir` is
rejected by the validator, the expected result for input outside a
pass's precondition, not a finding.

## The validator and its gate

`Validate.v` transcribes `valid_module/1` for code, clause group by
clause group. A function is valid when its uses, ops, instructions,
jumps and phis are well formed, every use has a dominating definition
(by the dominator tree's intervals, Cfg.v), named locals are declared once in the entry
block, and, in a checked module, `stage_func/6` holds: the evidence
pass over the blocks in order, `limit_reads/2`, and
`polls_every_cycle/1` (by repeatedly removing blocks with no unpolled
edge into what is left). A data object is valid when its alignment is
a power of two up to 4096, its linkage is one a Fil-C module allows
(with the items `extern(weak)` and `init(Kind, Prio)` ask for), its
float items are in range, its strings hold bytes, and it has no
`item(l, sym(_, _))`. An alias is valid when its linkage is `export` or
`weak`, no function or data shares its name, and its target is a
function, or data of a linkage an alias may name that no function calls
through the alias. ir.pl throws at the first problem; the model returns
`false`, so it follows ir.pl's clause groups and not its order of
evaluation.

Data items the interpreter does not lay out decode to `ItemOther`, and
linkages it does not know to `LOther`, each keeping its term: the
validator reads them, and the interpreter's layout is stuck on them.

Three places in ir.pl depend on how Prolog evaluates, and the model
copies them, as `Validate.v`'s header records: `offset_interval/8`
memoises successes but not failures under a depth limit of 32;
`pointer_distance/4` commits to the first shared base (a cut); and
`op_interval/9` commits after its heads, so `and` with a constant
tries its left operand first.

The gate is [rocq/valid.sh](../rocq/valid.sh). For each file,
`nanofil outcomes` prints the checked module, and
[rocq/mutants.pl](../rocq/mutants.pl) prints, for each item, the item
as it is and up to 150 mutants. A function's: a check deleted or moved,
a check's bounds, rights or alignment changed, a raw access's offset
moved by one, a free inserted between evidence and its use, a reuse
form given another proof, a poll edge removed. A data object's: its
alignment, its linkage, an item of each shape the validator looks at
appended, a byte, a long or an `x` constant prepended (which moves every
pointer item after it), the object renamed (also to another item's
name) or deleted. An alias's: its linkage, its
target and its name changed, or the alias deleted. And up to 150 items
inserted: an alias of each kind of target, under a fresh name and under
the name of a function the module calls without defining, a data
object of each linkage, and a data object under the first function's
name. `valid_module/1` judges each changed module, and
the model must reach the same verdict. Plain modules are skipped, and
so is a mutant that would make its module plain.

The corpus is the matrix's Fil-C fixtures and C tests; forty modules of
ten random functions each from [tests/gen.pl](../tests/gen.pl), whose
`filc` mode addresses its memory through `p` values, reaches outside
its slot and draws the memory loop above; and, with the reference
checks only, the 16 C programs of `tests/c/prog` that declare an alias,
a weak symbol, thread-local data or a constructor, which bring the
corpus's aliases and its kinds of data linkage. Programs with a
`// cflags:` line are left out, since they compile as progtest.sh does
and not as `cc-ir` does. The other programs are too slow for the
check, because each mutant is judged on its whole module; one run
over 169 of them agreed on all 73,330 verdicts it could judge.

| Corpus | Verdicts that agree | Outside the subset | Disagree |
| --- | --- | --- | --- |
| filc fixtures, C tests and gen modules, without `-O` (each `--checks` mode) | 64,589–68,260 | 253–256 | 0 |
| the same with `-O` | 45,541–48,193 | 253–256 | 0 |
| the 16 `tests/c/prog` programs (reference checks) | 9,505 | 3,012 | 0 |
| Lua's own functions, `rocq/lua.sh` (reference checks) | 6,345 | 0 | 0 |
| `rocq/tests/reuse.ir`, `snapshot.ir`, `floats.ir`, `dominance.ir`, `interval.ir` (reference checks) | 111, 145, 46, 41, 30 | 0 | 0 |

The counts were measured before the mutants for the three data
decisions below (prepended items, renames onto other items' names, data
under a function's name) were added; those add a few verdicts per item,
and the full campaign's receipt for that change had no disagreement.

The mutants test rejection as well as acceptance: on basic.ir,
`valid_module/1` judged 413 of them invalid and 210 valid. In the four
C programs with aliases or weak symbols, every kind of data and alias
mutation met both verdicts; for instance 38 retargeted aliases were
invalid and 35 valid, and 296 changed data linkages invalid and 363
valid. A mutant is `outside` when it is itself outside the subset, when
it changes its function's signature and a function outside the subset
calls it, or when it changes data or an alias that a function outside
the subset names, since the model cannot judge that function.

The gate can fail. I planted eight bugs in `Validate.v`, each found by
the gate and then reverted: a covered access that ignored its size;
evidence that survived an instruction that does not preserve it; a
hull allowed below its lower proof; cycles that needed no poll; data
aligned up to 8192; `item(l, sym(_, _))` allowed; calls through an
alias of data allowed; and an `extern(weak)` declaration with items.

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
- **Floats are bit patterns, rounded in one place.** As in interp.pl,
  an `s`, `d` or `x` word is the unsigned integer of its bits, never a
  host float, and `Ieee.v` computes with exact rationals and rounds in
  `round_ratio` alone. The classes are `Single`, `Double` and
  `Extended`, since a constructor `S` would shadow `nat`'s.
- **The variadic snapshot is a step of its own.** A variadic callee
  starts at `Snapshot xs l`: taking the snapshot allocates, so it is a
  `Fresh` step like `alloc`, before the entry block. The snapshot's
  pointer lives in the environment under `hidden(va_snapshot)`, the
  interpreter's key.
- **Dominance is cfg.pl's, by intervals.** The validator first
  computed dominator sets by a fixpoint of its own, roughly cubic in
  the number of blocks, and found each use's definitions by scanning
  the whole function. It now transcribes `cfg_idoms/2` and
  `dom_intervals/3`, and ir.pl's table of definition sites, over the
  name maps of `Maps.v`. cfg.pl sorts successors and predecessors in
  the standard order of terms; the model keeps each jump's order,
  which changes the reverse postorder and the preorder numbers but not
  the immediate dominators or the dominance relation. Lua's
  `luaV_execute` (995 blocks) went from over half an hour, unfinished,
  to under half a second for its dominance, and lvm.c's whole module
  takes 2.7 s against about a second for `valid_module/1`; the evidence
  pass (`stage_func`) is now most of that. A name's hash decides only
  its bucket, so the extraction computes it with OCaml's string hash:
  the Gallina one, eight integer operations per character, made small
  functions twice as slow as with lists.

  The gate did not at first notice a model that stopped `cfg_idoms`
  after one sweep, which settles every reducible graph.
  `rocq/tests/dominance.ir` is an irreducible graph, found by search,
  on which one sweep leaves a wrong idom; a mutant that deletes a
  definition then separates the two. That planted bug, and one where
  every reachable label dominates every other, are caught there; one
  that took each block's first processed predecessor as its idom was
  caught 121 times over the fixtures and gen modules.

  Three off-by-one plants at the intervals' comparisons:
  `rocq/tests/interval.ir` defines a temporary twice in one block, the
  second time from itself, so deleting the first definition leaves a
  use at its own definition's index; `site_dominates/4` compares
  indices strictly, and a model comparing them with `=<` accepts that
  mutant (caught twice, by the full campaign only). A strict upper
  bound in `dominates_by_interval` makes a leaf dominate nothing below
  it, caught by 24 base verdicts of the smoke corpus. A strict lower
  bound changes only whether a label dominates itself, which the
  validator never asks: a use in its definition's block compares
  indices, so that plant is equivalent and no fixture can catch it.
- **`nat` extracts to OCaml's `int`.** The model's `nat`s count list
  elements and fixpoint rounds. Unary, the bound of the old dominator
  fixpoint (the square of the reachable block count) overflowed the
  stack on Lua's `luaV_execute`, which has 995 blocks.
- **The runtime is a module type.** `Runtime.v` states what the model
  takes from the Fil-C runtime: where a new object goes, what free
  does, and what may change at a safepoint, as seven axioms
  ([runtime-axioms.md](runtime-axioms.md)). The model has one thread
  and no collector, so other threads and the collector show up only
  as the `safepoint` relation. `InterpRuntime` is interp.pl's
  (`alloc_base/6`, `free_res/4`, nothing at a safepoint) and proves
  every axiom, so the module type is consistent; `Run.v`'s `Driver` is
  a functor over `Runtime`, and the gates run `Driver InterpRuntime`.
  The step's `free` is the genv's `ge_free`, the runtime's, and
  `step_rel` takes any `fresh` base, which every runtime's `alloc`
  gives; Machine.v runs the steps over a runtime (Campaign 3, below).
- **Prolog's `//` on non-negative operands is `Z.div`.** ieee.pl's
  `//` truncates; `Z.quot` says that, but its extraction divides bit
  by bit and took minutes on the 16,000-bit ratios of an `x` denormal.
  Where both operands are non-negative the model uses `Z.div`, which
  extracts to zarith's division and agrees.

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
- **`renew_res/4` asked only about `obj`.** It answered "freed, so it
  traps" for an `obj(Base)` capability only, though `object_free_res`
  frees read-only heap objects too, and the variadic snapshot
  (`args_snapshot`) is one. `rocq/tests/snapshot.ir`'s `freed_snapshot`
  showed it: see the next section, which records the fix.

## What transcribing the validator made clearer

- **The stage belongs to the module.** `module_stage` reads the whole
  module: it is checked if any function uses a word of the checked
  stage (a check, a reuse form, a raw access, a flight or a poll
  edge). A mutant that removes the only poll edge of a
  module that has nothing else checked makes the module unchecked, and
  so valid, though it now has an unpolled cycle. The model reads the
  stage from every function, including those outside the subset.
- **Validity is a property of the module, not the function.** Deleting
  a function's `va_args` changes its signature, and that invalidates
  every caller. So the gate replaces one function and judges the whole
  module, and the model cannot judge a mutant whose callers are outside
  the subset.
- **Three data findings, decided by mbrock** (the decision record is
  the artifact "Campaign 3 prerequisites: three data findings to
  decide"). Each was a valid module whose meaning the validator, the
  interpreter and the assembler did not agree on, found by
  transcribing the validator. None of the decisions makes a module of
  the corpus invalid: 226 C modules, the IR fixtures, Lua's 34 modules
  and 40 modules of [tests/gen.pl](../tests/gen.pl) have none of these shapes.
  - *Data items have the header's shapes.* ir.pl checked only that
    float items are in range, that strings hold bytes and that a Fil-C
    module has no `item(l, sym(_, _))`, so
    `data(x, export, 8, [item(w, foo), bar])` was valid, and so was a
    pointer item at an odd offset; neither could be laid out by the
    interpreter or emitted by the backend. `data_item_shape/1` and
    `pointer_items_aligned/3` now refuse them, and `Validate.v`'s
    `data_item_ok` and `pointer_items_aligned` the same; `ItemOther` is
    always invalid. Campaign 3 needs no hypothesis that the layout
    succeeds.
  - *A call of data traps.* A symbol the module does not define stays
    external, which a Fil-C module may name (a closed world would make
    203 of the 226 C modules invalid). A direct `call` of data the
    module defines is valid, and native code's function check traps
    there; the interpreter was stuck, treating the name as an
    external. It now gives `trap(not_a_function)`, and `Semantics.v`'s
    `external_call` the same; `tests/filc/call-data.ir` compares that
    with native code. A deleted or renamed data object still makes its
    uses external. An independent review found two places where native
    code did not trap, both fixed: a constructor or destructor table
    entry has no getter, so a call (or a copy) of one is now invalid,
    as ir.pl's header already said (`not_init_entry/3`, and
    `init_entry_named` in the model); and a call of `local` data got a
    weak thunk that another object's function of the same name
    replaced, which a two-object link showed running that function, so
    filc_abi.pl's `lower_thunk` now keeps it local, as it does for a
    local function's. A second review of those two fixes, which also
    showed that a call of `tls(_)` data traps natively, found three more
    valid modules that got around them, each run natively; all three
    are now invalid (`valid_item/4` for data, `data_names_ok` in the
    model):
    - another data object's `item(p, sym(E, _))` took the address of
      a table entry E; natively that is an undefined getter, or
      another object's function E;
    - a table entry's item named something other than a function of
      the module (another entry, or data), which the header already
      forbade and which left an undefined function object;
    - an `extern(weak)` declaration beside a `local` definition of the
      same name made the definition's getter and thunk weak and
      global, so another object's function of that name ran. The C
      frontend declares weak only names it does not define.
  - *Names are unique.* `module_symbols/2` keeps the first item of each
    name, the interpreter's layout the last, and the assembler refuses
    both; with two functions of one name the interpreter crashed.
    `unique_names/1` now refuses two items, functions, data other than
    a weak declaration, and aliases, of one name, and `Validate.v`'s
    `valid_items` the same.
  Planted in the model, each rule is caught by the full campaign: no
  unique names (25 disagreements on three files), no pointer alignment
  (16), `zero(-1)` accepted (11), unknown items accepted (110), a
  non-atom symbol accepted (4), `x` taken as 16 bytes (1), the call
  stuck instead of trapping (2), a copy of a table entry accepted
  (30), a table entry naming data accepted (18), a weak declaration of
  a local definition accepted (14), and a pointer item naming a table
  entry accepted (5).
- **Entry evidence depends on block order.** An edge from a block not
  yet processed carries no evidence, the same as a poll edge. Block
  order is therefore part of the checked IR's meaning for the
  validator, and Campaign 3's soundness statement must be about the
  blocks in that order.

## A freed snapshot traps at its renew

`freed_snapshot` frees the variadic snapshot (`free` of `va_args` at
offset 0) between a check of it and a `renew` of that check. ir.pl
accepts the module, and the run ended `unchecked(span)`: a valid module
whose run is unchecked, a counterexample to Campaign 3's
`valid_no_unchecked` as stated, found in the Prolog itself. The model
agreed with the interpreter, so it was not a disagreement.

The interpreter was stricter than native code, not the other way round.
The emitted renew (`filc_amd64.pl`'s `fused(renew(...))`, which
`renew_hull` and `renew_if`'s fast path share) tests the free flag in
the object's flags byte through its lower, whatever the capability's
kind, and the pinned runtime's `object_for_deallocate` refuses special,
global and mmap objects and interior pointers but not READONLY ones. So
native Fil-C frees the snapshot and traps at the renew. `renew_res/4`
now treats a freed `ro` object as it treats a freed `obj` one, and
`Ops.v`'s `renew_res` says the same: the run traps out of bounds, as
`freed_snapshot_check` does. An Oracle review of the change found the
callers (renew, renew_hull, renew_if) consistent, the trap order
unchanged (a freed object fails its bounds before read-only is tested,
as native reports FREE first), and no other `obj`-only assumption about
freeing; only the snapshot is a freeable `ro` object, since read-only
data is not heap and its free is `invalid_free`.

## Disagreements

None so far, in the outcome gate or the validator gate, floats and
variadics included. No fixture was
needed, and the Prolog has not yet been contradicted. Making the comparison work needed two changes on the
OCaml side, neither of them semantic: a gas limit in the driver that
was too small for loops (now 2^60 steps, so the run's own fuel always
ends a run first), and atoms containing UTF-8 bytes in a reader.

## Campaign 3: the machine of a runtime

`Machine.v` is Campaign 3's first milestone. `Machine R` runs
Semantics.v's steps over a runtime R: a step that allocates nothing, an
allocation at R's `alloc`, or R's `safepoint` action, which may happen
before an instruction where `R.at_safepoint` holds and before a poll
edge, and nowhere else. A call of `free` is the genv's `ge_free`, which
Run.v's `Driver` sets to R's `free`. Two theorems, no admits:

- `mreachable_ready`: if R is ready to allocate in the first state, it
  is in every state a run reaches. Each step that allocates nothing
  writes only inside objects (its writes passed an access check) and
  only ends objects (`free`, an invocation's locals), which R's
  `ready_kept` allows; an allocation is R's `fresh_allocation`, and the
  variadic snapshot it may write lies inside the new object; a
  safepoint is R's `safepoint_ready`.
- `mstep_refines`: from a ready state each machine step is a
  `step_rel` step, its allocation's base fresh, or a safepoint action.
  What the soundness theorem proves of `step_rel` and `R.safepoint`
  therefore holds of every run of every runtime.

Decisions and findings:

- **Two readiness obligations join the module type.** `ready_kept`
  (the program's own writes inside objects and its ending of objects
  keep the runtime ready) and `safepoint_ready` (so do the runtime's
  actions) are about the runtime's own bookkeeping, not Fil-C, so they
  have no native test. `InterpRuntime` proves both.
- **`fresh` speaks of objects as `object_region` finds them.** It
  quantified over every region in the list, including one behind
  another of the same identity, which no access ever reads. Stated over
  `object_region`, as everything else is, `ready` and `fresh` follow
  from each other without a lemma about the region list's shape. No
  extracted function uses `fresh`, so the gates are unchanged.
- **Ending a local is not the runtime's free.** `lifetime_step` lets
  only heap objects end; an invocation's locals are stack objects that
  the program ends itself. Machine.v's `region_step` is the weaker
  relation the program's own steps satisfy.
- **The runtime acts before the instruction.** At an `at_safepoint`
  instruction or a poll edge the safepoint action comes first, and the
  instruction runs on what the runtime left, as native code runs after
  its pollcheck.
- **A negative extent has no machine step.** `fresh_allocation` covers
  extents from 0. Only a named local's constant size could be negative,
  and `valid` refuses that (0 to 2^31-1); heap sizes are read at `l`.
- **Proofs are kept fast.** Machine.v checks in about 4 seconds.
  `inversion` on an equation between large terms (the words a
  `va_arg` loads) took 17 seconds; `congruence` takes milliseconds, and
  `inst_step_let` states the generic `let` once instead of letting a
  case split unfold every op.

### The coverage lemma

`Coverage.v` is Campaign 3's second milestone, no admits, checked in
about a second. `covered_access_not_unchecked`: where ir.pl's
`covered_access/6` says a raw access instruction (`raw_load`,
`raw_load_pointer`, `raw_store`, `raw_store_pointer`) lies inside the
check that yielded its address operand, and that check passes in the
memory the access runs in, `inst_step` does not stop the instruction
with `unchecked`. It is arithmetic over `cap_access_res/7` in two
steps: `cap_access_covered` (a passed check of [A+Lo, A+Hi) passes for
every part of it at an alignment the check's implies and with rights it
allows) and `covered_access_checked` (the raw access's own check is such
a part).

Decisions and findings:

- **The check passes in the memory the access runs in.** The lemma
  does not say why; that is the evidence invariant's job, from the
  check having passed earlier and nothing between it and the use having
  freed or moved the object.
- **Objects end at or below 2^64 is a hypothesis, `objects_fit`.**
  Addresses wrap modulo 2^64 (`raw_address/3`) while bounds are
  unbounded integers, so the lemma is false for an object ending above
  2^64. The runtime axioms do not exclude one, and the interpreter makes
  one: see "An object past 2^64" below.
- **The capture replays sentences one at a time.** `1: { tac.` on one
  line is two sentences to Rocq but one to the proof-state capture's
  plan, which then drops `tac`; Coverage.v uses bullets instead.

## An object past 2^64

`rocq/tests/huge-object.ir` allocates an object of 2^64 - 2^32 - 80
bytes and then one of 256, which the interpreter's allocator (Next only
adds) places 64 bytes below 2^64. A check of the second object's bytes
[0, 128) passes, and a raw load at offset 64, which the check covers,
wraps to address 0 and runs `unchecked(out_of_bounds)`. ir.pl accepts
the module, and the model agrees with the interpreter: a counterexample
to `valid_no_unchecked` over the interpreter's runtime, found by the
coverage lemma's proof rather than by a test.

The interpreter is more permissive than native code. The pinned Fil-C
refuses `malloc` of 2^48 bytes or more ("filc safety error: attempt to
allocate object that is too big") and runs out of memory at 2^47, so no
native object ends above 2^64. The backend cannot emit this module's
check yet, so difftest does not compare it. Not yet fixed: the fix is
interpreter semantics (an allocation past a limit traps, as native code
does) and a runtime axiom (`fresh_allocation` bounds the object it
gives), with a native test, so it needs an Oracle review first.

## Next

1. An allocation bound: the interpreter's `alloc_base/6` traps where
   native Fil-C refuses an object, `fresh` bounds the object below
   2^64, with an axiom test for the limit, so `objects_fit` follows from
   `ready` and huge-object.ir traps.
2. The evidence invariant for proof persistence, stated over
   `Machine R`'s steps: between a check and its use, only
   `evidence_preserving/1` instructions and unpolled edges, so no
   safepoint action and no free.

Inquiries touched: none closed. The integer-at-`p` case is a small
input to the integer-to-pointer inquiry.
