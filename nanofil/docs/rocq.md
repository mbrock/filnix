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
| `Maps.v` | library(assoc) | name maps: a hash of the name, then an association list per hash, so a lookup's answer never depends on the hash; what each operation does to a lookup (`nm_find_add`, `nm_find_remove`, `nm_find_fold_add`) |
| `Ieee.v` | ieee.pl | binary32, binary64 and x87 extended as bit patterns: `decode/4`, `round_ratio/5`, `ieee_binary/5`, `ieee_convert/4`, `ieee_compare/5`, `ieee_from_int/3`, `ieee_to_int/3` |
| `Syntax.v` | ir.pl's header tables | classes, ops, values, instructions, jumps, blocks, functions, data, modules; `op_arg_classes/4`, `evidence_preserving/1`, `ahead_transparent/1`, `local_objects/2` |
| `Values.v` | interp.pl's values | `cap` (`none`, `obj`, `ro`, `fn`, `ext`), `ptr`, `word`; `word_at_class/3` |
| `Memory.v` | interp.pl's Memory section | regions, `mem`, `cap_access_res/7`, `free_res/4`, bytes and aux, `fresh` |
| `Runtime.v` | `alloc_base/6`, `free_res/4`; [runtime-axioms.md](runtime-axioms.md) | Campaign 2's `Module Type Runtime`, ten axioms and three readiness obligations, and `InterpRuntime`, which proves them |
| `Ops.v` | `alu/4`, `additive_res/4`, `kind_res/8` | integer and float ops, `check` and the reuse vocabulary, raw loads and stores, pointer-load and pointer-store protocols, `va_arg` |
| `Semantics.v` | `run/5`'s blocks, instructions, jumps, calls | the configuration, `step`, `step_rel`, `reachable`; the variadic entry snapshot |
| `Run.v` | `initial_memory/4` | module preparation, and `Driver`, a run over any `Runtime`'s allocations and free |
| `Machine.v` | — (Campaign 3) | the machine of a `Runtime`: steps, the runtime's allocations, its actions at safepoints; `ready` kept by every step; each step a `step_rel` step or a safepoint action |
| `Cfg.v` | cfg.pl | `func_cfg/2`, `cfg_idoms/2` (Cooper, Harvey and Kennedy), `dom_children/3`, `dom_intervals/3`, `dominates_by_interval/3` |
| `Validate.v` | ir.pl's `valid_module/1` | `valid_func`, `valid_data`, `valid_alias`, `valid_items`, `valid`: uses, ops, instructions, dominance, locals, the evidence pass, the reuse rules, `polls_every_cycle`, data linkage and items, aliases |
| `Dominance.v` | — (Campaign 3) | what Cfg.v's dominator intervals mean: the entry is reachable, reachable blocks' successors are, and what dominates a successor dominates its predecessor, but for the successor itself; only the entry dominates the entry; dominance is antisymmetric |
| `Interval.v` | `offset_interval/8`, `op_interval/9` (ir.pl) | the derivations of an offset interval as an inductive relation; every interval the walk answers is derived, and a derived interval holds of the values a run reads wherever the names it walks hold what their definitions computed and their single-definition operands are unchanged |
| `Sites.v` | `single_definitions/3`, `block_sites//1`, `definitions_dominate/3` (ir.pl) | every definition with its site; a single definition has one; a use is dominated by its single definition, and no single-definition operand of a definition is defined again where the definition's site dominates |
| `Identity.v` | — (Campaign 3) | no step of a run loses an object: each is as it was, or freed, given that the runtime's free keeps identities; a check that passed then passes again, or traps out of bounds |
| `Single.v` | `single_definitions/3`, `definitions_dominate/3` (ir.pl); the steps of interp.pl | in every frame of every run, each single definition whose site dominates the frame's point replays: its name holds what its instruction made from its operands' current values, in a memory that lay in the address space and that the current one persists from |
| `Coverage.v` | — (Campaign 3) | the coverage lemma: a raw access that `covered_access/6` puts inside a passed check gives no `unchecked` |
| `Evidence.v` | — (Campaign 3) | the evidence invariant at an instruction and an edge: what a live fact means, every case of `checked_inst_rest/7` keeps the pass's facts true, block entry keeps the meet, accesses the pass accepts give no `unchecked` |
| `Walk.v` | — (Campaign 3) | the evidence pass read back for the run-level invariant: block by block (`pass_fold`), position by position (`walks`), where it keeps facts (`relies`), a `check_local`'s own fact |
| `Steps.v` | — (Campaign 3) | what one step does to the running frame, point by point: snapshot, block entry, instruction, return |
| `Invariant.v` | — (Campaign 3) | the run-level invariant stated: what holds at each point of a frame (`at_pos`, `point_ok`, `inv`), the runtime hypothesis `spares`, and what each kind of step needs of it |
| `Persistence.v` | — (Campaign 3) | the evidence invariant over whole runs: every machine step keeps `inv` (one lemma per kind of step), and in every state of a run no raw access or raw call of a frame that is not doomed is `unchecked`, but by `hull_covered` |
| `Chain.v` | `offset_interval/8`, `guard_chain/3`, `pointer_distance/4`, `hull_covered/7` (ir.pl) | what a frame reads off the single definitions that dominate its point; along every run, no access `hull_covered` accepts gives `unchecked` |
| `Renew.v` | `renew_source_op/6`, `hull_renewable/8`, `half_known/6` (ir.pl); `renew_res/4`, `half_bound/6`, `half_res/4` (interp.pl) | along every run, no renew, renew over a hull or half check the pass accepts gives `unchecked` |
| `Guard.v` | `guard_covers/5`, `limit_covers/5`, `lower_chain/3` (ir.pl); `kind_res/8` (interp.pl) | along every run, no `renew_if` or `check_limit` the pass accepts gives `unchecked` |
| `Ahead.v` | `ahead_justified/3`, `ahead_block/6`, `ahead_edge/5`, `ahead_step/5`, `ahead_insts/8` (ir.pl) | the facts `check_ahead`'s backward pass keeps, as functions of the point, and that its one sweep computes them |
| `Doomed.v` | `doomed_result/5` (interp.pl); `raise_need/6`, `ahead_meet/2` (ir.pl) | along every run, a frame a `check_ahead` doomed never steps to `unchecked` |
| `Soundness.v` | `inst_result/5`, `raw_access/5`, `valid_use/3` | `valid_no_unchecked`: along every run of a checked module that starts ready, no step is `unchecked` |
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
The model builds independent theories in parallel and exports its checked
original sources and objects. The Nix parser check reuses those originals
without compiling them twice; every reprinted theory still compiles in its
own project copy, as does the Ltac fixture. A source-only checkout still
builds originals normally. No no-admit, parsing or typechecking gate is skipped.
`NANOFIL_MUTANTS=0` selects `mutants.pl --base`: it generates no mutations,
only the unchanged items' whole-module verdicts. This is a smoke check,
not rejection coverage or a soundness proof.
In particular, `dominance.ir`'s one-sweep-idom and always-true-dominance
plants, and `interval.ir`'s same-index plant, are detected by their
mutant verdicts, not their unchanged base verdicts. They are covered only by the full campaign, not the routine
no-mutants smoke check. This tradeoff is deliberate; a dominance or
other soundness-relevant change calls for the opt-in evidence.

CI (`.github/workflows/nanofil-rocq.yml`) runs the quick root after each
push that changes model, compiler/validator or gate inputs (its `paths`
list); unrelated web styling, rendering and documentation edits skip it.
Run it yourself before pushing such a change:
`nix build .#checks.x86_64-linux.nanofil-rocq`.

The complete outcome and mutation matrix described below is
`checks.x86_64-linux.nanofil-rocq-full`. Run it deliberately for a
soundness-relevant change, with `nix build` or the workflow's manual
`full` input. No nightly campaign is enabled.

All jobs retain timestamped progress through `tests/watch.py`; a corpus
file warns at 60 seconds and fails at 300. Timeouts fail, never omit
coverage. Independent outcome modes run in
parallel, as the validator modes already did. Lua's whole-module mutant
generation/judging uses independent item-index partitions after the
program cases finish; every changed module is still judged whole, and
inserted-item mutants occur only in partition zero. The union is checked
against the serial stream. Model inputs exclude fixtures/harnesses/docs;
the check excludes unrelated web/docs inputs. Outputs retain full logs
per mode/program.

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
  does, and what may change at a safepoint, as eight axioms
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
  validator, and Campaign 3's soundness-of-checking statement must be about the
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
  What the soundness-of-checking theorem proves of `step_rel` and `R.safepoint`
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
- **Objects end in the address space: `objects_fit`.** Addresses wrap
  modulo 2^64 (`raw_address/3`) while bounds are unbounded integers, so
  the lemma is false for an object ending above 2^64. The lemma takes
  `objects_fit` as a hypothesis (since "Objects end below 2^48", every
  object ends at or below 2^48, more than this lemma needs), and the runtime's `address_space`
  axiom supplies it wherever the runtime is ready: Machine.v's
  `mreachable_objects_fit` gives it in every state of a run that starts
  ready. See "An object past 2^64" below.
- **The capture replays sentences one at a time.** `1: { tac.` on one
  line is two sentences to Rocq but one to the proof-state capture's
  plan, which then drops `tac`; Coverage.v uses bullets instead.

### The evidence invariant, instruction by instruction

`Evidence.v` proves ir.pl's evidence pass sound one instruction and
one edge at a time. No admits; it checks in about 7 seconds, most of it
the two case splits over the check-like ops. A live fact
`live(Q, P, Lo, Hi, Rights, Align)` means at run time (`fact_holds`): Q
holds a pointer word, P evaluates to the same word, and the access check
of that pointer passes in the current memory. A check reads only the
memory's regions, so any step that changes no region keeps it.

- `let_step`, `preserving_step`: a `let` that continues, and any
  `evidence_preserving/1` instruction, changes no region and no
  temporary but the one it defines.
- `evidence_after_holds`: `evidence_after/3` keeps every fact true.
  The pass's kill of a redefined Q or P is exactly what the proof needs.
- `check_like_holds`: each check-like op (`check`, `check_ahead`,
  `renew`, `renew_hull`, `half_check`, `renew_if`, `check_limit`)
  continues only where the access check of its pointer passed, so the
  fact the pass adds after it holds, and so does a `check_ahead`'s wider
  range.
- `checked_inst_holds`: every case of `checked_inst_rest/7` keeps the
  pass's facts true: a check-like instruction with its access
  (`after_check`), a `check_local` (its Q killed), a `check_function`
  (no facts), a repeated getter (its temporary killed), and every other
  instruction.
- `entry_holds`: an unpolled edge changes neither memory nor
  temporaries; a fact of the pass's meet at a block's entry is a fact
  of every set it meets, so of the predecessor's exit facts; the phis
  change only their own temporaries, whose facts the pass drops.
- `checked_access_not_unchecked`, `generic_access_not_unchecked`: the
  access a check-like instruction is checked for gives no `unchecked`,
  and neither does a raw access the pass accepts by a live fact that
  covers it, given `objects_fit`.

Decisions and findings:

- **The model's validator is not refactored for the proof.** The last
  case of `checked_inst_rest` is copied as `generic_rest`, and
  `checked_inst_rest_generic` proves the two equal by computation, so
  Validate.v, the transcription the gates compare, is unchanged.
- **A `check_ahead` that dooms the frame has no fact.** When its wider
  check fails, `inst_step` traps early and the step continues doomed
  (`doomed_result`); its fact then does not hold. The instruction-level
  lemmas are about `inst_step`, where the doomed case does not
  continue; the run-level invariant must treat a doomed frame apart.
- **The renderer's grammar.** `H : context [...] |- _` in `match goal`
  reprints wrongly, so the tactics use `match type of H with context`;
  `N: { tac.` on one line is avoided, as before.

Persistence.v carries these along whole runs (next section).

### The evidence invariant over runs

`Persistence.v` proves, with no admits, that in every state a run of
`Machine R` reaches from a checked module's function, started ready,
the facts the pass computed for the running frame's position hold.
Its theorem `run_access_not_unchecked`: a frame that is not doomed runs
no raw access and no raw call to an `unchecked` outcome, unless the pass
accepted the access by `hull_covered`. With Walk.v, Steps.v and
Invariant.v it checks in about 5 seconds.

- **The pass block by block.** `pass_fold` reads `evidence_pass`'s fold:
  each block was passed from the exit facts the fold had when it reached
  the block, all kept to the end. A block reached by a back edge saw
  nothing on that edge (the fold had not reached its source), and the
  meet over an empty set is empty, so a back edge without a poll gives
  no facts the proof needs to justify.
- **Where the pass is.** `checked_inst_rest/7` takes a check and its
  access in one step, so the pass's positions are a subset of the
  instructions. `at_pos` says which: between two of the pass's steps,
  the live facts the next instruction relies on hold (`relies`: an
  evidence-preserving instruction, a raw access, a `check_local`, a
  repeated getter; before anything else the pass keeps no fact); at a
  block's end, those the unpolled edge carries; between a check and the
  access taken with it, the covering fact (`pair_claim`); after a
  `check_function`, that its function check passed.
- **The invariant** (`inv`): the running frame is a function of the
  module, its named locals lie above 0 (a `check_local`'s fact needs its
  address not to wrap), and, unless a `check_ahead` doomed it,
  `point_ok`; every waiting caller is `parked`, with no fact, after its
  call. `mstep_inv` proves every machine step keeps it: a step that
  allocates nothing (`next_inv`: snapshot, block entry, jump or return,
  an instruction or a call), an allocation (`alloc_inv`), and the
  runtime's action at a safepoint (`safepoint_inv`).
- **A `check_local`'s access** is now covered: the access check of the
  local passed and its fact holds (`check_local_fact`).

Decisions and findings:

- **The runtime's safepoints.** The module type lets a runtime act
  before any instruction that is not `evidence_preserving/1`
  (`safepoints`). The pass keeps facts across three such instructions:
  a pointer store taken with its check (its ensure-aux may exit), a
  `check_local`, and a repeated getter (`repeated_getters/4`). A local
  check is inline, and a repeated getter takes the fast path because
  the same getter returned earlier in this activation, so neither
  reaches a safepoint natively. A pointer store does: when its aux must
  be allocated and is not in zero mode, it exits to the runtime
  (`filc_exit_with_allocation_root`, filc_runtime.c 2578-2591, "anytime
  we do a store, it's a safepoint"), and `filc_exit` runs deferred
  signal handlers (1231-1250), which may free the checked object. The
  store then lands in the freed object's retained memory: safe natively
  by `retention`, which is Fil-C's own argument at that exit ("any
  object referenced from roots is guaranteed to be kept alive"), but
  `unchecked` in the model, whose raw access to a freed object is a
  false check. (An earlier version of this page said no such free can
  show; that was wrong for pointer stores.) The theorem takes this as a
  hypothesis, `spares`: at a safepoint before an instruction the pass
  relies on facts for, the runtime changes no region. The interpreter's
  runtime changes nothing at a safepoint (`interp_spares`), so
  `interp_access_not_unchecked` has no such hypothesis. mbrock's
  decision (November 2026): `spares` stays a hypothesis. Neither axiom
  that would remove it is true natively (no free at any safepoint; no
  safepoint at a pointer store). The principled alternative, weakening
  the conclusion to "checked, or its object was freed since its
  check", is left for later.
- **A runtime's free gives no `unchecked`.** The module type's
  `free_checked` now says so ("No run is unchecked"); `free_res`
  proves it, and native free returns or traps.
- **`InterpRuntime` is unsealed.** It was `: Runtime`, which hides that
  its safepoint changes nothing; `Driver InterpRuntime` and
  `Persistence InterpRuntime` still check it against the module type.
  The extracted model is unchanged (the gates agree).
- **A doomed frame claims nothing.** Its `check_ahead`'s fact does not
  hold; what it may do is the `check_ahead` corollary's.
- **The renderer's grammar and memory.** `do N tac` and `Module X <: T`
  do not parse yet; the files avoid them. Drawn as one 1360-line file
  the proof needed 1.7 GiB of dterm-rocq's 1 GiB stack: the drawn proof
  states grow with every name the other pages define, so it is four
  files (Walk.v, Steps.v, Invariant.v, Persistence.v) and one lemma per
  kind of step, each page below Machine.v's 777 MiB (Persistence.v 709
  MiB in the full site run).

Not yet: `hull_covered`, the reuse forms' own rules (a renew's
`unchecked(span)`, a half check's, a limit's, `unchecked(alias)`), the
doomed frame (`check_ahead`), and then `valid_no_unchecked` itself,
which assembles these with the initial readiness hypothesis. The reuse
forms rest on dominance, below.

### Dominance

The reuse forms' rules read single-definition names along flight
chains (`guard_chain/3`, `pointer_distance/4`), and a chain is a
relation between the values of two names: a flight's value and its
base's. In a loop the base is defined again on each iteration, so the
relation holds at a point only because the flight's definition
dominates it, and the base's dominates the flight's
(`definitions_dominate/3`). The proof that the reuse forms are sound
therefore needs the validator's answer to "does A dominate B?" to mean
what it says on the machine's runs.

`Dominance.v` proves it, with no admits, of `block_intervals` for every
function: of the dominator tree and intervals ir.pl computes, not of a
corrected copy. It checks in under two seconds.

- `dom_entry`, `dom_closed`: the entry block has an interval, and so
  does every successor of a block with one. A run enters only such
  blocks, so `definitions_dominate/3` skipping blocks without an
  interval skips no block a run reaches.
- `dom_edge`: a label that dominates a block's successor and is not the
  successor dominates the block. This is what keeps a dominance fact
  true across an edge.
- `dom_entry_top`, `dom_antisym`, `dominates_trans`,
  `dominates_refl`: the order facts.

Decisions and findings:

- **Soundness only.** The proof never shows that `cfg_idoms/2` computes
  the true immediate dominators (Cooper, Harvey and Kennedy's argument
  is about the fixpoint being the least). It uses three facts of what
  was computed: `reverse_postorder/6` starts at the entry and is closed
  under successors; at the last sweep, which changed nothing, each
  label's idom is a common ancestor of its predecessors that have one,
  since `common_dominator/5` only walks up; and `dom_intervals/3` gives
  each label the preorder numbers of its subtree. A tree with these
  properties passes every path from the entry through each ancestor,
  which is all ir.pl relies on.
- **The fuel bounds stay unproved.** Cfg.v's walks carry fuel and give
  no answer when it runs out. The theorems are about a computation that
  answered, so a bound that is too small would make the validator
  reject a function, not accept a wrong one; the gates would show it.
- **No two blocks share a label.** `dom_closed` and `dom_edge` take
  `no_dups` of the labels, which `valid_func` checks: the successor
  map `func_cfg/2` builds keeps the last block of a label, and the
  machine runs the first.
- **The tree has no cycle because the numbering stopped.**
  `subtree_intervals/6` with fuel numbers a subtree only if its depth is
  below the fuel (`si_depth`), so a cycle under the entry is impossible
  (`si_no_cycle`), and two labels whose intervals hold each other's
  first number are one (`dom_antisym`).
- `term_eqb_refl` moved from Evidence.v to Term.v, next to
  `term_eqb_eq`, for Maps.v's lemmas.

### Offset intervals

The reuse forms bound a flight's offset from its base by
`offset_interval/8`, a memoized walk with a depth limit through the
single definitions of integer names: a narrow `ext` or load, `copy`,
`and` with a mask, `urem`, `shl` and `mul` by a constant, `add`, and
`sub` of a constant. `Interval.v` proves, with no admits, in under two
seconds:

- `offset_interval_iv`: an interval the walk answers is an `iv`
  derivation, an inductive relation with one constructor per clause of
  `op_interval/9`. The memo keeps only derived answers (`memo_ok`), so
  neither it nor the depth limit appears in the relation.
- `iv_sound`: a derived interval holds of the value a run reads, modulo
  the class, wherever each name the derivation walks holds what its
  definition computes from its operands' current values (`let_holds`).
  Which names do is the run-level invariant's to say; the lemma takes
  any set of names closed under operands.

Decisions and findings:

- **An interval holds modulo the class.** `interval_fits/3` accepts any
  `l` interval, so `add` and `mul` may leave the range of a 64-bit
  word; such an interval bounds some integer congruent to the value,
  which is what a flight's address arithmetic needs. A `w` interval
  fits, so it bounds the signed word itself, as `ext(sw)` needs.
- **A narrow load's relation does not mention memory.** Any loaded
  value, extended, lies in the narrow range, so the relation survives
  every store.
- **An operand is read where the definition ran.** `iv_sound` takes
  each walked name's value to be what its definition computed in the
  environment it ran in, with its single-definition operands unchanged
  since. An operand that is not a single definition may have been
  defined again; the clauses that walk an operand walk only single
  definitions, and the others (`and`, `urem`, a narrow `ext`) bound the
  result whatever the operand held.
- **The walk is not refactored.** The derivation is a second statement
  of the same clauses beside Validate.v's transcription, which the gates
  compare, as Evidence.v does for the evidence pass.

### Where a name is defined

`Sites.v` joins the two ways ir.pl reads a function's definitions: the
list `single_definitions/3` filters, and the sites `block_sites//1`
records for `definitions_dominate/3`. No admits.

- `once_position`: a name with a single definition has one position.
- `use_dominated`: in a function whose definitions dominate their uses,
  a single-definition name used by an instruction of a reachable block
  is defined at a site that dominates the instruction.
- `no_use_redefined`: where a single definition's site dominates a point
  of a reachable block, none of its single-definition operands is
  defined at that point, so running the point leaves the values the
  definition read. With `dom_edge` this is what keeps a definition's
  relation to its operands true along a run.

### Identities persist

The reuse forms trust a check that passed earlier. That is sound only
if the checked object is still there at the reuse: as it was, so the
check passes again, or freed, so it traps (`persists_access`).
`Identity.v` proves it of every run that starts ready
(`mreachable_persists`): a step that allocates nothing keeps every
region or frees it in place, an allocation adds an object at a base no
object had, and the runtime's safepoint keeps every identity
(`rooting`). No admits.

Decisions and findings:

- **The runtime's free keeps identities, as an axiom.** The module
  type's `free_lifetime` says every identity after a free was one
  before, not that every one before is still there. A runtime whose free
  dropped a region could give its base to a later allocation, and a
  renew that names the old object would then check the new one: a
  valid module run to `unchecked(span)`. The theorems first took
  `free_ids` as a hypothesis; mbrock's decision (November 2026) made it
  the axiom `free_keeps_ids`: free reclaims nothing, only the
  collector does, at a safepoint, where `rooting` already keeps every
  identity. `InterpRuntime` proves it (`free_res_keeps_ids`), and
  Identity.v derives `free_ids R.free` from it (`R_free_ids`), so no run
  theorem takes it any more. Its native test, axiom-identity.c, checks
  that thousands of allocations right after a free, before any
  collection, never take the freed address. Writing it showed that
  after a collection the address may recur even while a local holds the
  pointer: nanofil keeps every local in a memory slot, whose stored
  capability the collector redirects to the free singleton, while clang
  keeps it in a frame root. Both trap. The model never reuses a base,
  so the two agree on whether every access through a capability the
  program holds traps, not on its address bits after a collection. The
  test therefore checks non-reuse only before any collection.

### The single-definition invariant

Each reuse form reads a relation between single-definition names: a
flight and its base, a proof and the pointer it checked, a span test or
a limit and the pointer it read. `Single.v` proves the relation holds
along every run. In every frame (the running one unless doomed, and each
waiting caller), each single definition whose site dominates the
frame's point *replays* (`replays`). Its name holds what its
instruction's own step made, in some earlier frame that agrees with the
current environment on the instruction's single-definition operands, and
the current memory persists from the memory that step left. A check
that passed then passes again or traps (`persists_access`). A flight's
capability is its lower donor's. `mreachable_sinv` proves this for any
runtime whose free keeps identities, and `interp_sinv` proves it for the
interpreter with no hypothesis but a ready start. No admits.

Decisions:

- **The relation is the instruction's own step, replayed.** There is no
  per-op relation table: each reuse form reads what it needs off
  `inst_step` for the op it trusts.
- **Only `let`s that are not `alloc`, and flights, replay.** A call's or
  an allocation's step does not continue with a value, and no reuse rule
  reads through one. Their names still move scope correctly
  (`scope_after` for a call's result on return).
- **Memory is handled once.** Every machine step's memory persists from
  the last (`mstep_persists`), so the step lemmas carry frames only, and
  a replay's memory follows by `scope_mem`. This is where `free_ids`
  enters, now from the axiom `free_keeps_ids`.
- **A doomed frame claims nothing.** Its `check_ahead` did not pass, so
  nothing after it is trusted. A doomed frame never returns to a caller
  or calls one, so every waiting caller is undoomed.

### Reading single definitions

`Chain.v` turns `Single.v`'s invariant into what the reuse forms read.
An offset interval the validator derives (`offset_interval/8`) holds of
the value the frame reads, where its names dominate the point
(`interval_at`). Each element of a pointer's guard chain (`guard_chain/3`)
that is a single definition holds of the pointer (`guard_chain_sound`).
So two pointers that `pointer_distance/4` puts D apart share a
capability, with addresses D apart modulo 2^64
(`pointer_distance_sound`).

The first reuse form is proved from these. A raw access that the pass
accepts by `hull_covered/7` gives no `unchecked`
(`hull_access_not_unchecked`). The precondition is that the live facts
hold and their pointers' single definitions dominate the point; the
evidence invariant now carries both, so along every run there is no
`hull_covered` exception left (`run_access_checked`,
`interp_access_checked`).

- Each span the rule reads off a live fact is a check of the access's
  capability that passed (`hull_span_passes`).
- An access between the span that starts at or below it and the span
  that ends at or above it then passes too (`cap_access_hull`). This
  step needs objects ending below 2^63 ("Objects end below 2^48").

No admits.

Decisions:

- **`guard_chain` and `pointer_distance` are rewritten by equation
  lemmas, never unfolded in a hypothesis.** Unfolding makes the kernel
  compare two unfoldings 64 levels deep, and `Qed` took minutes. With
  the equations it takes 0.02 s.
- **A write through the hull needs some passed write check of the
  capability, not one of the two bounding spans.** `hull_covered/7`
  takes write rights from any span, and a passed write check shows the
  capability is not read-only.
- **"The facts' pointers dominate" is part of the evidence invariant.**
  Invariant.v's `at_pos` now says each live fact's pointer has a single
  definition dominating the point (`live_dom`), and every step keeps it.
  Inside a block this is `definitions_dominate/3`
  (`use_dominated`). A fact also reaches a block's entry over every
  incoming edge (the meet), and there it needs the converse of
  `dom_edge`: what dominates every reachable predecessor of a block
  dominates the block (`dom_meet`). That holds because at the
  Cooper–Harvey–Kennedy fixpoint each block's idom is the *nearest*
  common ancestor of its predecessors (`idoms_nca`): `common_dominator/5`
  walks up from the later label in reverse postorder, and the depth-first
  walk lists each label after a predecessor (`func_cfg_parent`), so every
  ancestor comes earlier. ir.pl needed no change.
- **The closed theorem joins two invariants.** Persistence.v leaves the
  hull case with its facts holding and dominating (`hull_case`);
  Single.v's invariant supplies the replays. Chain.v's `Hull R` joins
  them: `run_access_checked` given `spares`, and
  `interp_access_checked` for the interpreter with no hypothesis but a
  ready start. Each file instantiates `Machine R`, and `mstep` is an
  inductive new in each instance, so a run is carried across
  (`mreachable_same`).
- **The point records its index.** `point_ok` and `parked` say the
  frame runs the suffix of its block from index k, so the facts'
  dominance is stated at k.
- **`access_ok_not_unchecked` is split out of the coverage lemma.**
  Both `covered_access` and `hull_covered` end at the same step: the raw
  access's own check passes, so `inst_step` does not give `unchecked`.

### Renew and the half check

`Renew.v` proves the next three reuse forms. A renew and a half check
trust Q1, the proof of an earlier check of P1, a single definition that
the pass records as a renew source (`renew_source_op/6`). A renew of P checks the whole span
of P only if P's span lies inside Q1's at the distance
`pointer_distance/4` finds. A half check tests one bound natively and
takes the other from Q1's span (`half_known/6`). The interpreter makes
the run `unchecked` where that trust was false: Q1 of another
capability is `unchecked(alias)`; a renew whose access check fails, but
not on a freed object, is `unchecked(span)`; and a half check whose
native test (`half_bound/6`) disagrees with the whole check is
`unchecked(half)`. A renew over a hull (`renew_hull`) trusts two
sources, QL and QH, whose spans bound P's from below and above
(`hull_renewable/8`). Along every run, a frame that is not doomed runs
none of the three to `unchecked` (`run_reuse_checked`, and
`interp_reuse_checked` for the interpreter, closed).

The proof has three steps:

- Q1 is an operand of the instruction, so its single definition
  dominates the point and replays (Single.v). Q1 holds the pointer P1
  held when the check passed, and memory has persisted since, so the
  object is as it was or freed (`renew_source_holds`).
- P is a known distance from P1. Its guard chain starts at the shared
  exact base or at a flight, so P reads as a pointer
  (`distance_pointer`), with P1's capability (`pointer_distance_sound`).
  That excludes `unchecked(alias)`.
- What is left is arithmetic over `cap_access_res/7`. A renew's span
  lies inside the source's, so its check passes, traps read-only, or
  finds the object freed, and `renew_res/4` keeps each as the program's
  outcome (`renew_access`). A half check's native bound says what both
  bounds of the whole check say (`half_bound_agrees`, `half_access`).
  A renew over a hull starts E bytes above QL's span and ends F bytes
  below QH's, with E and F in [0, 2^62]. Both spans lie in the address
  space, so neither sum wraps and the two readings of P's address are
  one integer (`hull_address`). The span then lies in the object as both
  checks saw it, and it renews as a renew does (`hull_renew_access`).

The half check needed three facts that nothing stated before:

- **The source's memory lay in the address space.** `half_known/6`
  bounds the distance by 2^62 from the source's span, and the argument
  needs that span below 2^48. Once the object is freed, the current
  memory no longer records where it ended. Single.v's `replays` now
  also keeps `objects_fit` of the memory the replayed instruction left,
  which every step's readiness supplies.
- **Objects start at or above 0.** A lower half check reads its
  address signed, `base =< B` with B above 2^63 taken as negative. An
  address that wrapped below 0 then fails the native test, as the
  whole check fails. Native addresses are unsigned, so `objects_fit`
  now says each object lies in [0, 2^48], and InterpRuntime's `ready`
  says so of every object below Next.
- **A freed object is empty.** A lower half check fails on any freed
  object, while the whole check fails there only if the bounds are
  empty. Free and the end of an invocation always empty them
  (`lifetime_step`, `region_step`), but a memory the runtime is ready
  in could hold a freed object with bounds, if a run started in one.
  A new readiness obligation, `freed_bounds`, says it does not
  (runtime-axioms.md, "Readiness").

No admits. Decisions:

- **A renew does not need the source's rights.** A renew asks for its
  own rights; on a read-only object a write traps `readonly`, which
  `renew_res/4` keeps as the program's trap.
- **A malformed instruction is not the pass's concern.** A renew,
  renew over a hull or half check of another class or arity does not
  step (`reuse_shape`), so the run theorem covers every instruction of
  each op.
- **A hull's two sources meet only in the current memory.** Each
  source's check passed in a memory of its own, and both persist into
  the current one, so the object is as both saw it or freed since. An
  object QL saw live and QH saw freed is empty, so QL's check could not
  have passed. No new hypothesis or runtime fact.
- **`Reuse R` builds on Chain.v's `Hull R`.** It reuses its two
  instances and `mreachable_same`, so no new instance of the machine is
  needed.

### Guards and limits

`Guard.v` proves the two reuse forms whose evidence is not a check.

A `renew_if` of P with guard G trusts a `span_test` of N0 that G names
(`guard_covers/5`). Where G is 0, it checks, and a check is never
`unchecked`. Where G is not 0, the span test found N0+[GLo, GHi) inside
N0's object, and P's guard chain puts P's span inside that one. The
renewed access then lies inside the object as it was
(`guard_inside`), so in a memory that persists it passes, traps
read-only or misaligned, or finds the object freed (`renew_inside`):
never `unchecked(span)`.

A `check_limit` of P with U trusts a `limit` of N0 whose size is the
check's span (`limit_covers/5`), and P's lower chain reaches N0
(`lower_chain/3`). Each step of a lower chain is a flight, whose
capability is its lower donor's, so P has N0's capability
(`lower_chain_sound`). The limit then matches, and the instruction
checks: never `unchecked(limit)`.

Along every run, a frame that is not doomed runs neither to `unchecked`
(`run_guard_checked`; `interp_guard_checked`, closed). No admits, and
no new hypothesis or runtime fact.

Decisions:

- **The span's width comes from `valid_op/1`, not from the object.** A
  span test reduces its two addresses modulo 2^64 separately. Their
  difference is the span's width only because the width is below
  2^64, which `valid_op/1` ensures (both ends signed 64-bit offsets).
- **The run theorems share one context lemma.** Renew.v's `run_point`
  states what holds at the point of a frame that is not doomed, at an
  instruction that is not a raw access: the pass accepted it, single
  definitions replay, and memory is in the address space. Both run
  theorems use it.

### Facts ahead

`Ahead.v` reads back `check_ahead`'s backward pass, the first step
toward its doomed frame. `ahead_justified/3` sweeps a function's
blocks once, last first, and keeps per point the *needs*: a base N and
an offset H that every path from the point reaches by a raw access
through N, before any poll edge, back edge or end. The file states
those facts as functions of the point: `block_exit` (the meet over a
block's edges, each reading its target's entry facts from the final
table) and `facts_from` (the instructions after a point, walked
backward). It proves the sweep computes them: each block's entry facts
are what its instructions make of its exit (`ahead_entry`), and each
accepted `check_ahead` is accepted with the facts after its own access
(`ahead_accepted`).

Decisions:

- **The facts are read from the final table.** An edge reads its
  target's entry only for a later block, which the sweep has already
  finished, and labels are unique, so no later step changes it.
- **Validate.v's `ahead_justified` is split as ir.pl's is**, into
  `ahead_fold`, `ahead_block`, `ahead_edge` and `ahead_accepts`, so the
  proofs read each part on its own. Behaviour is unchanged.
- **Reading single definitions asks less.** Chain.v's
  `pointer_distance_sound` and `guard_chain_sound`, and Guard.v, now
  take `scope_plain`: every single definition but a `check_ahead`
  replays. A doomed frame keeps that, while its doomed check_ahead
  cannot replay, so the same lemmas will serve it. Renew.v still asks
  every definition to replay, since a renew's source may be a
  check_ahead.

### The doomed frame

`Doomed.v` proves the last reuse form. A `check_ahead` whose early
bytes fail yields its pointer anyway and dooms the frame
(`doomed_result/5`). The interpreter then runs it to
`unchecked(ahead(Why))` if it reaches a poll edge, a return or an
instruction that is not ahead-transparent before an access fails. The
theorem `run_doomed_checked` says this never happens in a checked
module's run: a doomed frame never steps to `unchecked` of any kind.
`interp_doomed_checked` states it under the interpreter's runtime with
no hypothesis about safepoints; like the other run theorems, the
generic one takes `spares`.

The invariant, `dinv`, says what holds of a doomed frame
(`doomed_ok`):

- its scope holds weakly (`scope_weak`): each single definition
  replays, or is a `check_ahead` holding the pointer its operand read
  (`ahead_holds`), since the check failed and cannot replay;
- for the base N and offset K Ahead.v's `ahead_accepted` gave, with
  K + Lo near, the memory still holds the doom (`doom_mem`: N + K + Lo
  lies in N's object, and the check's range does not), and the
  validator's facts at the frame's point keep a need for N of at least
  K + Hi (`need_at`).

Every step keeps it (`mstep_dinv`). The check that dooms the frame
starts it from the pass's invariant and the single definitions in
scope (`doom_start`). An ahead-transparent instruction either keeps
the need (`step_keeps`, `raise_keeps`), or is the access that meets
it, which fails by the arithmetic of "A need past 2^64" below
(`need_access_fails`) and ends the run `trap(early)`. A jump keeps it
only through a later edge with no poll, which the meet guarantees
when its need is non-empty (`doomed_jump`). A doomed frame allocates
nothing, so a fresh step is impossible (`doomed_not_fresh`), and a
safepoint frees only what keeps the doom's memory
(`doom_mem_persists`). Given the invariant, `doomed_step_checked`
rules out each `unchecked` reason: `ahead`, because the need says an
access comes first; `alias` and `limit`, because renews, hulls, half
checks and limits ask only the capability of their source, which the
weak scope gives (`renew_not_alias`, `hull_not_alias`,
`half_not_alias`).

Decisions:

- **A doomed proof holds its pointer, not a passed check.** Reuse
  rules read only the pointer and its capability of it; `scope_weak`
  says exactly that, and `scope_plain` (Ahead.v) is what the reuse
  lemmas ask.
- **The need is carried as the validator's own facts at the frame's
  point.** Each step of the frame is a step of the backward walk read
  forward, so no new analysis is needed.
- **The access meeting the need is not located in advance.** Any
  access that raises the need past N + K + Hi fails; the need only
  says that one comes before the frame leaves the scheduled region.
- **`distance_pointer` moved to its own section in Renew.v**, which
  assumes only `scope_plain`, so the doomed frame's renews use it.

### No run is unchecked

`Soundness.v` assembles Campaign 3's theorem. `valid_no_unchecked`
says: in every state of a run of a checked module's function that
starts ready, `step` never answers `Done (Unchecked w)`. Its proof
reads each place an `unchecked` can come from and hands it to the run
theorem for that place:

| Source | Run theorem |
|---|---|
| a frame a `check_ahead` doomed | Doomed.v's `run_doomed_checked` |
| a raw load, store or call | Chain.v's `run_access_checked` |
| a renew, a renew over a hull, a half check | Renew.v's `run_reuse_checked` |
| a `renew_if`, a `check_limit` | Guard.v's `run_guard_checked` |
| the runtime's free | Runtime.v's axiom `free_checked` |

A frame that is not doomed steps to `unchecked` only where its next
instruction's result is (`step_unchecked_inst`): block entry, jumps and
returns give no such outcome. Of instructions, only a raw access, a
raw call, a reuse form, or a call of `free` can (`inst_unchecked_source`);
every other op either succeeds, traps or is undefined behaviour. The
validator reads a raw access only when its address is a temporary
(`raw_access/5`), and `raw_tmp` shows a checked module has no other:
`valid_use/3` never reads a global at class `a` nor a constant at a
proof class.

`interp_valid_no_unchecked` states it under the interpreter's runtime
with no hypothesis beyond the run starting ready; `Print Assumptions`
reports it closed.

What the theorem covers and what it does not:

- **The module is checked by Validate.v's `valid`**, which the gates
  compare with `ir:valid_module/1`, not by ir.pl itself.
- **External calls other than `free` are stuck** in the model, so the
  theorem says nothing about runs past them; Campaign 4's contracts
  extend the machine there.
- **The generic theorem has one runtime hypothesis**, `spares` ("The
  runtime's safepoints" above), which the interpreter's runtime
  satisfies. That free keeps identities and never answers `unchecked`
  are the module type's axioms `free_keeps_ids` and `free_checked`.
- **A run starts ready**, a hypothesis until the heap starts above the
  module's data.

Decisions:

- **`free_checked` is an axiom** (mbrock's decision, November 2026),
  with the native test axiom-free.c: free of null or a live heap
  object's base returns, and a second free, an interior pointer or a
  global's address traps. `InterpRuntime` proves it
  (`free_res_checked`).
- **The theorem is stated over Guard.v's machine instance**, the one
  Chain.v's, Renew.v's and Guard.v's run theorems share; a run is
  carried over to Doomed.v's instance (`mreachable_doom`).

## A need past 2^64

Planning the proof for `check_ahead`'s doomed frame turned up a module
ir.pl accepted and the interpreter ran to
`unchecked(ahead(out_of_bounds))`, where the reference program returns
normally: a counterexample to `valid_no_unchecked`, and a false early
trap natively.

A check_ahead of P = B + K is justified when every path ahead reaches
an access through B ending at B + H, with H at least K + Hi
(`ahead_insts/8`). The rule kept K and H within 2^62 of 0
(`near_offset/1`), so each is a true signed distance from B, but not
K + Lo. In `tests/unit.pl`'s case, B = a - (2^62 - 8) and
P = B - 2^62, so K = -2^62, and the check's Lo is -2^63: P + Lo is a + 8
modulo 2^64. A later access of B's bytes [2^62 - 8, 2^62) has H = 2^62,
far past K + Hi = -3 * 2^62 + 16, but its address is a itself. The
check's start and the need's end, 2^64 - 8 apart as integers, wrapped
onto each other: the access passed, and the doomed frame reached its
return.

The fix follows the existing rule: ir.pl's `ahead_insts/8` and
`widened/5` in schedule.pl, which emits check_ahead, both ask that K + Lo
be near too (Validate.v transcribes it). The access a path runs ends at
some H' of at least K + Hi and at most 2^62 (`raise_need/6`), so
H' - (K + Lo) bytes after P + Lo, at most 2^63; P + Lo lies in an object
below 2^48, so neither address wraps: where [Lo, Hi) failed, the access
fails too. Bounding the need instead would not do, since the meet over
a branch keeps the least need while the other arm's access may end at
2^62. Oracle reviewed the fix. The pass widens the same 55 checks in
tests/c with the bound as without it (docs/schedule.md, review
finding 3).

## An object past 2^64

`rocq/tests/huge-object.ir` allocates an object of 2^64 - 2^32 - 80
bytes and then one of 256, which the interpreter's allocator (Next only
adds) places 64 bytes below 2^64. A check of the second object's bytes
[0, 128) passes, and a raw load at offset 64, which the check covers,
wraps to address 0 and runs `unchecked(out_of_bounds)`. ir.pl accepts
the module, and the model agrees with the interpreter: a counterexample
to `valid_no_unchecked` over the interpreter's runtime, found by the
coverage lemma's proof rather than by a test.

The interpreter was more permissive than native code. The pinned Fil-C
refuses a heap object of more than 2^48 - 1 bytes before allocating
("filc safety error: attempt to allocate object that is too big",
`filc_prepare_allocate_object`), and one within that limit that the
address space cannot hold ("filc safety error: out of memory", at 2^47
here), so no native object ends above 2^64. The fix, Campaign 3's third
milestone, follows native code:

- **Too big is the op's.** `alloc_res/6` traps `too_big` for a size
  over `max_allocation_size/1` (2^48 - 1) before anything is allocated,
  as Ops.v's `alloc` does, for every runtime. huge-object.ir now traps
  there.
- **Out of memory is the runtime's.** The runtime's `alloc` returns
  `None` where it cannot hold the object, and the run ends
  `trap(out_of_memory)` (Run.v's `Driver`); Machine.v has no step there.
  Which allocations fail natively depends on the machine, so the module
  type lets any runtime refuse. The interpreter's address space ends at
  2^48, libpas's (`address_space/2`): an allocation whose Next would
  pass it fails, whether a heap object, a named local or a variadic
  callee's argument snapshot. Plain mode keeps no limit. Natively the
  snapshot is a heap object (`filc_promote_args_to_heap`) but a named
  local is a stack frame slot, so a local's `out_of_memory` exists only
  in the interpreter and the model; and native memory ends well before
  2^48, so sizes the interpreter allocates may trap natively, as any
  runtime may refuse.
- **The axioms bound the object.** `fresh` asks that the object end at
  or below 2^64, and the new axiom `address_space` that no object of a
  memory the runtime is ready in ends past it (`objects_fit`, now in
  Runtime.v; since tightened to 2^48, below). `InterpRuntime` proves both: its `ready` keeps Next at
  most 2^48. The native test is
  [axiom-address.c](../tests/c/prog/axiom-address.c): objects end below
  2^48, `malloc(2^48)` traps, and so does `malloc(2^48 - 1)`, which is
  within the size limit, so a runtime may refuse.
- **Fixtures.** huge-object.ir's runs cover the size limit and its
  boundary and an out-of-memory heap object, named local and argument
  snapshot (the model agrees on all nine). `tests/filc/alloc-limit.ir`
  runs in difftest with and without `-O`; difftest counts every safety
  error as a trap, so axiom-address.c checks the two messages.
- **The middle end.** Translation validation (`refines/2`, opt.pl) lets
  an optimized program run on where the original ran out of memory,
  since a refusal is the runtime's choice; `too_big` must stay.
  promote, which removes the allocs it promotes, keeps a Fil-C alloc
  over 2^48 - 1 bytes, or of a negative constant, which is 2^64 or more
  at `l` (`size_allocates/2`); alloc-limit.ir's `dead_too_big` and
  `dead_negative` failed `-O` validation without that. No other pass
  removes an alloc.
- **Reviewed.** An Oracle review confirmed the model transcribes the
  change (the size test, the three refusal sites, the strides) and the
  `too_big`/`out_of_memory` boundary natively, and found the `-O`
  validation failure, an axiom test that did not pin the boundary, and
  the open gap below; a second review of the fixes found promote still
  removing an alloc of a negative size.

Initial readiness is a hypothesis. A valid module's initial memory need
not be ready. ir.pl accepts `zero(N)` data of any size, and
`initial_memory/4` lays data out from 65536 with no limit, so data can
reach past 2^32, where heap objects start and overlap it, or past 2^64,
where a covered access wraps again: with `data(big, export, 16,
[zero(2^64)])` and a flight to 64 bytes below 2^64, `valid` accepts the
module and the model runs it `unchecked(out_of_bounds)`, as the review
showed. The interpreter cannot build such data (`item_bytes/3` makes
every zero byte and overflows its stack), so the gates do not see it.
Natively an 8 GiB global compiles and runs.

mbrock's decision: `valid_no_unchecked` takes "the run starts ready"
(`R.ready` of the runtime's start and the initial memory) as an explicit
hypothesis, as the machine's theorems already do, and the IR is
unchanged. Bounding filc data in `valid_module/1` at 2^32 was rejected:
it refuses static data the native toolchain accepts.

The planned long-term fix is to start the heap above the module's data:
the runtime's start state would depend on the module (for the
interpreter, Next from the end of the data layout, rounded up, rather
than `stack_base/1`'s fixed 2^32), so that every valid module whose data
fits the address space starts ready, and the hypothesis becomes a lemma.
Data past the address space would then be refused as the runtime
refuses an allocation it cannot hold. That changes interpreter semantics
and the module type's `start`, so it needs an Oracle review.

### Objects end below 2^48

`objects_fit` said every object ends at or below 2^64. That is enough
for one check: a covered access does not wrap (Coverage.v). It is not
enough for `hull_covered/7`, which joins the spans of several checks of
one object, related through `pointer_distance/4`, with each offset
within 2^62 of the access's base (`near_offset/1`), all modulo 2^64. Two
spans of an object are on the same side of the wrap only if the object
is smaller than about 2^63. So a runtime could be ready in a memory with
an object [2^16, 2^64 - 2^20), such as a large `zero(N)` data item, and
p 8 bytes below its end. Then a check of p+[0, 8) passes, a check of
[0, 8) through a flight at p + 2^62 - 8 passes after the address wraps,
inside the object, and an access at p+8, between the two spans, lands at
the object's end: `hull_covered` accepts it, and the run is
`unchecked(out_of_bounds)`. `valid_no_unchecked` over every runtime was
false as the axioms stood. The counterexample cannot arise in the
interpreter, whose `ready` keeps every object below 2^48, nor natively.
An end bound below 2^63 is enough for the hull, even for spans whose hi
is below their lo.

The same bound supplies what `half_known/6` and `hull_renewable/8`
assume of a checked address, that it is a user address below 2^56: under
the old axiom, a half check testing only the upper bound of a huge object
could have wrapped below its lower.

mbrock's decision: tighten the axiom to native's bound.
`objects_fit` now says every object ends at or below 2^48, libpas's
address space (`PAS_ADDRESS_BITS`), which is what
[axiom-address.c](../tests/c/prog/axiom-address.c) tests, for heap
objects, static and initialized data and an address-taken local; native
Fil-C also stores object addresses in 48 bits
(`FILC_OBJECT_AUX_PTR_MASK`).
`InterpRuntime` proves it unchanged: Next is at most 2^48. The
coverage lemma holds a fortiori. The alternatives were a hypothesis
on the hull theorem, and a width bound in ir.pl's hull rule, a validator
change with no native motivation. Initial readiness stays a hypothesis;
with this bound it also keeps a ready module's data below 2^48.

## Next

1. Starting the heap above the module's data, so that the initial
   readiness hypothesis becomes a lemma.

Inquiries touched: none closed. The integer-at-`p` case is a small
input to the integer-to-pointer inquiry.
