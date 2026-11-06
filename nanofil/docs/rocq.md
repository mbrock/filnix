# Campaign 1: the core model in Rocq

November 2026. This note reports on Campaign 1 of [formal.md](formal.md),
which builds on [campaign.md](campaign.md): what exists, the decisions
taken, what the transcription clarified, and what is left. The
development is in `nanofil/rocq/` and is checked by
`nix build .#checks.x86_64-linux.nanofil-rocq`.

## What exists

A Rocq 9.1 development, built with the Rocq and stdlib of the flake's
pinned nixpkgs. It contains no `Admitted`, no `Axiom` and no `Parameter`,
and the Nix check fails if any appears. Each file is a transcription of
the interpreter and cites the predicate it copies.

| File | Transcribes | Contents |
| --- | --- | --- |
| `Term.v` | ground Prolog terms | names (temporaries, labels, symbols) as terms compared by `==`; `char_code/2` |
| `Ieee.v` | ieee.pl | binary32, binary64 and x87 extended as bit patterns: `decode/4`, `round_ratio/5`, `ieee_binary/5`, `ieee_convert/4`, `ieee_compare/5`, `ieee_from_int/3`, `ieee_to_int/3` |
| `Syntax.v` | ir.pl's header tables | classes, ops, values, instructions, jumps, blocks, functions, data, modules; `op_arg_classes/4`, `evidence_preserving/1`, `ahead_transparent/1`, `local_objects/2` |
| `Values.v` | interp.pl's values | `cap` (`none`, `obj`, `ro`, `fn`, `ext`), `ptr`, `word`; `word_at_class/3` |
| `Memory.v` | interp.pl's Memory section | regions, `mem`, `cap_access_res/7`, `free_res/4`, bytes and aux, `fresh` |
| `Ops.v` | `alu/4`, `additive_res/4`, `kind_res/8` | integer and float ops, `check` and the reuse vocabulary, raw loads and stores, pointer-load and pointer-store protocols, `va_arg` |
| `Semantics.v` | `run/5`'s blocks, instructions, jumps, calls | the configuration, `step`, `step_rel`, `reachable`; the variadic entry snapshot |
| `Run.v` | `initial_memory/4`, `alloc_base/6` | module preparation, the interpreter's allocator as one fresh choice, a driver |
| `Validate.v` | ir.pl's `valid_module/1` | `valid_func`, `valid_data`, `valid_alias`, `valid_items`, `valid`: uses, ops, instructions, dominance, locals, the evidence pass, the reuse rules, `polls_every_cycle`, data linkage and items, aliases |
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

## The gate

`nanofil outcomes FILE` (main.pl, a new command) prints the checked
module that `difftest` would compare, then `interp:run/5`'s outcome on
each run line, as terms. [rocq/agree.sh](../rocq/agree.sh) pipes that
output into the extracted model. The model decodes the module, runs
every line, and prints `agree`, `disagree`, `outside` or `stuck_both`
for each; the script fails on any disagreement.

The Nix check runs `rocq/tests/*.ir` once with the reference checks.
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
(dominators by fixpoint), named locals are declared once in the entry
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
appended, the object renamed or deleted. An alias's: its linkage, its
target and its name changed, or the alias deleted. And up to 150 items
inserted: an alias of each kind of target, under a fresh name and under
the name of a function the module calls without defining, and a data
object of each linkage. `valid_module/1` judges each changed module, and
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
| `rocq/tests/reuse.ir`, `snapshot.ir`, `floats.ir` (reference checks) | 111, 145, 46 | 0 | 0 |

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
- **`nat` extracts to OCaml's `int`.** The model's `nat`s count list
  elements and fixpoint rounds. Unary, the bound of `dominators` (the
  square of the reachable block count) overflowed the stack on Lua's
  `luaV_execute`, which has 995 blocks.
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
- **ir.pl does not check the shape of a data item.** Only three
  things about items are checked: float items are `const(N)` in range,
  strings hold bytes, and a Fil-C module has no `item(l, sym(_, _))`.
  `data(x, export, 8, [item(w, foo), bar])` is valid. The model accepts
  the same, so its `ItemOther` items are valid and stuck. Campaign 3's
  statement about data needs the interpreter's layout to be total on
  valid modules, or the validator to check the shapes the layout reads.
- **A data object's name is not checked against its uses.** Deleting
  or renaming a data object is valid unless an alias targets it or
  has its new name: a symbol the module does not define is external,
  which a Fil-C module may name. So `valid` says nothing about whether a global names data
  or a function; the runtime decides.
- **The symbol table keeps the first item of each name.** An alias's
  call check reads only the first function of each name, as
  `module_symbols/2` indexes them; the model does the same.
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

## Next

1. Transcribe `cfg_idoms/2` (Cooper, Harvey and Kennedy) and
   `dom_intervals/3` for `dominators`, with maps instead of lists for
   environments and label sets. The present fixpoint over label sets
   is roughly cubic in the block count: the validator does not finish
   Lua's lvm.c (`luaV_execute`, 995 blocks) in half an hour, though
   valid_module/1 judges it in a second. The gate's corpus has no such
   function, so this is speed, not agreement.
2. The Campaign 2 `Module Type Runtime`: `fresh` and the lifetime facts
   of `Memory.v` are the first candidates to move into it.

Inquiries touched: none closed. The integer-at-`p` case is a small
input to the integer-to-pointer inquiry.
