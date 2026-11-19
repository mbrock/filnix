# Proving glibc at scale: specifications, regions, and compiler changes

This document is a design note for the next stage of the userland glibc proof campaign. It builds on [the formal campaign](formal.md), [the program logic](logic.md), [the runtime syscall boundary](zsys.md), and the concrete findings recorded in [Proving GNU Hello over userland glibc](hello-glibc.md). Where those pages establish why the campaign proves compiled C library code down to runtime system-call wrappers, this page examines the structure of the glibc proof tree itself and sets out how to make proofs of real compiled C easier to read, faster to check, more meaningful as C specifications, and resilient when the compiler changes.

> The diagnosis and measurements below reflect the repository at commits `decc6bdbad` and `fe74b8bf`, incorporating a specification-testing experiment and design review from GPT-6.2-Astra together with an architectural critique from Fable 5.2. None of the proposed tools or metatheorems described in Sections 3 through 7 exist yet unless the text links to an existing module.

## 1. Where the glibc proofs stand

The Rocq development under [rocq/](../rocq/) now spans roughly four hundred thousand lines, split between foundational theories in `rocq/theories/` and the userland glibc 2.44 proof tree in `rocq/glibc/`. At revision `decc6bdbad`, the tree breaks down as follows:

| Area | Hand-written files / lines | Generated files / lines | Role in the development |
| --- | ---: | ---: | --- |
| `theories/core`, `soundness`, `external` | 35 / 23,454 | — | IR syntax in [Syntax.v](../rocq/theories/core/Syntax.v), IEEE floats, small-step semantics in [Semantics.v](../rocq/theories/core/Semantics.v), [Runtime.v](../rocq/theories/core/Runtime.v) axioms, and [valid_no_unchecked] in [Soundness.v](../rocq/theories/soundness/Soundness.v) |
| `theories/logic` | 16 / 16,069 | — | Identity-keyed [[iris]] heap pieces in [Pieces.v](../rocq/theories/logic/Pieces.v) and [Heap.v](../rocq/theories/logic/Heap.v), instruction rules in [Logic.v](../rocq/theories/logic/Logic.v), SWAR lanes in [Lanes.v](../rocq/theories/logic/Lanes.v), and constant-time logic in [PoisonLogic.v](../rocq/theories/logic/PoisonLogic.v) |
| `theories/exec` | 9 / 6,843 | — | Abstract interpreter in [AbsRun.v](../rocq/theories/exec/AbsRun.v), cut-invariant inference in [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), and [[weakest-precondition]] soundness in [AbsSound.v](../rocq/theories/exec/AbsSound.v) |
| Standalone program and former Hello proofs | 87 / 41,688 | — | This historical count includes the now-removed proof of Hello against per-function libc contracts. |
| `glibc` | 827 / 133,728 | 587 / 179,668 | Userland glibc 2.44 proofs across `libio`, `hello`, `stdio`, `getopt`, `startup`, `string`, `intl`, `zsys`, `stdlib`, `nptl`, and `locale` |

### Four proof generations coexist

As the glibc proof tree grew past eight hundred hand-written files, four distinct ways of proving compiled IR emerged. Each generation removed a bottleneck of the previous one, yet hit a boundary that kept earlier styles in active use even in recent wide-stream `libio` commits such as [LibioWOverflowAllocateSteps.v](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v):

| Generation | Core modules | Adoption across 827 glibc files | What it solves | Why proofs still fall back |
| --- | --- | ---: | --- | --- |
| 1. Manual [[ssa]] stepping | [GlibcTactics.v](../rocq/glibc/tactics/GlibcTactics.v), [GlibcEnv.v](../rocq/glibc/base/GlibcEnv.v) | ~750 files: 347 name raw `"v43"` temporaries, 306 name `"L28"` labels, 326 thread [keeps] | Handles any [[separation-logic]] invariant, mid-block cuts, indirect vtable calls, and `free` | Couples lemmas and scripts to [[temporary]] numbers, [[block]] labels, check flavors, and instruction counts; accumulated 243 private tactics |
| 2. Reflective symbolic execution | [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v), [GlibcSymFunc.v](../rocq/glibc/tactics/GlibcSymFunc.v), [GlibcSymCall.v](../rocq/glibc/tactics/GlibcSymCall.v) | 6 proof files outside `GlibcSym*` | Executes whole blocks or bounded DAGs in one `vm_cast_no_check` step without `iFrame` search | Quotes only flat `live`, `icell`, `pcell`, and `bytes` atoms; rejects `int_cell`, [struct_at], narrow stores, [c_env], and domain pointer-load rules |
| 3. Whole-function abstract checking | [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), [AbsRun.v](../rocq/theories/exec/AbsRun.v), [AbsSound.v](../rocq/theories/exec/AbsSound.v) | 10 files in [CpuSound.v](../rocq/glibc/startup/CpuSound.v) covering 16 CPU-init functions | Infers loop invariants and checks whole functions by `vm_compute` | Requires [StoreStable] world invariants, exclusive whole-object ownership, static object sizes, and manual correspondence bridges in [CpuSpec.v](../rocq/glibc/startup/CpuSpec.v) |
| 4. C frames, layouts, and block tables | [CFrame.v](../rocq/glibc/tactics/CFrame.v), [CStruct.v](../rocq/glibc/tactics/CStruct.v), [CBlocks.v](../rocq/glibc/tactics/CBlocks.v) | 18 to 43 files, centered in `stdio` such as [PrintfWrite.v](../rocq/glibc/stdio/PrintfWrite.v) | States cuts by C variable name, eliminates numeric field offsets, and closes loops once via [blocks_close] | Steps instructions manually inside each block, hardcodes `"L15"` labels and numeric row indices, and falls back to raw SSA names on arithmetic temporaries |

The survey also examined how proofs use generated files.

1. Across `rocq/glibc/`, 127 generated `.v` files—mainly `*Src.v`, `*SrcNN.v`, and `*Module.v` sidecars—lack the phrase `"Do not edit"` in their first thousand bytes, so site rendering, cross-file indexing, and grammar checks do not skip them automatically.
2. Hello image proofs now import functions by symbol. For example, [LibioWOverflowDispatch.v](../rocq/glibc/libio/LibioWOverflowDispatch.v) imports the function family `HelloImageTypedIO`. Its import stays valid when an earlier function grows.

## 2. Architecture of the proposed proof stack

Nanofil already executes regions of checked IR symbolically and justifies the result in Iris. What authors lack is a single specification vocabulary shared between random testing and Iris proofs, a way to attach field-level ownership refinements where Fil-C's memory model demands them, and a compilation boundary that hides check-reuse optimizations from library lemmas.

```diagram
 C unit + C-level RegionSpec    c_pp.pl, c_lower.pl, opt.pl, --checks=reference
    │  spec tester + mutants       interp.pl / Transport.judge + shared atom specs
    ▼
 tested contract & witnesses    counterexample, witness, or mutant survival
    │  region validation           GlibcSymFunc.sym_func_rule + field entailments
    ▼
 reference-stage Iris triples   linked across glibc without Renew or HalfCheck
    │  closed pass simulation      Gallina reuse_refines -> labelled_safe
    ▼
 shipped combined binary        never_panics on the optimized check stream
```

Two cross-cutting design choices keep this stack small and prevent the codebase from accumulating a fifth coexisting proof style:

- First, Sections 3 and 4 share one reified assertion language. In [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v), the inductive types [GlibcSym.atom], [GlibcSym.ob], and [GlibcSym.facts] together with [GlibcSym.heap_den] already form a reified separation-logic fragment. Extending that fragment with user-defined predicates lets a single specification drive the Iris denotation, the reflective symbolic executor, and the specification tester's witness generator and permission mask. Keeping two separate contract languages in Prolog and Rocq would invite specification drift, which is the exact failure mode Section 3 exists to eliminate.
- Second, the region lifter consolidates Generations 2 and 4 rather than adding a fifth generation alongside them. Concretely, the lifter is [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v) extended with user predicates, [CFrame.v](../rocq/glibc/tactics/CFrame.v) variable names, and [CStruct.v](../rocq/glibc/tactics/CStruct.v) field lenses to replace Generation 4's manual intra-block stepping. Once a module's block proofs run through that combined path without per-instruction Ltac, its Generation-1 and Generation-4 stepping wrappers retire.

The remaining sections detail the four parts of the stack:

1. Section 3 tests specifications against both captured IR and code mutants before proving them, using language-neutral witnesses shared between SWI-Prolog and the extracted Gallina machine.
2. Section 4 checks C-emitted `RegionSpec` summaries against `--checks=reference` IR via syntax-free pointer-resolution entailments keyed by C struct fields.
3. Section 5 sharpens interactive stop diagnostics, precondition abduction, struct field lenses, provenance-checked cut selectors, and whole-image census metrics.
4. Section 6 scales abstract certificate checking in `theories/exec/` and proves closed check-pass simulation from `reference` to `combined` so library triples never see check optimizations.

## 3. Testing specifications against captured IR

In [Proving GNU Hello over userland glibc](hello-glibc.md), several expensive detours began when a proof author wrote down a plausible C specification that disagreed with the compiled library code on an edge case: `c: __isatty_nostatus` overwrote `c: errno` with `ENOTTY` when standard output was a pipe, an assumed contract for `c: _IO_unsave_markers` named byte offset `72` instead of `80`, the `TCGETS2` request constant in [OsIoctl.v](../rocq/glibc/zsys/OsIoctl.v) carried a one-digit decimal transcription error, and `c: puts` left zero pending bytes with `c: stdout->_mode` set to `-1`. Constant transcription bugs such as `TCGETS2` should be eliminated at the source by extracting header constants through nanofil's own C preprocessor via `c_pp:pp_file/3` in [c_pp.pl](../src/c_pp.pl) rather than copying decimal literals into Rocq by hand. For semantic edge cases, a specification tester over `interp:run/5` in [interp.pl](../src/interp.pl) falsifies bad contracts in milliseconds before anyone starts an Iris proof.

### A prototype experiment on `__isatty_nostatus`

To test this workflow against real captured code at `decc6bdbad`, GPT-6.2-Astra extracted the compiled body of `c: __isatty_nostatus` from `SysCode.v`, initialized a modeled `c: errno` cell to `7`, and executed the function in [interp.pl](../src/interp.pl) against two small `zsys_ioctl` stubs. Every test module passed `ir:valid_module/1`:

| Modeled `zsys_ioctl` behavior | Return value | Final `errno` | What the run establishes |
| --- | :---: | :---: | --- |
| Succeeds and leaves `errno` alone | `1` | `7` | Exercises the terminal path |
| Fails and writes `ENOTTY` (`25`) | `0` | `25` | Refutes any specification claiming `c: __isatty_nostatus` preserves `errno` |
| Stub checks historical typo `2150389802` instead of `2150388778` | `0` | — | Reaches the stub's rejection branch and exposes the constant mismatch despite passing `ir:valid_module/1` |

This small wrapper also exposes a sharp constraint on static read-only analyses: the IR body of `c: __isatty_nostatus` contains no store instruction at all, yet calling `zsys_ioctl` mutates both `c: errno` and the stack `kernel_termios` buffer. Any purity check for fractional ownership must consult callee and [[external-call]] summaries rather than scanning a function's instructions for stores.

At the same time, this flat-memory prototype covers only two of the four historical bugs cited above. Catching offset `72` versus `80` in `c: _IO_unsave_markers` and `c: puts` leaving `c: stdout->_mode` at `-1` requires generating structured `c: FILE` heap witnesses. Replaying every specification-fix commit in the git history will establish a concrete retrospective recall rate for the generator.

### Shared assertions, neutral witnesses, and specification mutation

The closest prior art is the [CN](https://www.cl.cam.ac.uk/~pes20/pldi2026-paper155-supplementary.pdf) group's *Code-Specify-Test-Debug-Prove* workflow and their [Fulminate](https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/43/Fulminate-Testing-CN-Separation-Logic-Specifications-in-C) framework for testing separation-logic specifications in C. Fulminate shows why testing separation-logic contracts requires more than concrete memory: a live object can hold a physically readable byte even when the caller's contract lent the callee no permission to read that offset.

Building the tester directly on the extended [GlibcSym.atom] language gives four capabilities at once:

- The generator derives both concrete initial heaps and an explicit lent-piece permission mask from the same reified precondition that [GlibcSym.heap_den] interprets in Iris, pairing computable shape checks with soundness lemmas on the pattern of [str_shape_b_sound] in [WordString.v](../rocq/glibc/string/WordString.v).
- Encoding each shrunk witness—initial heap, permission mask, and external-response script—in a language-neutral format such as [NFB](nfb.md) or shared term records lets both `interp:run/5` in SWI-Prolog and a widened [Transport.judge] entry point in [Transport.v](../rocq/theories/core/Transport.v) replay the identical run, providing free differential testing between the Prolog and extracted Gallina semantics.
- The runner separates `counterexample`, `entry_witness_found`, and `search_exhausted` verdicts. On proof debts such as the former `hd_close_stdout_wide` premise in [HelloGlibcDebts.v](../rocq/glibc/hello/HelloGlibcDebts.v), concrete heaps satisfy the quantified [GlibcSpec.fn_triple] entry shape and report `entry_witness_found`, while injecting a write error yields a `counterexample` naming the `c: strerror` and `c: dcgettext` path whose locale state the caller omitted.
- Running a specification against surviving semantic [[mutant|mutants]] of the C unit measures whether the postcondition actually states what the function computes rather than merely asserting memory safety, while invariants that hold across all tested traces can feed straight into [AbsInfer.verify] as untrusted loop candidates.

## 4. Lifting IR regions with field-keyed entailments

Two long-term ideas reinforce each other here. The first validates low-level IR against structured summaries in the spirit of [AutoCorres](https://trustworthy.systems/publications/nictaabstracts/Greenaway_AK_12.abstract.html) and [Katamaran](https://icfp22.sigplan.org/details/icfp-2022-papers/8/Verified-Symbolic-Execution-with-Kripke-Specification-Monads-and-no-Meta-Programming). The second automates resource framing through syntax-directed ownership refinements in the spirit of [RefinedC](https://plv.mpi-sws.org/refinedc/), showing both what stops [GlibcSym.sym_sound] today and how to state a generic pointer-load rule cleanly over [Logic.wp_read_with].

### What `load_narrow` hides in wide-stream overflow

In `c: _IO_wfile_overflow`, right after `c: _IO_doallocbuf` returns, glibc resets the three narrow read cursors `c: _IO_read_ptr`, `c: _IO_read_end`, and `c: _IO_read_base` to `c: _IO_buf_base`. In the `--checks=combined` capture of `__GI__IO_wfile_overflow`, that single C action compiles into sixteen checked IR instructions: three pointer loads, three pointer stores, four pointer-offset calculations, four [[half_check|half-checks]], and two [[renew|renewals]].

In [LibioWOverflowAllocateSteps.v](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v), the lemma [wp_wo_after_alloc] proves those sixteen instructions by hand:

```rocq
Lemma wp_wo_after_alloc e ch vb fb fr fl f2 nb wd wr w b stop Φ :
  0 < fb -> fb mod 8 = 0 -> fb+224 <= r_end fr -> r_end fr <= 2^63 -> in_buf fb nb b -> wo_setup_regs e fb ch ->
  wo_cells vb fb fr fl f2 nb wd wr w [null;null;null;null;null;null;b;stop] (wo_new_wide wd w) -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗ wo_cells vb fb fr fl f2 nb wd wr w [b;b;b;null;null;null;b;stop] (wo_new_wide wd w) -∗
    WP (block ee "L49") {{ Φ }}) -∗ WP (run e wo_after_alloc) {{ Φ }}.
Proof using Type.
  intros Fb Fa Fe Fr B (Hfp & Hch & Hck & H7).
  iIntros "(Hf & Hfl & Hf2 & Hfd & Hm & Hvt & Hwd & Hp & Hnb & Hl & Hw & Hwvt & Hb) HK".
  iDestruct "Hp" as "(P0 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & _)". change (off_ptr 6) with 56.
  change (off_ptr 0) with 8. change (off_ptr 1) with 16. change (off_ptr 2) with 24. unfold wo_after_alloc.
  do 2 step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P2".
  step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P0".
  step. check "Hf". load_narrow "P6". check "Hf". store "Hf" "P1". do 2 step.
  iApply ("HK" with "[%] [-]"); [unfold wo_setup_regs; split_and!; lookups; done|]. rewrite /wo_cells /=. by iFrame.
Qed.
```

Look closely at what the local tactic `load_narrow "P6"` proves on each read of `c: _IO_buf_base`. In Fil-C, loading a pointer with `LowerResolve` requires more than owning the `c: FILE` object's [[live]] token and the eight-byte pointer cell at offset `56`. Because [[fugc|FUGC]] can sweep capabilities to freed objects at a safepoint, [Logic.v](../rocq/theories/logic/Logic.v) asks for proof that the *target* capability stored in `c: _IO_buf_base` has not been freed: `~ freed_in (m_regions (ls_mem σ)) (ptr_cap b)`. For an idle or newly allocated stream buffer, three cases arise:

1. If the stored buffer pointer `b` is null, `CNone` is never freed and the load needs no target lifetime.
2. If `b` points into the stream's inline one-byte `c: _shortbuf`, its capability is `Obj fb`, so the `c: FILE` object's own `live fb fr` token already proves `fb` is not freed.
3. If `b` points into a separate heap buffer, `buf_idle nb` in [wo_cells] of [LibioWOverflowLoan.v](../rocq/glibc/libio/LibioWOverflowLoan.v) proves that second heap object is not freed.

In [LibioFflushIdle.v](../rocq/glibc/libio/LibioFflushIdle.v), [wp_load_buf_ptr] proves those three cases together, yet its statement is tied directly to the instruction syntax `Let d P (RawLoadPointer off [AuxRead; LowerResolve; AddressRead])`. A reflective executor cannot apply an Iris weakest-precondition lemma mid-computation, and [Logic.wp_raw_load_pointer_in] in [Logic.v](../rocq/theories/logic/Logic.v) cannot cover the inline `c: _shortbuf` case by putting `fb` into a separating `pts ps` piece list because `live fb fr` already owns `PLive fb`.

### Syntax-free field entailments and C-emitted `RegionSpec` summaries

Inspecting [Logic.wp_read_with] in [Logic.v](../rocq/theories/logic/Logic.v) reveals a cleaner split between the executor's generic pointer-load rule and domain invariants:

1. First, domain modules register syntax-free target-resolution entailments keyed by C struct field rather than instruction-tied weakest-precondition rules. To resolve a pointer `x` loaded from an object `fb` whose `live fb fr` token the executor already holds, a generic pointer-load step rule only needs a framed resource `R` satisfying a pure state-agreement entailment: together with `heap_interp σ` and `live fb fr`, `R` implies `~ freed_in (m_regions (ls_mem σ)) (ptr_cap x)` without consuming `live fb fr` or `R`. That single entailment covers null pointers, self-referential `c: _shortbuf` pointers (`Obj fb`), and external `buf_idle nb` heap buffers uniformly without case-splitting in the executor or introducing non-separating conjunctions into user assertions. Moreover, rather than scanning the proof context heuristically for `in_buf`, provenance already records that the load reads `c: fp->_IO_buf_base`: the sidecar attaches the refinement to the C field `struct _IO_FILE._IO_buf_base`, and the compiler emits untrusted hint indices that Rocq checks during replay. Call-boundary borrows such as [word_string_borrow] in [WordString.v](../rocq/glibc/string/WordString.v), where word-at-a-time string routines share an aligned boundary word between prefix and suffix, register analogous syntax-free split-and-wand entailments on user atoms.
2. Second, [c_lower.pl](../src/c_lower.pl) emits the first-order `RegionSpec` from the C statement tree rather than extracting it back out of compiled IR. Extracting `RegionSpec` from IR would only restate the IR. Having [c_lower.pl](../src/c_lower.pl) emit a small, deliberately bounded C-effect summary—here, setting `c: _IO_read_ptr`, `c: _IO_read_end`, and `c: _IO_read_base` to `c: _IO_buf_base`—makes the check genuine per-region translation validation: [GlibcSymFunc.v](../rocq/glibc/tactics/GlibcSymFunc.v) replays the `--checks=reference` IR region via [sym_func_rule] and verifies by `vm_compute` that the compiled blocks refine the C-level field effects.

Crucially, provenance-checked cut selectors from Section 5.3 and field focus from Section 5.2 must appear in the **lemma statement** as well as the proof script, so capture details like `"L49"`, `wo_after_alloc`, and positional eight-element pointer lists disappear from callers too:

```rocq
Lemma wp_wo_reset_read_cursors e fb fr ch nb b Φ :
  in_buf fb nb b ->
  c_env wo_after_alloc_cut e [("fp", WPtr (mkPtr fb (Obj fb))); ("ch", WInt ch)] ->
  struct_live wfile_records "_IO_FILE" fb fr -∗
  struct_at wfile_layout "_IO_FILE" fb
    [("_IO_read_ptr", VPtr null); ("_IO_read_end", VPtr null);
     ("_IO_read_base", VPtr null); ("_IO_buf_base", VPtr b)] -∗
  buf_idle nb -∗
  (∀ ee, ⌜c_env wo_set_wide_cut ee [("fp", WPtr (mkPtr fb (Obj fb))); ("ch", WInt ch)]⌝ -∗
    struct_live wfile_records "_IO_FILE" fb fr -∗
    struct_at wfile_layout "_IO_FILE" fb
      [("_IO_read_ptr", VPtr b); ("_IO_read_end", VPtr b);
       ("_IO_read_base", VPtr b); ("_IO_buf_base", VPtr b)] -∗
    buf_idle nb -∗
    WP (block ee wo_set_wide_label) {{ Φ }}) -∗
  WP (run e wo_after_alloc_region) {{ Φ }}.
Proof using Type.
  (* Validates the C-emitted RegionSpec by vm_compute via sym_func_rule,
     using the _IO_buf_base field entailment on buf_idle nb: *)
  admit.
Admitted.
```

## 5. Diagnostics, field focus, and corpus census

Alongside region lifting and specification testing, four targeted improvements remove daily friction and ground solver priorities in whole-image measurements.

### 5.1 Actionable stop diagnostics and gated abduction

When [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v) or [GlibcSymCall.v](../rocq/glibc/tactics/GlibcSymCall.v) stops today, it returns a raw [GlibcSym.stop_reason] such as `NoCell` or `NoLiveCap` at an integer offset. Joining that stop state with the `<Name>Src.v` tables for `block_src`, `footprint`, and call edges lets the executor and an interactive `rq` session report three facts together:

1. First, the diagnostic names the C operation, including source file, line, and field path, such as `wfileops.c:412` reading `c: fp->_IO_buf_base`.
2. Second, the diagnostic names the missing resource or field refinement, such as target-capability resolution for `b` on `struct _IO_FILE._IO_buf_base` via `buf_idle nb`.
3. Third, the diagnostic identifies the nearest caller in the call graph that already holds or drops that invariant.

Because [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v) already preserves untouched heap atoms automatically, propagating a missing spatial resource backwards across a call edge needs **abduction** of the missing anti-frame rather than full [bi-abduction](https://www.cs.ox.ac.uk/people/hongseok.yang/paper/popl09.pdf). Every abducted precondition edit must pass both the Section 3 witness tester and the `hello_premises.py` entry-satisfiability gate, ensuring that strengthening a callee contract never silently turns a caller debt unsatisfiable the way the former `hd_close_stdout_wide` premise did.

### 5.2 Struct field focus lenses and symbol-keyed fixtures

Opening two fields of `c: struct _IO_FILE` in [LibioFputsIdle.v](../rocq/glibc/libio/LibioFputsIdle.v) or [LibioWOverflowLoan.v](../rocq/glibc/libio/LibioWOverflowLoan.v) currently unpacks all seventeen fields of `file_fields` and re-frames all seventeen at exit. Extending [CStruct.v](../rocq/glibc/tactics/CStruct.v) with one generic `vm_compute` field-partition lemma lets a caller borrow just the four cursor fields needed by `wp_wo_reset_read_cursors` above and keep a closing [[magic-wand]] for the remaining thirteen fields, while extending [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v) to quote `int_cell`, narrow stores, and [struct_at] directly eliminates manual `struct_open` boilerplate.

Three small generator cleanups remove the remaining fixture fragility:

- Stamp `"Do not edit"` on all 127 unmarked `*Src.v` and `*Module.v` files.
- Update `rocq/scripts/glibc-code/skeleton.py` so new scaffolds emit [CBlocks.v](../rocq/glibc/tactics/CBlocks.v) tables and [CStruct.v](../rocq/glibc/tactics/CStruct.v) footprints rather than Generation-1 [keeps] skeletons.
- Replace numeric row indices in `goto_block "IH" "HK" 13%nat` in [PrintfLoopHead.v](../rocq/glibc/stdio/PrintfLoopHead.v) with `vm_compute` lookup by target cut, and extend `spec_inputs` in [GlibcSpec.v](../rocq/glibc/base/GlibcSpec.v) to instantiate single-constructor `Record` binders so specs stop nesting eighteen-element tuples.

### 5.3 Provenance-checked cut selectors

In [provenance.pl](../src/provenance.pl), `origin` parent links record syntactic containment or contribution rather than temporal value identity: reading `c: s->_mode` before a store and reading `c: s->_mode` after the store share a C spelling while denoting different runtime words, which is why [CFrame.v](../rocq/glibc/tactics/CFrame.v) suffixes duplicate live roots. Likewise, `c: _IO_do_write` appears at three separate call sites inside wide-stream overflow.

Semantic cut selectors—such as `wo_after_alloc_cut` and `wo_set_wide_cut` in Section 4—should therefore act as **IR-checked hints**: each selector names a loop header, switch case, or post-call point together with an edge or call-site witness when needed, resolves to concrete labels and signatures by `vm_compute`, and fails loudly at compile time if a recompile makes the selector ambiguous.

### 5.4 Whole-image stop-reason census, bit solvers, and second-client reuse

Before building new arithmetic solvers or ownership rules, three corpus-wide measurements should rank the bottlenecks empirically:

- Run [GlibcSym.v](../rocq/glibc/tactics/GlibcSym.v) and [AbsInfer.v](../rocq/theories/exec/AbsInfer.v) with naive default assumptions across every function in the 321 linked units of GNU Hello and histogram the resulting [GlibcSym.stop_reason] and abstract-domain failures.
- Harvest residual bitwise flag obligations (`Z.land`, `Z.lor`, sign extensions, and `2^64` wraps) across `libio`, `stdio`, `getopt`, and `string` to measure what share a small known-bits domain alongside [Lanes.v](../rocq/theories/logic/Lanes.v) discharges, while replacing recursive Ltac `put`-peeling in `lk_prove` of [GlibcTactics.v](../rocq/glibc/tactics/GlibcTactics.v) with one `vm_cast_no_check` lemma over [c_env] to cut `O(|writes| × |kept|)` `Qed` work to one computation.
- Link a second small client binary beyond GNU Hello against `rocq/glibc/` and record what fraction of proved glibc lemmas reuse unchanged, catching caller-specific contract assumptions early.

## 6. Scaling abstract verification and check-pass simulation

### 6.1 Certificates and interior windows in `theories/exec`

In [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), the boolean verifier [AbsInfer.verify] already accepts an untrusted candidate list of cut invariants, checks entry, and replays each cut, and [AbsSound.verify_sound_in] in [AbsSound.v](../rocq/theories/exec/AbsSound.v) turns acceptance into [AbsSound.spec_holds], as [CpuSound.v](../rocq/glibc/startup/CpuSound.v) demonstrates across sixteen CPU-initialization functions. Before moving fixpoint widening into SWI-Prolog, we should time [AbsInfer.plan], [AbsInfer.verify], and Rocq kernel checking separately on the CPU call tree to confirm where the time actually goes.

Extending `theories/exec/` to broader glibc code splits cleanly into two milestones:

1. The first milestone covers shared fixed-size table readers, allowing fractional read-only ownership via `ptsq dq` on objects that neither the function, its aliases, nor its callees and syscalls mutate, and automating generic `HasSpec` packaging while keeping semantic resource correspondence in [CpuSpec.v](../rocq/glibc/startup/CpuSpec.v) explicit.
2. The second milestone tackles borrowed interior windows on [wp_printf_buffer_write_window] in [PrintfBufferWriteWindow.v](../rocq/glibc/stdio/PrintfBufferWriteWindow.v), whose source is a borrowed interior byte slice `bytesq dq sb so ys` inside a larger object, whose destination owns writable bytes and shadow [[aux]] slots, and whose postcondition promises exact copied bytes in `window_after`.

Arithmetic and range engines can be shared between Campaign 5 for compiler check removal and Campaign 7 for `never_panics` of a linked program, while keeping separate acceptance theorems: a caller's string loan can prove a check safe for one call site, whereas erasing that check from emitted assembly requires proving the obligation across every admitted entry or guarding a specialized path.

### 6.2 Proving against `--checks=reference` and validating `check_reuse`

```diagram
Iris proofs link at:   --checks=reference   (adjacent Check + raw access)
                              │
                              │  Gallina reuse_refines (vm_compute per unit)
                              ▼
Closed safety moves to: --checks=combined    (labelled_safe / never_panics)
```

Today glibc units are captured after `-O`'s `--checks=combined` pipeline via `checks:checks_module/3` in [checks.pl](../src/checks.pl), forcing proofs to step over `Renew` and `HalfCheck` and breaking lemmas whenever check elimination improves. In [Logic.v](../rocq/theories/logic/Logic.v), [Logic.wp_check] places a [[later-modality]] on its continuation, so every redundant check deleted by `combined` strips one operational step and one later modality. That step-index mismatch is what makes transporting open [GlibcSpec.fn_triple] contracts from `reference` to `combined` painful—and we do not need open-triple transport at all.

Instead, proofs and check optimization separate cleanly at the closed whole-program boundary:

- Capture new glibc units at `--checks=reference`. Proofs never see [[renew|renewals]] or [[half_check|half-checks]], every memory access sits immediately after its own `Check` so a checked field load or store collapses into one derived rule, and all library [GlibcSpec.fn_triple] lemmas link uniformly at the `reference` stage. Upward check motion with `CheckAhead`, which can mark a [[doomed|doomed frame]] in [Semantics.v](../rocq/theories/core/Semantics.v), already lives in the opt-in `schedule` mode outside `combined`.
- Port the translation validators `check_reuse:reuse_refines/2`, `check_reuse:renew_refines/2`, and `check_reuse:guard_refines/2` from [check_reuse.pl](../src/check_reuse.pl) to Gallina as part of the [Gallina backend](gallina-backend.md) middle-end, prove once that validator acceptance implies operational forward simulation, and check each compiled unit by `vm_compute`.
- Transport only the closed whole-program theorem—[labelled_safe] in [Language.v](../rocq/theories/logic/Language.v) and `never_panics`—from the linked `reference` module to the shipped `combined` module via that simulation.
- Migrate incrementally without touching existing proofs. Both `reference` and `combined` satisfy [Validate.module_checked] in [Validate.v](../rocq/theories/core/Validate.v), and [Validate.valid_items] checks [Validate.valid_func] and [Validate.stage_func] independently on each function. A linked module can therefore keep the existing 133,728 lines of glibc proofs on `combined` functions while all new proofs target `reference`, refining the remaining `reference` functions to `combined` at the closed top level.

## 7. A tougher first milestone on wide-stream overflow

Once proofs target `--checks=reference` and closed simulation covers `combined`, invariance across check-reuse passes becomes an architectural guarantee of Section 6.2 rather than something each library proof has to demonstrate. A meaningful pilot on `c: _IO_wfile_overflow` in [LibioWOverflowAllocateSteps.v](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v) should therefore test genuine optimizer changes, mutant discrimination, and control flow:

1. First, test optimizer variation on `wp_wo_reset_read_cursors`: state the cursor reset with cut selectors and four focused `c: _IO_FILE` fields, register the `struct _IO_FILE._IO_buf_base` target-resolution entailment on `buf_idle nb`, and verify that the identical proof compiles both when `c: _IO_buf_base` is loaded three times and when load-forwarding collapses those reads into one load and three stores.
2. Second, test mutant discrimination in both directions: confirm that a semantically equivalent IR [[mutant]] reordering the three independent cursor stores still passes `vm_compute`, whereas a memory-safe wrong-cursor mutant storing `c: _IO_buf_base` into `c: _IO_write_base` instead of `c: _IO_read_base` fails with a diagnostic naming `_IO_write_base` and `_IO_read_base`.
3. Third, lift a neighboring region with a call and a branch: apply the same machinery to [wp_wo_after_walloc](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v#wp_wo_after_walloc), which calls `c: _IO_free_wbackup_area`, loads `c: _IO_save_base`, and branches on whether saved wide backup characters exist, exercising call framing and branch joins rather than sixteen straight-line instructions alone.
4. Fourth, establish the empirical baseline: measure historical lines of hand-proof diff per capture-changing compiler commit in the git log alongside `Qed` time and the count of registered field entailments, so the campaign can compare automated region proofs against concrete maintenance cost.

## Summary of priorities

| Track | Scope | Primary payoff |
| --- | --- | --- |
| **Shared assertions & spec tester (Sections 2 & 3)** | Extend [GlibcSym.atom] with user predicates; neutral witnesses across `interp:run/5` and [Transport.judge]; `c_pp` constants and spec mutation scoring | Prevents Prolog/Rocq spec drift and catches wrong constants, clobbered globals, and weak postconditions in <1 s |
| **Reference-stage proofs & pass simulation (Section 6.2)** | Capture new units at `--checks=reference`; port `check_reuse:reuse_refines/2` to Gallina; transport closed [labelled_safe] to `combined` | Eliminates `Renew`/`HalfCheck` noise and open-triple step-index pain while coexisting with all 133k lines of `combined` proofs |
| **Field focus, selectors & census (Section 5)** | [CStruct.v](../rocq/glibc/tactics/CStruct.v) focus lens, IR-checked cut selectors, gated abduction, symbol-keyed fixtures, and 321-unit stop-reason census | Removes 17-field `FILE` unpacks, `"L49"` coupling, and ranks bit-solver work empirically |
| **C-emitted `RegionSpec` & field entailments (Sections 4 & 7)** | `c_lower.pl` effect summaries + [sym_func_rule] + syntax-free field entailments, tested on cursor reset and [wp_wo_after_walloc](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v#wp_wo_after_walloc) | Consolidates Generations 2 and 4 into readable C-level lemmas resilient to optimizer rewrites |
| **Measured `exec/` windows (Section 6.1)** | Timing split on [CpuSound.v](../rocq/glibc/startup/CpuSound.v), shared-table `ptsq`, and borrowed slices on [wp_printf_buffer_write_window] | Scales push-button loop checking to read-only tables and interior byte windows |
