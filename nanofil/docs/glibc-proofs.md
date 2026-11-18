# Proving glibc at scale: specifications, regions, and compiler changes

This document is a design note for the next stage of the userland glibc proof campaign. It builds on [the formal campaign](formal.md), [the program logic](logic.md), [the runtime syscall boundary](zsys.md), and the concrete findings recorded in [Proving GNU Hello over userland glibc](hello-glibc.md). Where those pages establish why the campaign proves compiled C library code down to runtime system-call wrappers, this page examines the structure of the glibc proof tree itself and sets out how to make proofs of real compiled C easier to read, faster to check, more meaningful as C specifications, and resilient when the compiler changes.

> The diagnosis and measurements below reflect the repository at commit `decc6bdbad`, including a specification-testing experiment and design review contributed by GPT-6.2-Astra alongside the survey of `nanofil/rocq/`. None of the proposed tools or metatheorems described in Sections 3 through 7 exist yet unless the text links to an existing module.

## 1. Where the glibc proofs stand

The Rocq development under [rocq/](../rocq/) now spans roughly four hundred thousand lines, split between foundational theories in `rocq/theories/` and the userland glibc 2.44 proof tree in `rocq/glibc/`. At revision `decc6bdbad`, the tree breaks down as follows:

| Area | Hand-written files / lines | Generated files / lines | Role in the development |
| --- | ---: | ---: | --- |
| `theories/core`, `soundness`, `external` | 35 / 23,454 | — | IR syntax in [Syntax.v](../rocq/theories/core/Syntax.v), IEEE floats, small-step semantics in [Semantics.v](../rocq/theories/core/Semantics.v), [Runtime.v](../rocq/theories/core/Runtime.v) axioms, and [valid_no_unchecked] in [Soundness.v](../rocq/theories/soundness/Soundness.v) |
| `theories/logic` | 16 / 16,069 | — | Identity-keyed [[iris]] heap pieces in [Pieces.v](../rocq/theories/logic/Pieces.v) and [Heap.v](../rocq/theories/logic/Heap.v), instruction rules in [Logic.v](../rocq/theories/logic/Logic.v), SWAR lanes in [Lanes.v](../rocq/theories/logic/Lanes.v), and constant-time logic in [PoisonLogic.v](../rocq/theories/logic/PoisonLogic.v) |
| `theories/exec` | 9 / 6,843 | — | Abstract interpreter in [AbsRun.v](../rocq/theories/exec/AbsRun.v), cut-invariant inference in [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), and [[weakest-precondition]] soundness in [AbsSound.v](../rocq/theories/exec/AbsSound.v) |
| `theories/programs`, `hello_contracts` | 87 / 41,688 | — | Standalone C program proofs and retained libc-contract reference proofs |
| `glibc` | 827 / 133,728 | 587 / 179,668 | Userland glibc 2.44 proofs across `libio`, `hello`, `stdio`, `getopt`, `startup`, `string`, `intl`, `zsys`, `stdlib`, `nptl`, and `locale` |

### Four proof generations coexist

As the glibc proof tree grew past eight hundred hand-written files, four distinct ways of proving compiled IR emerged. Each generation removed a bottleneck of the previous one, yet hit a boundary that kept earlier styles in active use even in recent wide-stream `libio` commits such as [LibioWOverflowAllocateSteps.v](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v):

| Generation | Core modules | Adoption across 827 glibc files | What it solves | Why proofs still fall back |
| --- | --- | ---: | --- | --- |
| 1. Manual [[ssa]] stepping | [GlibcTactics.v](../rocq/glibc/GlibcTactics.v), [GlibcEnv.v](../rocq/glibc/GlibcEnv.v) | ~750 files: 347 name raw `"v43"` temporaries, 306 name `"L28"` labels, 326 thread [keeps] | Handles any [[separation-logic]] invariant, mid-block cuts, indirect vtable calls, and `free` | Couples lemmas and scripts to [[temporary]] numbers, [[block]] labels, check flavors, and instruction counts; accumulated 243 private tactics |
| 2. Reflective symbolic execution | [GlibcSym.v](../rocq/glibc/GlibcSym.v), [GlibcSymFunc.v](../rocq/glibc/GlibcSymFunc.v), [GlibcSymCall.v](../rocq/glibc/GlibcSymCall.v) | 6 proof files outside `GlibcSym*` | Executes whole blocks or bounded DAGs in one `vm_cast_no_check` step without `iFrame` search | Quotes only flat `live`, `icell`, `pcell`, and `bytes` atoms; rejects `int_cell`, [struct_at], narrow stores, [c_env], and domain pointer-load lemmas |
| 3. Whole-function abstract checking | [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), [AbsRun.v](../rocq/theories/exec/AbsRun.v), [AbsSound.v](../rocq/theories/exec/AbsSound.v) | 10 files in [CpuSound.v](../rocq/glibc/startup/CpuSound.v) covering 16 CPU-init functions | Infers loop invariants and checks whole functions by `vm_compute` | Requires [StoreStable] world invariants, exclusive whole-object ownership, static object sizes, and manual correspondence bridges in [CpuSpec.v](../rocq/glibc/startup/CpuSpec.v) |
| 4. C frames, layouts, and block tables | [CFrame.v](../rocq/glibc/CFrame.v), [CStruct.v](../rocq/glibc/CStruct.v), [CBlocks.v](../rocq/glibc/CBlocks.v) | 18 to 43 files, centered in `stdio` such as [PrintfWrite.v](../rocq/glibc/stdio/PrintfWrite.v) | States cuts by C variable name, eliminates numeric field offsets, and closes loops once via [blocks_close] | Steps instructions manually inside each block, hardcodes `"L15"` labels and numeric row indices, and falls back to raw SSA names on arithmetic temporaries |

The survey also surfaced two immediate repository hygiene issues:

1. Across `rocq/glibc/`, 127 generated `.v` files—mainly `*Src.v`, `*SrcNN.v`, and `*Module.v` sidecars—lack the phrase `"Do not edit"` in their first thousand bytes, so site rendering, cross-file indexing, and grammar checks do not skip them automatically.
2. Twenty-three hand-written proof files, including [LibioWOverflowDispatch.v](../rocq/glibc/libio/LibioWOverflowDispatch.v), import numbered text-slicer chunks such as `HelloImageCode137`. Because the slicer packs items into five-hundred-line files, any code-size change earlier in the 321-unit GNU Hello image shifts functions into neighboring slice numbers and breaks downstream imports.

## 2. Architecture of the proposed proof stack

Nanofil already knows how to execute a region of checked IR symbolically and justify the outcome in Iris. What authors lack is a clean way to state what an IR region means in glibc terms, test that claim rapidly before proving it, attach domain ownership rules where Fil-C's memory model demands them, and keep the resulting lemma intact across compiler captures.

```diagram
 captured glibc unit     c_lower.pl, opt.pl, pizlonate.pl
    │  spec tester                  interp.pl + reified piece permissions
    ▼
 falsified or witnessed contract    counterexample, witness, or exhausted
    │  first-order region summary   reads, writes, pointer hooks, exits
    ▼
 RegionSpec                         checked by GlibcSymFunc.sym_func_rule
    │  registered resource rules    wp_load_buf_ptr, word_string_borrow
    ▼
 glibc-level Iris lemma             reusable across check-stream captures
```

The sections below organize the work from immediate high-leverage tools to deeper metatheoretic decoupling:

1. Section 3 tests specifications before proving them by running captured glibc IR against concrete witnesses and reified ownership masks in SWI-Prolog.
2. Section 4 lifts IR regions with Katamaran-style first-order summaries and RefinedC-style registered resource rules, solving the pointer-target lifetime bottleneck that keeps `libio` proofs manual today.
3. Section 5 improves interactive diagnostics, struct field lenses, and provenance-checked cut selectors so routine block proofs stop unpacking whole C structures or citing raw slice numbers.
4. Section 6 scales certificate checking and proves check-pass refinement so optimization improvements in [checks.pl](../src/checks.pl) stop perturbing library proofs.

## 3. Testing specifications against captured IR

In [Proving GNU Hello over userland glibc](hello-glibc.md), several expensive detours began when a proof author wrote down a plausible C specification that turned out to disagree with the compiled library code on an edge case: `c: __isatty_nostatus` overwrote `c: errno` with `ENOTTY` when standard output was a pipe, an assumed contract for `c: _IO_unsave_markers` named byte offset `72` instead of `80`, the `TCGETS2` request constant in [OsIoctl.v](../rocq/glibc/zsys/OsIoctl.v) carried a one-digit decimal transcription error, and `c: puts` left zero pending bytes with `c: stdout->_mode` set to `-1`. A lightweight specification tester over `interp:run/5` in [interp.pl](../src/interp.pl) can catch both false preservation claims and wrong call constants in milliseconds before anyone writes an Iris proof.

### A prototype experiment on `__isatty_nostatus`

To test this workflow against real captured code at `decc6bdbad`, GPT-6.2-Astra extracted the compiled body of `c: __isatty_nostatus` from `SysCode.v`, initialized a modeled `c: errno` cell to `7`, and executed the function in [interp.pl](../src/interp.pl) against two small `zsys_ioctl` stubs. Every test module passed `ir:valid_module/1`:

| Modeled `zsys_ioctl` behavior | Return value | Final `errno` | What the run establishes |
| --- | :---: | :---: | --- |
| Succeeds and leaves `errno` alone | `1` | `7` | Exercises the terminal path |
| Fails and writes `ENOTTY` (`25`) | `0` | `25` | Refutes any specification claiming `c: __isatty_nostatus` preserves `errno` |
| Stub checks historical typo `2150389802` instead of `2150388778` | `0` | — | Reaches the stub's rejection branch and exposes the constant mismatch despite passing `ir:valid_module/1` |

This small wrapper also exposes an important constraint on static read-only analyses: the IR body of `c: __isatty_nostatus` contains no store instruction at all, yet calling `zsys_ioctl` mutates both `c: errno` and the stack `kernel_termios` buffer. Any purity check for fractional ownership must consult callee and [[external-call]] summaries rather than scanning a function's instructions for stores.

### Reifying ownership and distinguishing test outcomes

The closest prior art is the [CN](https://www.cl.cam.ac.uk/~pes20/pldi2026-paper155-supplementary.pdf) group's *Code-Specify-Test-Debug-Prove* workflow and their [Fulminate](https://popl25.sigplan.org/details/POPL-2025-popl-research-papers/43/Fulminate-Testing-CN-Separation-Logic-Specifications-in-C) framework for testing separation-logic specifications in C. Fulminate highlights why testing separation-logic contracts requires more than running concrete memory: a live object in memory can contain a physically readable byte even when the caller's contract lent the callee no permission to read that offset.

A specification tester for nanofil should fit the boundaries of the existing tools:

- First, the generator synthesizes concrete heaps and capabilities alongside an explicit ownership mask. While [interp.pl](../src/interp.pl) supports symbolic CLP(Z) scalars, it requires concrete addresses, capabilities, and allocation sizes at memory operations. Meanwhile, the extracted OCaml runner's [Transport.judge] entry point in [Transport.v](../rocq/theories/core/Transport.v) currently accepts only integer arguments rather than arbitrary initial heaps and external responses. Starting in SWI-Prolog lets a generator synthesize concrete object [[identity|identities]], bounds, byte contents, shadow [[capability|capabilities]], and permitted external responses alongside a permission table of lent pieces, shrinking any violation to a minimal witness. Computable boolean shape predicates paired with soundness lemmas, following [str_shape_b_sound] in [WordString.v](../rocq/glibc/string/WordString.v), bridge concrete test witnesses directly to Iris assertions.
- Second, the runner distinguishes three verdicts: `counterexample`, `entry_witness_found`, and `search_exhausted`. Keeping these verdicts separate matters for open proof debts such as [HelloGlibcDebts.hd_close_stdout] in [HelloGlibcDebts.v](../rocq/glibc/hello/HelloGlibcDebts.v). The premise inventory script marks that premise unsatisfiable because the write-error path reaches `c: strerror` and `c: dcgettext`, which demand locale state that the caller's start list does not supply. Because the premise itself is a quantified [GlibcSpec.fn_triple], concrete heaps readily satisfy its entry shape and report `entry_witness_found`, while injecting a write failure produces a `counterexample` naming the exact execution path and missing locale resource. Proving that no ghost state can satisfy the quantified premise remains a separate metatheoretic argument.

## 4. Lifting IR regions with registered ownership rules

Two long-term ideas naturally reinforce each other: lifting low-level IR into structured verification conditions in the spirit of [AutoCorres](https://trustworthy.systems/publications/nictaabstracts/Greenaway_AK_12.abstract.html) and [Katamaran](https://icfp22.sigplan.org/details/icfp-2022-papers/8/Verified-Symbolic-Execution-with-Kripke-Specification-Monads-and-no-Meta-Programming), and automating resource framing through restricted, syntax-directed ownership rules in the spirit of [RefinedC](https://plv.mpi-sws.org/refinedc/). Trying both ideas together on a single concrete region of glibc's wide-stream overflow code reveals why neither struct-offset tables nor naive shallow functions suffice on their own.

### What `load_narrow` hides in wide-stream overflow

In `c: _IO_wfile_overflow`, right after `c: _IO_doallocbuf` returns, glibc resets the three narrow read cursors `c: _IO_read_ptr`, `c: _IO_read_end`, and `c: _IO_read_base` to `c: _IO_buf_base`. In the captured block of `HelloImageCode137.v`, that single C action compiles into sixteen checked IR instructions: three pointer loads, three pointer stores, four pointer-offset calculations, four [[half_check|half-checks]], and two [[renew|renewals]].

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

Look closely at what the local tactic `load_narrow "P6"` is doing on each of the three reads of `c: _IO_buf_base`. In Fil-C, loading a pointer with `LowerResolve` requires more than owning the `c: FILE` object's [[live]] token and the eight-byte pointer cell at offset `56`. Because [[fugc|FUGC]] can sweep capabilities to freed objects at a safepoint, [Logic.v](../rocq/theories/logic/Logic.v) requires proof that the *target* capability stored in `c: _IO_buf_base` still resolves cleanly. For an idle or newly allocated stream buffer, three cases arise:

1. If the stored buffer pointer `b` is null, the load needs no target lifetime.
2. If `b` points into the stream's inline one-byte `c: _shortbuf`, the `c: FILE` object's own `live fb fr` token supplies the target lifetime.
3. If `b` points into a separate heap buffer, `buf_idle nb` in [wo_cells] of [LibioWOverflowLoan.v](../rocq/glibc/libio/LibioWOverflowLoan.v) supplies the lifetime of that second heap object.

In [LibioFflushIdle.v](../rocq/glibc/libio/LibioFflushIdle.v), the lemma [wp_load_buf_ptr] proves those three cases once from `in_buf fb nb b` and `buf_idle nb`. Teaching [GlibcSym.v](../rocq/glibc/GlibcSym.v) about `c: struct _IO_FILE` field offsets alone would leave the symbolic executor stuck on the very first pointer load, because owning `live fb fr` and four field cells does not explain why the capability stored inside `c: _IO_buf_base` is alive.

### First-order region summaries and Katamaran-style verification conditions

That observation shapes a concrete architecture for lifting IR regions without having to lift an entire complex C function at once:

1. First, the lifter describes a region with first-order data that Rocq can check by computation. If a lifter produced an arbitrary shallow Gallina function `def_foo : M unit`, a boolean checker in Rocq could not inspect its body directly. Following Katamaran, the lifter instead extracts or checks a first-order region summary `RegionSpec` naming which C fields and temporaries the region reads, which pointer-target resolution obligations arise, which fields it updates, and which cut labels it exits to. Because [GlibcSymFunc.v](../rocq/glibc/GlibcSymFunc.v) already executes branches, parallel [[phi]] assignments, and cut stops and connects its computed tree to Iris via [sym_func_rule], `vm_compute` can check the region's IR execution against that first-order summary directly, while a clean Gallina verification condition serves as its shallow interpretation.
2. Second, domain modules register proved resource-action lemmas in an ownership sidecar. Unlike [RefinedC](https://plv.mpi-sws.org/refinedc/), nanofil cannot sprinkle ownership attributes into upstream glibc `.c` files, and bare C types lack Fil-C invariants anyway. For example, lending a string suffix `c: s + k` to a callee uses [word_string_borrow] in [WordString.v](../rocq/glibc/string/WordString.v), which retains a fractional share because glibc's word-at-a-time string routines round unaligned pointers down to an eight-byte boundary and share the boundary word between prefix and suffix; a C `c: const char *` parameter expresses neither that shared word nor its reconstruction [[magic-wand]]. Instead, domain modules register input-directed resource rules whose inputs uniquely select which proved lemma applies:
   - When the executor sees a pointer load from a cell `x` with `in_buf fb nb x` and `buf_idle nb` in context, it selects [wp_load_buf_ptr].
   - When the executor sees a call demand `word_string (DfracOwn q1) (ptr_add p k) s2` while the caller holds `word_string (DfracOwn (q1 + q2)) p (s1 ++ s2)`, it selects [word_string_borrow] and parks the closing wand for the return.

With field focus from Section 5.2 and registered [wp_load_buf_ptr], the proof of the sixteen-instruction cursor reset states only what changes in glibc terms and survives any check-pass rewrite of the underlying block:

```rocq
Lemma wp_wo_reset_read_cursors e ch vb fb fr fl f2 nb wd wr w b stop Φ :
  0 < fb -> fb mod 8 = 0 -> fb + 224 <= r_end fr -> r_end fr <= 2 ^ 63 ->
  in_buf fb nb b -> wo_setup_regs e fb ch ->
  wo_cells vb fb fr fl f2 nb wd wr w [null; null; null; null; null; null; b; stop] (wo_new_wide wd w) -∗
  (∀ ee, ⌜wo_setup_regs ee fb ch⌝ -∗
    wo_cells vb fb fr fl f2 nb wd wr w [b; b; b; null; null; null; b; stop] (wo_new_wide wd w) -∗
    WP (block ee "L49") {{ Φ }}) -∗
  WP (run e wo_after_alloc) {{ Φ }}.
Proof using Type.
  (* Focuses {_IO_buf_base, _IO_read_ptr, _IO_read_end, _IO_read_base} + buf_idle nb,
     replays the region via sym_func_rule with wp_load_buf_ptr, and closes wo_cells: *)
  admit.
Admitted.
```

## 5. Diagnostics, field focus, and provenance

Alongside region lifting and spec testing, four smaller improvements remove most of the daily friction in hand-written and symbolic glibc proofs.

### 5.1 Actionable stop diagnostics and bi-abduction

When [GlibcSym.v](../rocq/glibc/GlibcSym.v) or [GlibcSymCall.v](../rocq/glibc/GlibcSymCall.v) stops today, it prints a raw IR reason such as `NoCell` or `NoLiveCap` at an integer offset. Joining that stop state with the `<Name>Src.v` tables for `block_src`, `footprint`, and call edges lets the executor and the interactive `rq` server report three facts at once:

1. First, the diagnostic names the C operation: the source file, line, and field path, such as `wfileops.c:412` reading `c: fp->_IO_buf_base`.
2. Second, the diagnostic names the missing resource or rule: for instance, resolving the loaded pointer requires target lifetime for `b`, matching the signature of [wp_load_buf_ptr] given `in_buf fb nb b` and `buf_idle nb`.
3. Third, the diagnostic identifies the nearest caller in the call graph that already holds or drops that invariant.

Propagating a missing spatial resource backwards across a call boundary, following [bi-abduction](https://www.cs.ox.ac.uk/people/hongseok.yang/paper/popl09.pdf) by Calcagno et al., can go one step further and propose a candidate contract edit covering both the missing resource anti-frame and the untouched frame for the author to run through the Section 3 spec tester before proving.

### 5.2 Struct field focus lenses and symbol-keyed fixtures

Opening two fields of `c: struct _IO_FILE` in [LibioFputsIdle.v](../rocq/glibc/libio/LibioFputsIdle.v) or [LibioWOverflowLoan.v](../rocq/glibc/libio/LibioWOverflowLoan.v) currently unpacks all seventeen fields of `file_fields` and re-frames all seventeen at exit. Extending [CStruct.v](../rocq/glibc/CStruct.v) with one generic `vm_compute` field-partition lemma lets a proof borrow any subset of named C fields and hold a closing wand for the rest, while extending [GlibcSym.v](../rocq/glibc/GlibcSym.v) to quote `int_cell`, narrow 8/16/32-bit stores, and [struct_at] directly lets symbolic execution step through `c: FILE` and `c: struct __printf_buffer` blocks without manual `struct_open` boilerplate.

In parallel, three small generator cleanups eliminate avoidable breakage:

- Emit a symbol-indexed function table in `rocq/scripts/glibc-code/generate.py` so none of the twenty-three proof files import numbered chunks like `HelloImageCode137`, and stamp `"Do not edit"` on all 127 unmarked `*Src.v` and `*Module.v` files.
- Update `rocq/scripts/glibc-code/skeleton.py` so new scaffolds emit [CBlocks.v](../rocq/glibc/CBlocks.v) tables and [CStruct.v](../rocq/glibc/CStruct.v) footprints rather than Generation-1 [keeps] skeletons.
- Replace numeric row indices in `goto_block "IH" "HK" 13%nat` ([PrintfLoopHead.v](../rocq/glibc/stdio/PrintfLoopHead.v)) with `vm_compute` lookup by target cut, and extend `spec_inputs` in [GlibcSpec.v](../rocq/glibc/GlibcSpec.v) to instantiate single-constructor `Record` binders so specs stop nesting eighteen-element tuples.

### 5.3 Provenance-checked cut selectors

In [provenance.pl](../src/provenance.pl), `origin` parent links record syntactic containment or contribution rather than temporal value identity: reading `c: s->_mode` before a store and reading `c: s->_mode` after the store share a C spelling while denoting different runtime words, which is why [CFrame.v](../rocq/glibc/CFrame.v) suffixes duplicate live roots. Likewise, `c: _IO_do_write` appears at three separate call sites inside wide-stream overflow.

Rather than trying to erase every SSA fallback from AST links alone, semantic cut selectors should act as **IR-checked hints**: a selector names a loop header, switch case, or call snapshot together with an edge or call-site witness when needed, and fails loudly at compile time if a recompile makes the selector ambiguous.

### 5.4 Corpus-measured bit solvers and environment transfer

Standard `lia` struggles when glibc combines bitwise flag masks (`Z.land`, `Z.lor`), 32-bit sign extension, and `2^64` modular wrapping. Before committing to a known-bits domain or bit-blasting solver alongside [Lanes.v](../rocq/theories/logic/Lanes.v), we should harvest the actual residual arithmetic obligations across `libio`, `stdio`, `getopt`, and `string` to see which small decision procedure discharges the largest share. Similarly, replacing recursive Ltac `put`-peeling in `lk_prove` ([GlibcTactics.v](../rocq/glibc/GlibcTactics.v)) with one `vm_cast_no_check` lemma over [c_env] shrinks `Qed` terms to one computation instead of `O(|writes| × |kept|)` steps.

## 6. Scaling abstract verification and check refinement

### 6.1 Certificates and interior windows in `theories/exec`

In [AbsInfer.v](../rocq/theories/exec/AbsInfer.v), the boolean verifier [AbsInfer.verify] already accepts an untrusted candidate list of cut invariants, checks entry, and replays each cut, and [AbsSound.verify_sound_in] in [AbsSound.v](../rocq/theories/exec/AbsSound.v) turns acceptance into [AbsSound.spec_holds], as [CpuSound.v](../rocq/glibc/startup/CpuSound.v) demonstrates across sixteen CPU-initialization functions. Before moving fixpoint widening into SWI-Prolog, we should time [AbsInfer.plan], [AbsInfer.verify], and Rocq kernel checking separately on the CPU call tree to confirm where the time actually goes.

Extending `theories/exec/` to broader glibc code splits cleanly into two milestones:

1. The first milestone covers shared fixed-size table readers, allowing fractional read-only ownership via `ptsq dq` on objects that neither the function, its aliases, nor its callees and syscalls mutate, and automating generic `HasSpec` packaging while keeping semantic resource correspondence in [CpuSpec.v](../rocq/glibc/startup/CpuSpec.v) explicit.
2. The second milestone tackles borrowed interior windows on [wp_printf_buffer_write_window] in [PrintfBufferWriteWindow.v](../rocq/glibc/stdio/PrintfBufferWriteWindow.v), whose source is a borrowed interior byte slice `bytesq dq sb so ys` inside a larger object, whose destination owns writable bytes and shadow [[aux]] slots, and whose postcondition promises exact copied bytes in `window_after`.

Arithmetic and range engines can be shared between Campaign 5 for compiler check removal and Campaign 7 for `never_panics` of a linked program, while keeping separate acceptance theorems: a caller's string loan can prove a check safe for one call site, whereas erasing that check from emitted assembly requires proving the obligation across every admitted entry or guarding a specialized path.

### 6.2 Staged check-pass refinement

```diagram
Check refinement: reference ─▶ reuse ─▶ combined
```

Today glibc units are captured after `-O`'s `--checks=combined` pipeline via `checks:checks_module/3` in [checks.pl](../src/checks.pl), so proofs step over the exact mix of `Check`, `Renew`, and `HalfCheck` instructions the pass emits. Two distinctions in the current model shape the theorem:

- First, `--checks=combined` runs forward [[reuse]], [[renew|renewal]], and [[half_check|half-checks]] via `check_reuse:reuse_refines/2` in [check_reuse.pl](../src/check_reuse.pl), whereas upward check motion with `CheckAhead`, which can mark a [[doomed|doomed frame]] in [Semantics.v](../rocq/theories/core/Semantics.v), lives in the separate opt-in `schedule` mode. Furthermore, `wp_check` in [Logic.v](../rocq/theories/logic/Logic.v) tests only `live b reg` and region bounds `r_end reg`, never byte ownership of struct padding; the semantic question for any widened check is strictly whether its extra bound can fail on an executed path.
- Second, operational whole-program safety via [labelled_safe] in [Language.v](../rocq/theories/logic/Language.v) is simpler to transport than open library triples via [GlibcSpec.fn_triple] in [GlibcSpec.v](../rocq/glibc/GlibcSpec.v). Deleting a redundant `Check` removes an operational step that an Iris proof may have spent to strip a [[later-modality]], and `fn_triple` quantifies over arbitrary step-indexed continuations and spatial resources.

We should therefore stage check refinement in two steps: first prove operational simulation from `reference` to `reuse` and then `combined` on the same optimized plain IR to transport whole-program [labelled_safe] and `never_panics`, and tackle open [GlibcSpec.fn_triple] transport as a second theorem with an explicit stuttering or fuel-indexed account of continuations.

## 7. A first milestone on wide-stream overflow

To evaluate region lifting, field focus, diagnostics, and registered ownership rules together before scaling across `rocq/glibc/`, we can run one controlled experiment on the sixteen-instruction cursor-reset region of `c: _IO_wfile_overflow` in [LibioWOverflowAllocateSteps.v](../rocq/glibc/libio/LibioWOverflowAllocateSteps.v):

1. For the compiler-variation test, we state the three-cursor reset once in glibc terms, supply [wp_load_buf_ptr] as the registered pointer-resolution rule, and verify that the identical proof compiles against two captures of `c: _IO_wfile_overflow` under `--checks=reference` and `--checks=combined`.
2. For the semantic-precision test, we run the same proof against a memory-safe [[mutant]] that stores `c: _IO_buf_base` into `c: _IO_write_base` instead of `c: _IO_read_base` while still passing `ir:valid_module/1`, confirming that the region check rejects the mutant with a diagnostic naming the mismatched C field.
3. For the empirical readout, we record which domain lemmas the author supplied, compare replay and `Qed` time against the manual `step` and `check` proof, and verify zero lines of proof diff across the two captures. Those numbers will tell us directly whether the next engineering investment belongs in ownership-rule automation, bitvector and modular arithmetic, or broader region lifting.

## Summary of priorities

| Track | Scope | Primary payoff |
| --- | --- | --- |
| **Specification QuickCheck (Section 3)** | SWI-Prolog witness & permission-mask runner over `interp:run/5`, tested on `c: __isatty_nostatus` and [HelloGlibcDebts.hd_close_stdout] | Catches wrong constants, clobbered globals, and missing lent resources in <1 s before proof work starts |
| **Field focus & fixture hygiene (Section 5.2)** | [CStruct.v](../rocq/glibc/CStruct.v) focus lens, symbol-keyed image imports, `"Do not edit"` headers, `CBlocks` skeletons | Eliminates 17-field `FILE` unpacks and fragile `HelloImageCode137` / row-index breakage |
| **Stop diagnostics & bi-abduction (Section 5.1)** | Source-mapped `GlibcSym` / `rq` stop reports + backward precondition propagation | Points directly to the C expression, missing resource rule, and caller contract edit |
| **Region lifter + resource sidecar (Sections 4 & 7)** | Katamaran-style first-order `RegionSpec` + [sym_func_rule] + registered rules ([wp_load_buf_ptr], [word_string_borrow]) | Readable glibc-level lemmas that survive check-stream and instruction-order changes |
| **Measured `exec/` windows & check refinement (Section 6)** | Timing split on [CpuSound.v](../rocq/glibc/startup/CpuSound.v), shared-table `ptsq`, [wp_printf_buffer_write_window], and `reference → reuse → combined` simulation | Scales push-button checking and decouples `-O` check passes from library proofs |
