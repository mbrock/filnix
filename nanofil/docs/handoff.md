# Prolog C Compiler with Fil-C Safety — Handoff

Oct 23, 2026 · @Mikael Brockman

## Purpose and direction

The goal is a C compiler written in Prolog. Its IR and backend take QBE as inspiration and foundation, and it emits memory-safe code under Fil-C's model. This document hands off what we learned in one research session: how the Fil-C pass works, what QBE and cproc look like inside, how to think about QBE's mutable style in Prolog, and what Markus Triska's *The Power of Prolog* implies for the design.

Direction, as agreed so far:

- **QBE is the starting point, not a compatibility target.** Phase one implements plain QBE semantics so we have a reference to test against. After that the IR is free to change, and it will need to, because Fil-C's pass depends on knowing which values are pointers and QBE's IR has no pointer type.
- **Pizlonation lives in our own IR.** The memory-safety transform is an IR-to-IR pass, not a patch on QBE text.
- **We probably write our own frontend too.** cproc is the model, a C11 frontend of about 8k lines. But a frontend written in Prolog can hand the backend Prolog terms directly.
- **No IR text round-trip is required.** If the whole pipeline lives in one Prolog process, the IR never needs to be parsed or printed except for debugging and for differential testing against real QBE.
- **The design follows Triska's purity discipline wherever it pays.** The biggest payoff is a relational IR semantics that also serves as the test oracle.

## How Fil-C's pizlonator works

The pass is one 17,522-line file, [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp), read at commit `cec28ab` (2026-10-22). About 4,500 lines of it (roughly 8493–13037) validate inline asm, and a large part is the check-scheduling optimizer. The core lowering is regular and much smaller.

**Objects.** Every object has a 16-byte header just before its payload, `{upper, aux}`. `aux` packs a 48-bit pointer to a shadow array with 16 flag bits above it: global, readonly, free, a special type (function = 1) and alignment. See `struct filc_object` in [filc\_runtime.h](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/libpas/src/libpas/filc_runtime.h).

**Flight pointers.** A pointer in a register or SSA value is the pair `{ptr, lower}`. `lower` points at the payload, so `lower[-16]` is `upper` and `lower[-8]` is `aux`.

**Invisible capabilities.** In memory, a pointer field stores only its 8-byte address, so the payload keeps C's layout. The `lower` goes in the aux array at the same offset, `aux_base + (ptr - lower)`. The aux array is allocated lazily on the first pointer store (`filc_object_ensure_aux_ptr_outline`); an object with no aux yields `lower = 0` for any pointer loaded from it. A low bit of 1 in an aux word marks an atomic box, an indirection used for atomically stored pointers.

**Access checks.** `buildCheck` emits up to six per access of size S, merged per canonical pointer into one cold failure block:

1. `lower != 0`.
2. Alignment, only when needed (on x86, pointer-typed accesses and atomics).
3. For writes, `(aux >> 48) & (READONLY|FREE) == 0`; that flags byte sits at `lower - 2`.
4. `ptr >= lower`.
5. `ptr + S <= upper`.
6. Not freed. This check is skipped when both bounds are checked, which implies free collapses the bounds (inferred, not verified in the runtime).

A failure calls `filc_optimized_access_check_fail(flightptr, &origin)`, where the origin is static data: size, alignment, write flag and source locations.

**Pointer load from the heap.** Load the lower from the aux slot and handle the box bit, then load the address from the payload.

**Pointer store to the heap.**

1. Ensure the aux array exists.
2. Store barrier: if `lower != 0` and `filc_current_marking_state != 0`, call `filc_store_barrier_for_lower_slow(thread, lower)`.
3. Store the lower to aux.
4. Store the address to the payload.

Storing an integer over a pointer slot leaves aux untouched, so the capability survives and only the address changes.

**Precise stack roots.** Each function pushes `filc_frame {parent, origin, lowers[N]}` onto `thread->top_frame`. The pass runs SSA liveness, colors pointer-carrying values into `lowers[]` slots, and stores each new pointer's lower right after the instruction that defines it. The GC finds N through `frame->origin->origin_node->num_lowers_ish`, a field of a static `filc_function_origin`. Callers root the arguments they pass; callees do not root their incoming arguments.

**Safepoints.** Every function entry checks the stack limit. Loop back-edges get a pollcheck, `test byte [thread+8], 0xE`, with a call to `filc_pollcheck_slow` when set. A separate pass, [DeleteRedundantPollchecks.cpp](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/llvm/lib/Transforms/Instrumentation/DeleteRedundantPollchecks.cpp), removes pollchecks dominated by another in the same loop.

**Globals are reached only through getters.** Each global `g` gets:

- a getter `pizlonated_g(thread, origin)` returning `{ptr, lower}`;
- a 16-byte cache `pizlonatedGP_g`;
- a data object `pizlonatedDO_g` (header plus payload);
- an aux array `pizlonatedDA_g` when the initializer holds pointers.

The first getter call registers the global with the GC (`filc_global_initialization_start`) and runs a `filc_constant_relocation[]` table that fills pointer fields by calling other getters.

**Functions.** Each function becomes an implementation, an alias, a getter and a function object (symbols in the ABI section). The function object's payload is `{fast_entry, generic_entry, signature}`. Its header has `upper == lower`, a zero-size object that cannot be read or written, and its aux pointer points at itself. An indirect call checks `lower != 0`, `ptr == aux_ptr(lower)`, special type = function, and the signature.

**Other rules.**

- Exceptions: every call returns `has_exception`; on true, branch to a block that pops the frame and returns true.
- `inttoptr` yields `lower = 0`, unless an abstract interpreter (`inferPointerAsIntLaundering`) traces the integer back to a single `ptrtoint`.
- Escaping allocas become heap allocations. Only proven non-escaping locals stay on the stack, with a stack aux.
- Struct copies go through `filc_memmove` so aux words move with the data.

## Fil-C ABI cheat sheet (x86-64)

This is what a compiler must emit to link against clang-built Fil-C code. It was read from the pass at `cec28ab`. Where a detail comes from LLVM's register assignment rather than the pass itself, it should be checked by compiling probes with `filcc -S`.

**Symbols for a function `f`**

| Symbol | What it is |
| --- | --- |
| `pizlonatedFIP<sig>_f` | Implementation, with `f`'s linkage |
| `pizlonatedFI<sig>_f` | External alias of the implementation; what direct callers call |
| `pizlonated_f` | Getter returning `{ptr, lower}` to the function object |
| `pizlonatedFO_f` | Function object: header plus `{fast_entry, generic_entry, signature}` |

A caller of an external `foo` also emits a weak hidden thunk named `pizlonatedFI<sig>_foo`. If the real definition has the same signature, the linker picks its strong alias and the call is direct. Otherwise the thunk calls the getter, checks the signature and falls back to the generic convention. That is link-time type checking done with symbol names.

**Signature encoding**

- Integers narrower than 64 bits are normalized to i64 and zero-extended.
- Each argument or return element is a digit in bijective base 11: i64 = 0, float = 1, double = 2, x87 long double = 3, v128 = 4, v256 = 5, v512 = 6, ptr = 7.
- `sig = 1 + ret + 133 * args`, allowing at most 2 return elements and 16 arguments.
- Signature 0 means the generic convention: variadic functions, byval arguments, and anything else that does not fit.

| C prototype | Symbol |
| --- | --- |
| `void f(void)` | `pizlonatedFI1_f` |
| `void *malloc(size_t)` | `pizlonatedFI142_malloc` |
| `size_t strlen(const char *)` | `pizlonatedFI1066_strlen` |
| `long f(long, long)` | `pizlonatedFI1598_f` |
| `int main(int, char **)` | `pizlonatedFI11839_main` |

**Fast convention.** It is the plain C calling convention with arguments `(thread, callee_lower, args…)`, so thread is in RDI and callee\_lower in RSI. Each pointer argument takes two GPRs (ptr, lower). LLVM probably splits a pointer pair across R9 and the stack when registers run out; verify before relying on it. The return is the LLVM struct `{i1 has_exception, rets…}`. By LLVM's `RetCC_X86Common`, `has_exception` comes back in AL and integer or pointer results in RDX, or RDX:RCX for a pointer. Floats return in XMM0/XMM1. For direct calls, callee\_lower is undefined.

**Generic convention.** The function type is `{i1, i64 ret_size} fn(thread, callee_lower, args_size)`. Arguments are laid out with each aligned to `max(8, alignment)`. The first 256 bytes go to the thread's inline payload buffer and the parallel aux buffer; the rest go to the outline buffers. Return values come back through the same buffers.

**Getters** have the type `{ptr, lower} getter(thread, origin)` and return in RAX:RDX.

**Thread struct offsets** (computed from the pass's struct layout)

| Offset | Field |
| --- | --- |
| 0 | `stack_limit` (entry check: `cmp [thread], rsp; jae filc_stack_overflow_failure`) |
| 8 | `state` (pollcheck mask 0xE) |
| 12 | `tid` |
| 16 | `top_frame` |
| 32 | `unwind_registers[2]` |
| 64 | `cookie_ptr` |
| 128 | `cc_inline_buffer` (256 bytes) |
| 384 | `cc_inline_aux_buffer` (256 bytes) |
| 640 | `cc_outline_buffer` |
| 648 | `cc_outline_aux_buffer` |
| 656 | `cc_outline_size` |
| 3072 | Thread-local allocators (inline allocation fast path) |

**Runtime entry points a compiler calls most:** `filc_allocate`, `filc_allocate_with_alignment`, `filc_store_barrier_for_lower_slow`, `filc_object_ensure_aux_ptr_outline`, `filc_optimized_access_check_fail`, `filc_check_function_call_fail`, `filc_pollcheck_slow`, `filc_memmove`, `filc_memset`, `filc_promote_args_to_heap` (va\_start), `filc_get_next_ptr_bytes_for_va_arg`, `filc_load_ptr_atomic_with_manual_tracking_outline` and `filc_store_ptr_atomic_outline`. The last two are usable as slow but correct outline helpers for every pointer load and store in a first version.

## QBE and cproc: what's inside

QBE plus cproc is a full C11 compiler in about 22k lines with a real SSA optimizer, slightly smaller than TCC. QBE was read at upstream `c081897` (2026-05-13). The upstream c9x.me git only serves dumb HTTP, which broke through the sandbox proxy, so we used Michael Forney's [sr.ht mirror](https://git.sr.ht/~mcf/qbe), whose newest branch sits one commit above upstream. [cproc](https://github.com/michaelforney/cproc) was read at `d1c53dd` (2026-06-01).

| Codebase | Files | Code lines (cloc) | Notes |
| --- | --- | --- | --- |
| QBE | 37 | \~13.9k | 1,447 commits, \~1,290 by Quentin Carbonneaux; tests, docs and minic excluded |
| cproc | 25 | \~8.0k | 375 test files (`.c` with expected `.qbe` output) |

**QBE layout.**

- `parse.c`: 1,449 lines.
- Middle end, \~4.3k lines: `ssa`, `cfg`, `alias`, `load`, `mem`, `copy`, `gvn`, `gcm`, `fold`, `simpl`, `ifopt`, `live`.
- Register allocation: `spill.c` (531) and `rega.c` (700).
- amd64 \~2.6k lines: isel 944, emit 881, `sysv.c` 721, `winabi.c` 763. arm64 \~1.9k; rv64 \~1.5k.
- Recent additions: `gvn.c` and `gcm.c` (2025-03), `ifopt.c` if-conversion (2026-01), Windows x64 ABI (2026-02).

**The pipeline** is one readable function, `func()` in `main.c`:

```
abi0 → cfg → promote → ssa → alias → loadopt → coalesce → gvn → simplcfg
→ gcm → [ifconvert] → abi1 → simpl → isel → live → loop → cost → spill → rega → emit
```

The real passes are interleaved with `fillcfg`, `filluse`, `filldom`, `filllive` and `fillalias`, which recompute cached analyses after each rewrite.

**QBE has no pointer type.** Its value classes are `w`, `l`, `s`, `d`, and a pointer is just an `l`. cproc turns `1 + x` into `%.3 =l add extern $x, %.2`. Fil-C's pass depends on knowing which values are pointers, so this is the main reason our IR will diverge from QBE.

**QBE already has the analyses a check optimizer needs.**

- `alias.c` (222 lines) gives every temp a base (stack slot, symbol or unknown) plus a constant offset. That is the pizlonator's `canonicalizePtr`, which lets it merge the checks for `p[0]`, `p[1]`, `p[2]` into one range check.
- Stack slots are classified `ALoc` or `AEsc`, the same split as Fil-C's non-escaping and escaping allocas.
- `promote()` turns non-escaping scalar slots into SSA temps.
- GVN and GCM would deduplicate repeated header loads (`upper`, `aux`).

**cproc** has its own small in-memory IR (`struct func`, `inst`, `value`) with clean choke points in `qbe.c` (1,542 lines): `funcload`, `funcstore`, `funccopy`, `funcalloc` and `convert`. Its output is literal; struct assignment, for example, is an unrolled word-by-word load and store sequence. The rest of the frontend is `expr.c` (1,441), `decl.c` (1,199) and `pp.c` (624). Since cproc knows C types, it is a natural place to mark pointer values before the backend sees them.

**Related.** [qbe-go](https://github.com/ugurkorkmaz/qbe-go) is an early Go reimplementation of QBE (18 commits, ARM64 only, builder API only). It shows that one person can reasonably reimplement QBE in another language. Its README's goal of bit-perfect equivalence is aspirational, since it uses linear scan where QBE does SSA-based spilling with its own greedy allocator.

## QBE's mutation habits, mapped to Prolog

QBE's "mutates everything" is really five separate habits, and each maps to Prolog differently. The common move is to separate the IR from facts derived from it, which QBE keeps tangled together on the same structs.

**The setting.** QBE handles one function at a time in an arena freed afterwards (`freeall()` in `main.c`), so mutation never escapes a function.

- `Ins` is a 16-byte record `{op:30, cls:2, to, arg[2]}`.
- Each operand is a `Ref`: a 3-bit kind (temp, constant, slot, call, mem…) plus a 29-bit index into a function table.
- Blocks hold arrays of `Ins`, `s1`/`s2` successor pointers and a `jmp`. Phis are linked lists, each argument paired with its predecessor block.
- `Blk` and `Tmp` also carry cached analysis: preds, idom, dominator links, frontier, liveness bitsets, loop depth; and def, uses, cost, slot, register hint, alias, width. Both have `visit` scratch fields.

| QBE habit | Where you see it | Prolog counterpart |
| --- | --- | --- |
| Recomputed analyses | The `fill*` calls throughout `func()` | Tabled relations over the IR (`live_in/2`, `idom/2`, `uses/2`); the `fill*` calls disappear |
| Backwards block rebuild | `emit()` writes downward, `*--curi = …`, then `idup` copies the result back | A DCG from old instructions to new; difference lists replace the buffer |
| In-place operand patching | Copy elimination rewriting `Ref`s | A substitution assoc mapped over the IR; with temps as logic variables, copy propagation is unification |
| Annotations passed between passes | `Tmp.slot`, `hint`, `cost`, `width`, `alias`; rega's `RMap` | Facts keyed by temp, or an assoc threaded through a `foldl`; `visit` marks become visited sets or tabling |
| CFG surgery | `simplcfg` merges blocks; spill and rega split edges | Write new block terms; labels are atoms, so rewiring is relabeling |

An instruction-selection pass as a DCG might look like this. Note the cut, which the purity section below argues against:

```prolog
sel([]) --> [].
sel([ins(D,K,mul,[X,c(N)])|Is]) --> { pow2(N, S) }, !, [ins(D,K,shl,[X,c(S)])], sel(Is).
sel([I|Is]) --> [I], sel(Is).
```

**When analyses must see changes.** Two options came up:

- **Versioned IR facts.** Store `ins(V, Blk, Idx, …)`. Each pass reads version V, asserts V+1 and abolishes V's tables. This makes QBE's "rewrite, then refill" explicit.
- **Incremental tabling.** Trealla supports `:- table p as incremental` plus `incremental(ins/N)`, so asserting or retracting IR facts invalidates dependent tables automatically. Its cost when many small changes trigger invalidations is unmeasured.

**Logic variables as temps** are tempting, but they cannot be database keys, and tabling compares terms only up to variable renaming. Use ground names such as `t(42)` in the IR, and keep logic variables for local pattern matching such as isel templates.

**What does not carry over.** The 3+29-bit `Ref`, the 16-byte `Ins` and the global `insb` buffer are about cache footprint and zero allocation. Prolog terms like `ins(t(3), l, add, [t(1), c(4)])` are slower but far easier to read, and that speed cost does not matter for a compiler that handles one function at a time.

## Lessons from The Power of Prolog

Markus Triska's [The Power of Prolog](https://www.metalevel.at/prolog) is directly relevant: Triska also wrote the CLP(Z) library Trealla ships (`library/clpz.pl`, 8k lines), so the book is the design philosophy behind the libraries we would build on. These are the chapters read, with their main points.

- **[Logical Purity](https://www.metalevel.at/prolog/purity).** A pure program behaves as a mathematical relation. It is pure if built only from pure pieces: unification, `dif/2`, CLP(Z) constraints, conjunction, disjunction, and higher-order predicates over pure goals. It must also respect observable laws: commutative conjunction, and monotonicity, meaning adding a constraint can only remove solutions. Cut, `->`, `assertz`, output and global state break purity, as do the legacy tests `\=`, `integer/1` and `=:=`. The payoffs are running in all directions, reordering goals, testing with plain queries, reading clauses in isolation, swapping search strategies and thread safety. Triska calls how far purity can be pushed for performance an open research question.
- **[Declarative Debugging](https://www.metalevel.at/prolog/debugging).** Prefix a goal with `*` (defined with `:- op(920,fy,*). *_.`) to remove it. Removing a goal can only generalize a monotonic program, so you restore goals one at a time until the unexpected failure returns; the last goal restored is the culprit.
- **[Data Structures](https://www.metalevel.at/prolog/data).** Prefer clean representations, where each case is identifiable by its principal functor (`leaf(X)` versus `node(L,R)`), over defaulty ones decided by an otherwise branch. Clean terms enable argument indexing and stay general. Use `library(assoc)` (AVL, O(log n)) for maps, and `double_quotes=chars`.
- **[Global Variables](https://www.metalevel.at/prolog/global) and [Thinking in States](https://www.metalevel.at/tist/).** State is a relation between an old and a new state (`I #= I0 + 1`); when stuck, add an argument. DCG semicontext (`state//1`, `state//2`) threads state implicitly. The Thinking in States chapter contains a small compiler that threads emitted instructions, offsets and program counter through a DCG, and emits forward jumps whose targets are unbound variables bound later.
- **[Definite Clause Grammars](https://www.metalevel.at/prolog/dcg).** DCGs describe sequences in general, not just parse them. Use `phrase/2,3` and `library(pio)` for lazy file reading, and semicontext pushback for lookahead. Left recursion needs a length bound or tabling.
- **[Meta-interpreters](https://www.metalevel.at/acomip/).** Programs are terms, so interpreters are short, especially over clean representations. Parts of execution can be reified: proof trees, depth limits, fair search. Partial evaluation removes the interpretive overhead; the chapter's DCG example drops from about 7 s to 0.016 s.
- **[Memoization](https://www.metalevel.at/prolog/memoization).** Tabling is the declarative form of memoization and fixes termination for left recursion. A hand-built `assertz` memo table only speeds things up and does not help termination.
- **[Efficiency](https://www.metalevel.at/prolog/efficiency).** Algorithms and indexing matter more than micro-tricks.
  - Use clean terms so indexing can tell cases apart.
  - Use `if_/3` and `zcompare/3` for case distinctions indexing cannot see.
  - Put cheap constraints first.
  - Never trade correctness for speed.

  Pure updates cost a logarithmic factor, and a C++ rewrite buys roughly 10×, not 100× or 1000×.
- **[Macros](https://www.metalevel.at/prolog/macros).** `term_expansion` and `goal_expansion` transform code once at compile time, the way DCG translation works. Expansion semantics vary between systems.

## Proposed design

The design is a pure Prolog pipeline from C source to assembly, with one IR whose semantics are defined relationally. Impurity is kept to a thin driver. The pieces, in the order we expect to build them:

&#91;embedded content: proposed compiler pipeline · 8 stages, 4 supports\]

Every stage is a pure relation; the IR interpreter checks each pass, and real QBE is a reference only in phase one.

1. **Clean IR terms.**
   - Operands: `t(N)`, `c(N)`, `slot(N)`, `glo(Name)`.
   - Jumps: `jmp(L)`, `jnz(V, L1, L2)`, `ret(V)`, `hlt`.
   - Instructions: `ins(Dest, Class, Op, Args)`.
   - The discriminating functor goes in the first argument so indexing dispatches.
   - Phase one keeps QBE's classes `w`, `l`, `s`, `d`. Phase two adds a pointer class (`p`) and, after pizlonation, flight pointers as explicit (ptr, lower) pairs.
2. **A relational IR interpreter.** Instruction semantics are defined with CLP(Z), e.g. `Z #= (X + Y) mod 2^64` for `add` on `l`. This is the reference semantics and the test oracle. Because it is pure, it runs in every direction:
   - **Translation validation:** run a function before and after a pass on the same symbolic inputs, and ask for an input where the results differ.
   - **Test generation:** fix an output and ask which inputs produce it.
   - **Superoptimization:** search for a shorter instruction sequence satisfying the same relation.
3. **QBE-equivalent middle end.** Passes are pure relations `pass(Fn0, Fn)`, with pass state threaded through semicontext DCGs as in Thinking in States. Analyses (CFG, dominators, liveness, alias, loops) are tabled relations. The driver asserts each IR version as facts so tables have small keys; that boundary is the one deliberate impure step.
4. **Instruction selection without cut.** Each rule states its full applicability conditions with `if_/3` or reified tests. The predicate then enumerates every valid tiling on backtracking, so cost-driven selection is collect-and-minimize, lburg style. A too-general rule shows up as an extra solution instead of a silent wrong choice.
5. **Register allocation.** State the problem in CLP(Z) with a cost to minimize. Our measurements show proving uncolorability explodes, so it needs a search budget and a greedy fallback modeled on QBE's spill-then-assign approach.
6. **Emission and block layout.** A DCG produces assembly text. Forward branch targets are unbound variables bound once a block's address is known, which does TCC-style backpatching with no machinery.
7. **Our own C frontend.** Model it on cproc: a DCG preprocessor and parser, with types known when lowering. It hands IR terms straight to the backend, so text IR is needed only for debugging and for differential tests against real QBE.
8. **Pizlonation as an IR pass.** Turn pointer-class values into flight pointers. Insert checks using the alias relation's base-plus-offset facts to merge ranges. Record lowers in a frame, add pollchecks at loop back-edges, and lower calls to Fil-C's fast or generic conventions so output links with clang-built Fil-C code. Start with outline runtime helpers for pointer loads and stores, then inline fast paths.

**Kept pragmatic on purpose:**

- Tabled liveness uses `\+ def(B,T)`. Negation of a ground goal over ground facts is sound, so callers must always pass ground arguments.
- Versioned facts exist only at pass boundaries.
- Register allocation has an impure time budget.

**A cheaper first target, for comparison.** An earlier idea was a TCC fork emitting the Fil-C ABI. TCC's two-register `SValue` (`r`/`r2`) fits flight pointers, its spills before calls make frame rooting simple, and backward `gjmp_addr` marks loop back-edges. The Prolog route trades that quick win for analyses and testability.

## Trealla Prolog as host

[Trealla](https://github.com/trealla-prolog/trealla) is a strong host. We built it from head (`ba473a6`, 2026-10-23) with `make NOSSL=1 ISOCLINE=1`, because the sandbox lacks `histedit.h`. It is about 67k lines of plain C99, with the standard library compiled into the binary. It builds for WASI, Go and Cosmopolitan, and embeds as `libtrealla.a`. A compiler written in it could ship as one binary, run in a browser, or link into a C program.

**Features that matter here**

- **Parsing:** DCGs and `phrase_from_file` via `library(pio)`.
- **Tabling:** native answer tries plus delimited-continuation suspension (`reset`/`shift`). It supports `min`/`max` answer subsumption, incremental tables (`as incremental`) and tables shared across threads (`as shared`). There is no general user-defined lattice.
- **Constraints:** CLP(Z) (Triska's, same as Scryer) and CLP(B), plus `dif/2`, `freeze/2` and `when/2`.
- **Data structures:** `assoc`, `rbtrees`, `ordsets`, `ugraphs`, `pairs`, `reif` (`if_/3`).
- **Mutable escape hatches:** `nb_setarg/3`, `nb_setval`/`b_setval`, blackboard (`bb_put`/`bb_get`) and `term_hash`. Backtrackable `setarg/3` is missing.
- **Concurrency:** engines, threads, futures and actors.

The libraries are Scryer-style (`dcgs`, `pio`, `charsio`, `clpz`), so code should mostly port between the two.

**Measurements** (sandbox machine). The CFG generator adds random back-edges, so nearly everything is live everywhere, which is much worse than real code.

| Workload | Size | Result |
| --- | --- | --- |
| Tabled liveness (3 rules) | 200 blocks / 300 temps → 40k facts | 0.35 s |
| Tabled liveness | 500 / 800 → 265k facts | 2.5 s |
| Tabled liveness | 1000 / 1500 → 976k facts | 8.6 s |
| Worklist liveness (assoc + ordsets) | 200 / 300 | 0.51 s |
| Worklist liveness | 500 / 800 | 4.8 s |
| Worklist liveness | 1000 / 1500 | Killed (out of memory) |
| CLP(Z) coloring, `ff` | 150 temps, 1,618 edges, 12–14 regs | 0.13–0.14 s |
| CLP(Z) coloring | 60 temps, 935 edges, 14 regs | 0.05 s |
| CLP(Z) coloring | Same graph, 10 regs | Unfinished after 120 s |
| DCG parse | 51k-line, 1.5 MB QBE-style function | 2.3 s (about 22k lines/s) |

The declarative tabled liveness is both the shortest version and the fastest.

**Pitfalls hit**

- `succ/2` is a builtin; name the CFG edge relation something else.
- yall lambdas copy their free variables on every call. A lambda closing over a large assoc ran out of memory immediately; use a named helper predicate or share variables explicitly.
- Imports are explicit: `char_type/2` needs `library(charsio)`, lambdas need `library(yall)`.
- An exception in an `initialization` goal drops into the REPL and waits for input, so run batch jobs with stdin closed.

Trealla also looks like a good candidate to build under Fil-C: plain C99, a plain Makefile and an existing sanitizer test target. A memory-safe Prolog running this compiler would make a good Filnix demo.

## Open questions and risks

- [ ] What does Fil-C's clang frontend do with struct arguments and returns before the pass sees the IR? The pass only sees `byval` (which forces the generic convention) and literal-struct returns. Answer by compiling probes with `filcc -emit-llvm`.
- [ ] Does LLVM split a flight pointer across R9 and the stack in the fast convention, and is `has_exception` guaranteed clean in AL? Compile probes with `filcc -S` and test calls in both directions between our output and clang objects.
- [ ] Does free really collapse an object's bounds, as the skipped not-freed check implies? Read the free path in `filc_runtime.c`.
- [ ] Can string literals be static readonly objects referenced without a getter, as function objects already are? Test against the collector.
- [ ] Pointer-class design: a new IR class `p`, or annotations on `l` values from the frontend? This decides how much of QBE's middle end changes.
- [ ] Escape analysis for locals: reuse the `ALoc`/`AEsc` classification to keep non-escaping locals on the stack, as Fil-C does.
- [ ] How do tabled analyses perform keyed on versioned facts versus incremental tabling, at realistic function sizes (hundreds of blocks, small live sets)?
- [ ] What search budget and greedy fallback make CLP(Z) register allocation predictable?
- [ ] setjmp/longjmp, inline asm, defining variadic functions and pointer atomics need special handling; plan to reject them at first.
- [ ] Running output in-process (`tcc -run` style) would need a native host that boots the Fil-C runtime, because a Fil-C process cannot generate executable code. Startup for that case is unexplored.

## Sources

**Code read, with commits**

- [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp), Fil-C `cec28ab` (2026-10-22)
- [DeleteRedundantPollchecks.cpp](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/llvm/lib/Transforms/Instrumentation/DeleteRedundantPollchecks.cpp)
- [filc\_runtime.h](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/libpas/src/libpas/filc_runtime.h)
- [X86CallingConv.td](https://github.com/pizlonator/fil-c/blob/cec28abc25d9e8b88c9df65b314942a18e87f7a8/llvm/lib/Target/X86/X86CallingConv.td) (LLVM return-register assignment)
- [QBE, sr.ht mirror](https://git.sr.ht/~mcf/qbe), upstream `c081897` (2026-05-13)
- [cproc](https://github.com/michaelforney/cproc), `d1c53dd` (2026-06-01)
- [TinyCC mirror](https://github.com/TinyCC/tinycc), mob `e23dabe` (2026-10-16)
- [Trealla Prolog](https://github.com/trealla-prolog/trealla), `ba473a6` (2026-10-23)
- [qbe-go](https://github.com/ugurkorkmaz/qbe-go)

**The Power of Prolog** — [contents](https://www.metalevel.at/prolog), [Logical Purity](https://www.metalevel.at/prolog/purity), [Data Structures](https://www.metalevel.at/prolog/data), [Global Variables](https://www.metalevel.at/prolog/global), [Thinking in States](https://www.metalevel.at/tist/), [Definite Clause Grammars](https://www.metalevel.at/prolog/dcg), [Meta-interpreters](https://www.metalevel.at/acomip/), [Memoization](https://www.metalevel.at/prolog/memoization), [Efficiency](https://www.metalevel.at/prolog/efficiency), [Declarative Debugging](https://www.metalevel.at/prolog/debugging), [Macros](https://www.metalevel.at/prolog/macros).

**Scratch files** from the session, in the sandbox scratchpad `/tmp/claude-0/-home-claude/38676654-aba4-5d33-a2b7-97a4d63695a0/scratchpad/`. They are not durable, so copy anything worth keeping.

- `live_tabled.pl`, `live_iter.pl` and `gen.py`: liveness benchmarks and the random CFG generator.
- `color.pl`: CLP(Z) register coloring.
- `parse.pl` and `big.ssa`: DCG parser for a QBE subset and its test input.
- `sig.py`: Fil-C signature calculator.
