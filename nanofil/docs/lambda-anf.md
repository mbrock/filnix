# λANF on nanofil IR: a second substrate for verified Gallina

November 2026. A campaign design, written before any of it is built. It
extends [the Gallina backend](gallina-backend.md) and
[the formal campaign](formal.md): where the Gallina backend moves
nanofil's middle and back ends into Rocq, this design asks how erased
Gallina itself should reach machine code inside a Fil-C process without
routing through OCaml, C++, or pointer-punning C.

Two names in the sketch this page grew from need separating up front:

- **Nanofil IR** ([ir.pl](../src/ir.pl), [Syntax.v](../rocq/theories/core/Syntax.v))
  is the compiler's representation: ground `module(Items)` terms of
  functions, basic [[block|blocks]], phis, instructions and data, in
  either the `unchecked` or `checked` [[stage]].
- **NFB** ([nfb.md](nfb.md), [nfb.pl](../src/nfb.pl),
  [Nfb.v](../rocq/backend/Nfb.v)) is not a second IR. It is the canonical
  binary encoding of a Nanofil IR module as little-endian 32-bit words
  (`nfb:module_nfb/2`, [Nfb.encode], [Nfb.decode]). A λANF backend
  targets Nanofil IR; NFB is the wire and cache format when a module
  crosses a library boundary such as `libnanofil`.

## The thesis

Nanofil IR was built to compile untrusted C under [[gimso|GIMSO]]: every
pointer carries a spatial and temporal [[capability]], [[pizlonate|pizlonation]]
(`pizlonate:pizlonate_module/2`, [Pizlonate.pizlonate_module]) writes
each obligation out as a check term, and a failed check stops the run in
a deterministic [[trap]] ([NullCapability], [OutOfBounds], [Misaligned],
[Readonly], [NotAFunction], [ArgumentSize], [ReturnSize], [InvalidFree],
[DoubleFree]), backed at run time by [[fugc|FUGC]].

Pure functional Gallina code — such as nanofil's own verified passes in
[Compile.v](../rocq/backend/Compile.v) and [Regs.v](../rocq/backend/Regs.v) —
has completely different memory traffic. Nearly every allocation is a
small immutable constructor that dies within microseconds, never aliases
mutable C memory, and never stores a C pointer. Giving every cons cell
its own Fil-C object header, [[aux]] table, FUGC store barrier and stack
root pays for guarantees a pure term graph does not use.

```diagram
 C translation unit
    │  c_lower.pl, middle end       p flight pointers, per-object capabilities
    ▼
 unchecked module(Items)
    │  pizlonate.pl                 explicit checks and poll edges
    ▼
 checked module(Items)              Syntax.module, encoded on the wire as NFB
    │  ValidFast.valid_fast         valid_no_unchecked gate
    ▼
 Compile.compile_allocated ── as, ld ──▶ Fil-C ELF / libnanofil.so
```

```diagram
 Rocq / Gallina development
    │  MetaRocq erasure             erases types and Prop to λ□
    ▼
 CertiRocq λANF                     uncurried, closure-converted, hoisted
    │  anf_lower (proposed)         one p arena capability, all values class w
    ▼
 checked module(Items)              same IR, validator and backend as C
```

Lowering MetaRocq and CertiRocq's λANF directly to Nanofil IR over a
single capability-checked 32-bit integer arena turns one backend into a
dual-substrate compiler:

- **Untrusted C modules** keep per-object `p` capabilities, `aux`
  shadow tables and concurrent FUGC marking.
- **Verified Gallina modules** emit into the same [Syntax.module] and
  NFB format, keep every functional value in scalar `w` temporaries
  (32-bit integers), bump-allocate in a cache-resident nursery slice of
  one `p` arena, evacuate survivors with a ~50-line barrier-free Cheney
  copy, and compile straight through [Compile.compile_allocated] without
  invoking `clang` or `FilPizlonator`.

> Milestones M0 ([bench/arena/](../bench/arena/)) and M1
> ([anf/](../anf/)) are built and measured; M2–M5 remain ahead. Section 7
> separates what is measured in this repository from the remaining
> hypotheses.

## 1. Why routing Gallina through C++ or C hurts

[The Gallina backend](gallina-backend.md) already extracts nanofil's
reader, pizlonator, validator, promotion pass, register allocator and
x86-64 emitter from Rocq. M6 and M8 measured two extraction targets on
the 36-function regex module `rx.ir` and on Lua's `lvm.ir`, where every
build prints identical assembly bytes:

| Build | `compile` (`rx` / `lvm`) | `compile-allocated` | Peak RSS (`rx` / `lvm`) |
|---|---|---|---|
| Prolog (`nanofil`) | 1.27 s / 2.87 s | — | 43 / 162 MB |
| OCaml (`ocamlopt`) | 0.34 s / 1.72 s | 0.41 s / 1.68 s | 56 / 149 MB |
| Crane C++ (M6) | 2.40 s / 8.36 s | 2.87 s / 9.53 s | 76 / 577 MB |
| Crane C++ (M8 `rc.h`) | 0.96 s / 4.75 s | 1.30 s / 4.59 s | 55 / 382 MB |
| Crane C++ (M8 `libgc`) | 1.01 s / 5.07 s | 1.50 s / 4.82 s | 79 / 436 MB |
| Crane C++ (256 MB heap) | 0.76 s / — | 1.01 s / — | 285 MB / — |
| CertiRocq C (`clang -O1`) | 8.89 s / 48.95 s | 13.77 s / 91.42 s | 185 / 1065 MB |
| CertiRocq C (`filcc -DVERIFFI`) | 165.4 s / — | — | 994 MB / — |

### What M6 and M8 actually found on Crane C++

Bloomberg's Crane extracts the backend to 36,106 lines of C++23. The
M6 and M8 profiles in [gallina-backend.md](gallina-backend.md) rule out
any single switch closing the 2.8–3.1× gap to `ocamlopt`:

- **Reference counting costs copies as well as destruction.** At M6
  (`2.40 s` on `rx.ir`), `perf record` found about 15% of time in
  freeing reference-counted `Term` trees (emptying `~Term` by hand
  dropped `rx.ir` to `2.05 s` and `lvm.ir` from `8.36 s` to `7.22 s`),
  another 15% copying and moving `Term` variants, and 7% in `memmove`.
  M8's `FastVariant`, `BoxedFields`, `BoundedNesting` and early-exit
  `Loopify` brought `rx.ir` down to `0.96 s`, and stalled there.
- **24-byte `Term` values and recursion.** Even with `Set Crane GC`
  making all 52 inductives trivially copyable and trivially
  destructible, `Term` stays 24 bytes — wider than the 16-byte register
  threshold of the x86-64 SysV ABI. Of the 12 recursive functions
  `Loopify` declined, `clang` turned no more into loops under `CRANE_GC`
  than under reference counts: five kept self-calls in both builds, six
  were inlined, and one had none.
- **General-purpose non-moving GC drowns in tiny allocations.** On
  `rx.ir`, `compile` makes **17.65 million allocations**, 14 million of
  them 32 bytes or smaller. Under native Boehm `libgc` (after clearing
  stale variant bytes so the live heap stayed near 30 MB rather than
  174 MB), **65–70%** of wall time was inside `libgc` itself, leaving
  about **0.30 s** of mutator work — essentially the whole runtime of
  the `ocamlopt` build (`0.34 s`). Even with a 256 MB initial heap and
  only four collections, `libgc` took 48% of the time in allocation.
- **`filcc` did not finish compiling the C++ unit.** When the `CRANE_GC`
  build was handed to `filcc` against Fil-C's `boehmgc` (FUGC behind
  Boehm's API), compilation did not finish: after 17 CPU minutes (and
  three minutes at `-O1`) at **8.9 GB** RSS, 98% of samples were in the
  Fil-C pass's `computeFrameIndexMap`. The build was stopped without
  establishing why `computeFrameIndexMap` blew up on that unit, so
  nothing is measured of FUGC's runtime speed on Crane's output.

### Why `ocamlopt` runs in 0.34 s — and why it cannot be `libnanofil`

`ocamlopt` matches the ~0.30 s pure mutator time because its runtime is
built around short-lived algebraic data: every value is one uniform
tagged word, nursery allocation decrements a hardware register and
checks one bound, and minor GC touches only live survivors. What it
cannot do is link into a Fil-C library such as a pizlonated `libpcre2`:
its runtime is native OCaml, outside Fil-C's capability model, so `rxc`
has to spawn `nanofil-backend` as a separate OS process on every cache
miss.

### The active comparison point: CertiRocq's own C backend

Before building a new backend, a companion experiment
([CertiRocq C build of the Gallina backend](https://ampcode.com/threads/T-01a1c7da-3aaf-76c0-bea7-1603749ae0bc))
tested CertiRocq's λANF-to-Clight C pipeline end-to-end on all six
`rocq/backend` entry points (`read_text`, [Compile.compile],
[Compile.compile_promoted], [Compile.compile_allocated],
`rev_lines_parts`, `first_todo`), both natively and under `filcc`:

- **CertiRocq's default inliner hangs; `--anf-variant 8` emits 3.89M lines.**
  At default `-O 1`, `inline_shrink_loop` stalls past 200 s before and
  after closure conversion. Passing `--anf-variant 8` skips those two
  loops while keeping `shrink_err`, `uncurry_top`, `inline_uncurry`,
  `lambda_lift`, `closure_conversion_hoist`, `DPE` and
  `merge_dup_funs`, finishing in **157 s** at `-O 1`
  (`65 s` at `-O 0`) with zero changes to `rocq/backend/*.v` and
  emitting **3,892,446 lines of Clight C** (135 MB, ~21k functions; split
  into 16 shards, `clang -O1` builds it in 19.3 s).
- **Native `clang -O1` is byte-identical at 29–61× OCaml's time, and cannot tail-call.**
  Because CertiRocq's stack-frame GC links a local
  `c: struct stack_frame frame` into `tinfo->fp`
  (`c: tinfo->fp = &frame`), the C compiler cannot tail-call-optimize
  even genuine Gallina tail loops (such as `IrText`'s byte reader on a
  367 kB chunk), overflowing an 8 MB C stack on `rx.ir`. Under
  `ulimit -s unlimited` (and after fixing a `Loader.v` vs.
  `Generate Glue` `bool` tag inversion), native C matches `ocamlopt`
  byte-for-byte across `rx.ir` (`8.89 s` `compile`, `12.28 s`
  `compile-promoted`, `13.77 s` `compile-allocated`; `0.26–0.33 s` in
  OCaml on the same orb) and `lvm.ir` (`48.95 s`, `48.89 s`, `91.42 s`
  at up to **1,065 MB** RSS, vs. `1.50–1.74 s` and `213–231 MB` in
  OCaml). The 29–61× gap comes from unmapped `nat` (unary `O | S n`),
  9-word `Ascii` blocks, 3-word string `cons` cells, and un-inlined
  `f_case_*` continuations.
- **Under `filcc`, default `intnat` panics and `-DVERIFFI` runs in 165.4 s / 994 MB on `rx.ir`.**
  Sharded into 16 files, CertiRocq's C avoids `FilPizlonator`'s
  `computeFrameIndexMap` blowup (`54.1 s` wall, `1.15 GB` RSS in default
  mode; `176.3 s` wall, `1.96 GB` RSS under `-DVERIFFI`). Default
  `c: typedef intnat value` traps immediately at run time
  (`cannot read pointer with null object`) because casting pointers
  through `intnat` strips capabilities. Compiling with `-DVERIFFI`
  (`c: typedef void *value`, plus three `(intnat)` casts on generated
  tag bit-ops) **runs cleanly and prints byte-identical assembly without
  modifying `gc_stack.c`**: each generation `space` is one `malloc`
  array of `c: void *` slots, so `$alloc + 1` keeps the generation's
  capability (`[-1]` header reads stay in bounds), odd immediates and
  headers sit as null-capability `c: void *` words, closure code
  pointers preserve their function capabilities in `aux`, and Cheney
  copying copies both payload and `aux`. Paying for `c: void *` on every
  functional word, however, costs **18.6× native CertiRocq C** (**165.4 s
  wall, 994 MB RSS** on `rx.ir` `compile` — roughly **500× `ocamlopt`**):
  every immediate, header, constructor field, Cheney copy and local
  becomes a dual-space `intval` + `aux` pointer operation tracked
  simultaneously by `gc_stack.c`, Pizderson frames, and FUGC's store
  barrier.

## 2. What Fil-C capabilities actually cost on functional heaps

In Fil-C ([filc.md](filc.md), [abi-findings.md](abi-findings.md)), a
pointer has two physical layouts:

- **In flight** (registers and frame slots): a `p` value ([Syntax.P]) is
  a 16-byte [[flight-pointer|flight pointer]], holding the 64-bit
  `intval` address and the 64-bit [[lower]] pointer to the target's
  `c: struct filc_object` header.
- **At rest in memory**: C compatibility keeps `sizeof(void *)` at 8
  bytes. Storing a pointer writes its 8-byte `intval` to the payload and
  its 8-byte `lower` to a separate [[aux]] allocation (`auxp[ptr - lower]`),
  created on the first pointer store by
  `filc_object_ensure_aux_ptr_outline` and rounded to `GCMinAlign` (16
  bytes). Every pointer store also tests `filc_current_marking_state`
  for [[fugc|FUGC]]'s grey-stack Dijkstra incremental-update store
  barrier (`filc_store_barrier_for_lower_slow`).

Immediately below `lower` sits the 16-byte `c: struct filc_object`
header (`upper` at `lower - 16`, `aux` flags and pointer at
`lower - 8`). A 2-field constructor such as `cons` (holding at least one
pointer field) therefore pays for two heap objects, not one:

```diagram
┌──────────────────────────────────┐ ← lower - 16
│ upper: one past payload (8 B)    │   16 B header
│ aux: flags + aux pointer (8 B)   │
├──────────────────────────────────┤ ← lower
│ field 0 intval (8 B)             │   16 B payload
│ field 1 intval (8 B)             │
├──────────────────────────────────┤ ← auxp
│ field 0 lower + field 1 lower    │   16 B aux (2nd object)
└──────────────────────────────────┘
```

Comparing one 2-field recursive constructor across all four substrates
shows why functional allocation traffic behaves so differently on each:

| Substrate | Bytes / 2-field node | Write barrier & roots |
|---|---|---|
| Fil-C (`p` fields) | **48 B** across 2 objects (16 B header + 16 B payload + 16 B `aux`; 32 B if scalar leaf) | `ensure_aux` + Dijkstra store barrier; `lowers[]` frame roots |
| Crane C++ | **24 B** `Term` variant + heap child (`rc.h` count or `libgc` block) | refcount updates or `libgc` lock/mark; C++ stack temporaries |
| OCaml / CertiRocq | **24 B** (8 B header + two 8 B words) | generational write barrier on mutation only; shadow/stack scan |
| **32-bit `w` arena** | **12 B** (4 B header + two 4 B `w` words) | **none** (pure functional, zero `p` in arena, zero FUGC roots) |

## 3. The 32-bit single-arena value representation

Instead of giving each Gallina constructor its own Fil-C allocation, a
compiled functional module holds **one** Fil-C capability `arena` of
[[class]] `p` ([Syntax.P]), backed by a contiguous anonymous mapping
viewed as `c: uint32_t arena[]`. Inside the module, every Gallina value
travels as an ordinary scalar temporary of class `w` ([Syntax.W], 32-bit
integer).

### Virtual layout and physical memory

One contiguous index space splits into a lower **major slice** for
promoted survivors, a fixed **nursery window** at the top for bump
allocation, and a small **guard tail** past `NURSERY_END`:

```diagram
┌──────────────────────────────────┐ ← 0
│ major survivors (faulted on GC)  │
├──────────────────────────────────┤ ← major_idx
│ unfaulted virtual pages (0 RSS)  │
├──────────────────────────────────┤ ← nursery_base
│ bump nursery (2–4 MiB, L2/L3)    │
├──────────────────────────────────┤ ← nursery_end
│ guard tail (4 KiB = 1024 words)  │
└──────────────────────────────────┘ ← slab_end
```

On 64-bit Linux, reserving an unbacked anonymous range with
`c: mmap(NULL, bytes, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0)`
consumes virtual address space without faulting physical frames until
words are written. Under Fil-C, `mmap` routes through `zsys_mmap`
(`FILC_OBJECT_FLAG_MMAP`), which hands back a genuine `p` capability
with `aux = NULL`, and `c: madvise(arena, major_bytes, MADV_DONTNEED)`
routes through `zsys_madvise` to release physical major pages in `O(1)`
between independent compiler invocations while keeping the capability
valid. M1 verified that `verse_heap` skips zeroing `FILC_OBJECT_FLAG_MMAP`
payloads and touches only one 4-byte chunk-map word per 512 KiB chunk
(**8 KiB/GiB**), granting single reservations up to **4 TiB** in
`fugc_destructor_heap` and adding only **+0.37 MiB** RSS for the full
`8 GiB + 4 KiB` arena.

### Uniform 32-bit tagged words (`w`) and block headers

Every functional value is one 32-bit `w` word, following OCaml's low-bit
tagging shrunk to 32 bits:

| Bit 0 | Layout of `w` word | Meaning |
|---|---|---|
| `1` | `c: (val << 1) | 1` | Unboxed 31-bit immediate: constant constructors (`None`, `[]`, `true`, `O`), mapped `ascii` bytes, small integers, or hoisted function IDs |
| `0` | `c: idx << 1` | Boxed value at word index `idx = w >> 1` in `arena[]`, addressing up to `2^31` words (**8 GiB** of 4-byte cells; word `0` reserved) |

Because 0-ary constructors are always odd immediates, **every boxed
block in `arena[]` has arity `k ≥ 1`**: at least two 32-bit words, a
header at `arena[idx]` followed by `k` field words at
`arena[idx + 1 .. idx + k]`. That guarantees `arena[idx + 1]` always
exists to store a forwarding index during Cheney evacuation.

```diagram
┌──────────────────────────────────┐ ← 4 * idx
│ header: arity:22 · st:2 · ord:8  │
├──────────────────────────────────┤ ← +4
│ field 0 (or forwarding dst)      │
├──────────────────────────────────┤
│ fields 1 .. k - 1 (w words)      │
└──────────────────────────────────┘ ← +4 * (k + 1)
```

Putting both generations inside one `arena[]` base capability buys four
properties at once:

- **Branchless field loads.** Reading field `i` of `y` is
  `arena[(y >> 1) + i + 1]` whether `y` lives in the nursery or in
  major.
- **One-comparison nursery test.** During minor GC, a boxed word `v` is
  young iff `(v >> 1) >= NURSERY_BASE` (`cmp(uge, w)`).
- **4× cache density over Fil-C pointer nodes.** A 2-field `cons` cell
  is 12 bytes (three `w` words), fitting five list nodes per 64-byte
  cache line instead of one or two.
- **Pure-`w` closures.** A hoisted function's code pointer is not a
  64-bit native address or a `p` capability: each hoisted function in
  the module gets a dense integer ID encoded as an immediate
  `c: (fid << 1) | 1` in field 0 of a 2-field closure block
  `[fid_imm, env]`. Nothing in `arena[]` ever triggers `ensure_aux` or
  a FUGC barrier.

## 4. CertiRocq's real λANF and its lowering to Nanofil IR

In the MetaRocq → λ□ (`EAst.term`) → CertiRocq λANF pipeline, types and
`Prop` proofs are erased, multi-argument applications are uncurried,
free variables are packaged into explicit closure records
(`closure_conversion_hoist`), and every intermediate result is bound to
a variable. In `CertiRocq.LambdaANF.term`, the real expression grammar
has nine constructors plus mutually recursive `fundefs`:

```rocq
Inductive exp : Type :=
| Econstr (x : var) (t : ctor_tag) (ys : list var) (e : exp)
| Ecase (x : var) (arms : list (ctor_tag * exp))
| Eproj (x : var) (t : ctor_tag) (n : N) (y : var) (e : exp)
| Eletapp (x : var) (f : var) (ft : fun_tag) (ys : list var) (e : exp)
| Efun (fds : fundefs) (e : exp)
| Eapp (f : var) (ft : fun_tag) (ys : list var)
| Eprim_val (x : var) (p : primitive_value) (e : exp)
| Eprim (x : var) (p : prim) (ys : list var) (e : exp)
| Ehalt (x : var)
with fundefs : Type :=
| Fcons (f : var) (ft : fun_tag) (xs : list var) (body : exp) (rest : fundefs)
| Fnil.
```

Two details missing from simplified textbook ANF matter directly in the
lowering:

1. **`Efun` join continuations must become IR blocks, not functions.**
   When CertiRocq's ANF translator lowers `let x := match y with ... in e`,
   it binds `e` as a local 1-argument function `Fcons k ft [x] e Fnil`
   called in tail position (`Eapp k ft [r]`) from each branch so `e` is
   not duplicated. In CertiRocq's C backend, skipping `inline_shrink_loop`
   turned those continuations into the 21,175 hoisted `f_case_*` C
   functions seen on `Compile.compile`. Because Nanofil IR is a CFG with
   phis (`block(Label, Phis, Insts, Jump)`), any local `Fcons` whose
   uses are all tail `Eapp`s in scope lowers directly to a `block` with
   `phi(tmp(x), w, Pairs)` — no closure, no call, and no dependence on
   an exponential inlining loop.
2. **Constructor tags and stdlib primitives.** In λANF, `t : ctor_tag`
   is a global `positive` key into `ctor_env`, which gives both
   `ctor_arity` and `ctor_ordinal` (the 0-based index within one
   inductive, separate for 0-ary and boxed constructors). And as the
   19,616 `Ascii` allocations in `compile8.c` showed, stdlib `ascii`,
   `string`, `nat` and `Z` must be mapped before or at λANF lowering:
   `ascii` to immediate bytes `c: (byte << 1) | 1`, `string` to packed
   byte blocks in `arena[]`, and `Z` / `nat` to 31-bit signed/unsigned
   immediates with an overflow branch to multi-word arena bigints.

### Instruction-by-instruction lowering

Each hoisted λANF function lowers to a Nanofil IR `func` taking
`param(p, tmp(arena))`, `param(p, tmp(state))` (holding `young_idx`,
`major_idx`, `nursery_end`, and the shadow root stack pointer; `young_idx`
stays cached in a local `w` temporary between calls) and `param(w, tmp(Xi))`
for its λANF parameters. Following `LambdaANF_to_Clight_stack.max_allocs`,
all `Econstr` allocations along a call-free segment coalesce into **one**
nursery bound test `young_idx + max_words > NURSERY_END` at the head of
the segment:

| λANF form | Nanofil IR lowering (`arena : p`, values at class `w`) |
|---|---|
| `Econstr` (0-ary) | Bind `tmp(x)` at `w` to immediate `const(2 * ord + 1)`, continue with `e` |
| `Econstr` (`k`-ary) | Bump `idx = young_idx` by `k + 1`; `flight` + one `check(0, 4*(k+1), write, 4)` + `raw_store`s for header `(k << 10) \| ord` and `y1..yk`; bind `tmp(x)` to `idx << 1` |
| `Eproj` | Shift `idx = shr(y, 1)`, scale `4 * idx` at class `l`, `flight` + `check` + `raw_load(uw, 4*(i+1))` into `tmp(x)` |
| `Ecase` | Test `and(x, 1)`: immediate chain switches on `shr(x, 1)`; boxed chain loads `hdr = arena[x >> 1]` once and branches on `and(hdr, 255)`; local `Efun` join arms merge at a `block` with `phi` |
| `Eapp` (local) | Intra-CFG `goto(poll(L_f))` feeding `L_f`'s entry `phi`s (polls every cycle, zero stack growth) |
| `Eapp` (call) | Known `f`: `call` `global(F)` then `ret`. Closure `v`: load `fid` from field 0 of `v`, dispatch `ft`'s switch table |
| `Eletapp` | Push boxed temporaries in `FV(e) \ {x}` onto `state`'s `w` root stack, flush `young_idx`, `call` `f`, reload `young_idx` and spilled `FV(e)` (updated if GC ran), continue with `e` |
| `Eprim_val` / `Eprim` | Tagged 31-bit operations on `w` (e.g. `add`: `add(a, b - 1)` with 64-bit `l` overflow check when lowering `Z`) |
| `Ehalt` | Flush `young_idx` to `state`, `ret(tmp(x))` |

### Worked examples: `Cons` allocation and `list_sum` in checked IR

Allocating a 2-field `Cons(h, tl)` cell (boxed ordinal `0`, arity `2`,
so header `(2 << 10) | 0 = 2048`) after the segment's coalesced nursery
check emits one `flight`, one 12-byte `check`, and three `raw_store`
instructions sharing that proof:

```prolog
let(tmp(idx64), l, ext(uw), [tmp(yg)]).
let(tmp(off), l, shl, [tmp(idx64), const(2)]).
flight(tmp(dst), add, [address(tmp(arena)), tmp(off)], lower(tmp(arena))).
let(tmp(a), a, check(0, 12, write, 4), [tmp(dst)]). % covers header + 2 fields
raw_store(w, 0, const(2048), tmp(a)).               % header: arity 2, ordinal 0
raw_store(w, 4, tmp(h), tmp(a)).                    % field 0
raw_store(w, 8, tmp(tl), tmp(a)).                   % field 1
let(tmp(yg1), w, add, [tmp(yg), const(3)]).         % bump young_idx by 3 words
let(tmp(x), w, shl, [tmp(yg), const(1)]).           % even-tagged boxed index
```

Walking that list in tail-recursive `list_sum` (`Nil` immediate `1`, `h`
at `+4`, `tl` at `+8`) uses nothing outside
[Syntax.v](../rocq/theories/core/Syntax.v)'s core subset today:

```prolog
% Checked Nanofil IR for tail-recursive list_sum(arena, xs, acc).
% Nil = 1 ((0 << 1) | 1); Cons(h, tl) at idx has h at +4, tl at +8.
func(list_sum, local, w,
     [param(p, tmp(arena)), param(w, tmp(xs0)), param(w, tmp(acc0))], [
    block(entry, [], [], goto(loop)),
    block(loop, [
        phi(tmp(xs), w, [entry-tmp(xs0), step-tmp(tl)]),
        phi(tmp(acc), w, [entry-tmp(acc0), step-tmp(acc1)])
    ], [
        let(tmp(tag), w, and, [tmp(xs), const(1)])
    ], branch(tmp(tag), done, step)),
    block(step, [], [
        let(tmp(idx), w, shr, [tmp(xs), const(1)]),
        let(tmp(idx64), l, ext(uw), [tmp(idx)]),
        let(tmp(off), l, shl, [tmp(idx64), const(2)]),
        flight(tmp(cell), add, [address(tmp(arena)), tmp(off)], lower(tmp(arena))),
        let(tmp(a), a, check(0, 12, read, 4), [tmp(cell)]),
        touch(tmp(a)),
        let(tmp(h), w, raw_load(uw, 4), [tmp(a)]),
        let(tmp(tl), w, raw_load(uw, 8), [tmp(a)]),
        let(tmp(h0), w, sub, [tmp(h), const(1)]),
        let(tmp(acc1), w, add, [tmp(acc), tmp(h0)])
    ], goto(poll(loop))),
    block(done, [], [], ret(tmp(acc)))
]).
```

Notice what [Regs.v](../rocq/backend/Regs.v) ([Regs.valid_alloc])
already makes of this function without any new compiler pass:

- Both field reads (`+4` and `+8`) share **one** `check(0, 12, read, 4)`
  (fused through `touch(tmp(a))` at offset `0`, as [Fuse.v](../rocq/backend/Fuse.v)
  expects) under M7's forward [[evidence]] rules ([m7.md](m7.md), [stage_func]),
  because `raw_load(uw, 4)` is [evidence_preserving].
- `xs` and `acc` are integer `w` phis; `Regs.v` colors phi partners into
  the same callee-saved/scratch GPRs (`%r10`, `%r11`, `%rbx`,
  `%r12`–`%r15`) so the loop back-edge updates registers in place.
- Only **one** `p` capability (`tmp(arena)`) is live in the entire
  function: one slot in `lowers[]`, regardless of how deep the functional
  data structure is.

### Exact root scanning without Pizderson frame blowup

In λANF, a non-tail call occurs only at `Eletapp(x, f, ft, ys, e)`. The
values that must survive the call are exactly `FV(e) \ {x}`. Because
every one of them has class `w`, neither `frame_slots.pl` /
`FrameSlots.v` nor `FilPizlonator` treats them as pointer roots, and
FUGC never inspects functional stack frames. Instead, `Eletapp` writes
the live boxed `w` temporaries into a contiguous `c: uint32_t roots[]`
slice in `state` before calling `f`, and reloads them into fresh SSA
temporaries on return in case a minor collection evacuated nursery
blocks into major.

## 5. Zero-barrier Cheney minor GC

Because pure Gallina never mutates an existing constructor field, an
object in the major slice (`0 .. major_idx`) can **never** point into
the nursery (`NURSERY_BASE .. young_idx`): every child of a promoted
block was allocated before its parent and is evacuated alongside it.
Unlike OCaml or CertiRocq's general C runtime (`gc_stack.c`), the minor
collector needs **no write barrier and no remembered set**.

When a segment's coalesced nursery test `young_idx + max_words > NURSERY_END`
fires, a self-contained Cheney evacuator copies only live nursery
survivors into `major_idx` and resets `young_idx = NURSERY_BASE`:

```c -O
#include <stddef.h>
#include <stdint.h>

struct anf_state {
    uint32_t young_idx;
    uint32_t major_idx;
    uint32_t nursery_base;
    uint32_t major_limit;
    uint32_t root_sp;
};

static uint32_t evacuate_word(uint32_t *arena, struct anf_state *st, uint32_t w) {
    if (w & 1U)
        return w;
    uint32_t idx = w >> 1;
    if (idx < st->nursery_base)
        return w;
    uint32_t hdr = arena[idx];
    if (hdr == 0xFFFFFFFFU)
        return arena[idx + 1] << 1;
    uint32_t arity = hdr >> 10;
    uint32_t dst = st->major_idx;
    st->major_idx = dst + arity + 1U;
    arena[dst] = hdr;
    for (uint32_t i = 1; i <= arity; i++)
        arena[dst + i] = arena[idx + i];
    arena[idx] = 0xFFFFFFFFU;
    arena[idx + 1] = dst;
    return dst << 1;
}

void minor_gc(uint32_t *arena, uint32_t *roots, struct anf_state *st) {
    uint32_t scan = st->major_idx;
    for (uint32_t r = 0; r < st->root_sp; r++)
        roots[r] = evacuate_word(arena, st, roots[r]);
    while (scan < st->major_idx) {
        uint32_t arity = arena[scan] >> 10;
        for (uint32_t i = 1; i <= arity; i++)
            arena[scan + i] = evacuate_word(arena, st, arena[scan + i]);
        scan += arity + 1U;
    }
    st->young_idx = st->nursery_base;
}
```

> Click **IR** on `minor_gc` or `evacuate_word` above on the site to
> inspect the exact checked Nanofil IR that nanofil's C frontend and
> pizlonator already emit for the collector itself.

### What happens when the major slice grows

Cheney minor evacuation reclaims the 95–99% of functional allocations
that die in the nursery, but long compilations still promote survivors.
Two regimes need distinguishing:

- **Per-unit and streaming runs.** A regex compile in `rxc` (`rx.ir`)
  holds ~30 MB live at most; [EmitModule.v](../rocq/backend/EmitModule.v)
  already compiles SQLite one module item at a time so assembly lines do
  not stay live across the whole file. Resetting `major_idx = 0` (and
  calling `MADV_DONTNEED` past a threshold) between independent units
  reclaims the entire major heap in `O(1)`.
- **Whole-module compiles.** SQLite's 78 MB IR text peaked at 1.3 GB in
  OCaml ([gallina-backend.md](gallina-backend.md), M4). If promoted data
  within a single unit ever approaches `major_limit`, two remedies stay
  inside the 32-bit `w` representation: a larger virtual major range (up
  to `8 GiB - 4 MiB` with `MAP_NORESERVE`), or a two-finger / semi-space
  major compaction pass run from the same `roots[]` stack when
  `major_idx + (young_idx - nursery_base) > major_limit`. If even the 8 GiB
  addressable limit is exceeded, the runtime traps with `OutOfMemory` —
  which [Panics.v](../rocq/theories/logic/Panics.v) classifies as a [refusal],
  not a safety failure.

## 6. IR extensions, `Semantics.v`, `Logic.v`, and the validator

### Does `call` have or need a tail form?

In [ir.pl](../src/ir.pl) and [Syntax.v](../rocq/theories/core/Syntax.v) today,
`call(Res, Callee, Args)` and `raw_call(Res, Callee, Args)` are ordinary
block instructions ([Syntax.inst]), **not** block-ending jumps
([Syntax.jump]); every Fil-C function pushes a Pizderson root frame on
entry (`filc_abi:lower_function/5`), restores it at `ret`, and tests
`%al` for unwinding after a call (`c_types.pl` treats C's `musttail`
attribute as a hint and lowers it to an ordinary call).

Whether λANF needs a tail-call instruction depends on which calls remain
after CFG lowering:

1. **Self-recursion, mutual `Efun` clusters, and join continuations.**
   No new IR form is needed. Lowering a tail `Eapp` within one function
   (or a mutually recursive cluster merged into one `func` with an entry
   tag dispatch) emits `goto(poll(L))` with `phi` arguments — zero stack
   frames and full register coalescing in `Regs.v`.
2. **Cross-function calls in direct-style ANF (`--direct`).** CertiRocq
   compiles in direct style by default (its `--cps` mode overflows the C
   stack on its own benchmarks). Cross-cluster `Eapp` depth is bounded
   by real call depth, and functional frames hold at most one `p` root
   (`arena`). Ordinary `call` followed by `ret` suffices unless a pass
   recurses deeply across unmerged higher-order functions.
3. **Unbounded cross-function tail calls.** Only if measurement on
   `Compile.compile` shows deep mutual or closure tail chains would we
   choose between a module-level dispatch trampoline (zero IR changes)
   and a genuine `tail_call` / `raw_tail_call` jump in [Syntax.jump]
   (popping the Pizderson frame before jumping when fast signatures
   match, at the cost of adding a constructor to every proof over
   `jump`). Keep `ir.pl` and `Syntax.v` untouched first and measure.

### Connecting to `Validate.v`, `Semantics.v`, and `Logic.v`

Because λANF lowers to standard checked Nanofil IR, it connects to the
formal campaign ([formal.md](formal.md), [logic.md](logic.md)) in four
distinct steps, each useful before the next is proved:

```diagram
Safety now: λANF lowering ─▶ Validate.valid ─▶ valid_no_unchecked ─▶ GIMSO
Panic-free: arena_inv ─▶ Logic.v WP rules ─▶ Logic.heap_never_panics ─▶ never_panics
Zero-check: entry span_test ─▶ Campaign 5 discharged(Cert) ─▶ raw movl
Refinement: MetaRocq λ□ ─▶ LambdaANF.eval ─▶ step_rel simulation ─▶ verified compiler
```

1. **Immediate GIMSO safety via the validator (`Validate.v`, `Soundness.v`).**
   Before any proof is written about `anf_lower`, its output passes
   [valid_fast] (`= [Validate.valid]`). By [valid_no_unchecked], no run
   ever reaches an [[unchecked]] access: a bug in `anf_lower` or in
   `minor_gc` can at worst trigger a clean Fil-C [[trap]], never memory
   corruption, even inside an untrusted C host process.
2. **Proving `[never_panics]` in [Logic.v](../rocq/theories/logic/Logic.v) without the full heap graph.**
   In today's validator, live check evidence is cleared at every
   `poll(L)` edge and `call`, because arbitrary C code might `free` a
   heap object. In [Logic.v](../rocq/theories/logic/Logic.v), however,
   [Runtime.v](../rocq/theories/core/Runtime.v)'s axiom [collector_live]
   guarantees that no safepoint ever frees a live region, and a pure
   λANF module never calls `free`. Even better, **spatial safety of
   `Eproj` does not depend on the GC graph invariant**: for any 32-bit
   `w` value `y` (`0 <= y < 2^32`) and any static field index
   `0 <= i < 1023`, the shifted word index `y >> 1` satisfies
   `0 <= y >> 1 < 2^31`, so the byte access `[4*(y>>1) + 4*(i+1), +4)`
   always lies below `2^33 + 4096` bytes (`SLAB_END` with the 4 KiB
   guard tail)! Only `Econstr` and `minor_gc` writes need the simple
   scalar bounds `0 <= major_idx <= nursery_base <= young_idx <= nursery_end`:

```rocq
Definition arena_bounds (base len : Z) (mj yg nb ne : Z) : Prop :=
  len = 2 ^ 33 + 4096 /\
  0 <= mj /\ mj <= nb /\
  nb <= yg /\ yg <= ne /\
  4 * ne <= 2 ^ 33.
```

   Combining `arena_bounds` with the Iris `live` token (`Heap.v`) proves
   [never_panics] via [Logic.heap_never_panics] by local arithmetic
   (`lia`) and Löb induction across `poll(L)` edges.
3. **Erasing bounds checks statically (`formal.md` Campaign 5).**
   Today's `ir.pl` cannot drop the `check` before an `Eproj` across a
   `poll` or `call` without a validator extension (`span_test` +
   [RenewIf] still tests the `FREE` flag natively and expires at
   safepoints). Once Campaign 5's `discharged(Cert)` gate accepts an
   entry `span_test(0, 2^33 + 4096)` paired with a `no-free` certificate
   from step 2, every `Eproj` lowers to a single bare x86-64 load
   (`movl 4(%rax,%rcx,4), %edx`) with zero check branches while keeping
   [valid_no_unchecked] closed.
4. **Functional correctness (`LambdaANF.eval` to [step_rel]).**
   Proving that the lowered IR computes the same result as Gallina uses
   the full representation relation — linking CertiRocq's big-step
   `bstep_cost` (`LambdaANF/eval.v`) to [Semantics.v](../rocq/theories/core/Semantics.v)'s
   small-step [step_rel] through Cheney's graph isomorphism on
   `arena[]`. Together with a verified backend simulation from `step_rel`
   to `Asm.v`, this closes the self-hosting loop noted at the end of
   [gallina-backend.md](gallina-backend.md).

### The C FFI boundary for `libnanofil`

At the module boundary, a Gallina library compiled via λANF → Nanofil IR
exposes ordinary Fil-C entry points — for example
`c: int nanofil_compile_nfb(const uint8_t *in_buf, size_t in_len, uint8_t **out_buf, size_t *out_len)` —
whose input and output buffers are standard Fil-C `p` capabilities. A
thin wrapper copies `in_buf` into a packed byte block in the private
arena, runs the pure `w`-word compiler, copies the emitted assembly or
object bytes out into a fresh Fil-C buffer, and resets `young_idx` and
`major_idx` (or `MADV_DONTNEED`s the major slice). Neither `clang` nor
`filc++` ever compiles generated C or C++ for the compiler itself.

## 7. Knowns, hypotheses, and what needs measuring

| Status | Claim and basis / measurement needed |
|---|---|
| **Known** | `ocamlopt` compiles `rx.ir` in `0.26–0.34 s` (`56–60 MB`); Crane C++ mutator work is `~0.30 s` alongside `65–70%` in `libgc` over 17.65M allocations ([gallina-backend.md](gallina-backend.md), M6/M8) |
| **Known** | `filcc` hit 8.9 GB / 17 min in `computeFrameIndexMap` on Crane's monolithic 36k-line C++; stopped without diagnosing the pass or measuring FUGC at run time (M8) |
| **Known** | CertiRocq C (`--anf-variant 8`, 16 shards) matches OCaml byte-for-byte: native `clang -O1` takes `8.89–13.77 s` on `rx.ir` and `48.95–91.42 s` (`1,065 MB`) on `lvm.ir`, needing `ulimit -s unlimited` because `&frame` blocks tail calls; `filcc -DVERIFFI -O1` builds in `176.3 s` and runs `rx.ir` `compile` in **`165.4 s` / `994 MB`** (18.6× native C, ~500× OCaml) because every `value` is a `void *` capability ([CertiRocq C thread](https://ampcode.com/threads/T-01a1c7da-3aaf-76c0-bea7-1603749ae0bc)) |
| **Known** | `Regs.v` reaches `1.05×` of Prolog `-O` on regex code and compiles `rx.ir` in `0.30 s` (M7) |
| **Known (M0)** | On `list_sum`, `term_eqb` and persistent `avl` ([bench/arena/](../bench/arena/)), `nanofil-backend compile-allocated` over the 32-bit `w` arena runs at **`1.98×` `ocamlopt` today** (checked IR) and **`1.69×` with check erasure** (matching `filcc -O2` C arena's `1.64×`), vs. **`2.69×`** for a `void *` `-DVERIFFI` nursery and **`7.38×`** for per-node `malloc` + FUGC |
| **Hypothesis** | Scaling from M0's kernels to full `Compile.compile` on `rx.ir` stays within `1.5–2×` of `ocamlopt` once CFG join recovery and mapped 31-bit `Z` / `nat` / packed `string` are in place (tested in M3) |
| **Hypothesis** | Lowering local join `Efun`s and tail loops to `goto(poll(L))` + `phi` (with no `&frame` address-taking on the native stack) eliminates the 8 MB stack overflow seen in CertiRocq C without adding a cross-function `tail_call` jump |
| **Known (M1)** | `zsys_mmap` (`MAP_NORESERVE`, `fugc_destructor_heap`) grants up to **`4 TiB`** in one reservation at **`8 KiB/GiB`** chunk-map overhead (**`+0.37 MiB`** RSS for the full `8 GiB + 4 KiB` arena), `zsys_madvise` (`MADV_DONTNEED`) reclaims `64 MiB` and `256 MiB` major slices immediately while keeping the `arena` capability valid, and [anf/](../anf/) passes 10,000 randomized tree-rewrite steps (1,851 minor GCs in a 256-word nursery) under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1` |

## 8. Milestones

Each milestone ends with a runnable gate and a recorded measurement, on
the pattern of [gallina-backend.md](gallina-backend.md).

**M0. Hand-lowered arena probe against `ocamlopt` and `filcc -DVERIFFI`.**
With the [CertiRocq C baseline](https://ampcode.com/threads/T-01a1c7da-3aaf-76c0-bea7-1603749ae0bc)
in hand (`8.89 s` native C and `165.4 s` / `994 MB` under
`filcc -DVERIFFI` on `rx.ir`), write three representative recursive
kernels (`list_sum`, `term_eqb`, AVL lookup + insert) directly in
Nanofil IR over the 32-bit arena, compiled by
`nanofil-backend compile-allocated`, both with standard `check`s and
with hoisted `span_test` / raw loads. Gate: difftest parity and `perf stat`
instruction + L1/L2 miss counts against `ocamlopt` and `filcc`.

*Done* ([bench/arena/](../bench/arena/)). `kernels.ir` (1,060 lines of
checked IR: `evacuate_word`, `minor_gc`, `list_build`, `list_sum`,
`term_build`, `term_eqb`, and persistent `FMapAVL`-shaped `avl_insert`,
`avl_bal` and `avl_lookup`) validates with [valid_fast], allocates with
[Regs.v](../rocq/backend/Regs.v), passes `difftest.sh` (`interp.pl` vs.
native Fil-C over a 64-word nursery forcing evacuations mid-recursion; a
planted un-reloaded `roots[]` bug fails immediately), and passes a
1,024-word nursery stress run (47,434 minor GCs) under
`FUGC_SCRIBBLE=1 FUGC_VERIFY=1`. Median wall times over 7 interleaved
CPU-pinned rounds on an orb (`scale = 3`: 24.6M `Cons` cells, 11.8M
`Term` blocks, 7.2M 24-byte `AVL` nodes; hardware PMU counters are
masked in the orb VM and can be collected on `swa`):

| Mode | `list_sum` | `term_eqb` | `avl` | Geomean | RSS |
|---|---:|---:|---:|---:|---:|
| `ocamlopt -O2` | 150.7 ms | 106.1 ms | 169.1 ms | **1.00×** | 9.5 MB |
| `c-arena-native` (`gcc -O2`) | 168.1 ms | 104.3 ms | 161.7 ms | **1.02×** | 19.3 MB |
| `c-arena-filcc` (`filcc -O2`) | 234.8 ms | 170.0 ms | 299.8 ms | **1.64×** | 46.7 MB |
| `arena-ir-erased` (`Regs.v`, no checks) | 236.3 ms | 179.0 ms | 309.0 ms | **1.69×** | 46.7 MB |
| `arena-ir-checked` (`Regs.v`, today) | 266.4 ms | 221.2 ms | 354.1 ms | **1.98×** | 46.7 MB |
| `filc-veriffi` (`void *` nursery) | 472.8 ms | 337.2 ms | 328.3 ms | **2.69×** | 99.8 MB |
| `filc-fugc` (per-node `malloc`) | 1082.4 ms | 1071.2 ms | 937.7 ms | **7.38×** | 35.9 MB |

Four findings shape M1–M5:

- **Within 2× of `ocamlopt` today, with zero IR or backend changes.**
  `arena-ir-checked` hits **1.98×** (`1.77×` to `2.09×`) using existing
  `check(0, Size, Rights, 4)` + `touch` + `FReused` field sharing.
- **Check erasure buys 15% (`1.98× → 1.69×`) and matches `filcc -O2` (`1.64×`).**
  Stripping the 96 inline check blocks (`erase_checks.py`: `list_sum`
  loop `36 → 24` x86-64 instructions, `list_build` `49 → 35`,
  `avl_lookup` `49 → 37`) brings `Regs.v` within 3% of Clang/LLVM `-O2`
  on the same arena. The remaining `1.02× → 1.69×` gap over native C is
  Fil-C's `poll` safepoints on loop back-edges and Pizderson frame
  push/pop on recursive calls (`term_eqb`, `avl_insert`).
- **FUGC per-node allocation is 7.38× (`10.10×` on `term_eqb`).** This
  supplies the runtime figure M8 could not measure on Crane: allocating
  tens of millions of short-lived 16–48 B functional nodes through
  `malloc` + FUGC is dominated by per-object allocation, `ensure_aux`
  and concurrent marking.
- **Even with mapped C ints, a `void *` nursery costs 2.69× and 2× RSS.**
  Isolating `-DVERIFFI` from CertiRocq's unary-`nat`/`Ascii` bloat still
  leaves a 1.6× runtime and 2.1× memory penalty over the 32-bit `w`
  arena from dual-space `intval` + `aux` writes and FUGC barriers.

**M1. The arena and Cheney collector as a verified-clean Fil-C module.**
Implement `anf_arena_init` (`zsys_mmap` / `zsys_madvise`), `minor_gc`,
shadow root helpers, packed byte blocks and 31-bit/bigint `Z` helpers in
~200 lines of C/IR compiled by nanofil. Stress with a 256-word nursery
under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1` so evacuation runs every few
hundred constructors, plus `OutOfMemory` boundary tests. Gate: zero
panics or memory mismatches across 10,000 randomized tree-rewrite steps;
measured RSS of `MAP_NORESERVE` and `MADV_DONTNEED`.

*Done* ([anf/](../anf/)). `anf_arena.c` (`anf_arena_init`,
`anf_arena_reset`, `anf_arena_destroy`, `anf_minor_gc`, inline shadow
`roots[]` at `st + 1` so neither `arena` nor `st` allocates an `aux`
table, `ANF_ST_BYTES` no-scan byte blocks, canonical 31-bit /
base-`2^32` `ANF_ST_BIGINT` `Z` helpers, and `anf_oom` lowering
`__builtin_alloca((1ULL << 48) - 1)` to a core `alloc(16)` that every
runtime refuses with [OutOfMemory]) compiles cleanly through both Prolog
`nanofil -O` and `nanofil-backend compile-allocated` ([valid_fast] +
[Regs.valid_alloc], byte-identical on `compile`, `compile-promoted` and
`compile-nfb`). Under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1` over a **256-word
nursery**, `test_arena.c` passes a `28^2`-pair differential `Z` suite
spanning `0` through `2^192` (49 minor GCs), adversarial `ANF_ST_BYTES`
blocks containing raw nursery-pointer-lookalike words (22 minor GCs),
**10,000 randomized algebraic tree-rewrite steps** with DAG diamond
sharing and mid-run `MADV_DONTNEED` resets (**1,851 minor GCs**, 63,658
words promoted, zero panics or mismatches), and `SIGTRAP` [OutOfMemory]
boundary checks (major exhaustion, oversized allocation, shadow root
overflow); five planted bugs (omitted forwarding marker, scanning
`ANF_ST_BYTES` or `ANF_ST_BIGINT` payloads, `-2^30` normalization
off-by-one, and omitted `major_limit` check) each fail immediately.
Orb RSS lifecycle on the full `8 GiB + 4 KiB` (`2^33 + 4096` B) arena
(`probe_mmap.c`, under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`):

| Stage (`8 GiB + 4 KiB` slab) | `VmRSS` | `ΔRSS` | `AnonDirty` |
|---|---:|---:|---:|
| Process baseline | 29.04 MiB | +0.00 MiB | 8.29 MiB |
| `anf_arena_init` (`+1 MiB` roots) | 29.41 MiB | **+0.37 MiB** | 8.41 MiB |
| Fault `4 MiB` nursery + guard | 33.24 MiB | +4.20 MiB | 12.78 MiB |
| Fault `64 MiB` in `major` | 97.43 MiB | +68.40 MiB | 76.80 MiB |
| `MADV_DONTNEED` reset (`64 MiB`) | 33.47 MiB | **+4.44 MiB** | 12.81 MiB |
| Fault `256 MiB` in `major` | 289.47 MiB | +260.43 MiB | 268.84 MiB |
| `MADV_DONTNEED` reset (`256 MiB`) | 33.51 MiB | **+4.48 MiB** | 12.85 MiB |
| After 5 FUGC cycles (arena live) | 33.66 MiB | +4.63 MiB | 13.26 MiB |

Two runtime details from `libpas` explain these numbers and guide M2–M4:

- **`8 KiB/GiB` chunk-map cost up to `4 TiB`.** In `verse_heap`,
  `finish_allocate_large` skips `pas_zero_memory` on
  `FILC_OBJECT_FLAG_MMAP` allocations and records one 4-byte
  `verse_heap_chunk_map_entry` per 512 KiB chunk (`8 KiB/GiB` of virtual
  span: measured `+0.61 MiB` RSS at `16 GiB`, `+2.50 MiB` at `256 GiB`,
  `+8.51 MiB` at `1 TiB`, `+32.51 MiB` at `4 TiB`).
- **Keep one persistent module arena; reset with `MADV_DONTNEED`.** While
  `arena` is live, FUGC never touches its payload even under
  `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`. Because `fugc_destructor_heap` joins
  `fugc_scribble_set` when `FUGC_SCRIBBLE=1`, however, sweeping a *dead*
  (unmapped/unreachable) `MMAP` object calls `c: memset(start, 0xac, size)` across its
  full virtual length; keeping a single module-lifetime `8 GiB` arena and
  releasing promoted pages via `anf_arena_reset` (`zsys_madvise`) avoids
  dead-slab scribbling while reclaiming physical RAM in `O(1)`.

**M2. Core λANF → Nanofil IR compiler with CFG join recovery.**
Write `AnfLower.v` in Gallina, tapping CertiRocq's λANF pipeline after
`closure_conversion_hoist` (`--anf-variant 8` — no `inline_shrink_loop`):
recover local tail-called `Efun` continuations as `block` + `phi`,
compile self/cluster `Eapp` to `goto(poll(L))`, assign dense IDs to
hoisted functions for pure-`w` closures, coalesce `max_allocs` nursery
checks, and emit checked [Syntax.module] items validated by [valid_fast]
and lowered by [Compile.compile_allocated]. Gate: CertiRocq's standalone
programs and `rocq/backend/Asm.v` + `Order.v` match `ocamlopt` byte for
byte.

**M3. Stdlib mappings (`Z`, `nat`, `ascii`, `string`) and `Compile.compile`.**
Map `ascii` to immediate `w` tags, `string` to packed arena byte blocks,
and `Z` / `nat` to 31-bit tagged immediates with arena bigint fallback,
held by a `SelfTest.v` differential suite against `vm_compute` (including
values across `2^30`, `2^31` and `2^64`, as `CraneSelfTest.v`
does). Compile `read_text`, [Compile.compile], [Compile.compile_promoted]
and [Compile.compile_allocated] to a Fil-C binary via `nanofil-backend`.
Gate: byte-identical assembly on all 376 C corpus units and 38 IR
fixtures, and runtime on `rx.ir` within 2× of `ocamlopt` (or the gap
profiled to instruction level).

**M4. In-process `libnanofil` and three-stage self-hosting.**
Link the arena-compiled Gallina backend behind `nanofil_compile_nfb` /
`nanofil_compile_ir` as a pure Fil-C shared library (`libnanofil.so`),
wire `rxc` to call it in-process without spawning `nanofil-backend`, and
run a three-stage bootstrap: stage 1 (`ocamlopt` build) compiles the
λANF of the backend + `AnfLower.v` to stage 2 (Fil-C ELF), which
compiles the same NFB/λANF input to stage 3 assembly. Gate: stage 2 and
stage 3 assembly are byte-identical; `rxc` passes all 39 hook patterns
under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1` with recorded cold-miss latency.

**M5. `never_panics`, Campaign 5 check erasure, and λANF simulation.**
Prove `arena_bounds` + `live` preservation in [Logic.v](../rocq/theories/logic/Logic.v)
to establish [never_panics] for lowered modules ([Logic.heap_never_panics]),
discharge the arena `check`s through Campaign 5's certificate gate so
`Eproj` and `Econstr` emit single `movl` instructions with
[valid_no_unchecked] intact, and prove forward simulation from
`LambdaANF.eval` to [Semantics.v](../rocq/theories/core/Semantics.v)'s
[step_rel].

## Decisions wanted

Each has a recommendation so M0 can start without waiting.

1. **Where to tap MetaRocq / CertiRocq.** Recommended: tap
   post-closure-conversion λANF under `--anf-variant 8` (reusing
   CertiRocq's erasure, uncurrying, lambda-lifting and closure
   conversion while skipping `inline_shrink_loop`, since CFG join
   recovery handles `f_case_*` continuations in linear time), rather than
   writing uncurrying and closure conversion again from `λ□`.
2. **Grammar stability in M0–M4.** Recommended: change nothing in
   `ir.pl` or `Syntax.v` through M4. Use existing `check`s with M7
   adjacency reuse, `goto(poll(L))` for intra-function tail loops, and
   ordinary `call` for cross-function calls; revisit Campaign 5 check
   discharge and any `tail_call` terminator only with M0 and M3 profiles
   in hand.
3. **One Fil-C capability for the arena, no runtime escape hatch.**
   Recommended: allocate the arena through `zsys_mmap` (`p` capability
   with `FILC_OBJECT_FLAG_MMAP`) rather than adding any unchecked raw
   pointer mode to the runtime, so GIMSO and [valid_no_unchecked] hold
   unconditionally from M0 onward.
