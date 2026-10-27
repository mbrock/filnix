# Code quality: where nanofil -O spends its instructions, and the plan

nanofil should be usable for Linux userland programs. Fil-C's own
overhead is accepted; nanofil's on top of it should not be obscene.
The target is QBE-class code: roughly within 1.5–2× of filcc `-O2` in
time, without vectorization or sophisticated arithmetic analysis. This
file holds the benchmark gate, a profile of where `-O` spends its
instructions, and a ranked plan. It is separate from the semantic
campaign ([campaign.md](campaign.md)): nothing here weakens a check,
and safety decisions are flagged for review before implementation.

## The benchmark gate

[`bench/`](../bench) builds zlib 1.3.2 (`minigzip`), bzip2 1.0.8, lz4
1.10.0 and Lua 5.4.7 with filcc `-O2` (`ref`) and with nanofil in each
mode, through the same `nanofil-cc` wrapper the Nix checks use:

| Mode | nanofil options |
| --- | --- |
| `off` | none: the reference backend without the middle end |
| `O` | `-O` (with selected branches, item 2) |
| `O-reuse` | `-O --checks=reuse` ([m7.md](m7.md)) |
| `O-local` | `-O --registers=local` ([m6.md](m6.md)) |
| `O-refbranches` | `-O --branches=reference`: `-O` before item 2 became its default |
| `O-function` | `-O --registers=function` (item 3a below; `--argstr only O,O-function` builds a subset) |

From the repository root, on swa (or any quiet x86-64 machine with perf):

```sh
nix build --impure -f nanofil/bench -o nanofil/bench/out
cd nanofil/bench && python3 run.py            # --trials N --cpu C --modes ref,O --only lua
```

`run.py` first runs every workload with every build and requires its
stdout to equal ref's byte for byte. Then it runs one warm-up round and
seven timed rounds; within a round each workload runs every mode in a
shuffled (seeded) order, pinned to one CPU under `perf stat`, which
counts user instructions and task-clock. Before each run it waits until
the pinned core and its SMT sibling are below 5% busy. It prints
medians, each mode's ratio to ref (time, with instructions in
parentheses, and the trials' min..max), the geometric means, and writes
the samples to `results.json`. A full run takes about ten minutes.

The inputs are built by Nix from pinned sources only: `text` is the
sorted C sources of the four tarballs, repeated to 4 MiB; `random` is
4 MiB of SHA-256 counter output. The workloads compress and decompress
them (decompression inputs are ref's own output) and run three Lua
scripts: [int.lua](../bench/int.lua) (an integer loop),
[tab.lua](../bench/tab.lua) (table reads) and
[str.lua](../bench/str.lua) (string formatting, sort, gsub).

It is not part of `nix flake check`: timings need a quiet machine.

filcc is not deterministic: compiling the same file twice gives different
code (October 2026; zlib's `deflate.c`, bzip2's `blocksort.c`, lz4's
`lz4.c` and `lz4hc.c` all differ run to run, and three compiles of
`lz4.c` disassemble to 57,561, 57,729 and 57,594 lines). A rebuilt filcc
lz4 ran `-9` in 2.99G instructions once and 2.84G another time. The
cause is FilPizlonator's check order, which follows heap addresses
([abi-findings.md](abi-findings.md#filcc-output-depends-on-heap-addresses)). So pin
the reference: `run.py` and `profile.py` take filcc's builds from
`bench/ref` when it exists (`--ref DIR`), else from `out`. Pin once with

```sh
nix-store --add-root nanofil/bench/ref --realise $(readlink -f nanofil/bench/out)
```

and compare runs only against the same `ref` (run.py prints its path).

### Baseline (October 2026)

At [`ab05a5b`](https://github.com/mbrock/filnix/commit/ab05a5b682bb) on
swa (Ryzen 9 7950X3D, CPU 6), seven trials, median task-clock in ms with
user instructions:

| Workload | ref | off | O | O-reuse | O-local |
|---|--:|--:|--:|--:|--:|
| zlib -6 text | 133.4 ms, 1.96G | 1128.0 ms, 23.87G | 613.0 ms, 11.72G | 616.2 ms, 11.72G | 590.1 ms, 11.52G |
| zlib -d text | 17.8 ms, 0.19G | 106.9 ms, 2.38G | 59.8 ms, 0.89G | 58.1 ms, 0.89G | 54.0 ms, 0.87G |
| bzip2 -9 text | 273.6 ms, 4.67G | 2562.2 ms, 52.47G | 981.8 ms, 18.56G | 979.3 ms, 18.56G | 898.1 ms, 18.04G |
| bzip2 -d text | 93.4 ms, 1.43G | 527.5 ms, 11.90G | 581.1 ms, 6.63G | 580.0 ms, 6.63G | 547.0 ms, 6.42G |
| lz4 -1 random | 13.5 ms, 0.03G | 145.3 ms, 2.23G | 53.2 ms, 0.71G | 52.1 ms, 0.71G | 50.8 ms, 0.71G |
| lz4 -9 text | 164.2 ms, 2.99G | 4580.2 ms, 73.54G | 1066.1 ms, 17.91G | 1079.0 ms, 17.91G | 959.7 ms, 17.54G |
| lz4 -d text | 12.6 ms, 0.07G | 181.8 ms, 3.13G | 81.5 ms, 1.29G | 83.1 ms, 1.29G | 81.0 ms, 1.30G |
| lua int | 53.0 ms, 1.19G | 706.2 ms, 13.76G | 335.5 ms, 7.27G | 338.8 ms, 7.27G | 325.0 ms, 7.00G |
| lua tab | 42.7 ms, 0.98G | 431.8 ms, 9.86G | 266.4 ms, 5.66G | 265.2 ms, 5.66G | 256.4 ms, 5.46G |
| lua str | 263.2 ms, 3.53G | 2939.9 ms, 37.44G | 503.4 ms, 7.41G | 500.6 ms, 7.40G | 488.9 ms, 7.30G |

Ratio to filcc `-O2`, time (instructions):

| Workload | off | O | O-reuse | O-local |
|---|--:|--:|--:|--:|
| zlib -6 text | 8.45 (12.16) | 4.59 (5.97) | 4.62 (5.97) | 4.42 (5.87) |
| zlib -d text | 6.00 (12.32) | 3.36 (4.62) | 3.26 (4.62) | 3.03 (4.47) |
| bzip2 -9 text | 9.36 (11.23) | 3.59 (3.97) | 3.58 (3.97) | 3.28 (3.86) |
| bzip2 -d text | 5.65 (8.34) | 6.22 (4.65) | 6.21 (4.65) | 5.86 (4.50) |
| lz4 -1 random | 10.79 (74.92) | 3.95 (23.91) | 3.87 (23.90) | 3.77 (23.97) |
| lz4 -9 text | 27.90 (24.62) | 6.49 (6.00) | 6.57 (6.00) | 5.85 (5.87) |
| lz4 -d text | 14.45 (44.00) | 6.48 (18.22) | 6.61 (18.22) | 6.43 (18.23) |
| lua int | 13.32 (11.59) | 6.33 (6.12) | 6.39 (6.12) | 6.13 (5.89) |
| lua tab | 10.11 (10.05) | 6.24 (5.76) | 6.21 (5.76) | 6.00 (5.57) |
| lua str | 11.17 (10.59) | 1.91 (2.10) | 1.90 (2.09) | 1.86 (2.07) |
| geomean | 10.58 (16.40) | 4.61 (6.30) | 4.60 (6.30) | 4.36 (6.16) |

`-O` is 2–6× slower than filcc, 4.5× by the geometric mean, and the
time ratios follow the instruction ratios except where noted below.
`--checks=reuse` changes nothing after `-O` ([m7.md](m7.md)), and
`--registers=local` gains about 5%.

## Where the instructions go

### Method

Instruction-level attribution needs to know what produced each emitted
instruction. [`bench/profile/marks.patch`](../bench/profile/marks.patch)
makes a copy of the emitter put a local label before each IR
instruction, each ABI action, each part of a jump (branch test, phi
copies, poll, jump) and each frame-slot access (naming the slot's kind:
temporary, lower, phi shadow, thread, aux). Local labels change no code:
the marked and unmarked objects' `.text` are identical.
[`bench/profile`](../bench/profile/default.nix) builds the four programs
with it at `-O` and assembles them with `as -g`, so each instruction's
DWARF line is its line in the marked `.s`:

```sh
nix build --impure -f nanofil/bench -o nanofil/bench/out      # inputs and filcc builds
nix build --impure -f nanofil/bench/profile -o nanofil/bench/profile/out
cd nanofil/bench/profile && python3 profile.py                 # valgrind on PATH or $VALGRIND
```

`profile.py` counts the exact executed instructions per `.s` line with
cachegrind (`--cache-sim=no`) and classifies each line by the marker
before it and its form. If the patch stops applying after emitter
changes, regenerate it from a marked copy. Valgrind needs `--aspace-minaddr=0x100000000`: Fil-C's
ioctl wrapper asserts that an integer argument below 4 GiB is not a heap
pointer, and valgrind otherwise places the heap there. Cachegrind's
totals agree with perf's to within 0.1% for the compressors; Lua differs
by up to 1G instructions in GC threads, which this attribution counts as
runtime. IBS op sampling (`perf record -e ibs_op/cnt_ctl=1/u`) of the
same marked binary agreed within about 2 points per category, except that
macro-fused `test`/`jz` pairs count as one op there.

| Category | Instructions |
| --- | --- |
| scalar temps | `rbp` loads and stores of `w`/`l`/`s`/`d` temporaries and phi shadows: operand loads, result stores, phi copies |
| pointer temps | the same for `p` addresses, and temporaries moved at call sites |
| checks | the access check sequence (`test`, `cmp`, upper load, `sub`, `jb`/`ja`, flags and alignment) |
| lowers | loads and stores of `lowers[]` entries: flight pointers, phis, call arguments |
| calls/frames | prologue, epilogue, frame push/pop, roots zeroing, origins, call sequences, getters, thunks |
| polls | pollchecks on back edges |
| selection | constant moves, `setcc`/`movzbl` of booleans, `test`/`jz` of them, unconditional jumps |
| ops | the operation itself: ALU instruction, memory access, address arithmetic, `movs`/`movz` extension |
| runtime | everything outside nanofil's code: libc, the Fil-C runtime, the GC |

### Result

At [`3576b51`](https://github.com/mbrock/filnix/commit/3576b5180f1b),
nanofil `-O`, billions of instructions (share of nanofil's total):

| Workload | filcc | nanofil -O | scalar temps | pointer temps | checks | lowers | calls/frames | polls | selection | ops | runtime |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| zlib -6 | 1.97 | 11.73 | 2.97 (25%) | 1.42 (12%) | 2.70 (23%) | 1.31 (11%) | 0.14 (1%) | 0.11 (1%) | 1.53 (13%) | 1.51 (13%) | 0.02 (0%) |
| zlib -d | 0.20 | 0.90 | 0.23 (26%) | 0.11 (12%) | 0.17 (19%) | 0.11 (12%) | 0.06 (7%) | 0.01 (1%) | 0.10 (11%) | 0.09 (10%) | 0.02 (2%) |
| bzip2 -9 | 4.69 | 18.56 | 4.08 (22%) | 2.12 (11%) | 5.20 (28%) | 1.72 (9%) | 0.36 (2%) | 0.17 (1%) | 2.06 (11%) | 2.83 (15%) | 0.03 (0%) |
| bzip2 -d | 1.43 | 6.63 | 2.21 (33%) | 0.69 (10%) | 1.34 (20%) | 0.64 (10%) | 0.06 (1%) | 0.06 (1%) | 0.80 (12%) | 0.80 (12%) | 0.02 (0%) |
| lz4 -1 rnd | 0.03 | 0.71 | 0.04 (6%) | 0.04 (5%) | 0.03 (4%) | 0.02 (3%) | 0.22 (31%) | 0.00 (0%) | 0.02 (3%) | 0.02 (3%) | 0.32 (45%) |
| lz4 -9 | 2.84 | 17.94 | 5.19 (29%) | 1.52 (8%) | 1.99 (11%) | 1.02 (6%) | 3.72 (21%) | 0.09 (0%) | 2.34 (13%) | 1.55 (9%) | 0.53 (3%) |
| lz4 -d | 0.07 | 1.32 | 0.07 (5%) | 0.06 (5%) | 0.08 (6%) | 0.04 (3%) | 0.32 (24%) | 0.00 (0%) | 0.05 (4%) | 0.06 (5%) | 0.62 (47%) |
| lua int | 1.19 | 7.37 | 2.01 (27%) | 0.47 (6%) | 0.67 (9%) | 0.44 (6%) | 0.07 (1%) | 0.05 (1%) | 2.67 (36%) | 0.88 (12%) | 0.11 (2%) |
| lua tab | 0.98 | 5.71 | 1.51 (26%) | 0.39 (7%) | 0.59 (10%) | 0.37 (6%) | 0.01 (0%) | 0.04 (1%) | 2.02 (35%) | 0.72 (13%) | 0.06 (1%) |
| lua str | 2.94 | 6.22 | 0.69 (11%) | 0.56 (9%) | 0.94 (15%) | 0.48 (8%) | 0.86 (14%) | 0.03 (0%) | 0.82 (13%) | 0.83 (13%) | 1.00 (16%) |

Per-function cachegrind counts on the filcc builds show the same
functions 4–7× smaller (`longest_match` 6.77G vs 0.97G,
`BZ2_decompress` 5.54G vs 1.10G, `luaV_execute` 7.05G vs 1.17G).

### Findings

- **Every value round-trips through the frame.** Scalar temporaries
  alone are 22–33% of the compressors' instructions; with pointer
  temporaries and lowers, frame traffic is 40–55%. A promoted loop
  variable costs four moves per phi per edge (value to shadow, shadow to
  phi), 12–19% of zlib `-6`, lz4 `-9` and bzip2 `-d`.
- **The phi copies also cost latency.** bzip2 `-d` is *slower* with `-O`
  (577 ms) than without (524 ms) despite 44% fewer instructions: its IPC
  halves (2.4 vs 4.8) and store-to-load forwards rise from 68M to 384M.
  Promotion turned memory variables into loop-carried store/reload chains
  through phi shadows. Register allocation removes them.
- **Lua's switch is a linear compare chain.** `dispatch_cases`
  (c_lower.pl) compares the opcode with each case in turn, about eleven
  instructions per case. Blocks that only compare with a constant and
  branch are 44% of `lua int` and 43% of `lua tab` (3.2G and 2.5G), 7% of
  `lua str`, and at most 1% elsewhere.
- **Checks are 9–28%**, nine instructions plus two frame loads per access.
  filcc's equivalent is four or five (`cmp lower; jb; cmp upper; jae`),
  with the null test and upper load hoisted out of loops.
- **Small functions are called, not inlined.** lz4 `-9` spends 3.6G
  (20%) in calls to `LZ4_read16`, `LZ4_read32`, `LZ4_isLittleEndian`,
  `LZ4_count` and friends, which clang inlines; Lua's `index2value` is
  similar. Each call pushes a frame, zeroes roots and stores origins.
- **Small `memcpy` goes to the runtime.** lz4 `-d` and `-1` spend 45–47%
  in `filc_native_zmemmove` and friends for 8- and 16-byte copies.
- **Boolean materialization.** A branch on a comparison computes
  `setcc`, `movzbl`, stores, reloads, `test`s and `jz`s, then jumps
  twice (`jz false; jmp true; false: jmp false`), even to the next block.
  That is 5–7% outside Lua and 20% in Lua's VM.
- **Polls are about 1%**; not worth changing.
- **ops alone are close to filcc's whole count** (zlib `-6` 1.51G vs
  1.97G, bzip2 `-9` 2.83G vs 4.69G). After the overheads go, the gap
  will be in checks, addressing and the middle end, not in the operations
  themselves.

## The plan

Ranked by expected yield over cost. Yields are shares of `-O`'s current
instructions from the profile, not measured results; overlapping items
do not add. Every item keeps the reference path (no `-O`, `--registers=stack`,
`--checks=reference`) selectable and byte-identical (snapshot gate),
adds fail-first tests for behaviour it changes, and is measured with the
gate above before it becomes a default.

| # | Item | Expected yield (instructions) | Cost | New safety decision |
| --- | --- | --- | --- | --- |
| 1 | Switch dispatch by binary search | 35–40% of Lua int/tab, 5% of Lua str | small | no |
| 2 | Branch selection: branch on flags, fall through | 5–7%; about 10% of Lua after 1 | small–medium | no |
| 3 | Whole-function scalar register allocation, register operands | up to 20–30%, less in call-heavy functions; more in time where phi chains limit IPC | large | no, under the conditions below |
| 4 | Inlining small functions | about 20% of lz4 `-9`, 5–10% of Lua str | medium | no; changes panic origins |
| 5 | Pointer register allocation | 15–23% of the compressors | large | **yes**: roots |
| 6 | Shorter check sequences | 4–11% | medium | **yes**: check implementation |
| 7 | Inline small constant `memcpy` | 45% of lz4 `-d` and `-1` | medium | **yes**: capability copying |
| 8 | Cheap middle end (folding, value numbering) | small, unmeasured | medium | no |

### 1. Switch dispatch by binary search

Lower a switch with more than four cases as a balanced binary search
over its sorted case values, comparing with the promoted controlling
type's signedness (`slt` or `ult` at its class), with linear equality
tests at leaves of up to four. `convert_int/3` reads each case value with
the type's signedness, so a numeric sort is the type's order. Duplicate
values after conversion are now rejected, as C11 6.8.4.2p3 requires and
clang does; before, the first case silently won. It is frontend lowering
into existing IR (`cmp`, `branch`), purely scalar, and changes no
observable behaviour of a valid program. Expected: 35–40% of `lua int`
and `lua tab`, 5% of `lua str`. Cost: small, in `c_lower.pl`'s
`dispatch//4`. Validation: difftests of switches over `int`, `unsigned`,
promoted `signed char`, `long` and `unsigned long` with values at each
type's extremes, against clang and the interpreter, with and without
`-O`; a unit test that every case of a 64-case switch is reached within
20 blocks; a reject test for duplicates; snapshot changes only where a
switch has more than four cases; the Lua gate.

*Implemented in this round; see [Results](#results-of-this-round).*

A jump table would go further. Each level of the binary search is a
compare and a hard-to-predict branch (about 7 levels for Lua's 83
opcodes); a table needs one bounds test and one indirect jump. It needs
a new IR terminator, a grammar change for the orchestrator to agree,
with interpreter, validator and emitter support. It is a control-flow
integrity question, not a capability one: the index must be explicitly
zero-extended (an incoming `w` word may have nonzero upper bits), the
range test must be unsigned after subtracting the minimum, the table
should hold label differences (no dynamic relocations), and every
checker must know every successor of the indirect jump.

### 2. Branch selection

Branch directly on a comparison's flags when its only use is the branch
that ends its block (`cmpl; jl`), and lay out the jump to the next block
as a fallthrough. Today a branch on a comparison computes `setcc`,
`movzbl`, stores, reloads, `test`s and `jz`s, then jumps twice. Every
binary-search level of item 1 pays that cost too, so this comes next.
Expected: 5–7%, about 10% of Lua after item 1. Cost: small to medium.
Validation: like M6's immediate selection, an opt-in selection checked
by emitted-form tests, difftests against clang and the interpreter, and
the gate; item 3's checker adds one pairing rule for it (a `jz` on a
register holding `zext(setcc(C, F))` is `j¬C` on flags F, with flags
live across the transfer).

*Implemented in this round; the `-O` default since its gate result, see [Results](#item-2-branch-selection).*

### 3. Whole-function scalar register allocation with register operands

Assign `w`/`l` temporaries, phis and phi shadows to registers for the
whole function: values live across any `call` instruction (calls, polls,
allocation, and the helpers inside fused pointer operations) in the five
callee-saved registers, the others also in `r10`/`r11`. Coalesce phis
with their shadows and inputs, sequentializing the parallel copy, so
most phi copies vanish and the rest are register moves. Then select
operations with register and immediate operands (`addl %r12d, %ebx`)
instead of loading into scratch registers and storing back. The thread
pointer, reloaded from its slot before every call and poll, can live in
a callee-saved register too, though that is under 1% of instructions.
`s`/`d` follow with XMM registers; `x` (x87) temporaries stay in memory.

Expected: most of the scalar-temp share where registers suffice. Five
callee-saved registers will not hold every call-crossing value of
call-heavy functions such as `luaV_execute` or `BZ2_decompress`, so the
first step is to estimate coverage per hot function from the profile's
per-slot counts. Time should gain more than instructions where phi
chains bound IPC (bzip2 `-d`). Cost: large.

Coverage, estimated by `bench/profile/coverage.py` on the marked `-O`
build (selected branches). A home is an rbp offset that no pointer
payload, lower or address-taking instruction touches. Liveness is per
offset over the function's control-flow graph, and a home crosses a
call when it is live after a call that returns. The script colours
homes greedily by executed instructions (cachegrind), without splitting
and with temps that share a slot merged into one node, so it
underestimates:

| Function (workloads) | Scalar home traffic | Live across a call | Covered | Covered if slow paths save `r10`/`r11` |
|---|--:|--:|--:|--:|
| `luaV_execute` (lua int, tab, str) | 1.92G, 26% of the function | 84% | 98% | 100% |
| `longest_match` (zlib -6) | 2.16G, 34% | 36% | 92% | 94% |
| `BZ2_decompress` (bzip2 -d) | 1.74G, 34% | 65% | 47% | 53% |
| `LZ4HC_InsertAndGetWiderMatch` (lz4 -9) | 3.68G, 52% | 68% | 70% | 70% |
| all four | 9.50G | | 76% | |

`frame_slots` already packs short-lived temps into a few hot slots
(`luaV_execute`'s five hottest homes carry 87% of its traffic), so few
registers go far: at most 6 of its homes are live at once. `BZ2_decompress`
is limited by pressure: a median of 22 and at most 26 homes are live at
once, the state its resumable decoder keeps across the loop.
`LZ4HC_InsertAndGetWiderMatch` is limited by real calls (`LZ4_read32`, `LZ4_count`, `LZ4HC_countBack`),
which inlining (item 4) removes. The last column assumes that poll,
store-barrier and ensure-aux slow paths, which are cold, save `r10`/`r11`.

It is not a new safety decision under four conditions, which Oracle
checked against the runtime and emitter. The runtime never inspects
mutator registers: stacks are scanned only through `top_frame` lowers,
and longjmp ends in native `_longjmp`, which restores callee-saved
registers for the setjmp caller as the ABI requires. Getters, thunks and
adapters that use `rbx`/`r12`/`r13` save and restore them.

- Functions that call setjmp keep reference emission, as in M6.
- Only `w`/`l` homes that never alias a `p` payload or lower (frame
  slot sharing can mix them) are eligible, as in M6. Putting pointer
  material in registers is item 5.
- Callee-saved registers are saved after the stack check and restored
  before every `leave`: success, exception and native returns.
- Allocated registers are disjoint from the emitter's scratch registers
  (`rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`, `r9`). Check-fail blocks read
  `rax`/`rcx`. A phi written on a poll edge is live across the poll's call.

Validation extends M6's translation validation instead of trusting the
allocator, in the style of Rideau and Leroy's validated allocation. The
reference stream (every value in its slot) and the allocated stream must
have the same control skeleton and the same order of non-move
instructions. The allocator supplies an untrusted location map per
label. The checker computes its own width-aware liveness on the reference
stream (low and high halves separately, as M6 does, since a `w` value
can be stored at `l` width). At every transfer it requires equal values
for live homes, every non-allocatable register and the flags; at a label
it assumes fresh common values; a call clobbers caller-saved registers
to fresh shared values; at `ret`, callee-saved registers, `rsp` and
`rbp` must equal their entry values. Its control-flow graph must include
every local label (`..jnz.false`, poll and no-poll labels, `..exc`,
`..fail.*`), fallthrough, the stack-overflow jump and `ud2`, and reject
any unknown transfer. Operations pair by `amd64_contract.pl` form with
operand roles (subtraction order, two-address destinations, `div`'s
`rax`/`rdx`, `cl` counts, `setcc` partial writes, imm32 sign extension),
treating arithmetic as uninterpreted. Memory operands may name only
non-allocated homes, never the stale slot of an allocated one. Once
measured better, it replaces the region-local `--registers=local`.

*Step 3a (register homes, moves only) implemented opt-in as
`--registers=function`; see [Results](#item-3a-whole-function-scalar-register-homes).*

### 4. Inlining small functions

Inline calls to small non-recursive functions before promotion, so the
callee's code is pizlonated and checked in place like any other code.
Exclude setjmp, VLAs and `alloca`, variadics and functions with local
storage. Expected: about 20% of lz4 `-9`, 5–10% of `lua str`, small
elsewhere. Cost: medium (renaming, source contexts, size limits). It is
an unchecked-IR transformation before pizlonation; validation is the
middle end's run-by-run refinement (`-O` difftest) and the gates. It
changes panic origins and stack traces (the inlined access reports the
caller's frame), an observation change to state and review with it.

### 5. Pointer register allocation — needs review

Keep `p` addresses, and then lowers, in registers between safepoints.
Expected: most of the pointer-temp and lower shares, 15–23% of the
compressors. It is a **safety decision**: a lower held only in a register
is invisible to the collector. The proposed rule: every `call`
instruction is a safepoint, with no exemptions (polls, `filc_allocate`,
ensure-aux and the store-barrier slow path included: an exited thread's
frames are scanned, and a filcc callee may spill a callee-saved register
to the unscanned native stack). At each, every live pointer's lower must
be in its `lowers[]` entry. FUGC does not move objects and allocates
black, so register copies stay valid after the spill; stale entries only
extend lifetimes; signals are deferred to polls. The checker must verify
two more obligations: each live lower's entry symbolically equals its
register at each safepoint, and lower material never enters a home that
item 3 treats as scalar. Needs Oracle review of the implementation
design before it starts, per the root AGENTS.md.

### 6. Check sequences — needs review

Select a shorter check with the same failure behaviour: the same fail
function, arguments and origin, the rights test (`-2(%rcx)`) and the
alignment test. The `sub`/`jb` pair guards a borrow in `upper − size`;
it can be dropped only from `upper ≥ lower ≥` the heap's minimum address
`> size`. A `ptr + size` form must catch the carry, since after `l`
arithmetic the address is arbitrary. Reusing a loaded upper bound must
end at every call, since `free` sets `upper = lower`. Hoisting checks
out of loops needs M7's spatial/temporal split ([m7.md](m7.md#limits)).
Expected: about 40% of the check share, 4–11%. Review each sequence
against the check's contract before adoption.

### 7. Small constant `memcpy` — needs review

An inline copy must preserve what `filc_memmove` does: null, bounds and
write checks on both pointers; copying aux for in-phase words, and
clearing the destination's aux where out of phase or partly overwritten;
aux allocation (an exit, so a safepoint) and the barrier. The smallest
safe version copies inline only when neither object has an aux pointer,
the runtime's "nothing to do" case, and calls the runtime otherwise.
Expected: 45% of lz4 `-d` and `-1`.

### 8. A cheap middle end

Constant folding and propagation, local value numbering of pure
operations, and dead-code removal on unchecked IR, validated by the
existing refinement checks. Expected: small and unmeasured; constant
moves are 3–11% today, partly removed by immediate operands (M6) and
item 3. Last because the profile shows little to gain yet.

### Projection

From the profile's shares: items 1–4 leave the compressors at about 3–4×
filcc's instructions and Lua at about 3×; items 5 and 6 bring them to
about 2–3×. Reaching 1.5–2× in instructions also needs check hoisting
and better addressing. Time should improve more than instructions where
phi chains and frame traffic limit IPC.

## Results of this round

### Item 1: switch dispatch by binary search

The gate at `ab05a5b` and with item 1, `-O` time ratio to filcc `-O2`
(instruction ratio); `*` marks a row whose `-O` trial times overlap the
previous column's:

| Workload | ab05a5b | item 1 |
|---|--:|--:|
| zlib -6 text | 4.59 (5.97) | 4.54 (5.97)* |
| zlib -d text | 3.36 (4.62) | 3.21 (4.60)* |
| bzip2 -9 text | 3.59 (3.97) | 3.59 (3.97)* |
| bzip2 -d text | 6.22 (4.65) | 6.20 (4.65) |
| lz4 -1 random | 3.95 (23.91) | 3.72 (23.16)* |
| lz4 -9 text | 6.49 (6.00) | 6.56 (6.31)* |
| lz4 -d text | 6.48 (18.22) | 5.94 (17.93)* |
| lua int | 6.33 (6.12) | 4.30 (3.93) |
| lua tab | 6.24 (5.76) | 4.12 (3.77) |
| lua str | 1.91 (2.10) | 1.86 (2.03)* |
| geomean | 4.61 (6.30) | 4.16 (5.76) |

Lua's integer loop and table reads execute 36% fewer instructions (7.27G
to 4.65G, 5.66G to 3.63G) and take 32–34% less time; nothing else moves
beyond noise. bzip2 `-d`'s ranges separate by 1% (581 to 588 ms), with
identical instruction counts: layout noise. The filcc builds were
rebuilt between the two runs, and lz4's is not reproducible: its `-9`
runs 2.99G instructions in one build and 2.84G in the other, which moves
lz4's ratios though nanofil's own counts are unchanged. From item 2 on,
the gate pins filcc's builds (`bench/ref`) to the ones this run used.

After item 1, blocks that only compare a value with a constant and
branch (`profile.py`'s upper bound on switch dispatch) are still 13% of
`lua int` and 12% of `lua tab`: about seven levels of ten instructions
each per dispatch. Item 2 shortens each level.

### Item 2: branch selection

`--branches=selected` (or `NANOFIL_BRANCHES=selected`) landed opt-in,
and after the gate below it became the default under `-O`. Without
`-O` the reference branches stay the default, so the 1,080 snapshot
outputs (none use `-O`) are byte-identical; `-O --branches=reference`
gives the earlier `-O` output, which the Nix checks and the gate's
`O-refbranches` mode keep running. A block whose last instruction is a
`w`/`l` comparison read by nothing but the block's branch emits `cmp`
(register or imm32 operand) and a conditional jump; the boolean is never
materialized. Of the two arms, a plain edge (no phi copies, no poll)
gets the conditional jump straight to its block; the other edge's copies
follow, and an edge to the next block falls through. A branch on any
other value tests it and does the same. Setjmp functions keep the
reference. The M6 cache checker accepts the selected stream unchanged:
conditional jumps and labels were already region boundaries.

The gate, with filcc's builds pinned to the item-1 run's (`item 1 rerun`
is `-O` in the same run as item 2):

| Workload | ab05a5b `O` | item 1 `O` | item 1 rerun `O` | item 2 `-O --branches=selected` |
|---|--:|--:|--:|--:|
| zlib -6 text | 4.59 (5.97) | 4.54 (5.97)* | 4.55 (5.97)* | 4.40 (5.68) |
| zlib -d text | 3.36 (4.62) | 3.21 (4.60)* | 3.04 (4.60) | 2.99 (4.33)* |
| bzip2 -9 text | 3.59 (3.97) | 3.59 (3.97)* | 3.59 (3.97)* | 3.36 (3.69) |
| bzip2 -d text | 6.22 (4.65) | 6.20 (4.65) | 6.10 (4.65) | 6.02 (4.30) |
| lz4 -1 random | 3.95 (23.91) | 3.72 (23.16)* | 3.78 (23.22)* | 3.71 (22.62)* |
| lz4 -9 text | 6.49 (6.00) | 6.56 (6.31)* | 6.66 (6.31)* | 6.53 (5.91)* |
| lz4 -d text | 6.48 (18.22) | 5.94 (17.93)* | 5.91 (17.90)* | 5.82 (17.48)* |
| lua int | 6.33 (6.12) | 4.30 (3.93) | 4.38 (3.93)* | 4.03 (3.43) |
| lua tab | 6.24 (5.76) | 4.12 (3.77) | 4.09 (3.77)* | 3.71 (3.32) |
| lua str | 1.91 (2.10) | 1.86 (2.03)* | 1.83 (2.04)* | 1.77 (1.94) |
| geomean | 4.61 (6.30) | 4.16 (5.76) | 4.14 (5.76) | 3.98 (5.38) |

Instructions fall 5–13% against `-O` in the same run, time 2–9%, with
separated trial ranges except for lz4 and zlib `-d`. bzip2 `-d` is still
slower with `-O` than without: 579 ms for `-O`, 572 ms with selected
branches, against 525 ms off. The phi store/reload chains need item 3.

With selected branches, const-compare blocks are 5.0% of `lua int` and
4.6% of `lua tab` (0.21G of 4.17G, 0.15G of 3.25G), 1% of `lua str`: an
upper bound on what a jump table could still remove.

### Item 3a: whole-function scalar register homes

`--registers=function` (or `NANOFIL_REGISTERS=function`) is opt-in. A
fixed map per function puts scalar `w`/`l` homes and phi shadows in
registers: `rbx` and `r12`–`r15` for homes live across a call, `r10`/`r11`
too for the others. Only moves of a mapped home change; instruction
selection is M6's immediate selection with selected branches, as in
`--registers=local`, which this mode replaces. Setjmp functions keep the
reference. The allocator (`amd64_regs.pl`) colours homes greedily by
loop-weighted references; the checker (`amd64_regs_check.pl`) trusts
none of that. It rebuilds the allocated stream from the reference
stream, the map and the save slots and requires equality, then proves
on its own width-aware liveness over a complete CFG that every live half
of a mapped home equals its register: nothing mapped is live at entry or
at a `leave`, a write to a home leaves the other homes of its register
dead, a 32-bit store leaves the high half dead, and `r10`/`r11` homes are
dead after every call. Fixtures in `tests/regs_check.pl` each fail when
the obligation they target is removed.

The gate in one run (filcc pinned):

| Workload | `O` | `O-local` | `O-function` |
|---|--:|--:|--:|
| zlib -6 text | 4.40 (5.68) | 4.23 (5.62) | 3.18 (5.62) |
| zlib -d text | 2.93 (4.33) | 2.82 (4.23)* | 2.53 (4.22) |
| bzip2 -9 text | 3.37 (3.70) | 3.11 (3.62) | 2.64 (3.61) |
| bzip2 -d text | 6.09 (4.30) | 5.91 (4.19) | 4.31 (4.20) |
| lz4 -1 random | 4.11 (23.06) | 3.95 (23.24)* | 3.77 (23.14)* |
| lz4 -9 text | 6.38 (5.91) | 5.68 (5.81)* | 5.54 (5.87) |
| lz4 -d text | 6.34 (17.45) | 6.28 (17.49)* | 5.98 (17.46)* |
| lua int | 3.85 (3.43) | 3.74 (3.21) | 3.34 (3.24) |
| lua tab | 3.75 (3.32) | 3.71 (3.13)* | 3.36 (3.14) |
| lua str | 1.80 (1.94) | 1.75 (1.92)* | 1.68 (1.93)* |
| geomean | 4.03 (5.39) | 3.87 (5.27) | 3.41 (5.28) |

Instruction counts barely move (a register move replaces a slot move),
but time falls 15% on the geomean and up to 29% (bzip2 `-d`, 568 → 403
ms; zlib `-6`, 595 → 429 ms): store-to-load forwarding chains through
frame slots were the bottleneck. bzip2 `-d` is now faster with `-O`
than off (403 ms against 525 ms). Step 3b, register operands instead of
moves through `rax`/`rcx`, is what removes instructions. Compile time
of the largest files rises from 2.9–3.8 s to 4.4–4.6 s.

Oracle reviewed the result before it shipped. It found no runtime
interaction to fix (callee-saved registers are preserved by every callee
and restored by native `_longjmp`; roots are only `lowers[]`), but five
streams the checker wrongly accepted, none of which the emitter
produces: a mapped home written, a label, or a branch before the stack
check (which would lose or never save a caller's register), mapped homes
closer than 8 bytes, a duplicate pointer description of a mapped home,
a `movq` immediate outside imm32 (the register form assembles as
`movabs`), and a `call` to a label in the body. The checker now rejects
each, with a fixture that fails when its rule is removed.

## Review

Oracle reviewed this plan before implementation. Its findings, all
folded in above:

- **Item 1:** duplicate case values were never diagnosed, and a search
  must not pick an arbitrary one of them; nanofil now rejects them. The
  promotion and signedness reasoning is sound and purely scalar.
- **Jump tables:** the instruction estimate was too low, and the risk is
  control-flow integrity (index extension, unsigned range test, label
  differences, known successors), not capabilities.
- **Ranking:** branch selection moved before allocation, since every
  search level pays for boolean branches. Keeping the thread pointer in
  a register was suggested; the profile puts it under 1%. Allocation's
  yield is limited by callee-saved registers in call-heavy functions.
- **Item 3:** free of new safety decisions under the four conditions
  listed. The first checker design was unsound: it did not require
  callee-saved registers at `ret`, compared only homes (not registers
  and flags live across transfers), ignored widths, under-specified the
  control-flow graph, paired operations too loosely, left memory operands
  unconstrained, and could not express spilling. The design above is the
  smallest sound one it proposed.
- **Item 5:** every `call` is a safepoint, and the checker must also
  verify lower/register equality and that lowers never enter scalar homes.
- **Item 6:** the borrow test's justification was wrong; it guards
  `upper − size`, not address wrap.
- **Item 7:** the full `filc_memmove` contract, and a no-aux-only first
  version.
- **Item 4:** inlining changes panic origins and stack traces.
