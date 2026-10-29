# Code quality: where nanofil -O spends its instructions, and the plan

nanofil should be usable for Linux userland programs. Fil-C's own
overhead is accepted; nanofil's on top of it should not be obscene.
The target is QBE-class code: roughly within 1.5–2× of filcc `-O2` in
time, without vectorization or sophisticated arithmetic analysis. This
file holds the benchmark gate, a profile of where `-O` spends its
instructions, and a ranked plan. It is separate from the semantic
campaign ([campaign.md](campaign.md)): nothing here weakens a check,
and safety decisions are flagged for review before implementation.

## Summary (October 2026, at `2ce8b0f`)

**Where we are.** `-O` runs the eleven gate workloads at a geomean of
**2.13–2.18× filcc `-O2`'s time** (3.2× its instructions; run-to-run
spread about ±0.03). The round started at **4.61× (6.30×)** on the
first ten workloads, at `3576b51`. Ten of the eleven are within
1.5–2.5×. lz4 `-d` is 3.0×, bound by calls. The target was 1.5–2×.

**How.** Each step's gate run, before → after. The workload set gained
SQLite at 3a's default and the reference pin changed once, so the steps
chain only approximately:

| Step | Geomean time (instructions) |
| --- | --- |
| Baseline, every value in a stack slot | 4.61 (6.30) |
| 1 switch dispatch by binary search | → 4.16 (5.76) |
| 2 branch selection | → 3.98 (5.38) |
| 3a whole-function scalar register homes (default; SQLite added) | → 3.23 (4.93) |
| 3b register operands, region checker | → 3.14 (4.49) |
| 5a-loads frame cells | 3.06 → 2.89 |
| 7a inline small constant `memcpy` | 2.87 → 2.67 |
| split float pools | 2.68 → 2.46 |
| 6a no borrow test in checks | 2.46 → 2.44 |
| 4 inlining small leaf functions | 2.44 → 2.34 |
| 3d a home per temporary (`--registers=temps`) | 2.35 → 2.24 |
| 9 phi shadows shared by position | 2.24 → 2.15 |
| punned union reads promote | 2.14 → 2.13 |
| 5b-1 `--registers=flow` (opt-in, not adopted) | 2.12 |
| 8 cheap middle end (`--simplify=full`, the `-O` default) | 2.14 (3.23) → about 2.0 (2.89) |

Every step is translation-validated or checked against the reference
path, and the reference stays selectable and snapshot-identical. No
check was weakened, and no root or GC invariant changed except item 9's
shadow sharing (option A, Oracle-reviewed).

**The gate now** (7 trials, cpu 6, ratio to filcc `-O2`: time
(instructions), with its min..max time range):

| Workload | filcc ms | `-O` | `-O --registers=flow` |
| --- | --: | --: | --: |
| zlib -6 | 134.0 | 2.51 (4.08) 2.48..2.54 | 2.48 (4.06) |
| zlib -d | 17.6 | 2.06 (3.19) 1.97..2.13 | 2.04 (3.18) |
| bzip2 -9 | 273.7 | 2.01 (2.52) 2.00..2.07 | 1.97 (2.49) |
| bzip2 -d | 93.9 | 2.43 (3.11) 2.40..2.52 | 2.38 (3.09) |
| lz4 -1 | 13.7 | 2.26 (10.81) 2.08..2.35 | 2.21 (10.76) |
| lz4 -9 | 162.1 | 2.49 (3.07) 2.45..2.51 | 2.43 (3.06) |
| lz4 -d | 12.4 | 2.99 (6.84) 2.88..3.21 | 2.98 (6.79) |
| lua int | 50.1 | 2.14 (2.35) 2.09..2.28 | 2.09 (2.32) |
| lua tab | 41.9 | 2.00 (2.26) 1.95..2.12 | 2.11 (2.24) |
| lua str | 263.6 | 1.50 (1.61) 1.49..1.51 | 1.49 (1.61) |
| sqlite | 661.2 | 1.97 (1.99) 1.97..1.99 | 1.93 (1.98) |
| geomean | | 2.18 (3.23) | 2.16 (3.21) |

**What remains, and why it stays** (shares of `-O`'s instructions, from
the profile at `04c7e7c` and the re-measurement under 5b):

- **Check count, 18–39%.** Each check is the pin's own sequence (6a);
  the gap is how many run. filcc merges and hoists checks (bzip2 `-9`:
  540M against 230M). Widening a check moves a trap before earlier
  stores and reports the wrong access. That is the observation-contract
  change campaign.md rules out, so 6c-2 was rejected. Hoisting needs
  M7's spatial/temporal split. This is the gap that stays.
- **Pointer frame traffic, 16–30%** at `04c7e7c`, stores included;
  64-bit frame-word loads alone are 6–17%. Each access reloads the
  pointer and lower from the frame. Forwarding is exhausted: 5b-1 reaches what
  is still in a register, at most 1.7%. What is left (2.5–11%, up to
  16% across calls) needs pointer homes in registers. That is register
  pressure in the hot functions (3d), plus GC root rules for lowers
  held in registers (5b-2, deferred). The loads hit L1, so time gains
  would be smaller.
- **Calls to extern helpers, 12–16%** in lz4 `-9`, Lua str and SQLite,
  and 36–43% in lz4 `-1`/`-d`. The Fil-C runtime's helpers (allocation,
  `memcpy`/`memset` of non-constant size, string and pollcheck slow
  paths) and libc are out-of-line calls through the ABI's frame
  protocol. The runtime's own instructions are 18–26% of lz4
  `-1`/`-d`, Lua str and SQLite. filcc's builds run the same runtime, so
  only the calling side is nanofil's to shrink: wider small-copy
  filters, and inlining across modules, which nanofil does not do.
- **Register pressure.** Sixteen registers hold scalar homes, scratch and
  the checks' operands. bzip2 `-d`'s `BZ2_decompress` keeps phi shadows
  in the frame (0.69G), and webs (3d) would not change that.
- Selection (5–15%: boolean tests, constant moves, `setcc`) and copies
  (4–13%) remain, each spread over many small patterns. The middle end
  (item 8) was never needed for the target.

## The benchmark gate

[`bench/`](../bench) builds zlib 1.3.2 (`minigzip`), bzip2 1.0.8, lz4
1.10.0, Lua 5.4.7 and SQLite 3.51.2 (the amalgamation and shell of
[nix/sqlite.nix](../nix/sqlite.nix)) with filcc `-O2` (`ref`) and with nanofil in each
mode, through the same `nanofil-cc` wrapper the Nix checks use:

| Mode | nanofil options |
| --- | --- |
| `off` | none: the reference backend without the middle end |
| `O` | `-O` (selected branches, item 2; `--registers=temps`: register homes with register operands and frame cells, items 3a, 3b, 5a-loads and 3d; inlining, item 4; inline small copies, 7a) |
| `O-reuse` | `-O --checks=reuse` ([m7.md](m7.md)) |
| `O-noinline` | `-O --inline=none` |
| `O-refbranches` | `-O --branches=reference`: `-O` before item 2 became its default |
| `O-stack` | `-O --registers=stack`: the reference emission under the middle end (`--argstr only O,O-stack` builds a subset) |
| `O-call` | `-O --memcpy=call` |

The modes `O-local`, `O-function`, `O-operands`, `O-cells` and `O-flow`
of earlier tables measured register modes retired in October 2026
(register modes, below).

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
[str.lua](../bench/str.lua) (string formatting, sort, gsub), and SQLite
on [sqlite.sql](../bench/sqlite.sql): an in-memory database of 5,000
customers and 50,000 orders with joins, windows, a correlated subquery,
JSON, updates, FTS5 and a sort. nanofil needs 1.5–2.5 minutes and up to
7 GB for each build of `sqlite3.c`, so build only the modes you compare
(`--argstr only off,O`).

It is not part of `nix flake check`: timings need a quiet machine.

filcc is not deterministic: compiling the same file twice gives different
code (October 2026; zlib's `deflate.c`, bzip2's `blocksort.c`, lz4's
`lz4.c` and `lz4hc.c` all differ run to run, and three compiles of
`lz4.c` disassemble to 57,561, 57,729 and 57,594 lines). A rebuilt filcc
lz4 ran `-9` in 2.99G instructions once and 2.84G another time. The
cause is FilPizlonator's check order, which follows heap addresses
([abi-findings.md](abi-findings.md#filcc-output-depends-on-heap-addresses)). So pin
the reference: `run.py` and `profile.py` take filcc's builds from
`bench/ref/PROGRAM/ref` when it exists (`--ref DIR`), else from `out`.
Pin a program once, as a GC root, with

```sh
nix-store --add-root nanofil/bench/ref/sqlite/ref --realise $(readlink -f nanofil/bench/out/sqlite/ref)
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
temporary, lower, phi shadow, thread, aux). The post-emission passes
(register homes, operands, cells) would see a mark as a block boundary,
so they run on the stream without marks, and the emitter writes the
marked stream they ran on after each function as comments.
[`remark.py`](../bench/profile/remark.py) aligns the two block by block
(labels survive the passes) and puts each mark back before the line its
pre-pass line became. The marked and unmarked binaries' `.text` are
identical (checked for all five programs at `04c7e7c`).
[`bench/profile`](../bench/profile/default.nix) builds the programs
with it at `-O` and gives each instruction its line in the marked `.s` as
DWARF line info. [`loc.awk`](../bench/profile/loc.awk) writes it, in
files of 2^20 lines, because valgrind keeps 20 bits of a line number
and `sqlite3.c`'s `.s` has 3.7M lines:

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
| copies | moves between general registers outside checks and ABI sequences: what a home in a register still costs (since register allocation; not in the first profile) |
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

### Where we are now (04c7e7c)

At [`04c7e7c`](https://github.com/mbrock/filnix/commit/04c7e7cb1d09)
(`-O` is `--registers=temps`, `--inline=small`, phi shadows shared), the
same method, all eleven workloads, billions of instructions (share of
nanofil's total):

| Workload | filcc | nanofil -O | scalar temps | copies | pointer temps | checks | lowers | calls/frames | polls | selection | ops | runtime |
|---|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|--:|
| zlib -6 | 1.97 | 8.02 | 0.17 (2%) | 0.85 (11%) | 1.07 (13%) | 2.42 (30%) | 1.08 (13%) | 0.14 (2%) | 0.11 (1%) | 0.95 (12%) | 1.22 (15%) | 0.02 (0%) |
| zlib -d | 0.20 | 0.62 | 0.02 (3%) | 0.07 (12%) | 0.09 (15%) | 0.15 (25%) | 0.09 (15%) | 0.06 (9%) | 0.01 (1%) | 0.03 (5%) | 0.08 (12%) | 0.02 (3%) |
| bzip2 -9 | 4.67 | 11.81 | 0.08 (1%) | 0.88 (7%) | 1.29 (11%) | 4.66 (39%) | 1.28 (11%) | 0.45 (4%) | 0.17 (1%) | 0.64 (5%) | 2.29 (19%) | 0.05 (0%) |
| bzip2 -d | 1.43 | 4.44 | 0.77 (17%) | 0.37 (8%) | 0.53 (12%) | 1.21 (27%) | 0.53 (12%) | 0.06 (1%) | 0.06 (1%) | 0.28 (6%) | 0.63 (14%) | 0.02 (0%) |
| lz4 -1 rnd | 0.03 | 0.32 | 0.00 (0%) | 0.02 (7%) | 0.01 (3%) | 0.03 (8%) | 0.01 (4%) | 0.14 (43%) | 0.00 (0%) | 0.01 (4%) | 0.01 (4%) | 0.08 (26%) |
| lz4 -9 | 2.84 | 9.71 | 0.76 (8%) | 1.27 (13%) | 0.78 (8%) | 1.83 (19%) | 0.78 (8%) | 1.48 (15%) | 0.09 (1%) | 1.32 (14%) | 1.20 (12%) | 0.21 (2%) |
| lz4 -d | 0.07 | 0.54 | 0.00 (1%) | 0.03 (6%) | 0.03 (5%) | 0.07 (13%) | 0.04 (7%) | 0.20 (36%) | 0.00 (0%) | 0.03 (5%) | 0.05 (9%) | 0.10 (18%) |
| lua int | 1.18 | 2.88 | 0.00 (0%) | 0.26 (9%) | 0.40 (14%) | 0.60 (21%) | 0.40 (14%) | 0.08 (3%) | 0.05 (2%) | 0.44 (15%) | 0.53 (18%) | 0.11 (4%) |
| lua tab | 0.96 | 2.18 | 0.00 (0%) | 0.19 (9%) | 0.32 (15%) | 0.53 (25%) | 0.33 (15%) | 0.00 (0%) | 0.04 (2%) | 0.32 (15%) | 0.42 (19%) | 0.02 (1%) |
| lua str | 2.60 | 4.78 | 0.02 (0%) | 0.18 (4%) | 0.40 (8%) | 0.85 (18%) | 0.41 (9%) | 0.75 (16%) | 0.03 (1%) | 0.31 (7%) | 0.63 (13%) | 1.21 (25%) |
| sqlite | 10.98 | 21.83 | 0.25 (1%) | 0.88 (4%) | 2.31 (11%) | 5.40 (25%) | 2.32 (11%) | 2.65 (12%) | 0.14 (1%) | 1.25 (6%) | 2.76 (13%) | 3.86 (18%) |

The campaign so far, `-O` against filcc `-O2`: nanofil's instructions
at `3576b51` and now, and the gate's time ratio (instruction ratio) at
[`ab05a5b`](https://github.com/mbrock/filnix/commit/ab05a5b682bb) and at
`04c7e7c` (item 9's gate):

| Workload | instructions then | now | time ratio then | now |
| --- | --: | --: | --: | --: |
| zlib -6 | 11.73G | 8.02G | 4.59 (5.97) | 2.48 (4.08) |
| zlib -d | 0.90G | 0.62G | 3.36 (4.62) | 1.91 (3.20) |
| bzip2 -9 | 18.56G | 11.81G | 3.59 (3.97) | 1.99 (2.52) |
| bzip2 -d | 6.63G | 4.44G | 6.22 (4.65) | 2.39 (3.11) |
| lz4 -1 | 0.71G | 0.32G | 3.95 (23.91) | 2.12 (10.62) |
| lz4 -9 | 17.94G | 9.71G | 6.49 (6.00) | 2.67 (3.41) |
| lz4 -d | 1.32G | 0.54G | 6.48 (18.22) | 2.86 (7.29) |
| lua int | 7.37G | 2.88G | 6.33 (6.12) | 2.13 (2.35) |
| lua tab | 5.71G | 2.18G | 6.24 (5.76) | 1.99 (2.26) |
| lua str | 6.22G | 4.78G | 1.91 (2.10) | 1.51 (1.62) |
| geomean of these ten | | | 4.61 (6.30) | 2.17 (3.44) |
| sqlite (added at `0879a72`; then is the old `-O` there) | | 21.83G | 2.67 (2.48) | 1.97 (1.99) |

With SQLite the geomean is 2.15 (3.27). Scalar frame traffic went from
22–33% of the compressors to 1–3%, except bzip2 `-d` (17%) and lz4 `-9`
(8%), where register pressure leaves phi shadows in the frame
(`BZ2_decompress`'s are 0.69G). Its replacement, moves between
registers, is 4–13%. Lua's switch chains are gone, the runtime's share
of lz4 `-1`/`-d` (its small `memcpy`s) went from 45–47% to 18–26%, and
checks fell only by 6a's borrow test: bzip2 `-9` ran 5.20G of them and
runs 4.66G.

Where the rest is, as a share of `-O`'s instructions:

- **Checks, 18–39%** outside lz4's call-bound runs, now the largest
  category. The sequence is the pin's own eight instructions (6a); the
  gap is their count, which filcc gets down by merging and hoisting
  checks, the class 6c-2 rejected for the observation contract
  (bzip2 `-9`: 540M checks, against filcc's 230M). No item is proposed;
  it is the gap that stays.
- **Pointer payloads and lowers, 16–30%** (lz4 `-1`/`-d` 7–12%). Every
  access reloads the pointer and its lower from the frame after a label
  or a check's `jcc`.
  Measured on the final `.s` (a forward must-analysis per function over
  its CFG, cachegrind counts per line): of the remaining loads of
  pointer and lower frame words, 49–84% read a word whose value was
  loaded or stored earlier on every path with no call or poll in
  between, and nearly all of those are still in the register that
  loaded or stored it. That is 4–12% of all instructions on nine
  workloads (table under 5b-1), reached only by forwarding across both
  labels and checks' `jcc`s. Allowing calls in between adds 5–40
  points of those loads, mostly in Lua and SQLite, but needs
  callee-saved registers. Stores are one address and one lower per
  definition plus pointer phi copies through shadows (zlib `-6` 0.4G,
  SQLite 0.6G).
- **Calls, 12–16%** in lz4 `-9`, Lua str and SQLite, 36–43% in lz4
  `-1`/`-d`. In lz4 `-9`, `LZ4_isLittleEndian` (0.74G) is never inlined:
  it reads a byte of a `U32` union, the local does not promote, and the
  inliner only admits callees whose locals promote. So `LZ4_NbCommonBytes`,
  `LZ4_count` and `LZ4HC_countBack` stay calls too. In lz4 `-1`/`-d` it is
  the small-`memcpy` filter and the `XXH32` helpers.
- **Selection, 5–15%**: boolean tests (`test`/`jz` 2–6%), constant moves
  (Lua 5.8%), boolean materialization (`setcc`/`movzbl` 0.4–2.6%) and
  jumps (0.6–1.9%).
- **Copies, 4–13%**, and in-place zero extensions (`movl %r11d, %r11d`,
  0.4–3.2%) among them.
- **Ops, 12–19%**, already close to filcc's whole count in the
  compressors. Multiplies by a power of two are 0.2–1.7%.

### Findings (3576b51)

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

## Register modes: inventory and retirement (October 2026)

Seven `--registers` modes have accumulated, one per step. Each step's
checker extends the previous one, and temps, the `-O` default, runs all
of them. So most intermediate modes add check time, snapshot modes and
configurations, but no trusted code of their own. Gate at `2ce8b0f`
(7 trials, all modes in one run): geomean time (instructions) ratio to
filcc `-O2`, and the `nanofil` check's step time for each mode (610 s
in all, from the last check's timings):

| Mode | What it is | Trusted code of its own | Untrusted code of its own | Still uses it | Check time | Gate | Dominated by temps? |
| --- | --- | --- | --- | --- | --: | --- | --- |
| `stack` | reference emission (no `-O` default, setjmp functions) | none: it is the reference | none | everything: difftests, snapshot `O.`, `O-stack` configurations | 41 s (`-O`) | 3.48 (4.23) | yes, kept as the reference |
| `local` (M6) | block-local validated scalar cache | `amd64_cache_check.pl`, 266 lines | `amd64_cache.pl` 152; `placed_lines(local)` 25 | 11 program configurations (bzip2, hello, lz4, zlib `local` and `O-local`; Lua `local-plain`, `local-optimized`; SQLite `reuse` = local + `--checks=reuse`); `tests/cache_check.pl` 475, `tests/registers.pl`; m7.md's GC fixtures with reuse | 97 s | 3.32 (4.06) | yes: more instructions and slower on all 11 (lz4 `-1`'s ranges overlap) |
| `function` (3a) | whole-function scalar homes, `split` pools | none: `check_regs` (lines 1–533 of `amd64_regs_check.pl`) runs in every allocating mode | the `split` pool choice (2 clauses in `frame_slots.pl`, 1 in `filc_amd64.pl`). The allocator stays: temps' first lowering runs it (`map`) | the "function corpus" step (the only allocating-mode corpus run); snapshot `F.` | 60 s | 2.58 (4.08) | yes, on instructions on all 11; time ties on lz4 `-1` and `-d` (ranges overlap) |
| `operands` (3b) | `function` with register operands, no cells | none: `check_operands/3` is temps' checker with no cells | `operand_cells(operands, …)`, 1 clause | snapshot `P.` | 36 s | 2.44 (3.50) | yes, instructions on all 11; time within noise only on lz4 `-1`/`-d` |
| `cells` (5a-loads) | `operands` with frame cells, `split` pools | none: the cell rules (`valid_cells/3`, cell stores) are temps' too | `split` pools (as `function`) | snapshot `C.` and `I.` (cells with inlining); the no-`-O` "registers cells" block | 67 s | 2.28 (3.38) | yes, instructions on all 11; time ties on lz4 `-1`/`-d` and Lua str |
| `temps` (3d) | `cells` on a frame with a home per temporary | (all of the above) | `temps_first/5`, own pools | the `-O` default | (the `-O` suites) | **2.18 (3.23)** | — |
| `flow` (5b-1) | `temps` with Rule 1 and label facts | 122 lines (`continued_jump/3`, `edge_facts/4`, `label_facts/5`, `well_formed_facts/4`, `fact_labels/2`) | about 200 lines in `amd64_regs.pl` | opt-in only; snapshot `W.` | about 25 s | 2.16 (3.21) | no: 1–2% faster on four workloads, +14% compile on `sqlite3.c` |

**Proposal.** Keep `stack` (the reference), `temps` (the default) and
the allocator, operand checker and cell checker that temps runs.
Retire as selectable modes:

1. **`local`.** This removes the only intermediate mode with trusted
   code of its own: `amd64_cache_check.pl` (266) and `amd64_cache.pl`
   (152), their 475 lines of checker tests, and 10 program builds. The
   SQLite `reuse` configuration becomes `-O --checks=reuse` on temps.
   `--checks=reuse` does not depend on local. m7.md's "GC fixtures with
   `--registers=local`" step becomes temps. `tests/registers.pl` tests
   immediate selection through `local`. The selection (`sel(local, …)`)
   is the allocating modes' too, so those tests move to temps emission.
   M6 stays in the record (m6.md); the mode no longer runs.
2. **`function`, `operands` and `cells`.** No trusted code goes. Their
   checks run inside temps. This removes the `split` pool choice, three
   snapshot modes (`F.`, `P.`, `C.`; `I.` becomes temps with inlining),
   and about 100 s of check steps (163 s, less the two kept). Two steps are kept, retargeted to
   temps: the corpus run (today's "function corpus", the only corpus run
   through the register checkers) and the no-`-O` block. `-O
   --branches=reference --registers=local` is dropped, since `-O
   --branches=reference` already runs on temps.
3. **`flow`: the orchestrator's choice.** 5b forwarding is closed
   (re-measurement above), so flow is not a base for a later item; 5b-2
   would be function-wide pointer homes under `check_regs`, not facts.
   Either retire it (122 trusted lines, one snapshot mode, about 25 s),
   or make it the default for its 1–2% (its gate test passed with
   separated ranges on four workloads, at +14% compile time). Keeping it
   opt-in pays the cost and gets nothing. Recommended: retire it.

Net, with flow retired: about 390 lines of trusted checker code
(266 + 122), about 400 lines of untrusted code and 475 of tests;
`nanofil` check about 610 s → about 390 s; 10 fewer program builds;
snapshot modes 7 → 3 (`O.`, `T.`, `I.`): 5 outputs per input instead of 9.
Bench modes `O-local`, `O-function`, `O-operands`, `O-cells` go,
`O-stack` stays. The other axes (`--branches`, `--checks`, `--memcpy`,
`--inline`) are not part of this proposal.

**Outcome (approved and done).** The orchestrator approved all three,
flow included, with these conditions: the kept modes' outputs do not
change, every checker rule keeps its test, the removed modes' coverage
moves to temps, and a retired value fails loudly. In the commit after
`7fc3fa2`:

- *Unchanged outputs.* The snapshot's 2,965 outputs (no `-O`,
  `-O --registers=stack`, temps, and temps with inlining) and the `-O`
  assembly of `sqlite3.c` (59 MB) are byte-identical to `7fc3fa2`'s.
- *Removed:*
  - trusted, 377 lines net: `amd64_cache_check.pl` (266) and flow's
    Rule 1 and label facts in `amd64_regs_check.pl` (111);
  - untrusted, 359 net: `amd64_cache.pl`, flow's rewrite, the
    `local` placement and the `split` pool choice;
  - tests, 768 net: `cache_check.pl`, the cache tests in
    `registers.pl`, flow's 31 cases and plants, `bench-registers`.
- *Kept tested.* The function, operands and cells checkers stay because
  temps runs them, with all their fixtures and plants in
  `regs_check.pl`. Unit tests that compiled through `cells`, `function`
  or `operands` compile through temps; those that used `split` pools as
  a comparator use `own` or `shared`.
- *Coverage moved to temps:* difftest, ABI and GC stress (setjmp
  included), the ensure-aux trace, memcpy, checks and programs, all
  without `-O`; the corpus; and reuse with GC stress.
  `--checks=reuse` builds zlib, bzip2, lz4, hello and Lua with and
  without `-O`, and SQLite with `-O`. Before, SQLite's reuse
  configuration ran on local.
- *Refused.* `tests/registers.sh` (a check step) requires each retired
  value, by option and by `NANOFIL_REGISTERS`, to exit nonzero with no
  output and `registers=MODE was retired (docs/perf.md); registers must
  be stack or temps`. Planting `flow` back into the accepted list fails
  it: the mode then falls back silently to stack emission.
- *Check time.* The `nanofil` check went from 498 s to 396 s and from 95
  steps to 65. Program builds: 10 fewer, 5 more (`O-reuse` for zlib,
  bzip2, lz4, hello and Lua). Snapshot: 5 outputs per C input instead
  of 9.

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

### Status (04c7e7c, updated at the retirement)

Closed, each the `-O` default unless it says otherwise:

| Item | What landed | Where |
| --- | --- | --- |
| 1 | switch dispatch by binary search | item 1 |
| 2 | branch selection: branch on flags, fall through | item 2 |
| 3a | whole-function scalar register homes | item 3, 3a result |
| 3b | register operands, with the region checker | 3b contract and result |
| 3c | indexed frame operands (lz4's `lea D(%rbp,%rax)` functions) | 3c |
| temps | a home per temporary (`--registers=temps`), the frame grown by at most 1.08× | 3d, temps as the `-O` default |
| 5a-loads | frame cells: loads forwarded from a register within a region | 5a-loads result |
| 6a | no borrow test after `upper − Size` | 6a |
| 6c-1 | checks of related pointers; `--checks=reuse`, opt-in (no time win) | 6c |
| 7 | small constant `memcpy` through a filter in front of the call | 7a result |
| 9 | phi shadows shared by position (option A: shadow lowers stay roots) | 9 result |
| inlining | small local leaf functions (`--inline=small`) | item 4 result |
| 5b-1 | `--registers=flow`: cells across checks' jumps and labels; opt-in, then retired (1–2%, +14% compile) | 5b-1, 5b re-measured |
| punned reads | promote reads a union through a narrower member (lz4) | punned union reads |
| 8 | the cheap middle end (`--simplify=full`) | 8: result |
| retirement | the register modes `local`, `function`, `operands`, `cells` and `flow` removed; `stack` and `temps` remain | register modes |

Rejected or dropped, and why:

| Item | Why |
| --- | --- |
| jump tables | after binary search and branch selection, compare-and-branch blocks are an upper bound of 6% of Lua int/tab (0.17G and 0.12G now) and 1% elsewhere, for a new IR terminator and a control-flow-integrity contract (index extension, the unsigned range test, label differences, every successor known to every checker) |
| store-side 5a (5a, full) | its measured ceiling: cell stores overwritten before a boundary are 2.8–3.8% of `rbp` stores, 0.3–0.5% of static instructions; dropped by the orchestrating thread |
| 6c-2, check widening | moves a trap earlier, before scalar stores that precede the failing access, and reports the first access instead of the failing one: the observation-contract change campaign.md rules out, for 2–4% |
| load reuse (6d) | reaches 0–2% of bzip2 `-9`'s checks: stores through other roots kill the facts, and the 2% needs a type-based alias rule Fil-C does not have |
| loop alignment | `.p2align` at backward-jump targets left the geomean at 2.97 against 2.97 and only moved layout noise, for 0.2% padding |
| webs (3d) | contract approved, then held: temps already beat its estimate, and what remains is register pressure |

Not proposed: 6b (at most 2%). Deferred: 5b, now proposed as 5b-1 below.

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

*Step 3a (register homes, moves only) implemented as
`--registers=function`, the `-O` default since its gate result; see
[Results](#item-3a-whole-function-scalar-register-homes).*

#### Step 3b: register operands, and the region checker's contract

*Contract written before the implementation, for review.*

3a leaves values flowing through scratch registers: `movl %ebx, %eax;
movl %r13d, %ecx; cmpl %ecx, %eax` where `cmpl %r13d, %ebx` would do, and
`movl $1, %ecx; addl %ecx, %eax`. A rewrite pass over the 3a stream
(untrusted, `amd64_regs.pl`) forwards register and immediate copies into
the instructions that read them, retargets a scratch result into the home
it is copied to, and deletes copies left dead. The region checker
(`amd64_regs_check.pl`) relates the 3a stream A (already validated
against the reference R) to the rewritten stream B. It knows nothing of
the rewrite's rules.

**Lines.** A *move* is an `ins(mov,{l,q},[Src,reg(Y)])` term whose source
is a general register or an integer immediate, or `ins(movabs,q,[imm(I),reg(Y)])`,
where Y is not `rsp` or `rbp`; no move writes the flags. Every other line
is a *paired* line, and A and B must contain the same paired lines in the
same order. Moves may appear, disappear or differ freely. Every line of B
must have audited effects (`amd64_contract.pl`), as every line of A does;
the contract admits no high-byte registers (`%ah`).

**Immediates.** An immediate's value is I mod 2^W at its operation's
width W. A `q` operation other than `movabs` accepts only
−2^31 ≤ I < 2^31 (sign-extended; GNU as would otherwise turn `movq` into
`movabs` without sign extension, or reject it), an `l` one
−2^31 ≤ I < 2^32, `b` and `w` their own ranges, a shift count 0..255, and
`movabs` −2^63 ≤ I < 2^64. A symbolic immediate (`imm(Sym)`) is never a
move and is compared syntactically.

**Values.** Each stream has a symbolic state: the low and high 32 bits
of each general register, each XMM register as one value, and the
flags. A value is a ground term: `const(N)` (N in 0..2^32−1), `in(R,H,K)`
(the value of half H of R at region entry, K = shared or the stream's
name), `res(J,P,H)` (half H of output P of paired line J; an XMM or flags
output has one value, `res(J,P)`), and the width wrappers
`byte(V)`, `word(V)`, `merge8(Old,New)` and `merge16(Old,New)` for 8- and
16-bit reads and writes. Equality is syntactic (`==`); arithmetic is
uninterpreted.

- A move executes in its stream only. `movq` copies both halves,
  `movl` copies the low half and sets the high half to `const(0)`, an
  immediate sets constants (sign-extended to the high half for `q`;
  `movl $I` zero-extends).
- A paired line requires A's and B's lines to have the same mnemonic,
  size, operand count and audited effect shape: each position is a source
  or destination, GPR or XMM, at the same width, and operand kinds match
  per position, except that a source position may be a register in one
  stream and an immediate in the other. A line that is a boundary in
  either stream (below) must be syntactically identical in the other.
  Every operand that is not a register, immediate or memory operand
  (labels, `sym`, `plt`, directive arguments) must be identical. Then,
  position by position: a register or
  immediate source operand must have the same value in A and B at the
  operand's width (a register reads `byte`, `word`, the low half, or both
  halves; an immediate is its `const`s, sign-extended for `q`). A memory
  operand must have the same form, displacement and symbol, and base and
  index registers with equal 64-bit values. A two-address destination
  is also a source and is compared the same way. Implicit operands
  (`div`'s `rax`/`rdx`, `cltd`/`cqto`, flag reads of `jcc`, `setcc` and
  shifts) are fixed by the equal mnemonic and must have equal values; a
  `cl` shift count is an explicit operand, compared like any source.
  Then each written location gets `res` in both streams, at the
  position's location in each: a 32-bit register write sets the low half
  and `const(0)` high, 64 bits both halves, 8 and 16 bits
  `merge8`/`merge16` of *each stream's own* old low half (the source
  check compared only the low byte or word), an XMM write the XMM value,
  and flags the form defines become `res(J,flags)`. Flags a form
  preserves or leaves undefined (`btc`'s ZF, `imul`'s and `div`'s
  undefined flags) get stream-distinct symbols instead. The SSE
  arithmetic forms (`add`, `sub`, `mul`, `div` with `ss`/`sd`) preserve
  the flags; only the integer forms define or undefine them. Because the line
  is the same deterministic instruction on equal inputs, its defined
  outputs are equal.
- Memory is not modelled. Every memory access is a paired line, so both
  streams make the same accesses in the same order at equal addresses
  with equal stored values; a load's result is `res` and is shared.

**Regions.** A region is a maximal run of lines between *boundaries*:
labels, branches (`jmp`, `jcc`), `call`, `ret`, `leave`, `push`, `pop`,
`ud2`, and any write to `rsp` or `rbp`. Boundary lines are paired lines
(so they are identical and in the same order) and cannot be moves. A
region's start state:

- General register families live at the region start get the same
  `in(R,H,shared)` in A and B; dead ones get `in(R,H,a)` in A and
  `in(R,H,b)` in B, so a read B makes of a register that A treats as
  dead is caught. Home registers (`rbx`, `r12`–`r15`, `r10`, `r11`),
  `rsp`, `rbp` and XMM registers always start shared.
- The flags start shared if live, else as distinct symbols in A and B.
- After a boundary that does not fall through (`ret`, `ud2`, `jmp`), the
  lines up to the next boundary are unreachable: control enters the body
  only at its start and at labels, and boundaries are identical, so B has
  A's CFG. They must pair by mnemonic and size, but nothing is compared
  there, nor at the boundary that ends them; a label reached by a jump is
  covered by the jump's own region end, which compares everything live
  into its target. (Added during implementation: the exception block
  after a `ret` made identical streams fail.)

At each region end, just before the boundary line, A and B must agree,
on both halves of every compared general register, on: every home
register, `rsp` and `rbp`, every XMM register, each scratch register
family (`rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`, `r9`) live after that
point, and the flags if live. The boundary line
is then checked as a paired line. At the function's end each `ret` is a
boundary, so B returns what A returns and preserves the callee-saved
registers as A does; 3a's checker proved A does.

**Liveness.** The checker computes scratch-family and flags liveness
itself from R; it never accepts liveness from the rewrite. It is the 3a
checker's liveness pass, extended by one bit per scratch family and one
for the flags: one liveness run per function, shared with 3a's where 3a
runs one. Functions 3a skips (empty map, no candidates) get that one run
with no home bits. If the CFG cannot be built (`successors/2` fails), B = A.
The scope is the implementation body only, not adapters, getters or
thunks. A read at any width uses the
family; a 32- or 64-bit write defines it; an 8- or 16-bit write uses and
defines it (it keeps the rest). Flags: read by `jcc` and `setcc`; defined by any writing line, shifts
included. (The contract first counted a shift, whose zero count keeps the
flags, as a read too. That kept the flags live from a `div`, whose flags
are stream-distinct, to every boundary before the next shift by `%cl`,
and rejected identical streams in zlib's `adler32_z`. A shift's output
flags are shared only if its input flags are equal, so unequal inputs
still give unequal outputs that a later read rejects.) A
`call` uses all seven scratch families (the checker does not know the
callee's arity) and defines them; `ret` uses `rax`, `rcx` and `rdx` (the
fast ABI returns two words in `rdx` and `rcx`; the contract first said
`rax` and `rdx`, and `tests/c/prog/structs.c` failed in operands mode
until the fixture `at_ret_rcx` and this fix); the
stack-overflow jump uses all; `ud2` uses none. This is the same CFG as
3a's, which rejects unknown transfers, so check-fail blocks make `rax` and
`rcx` live at the conditional jumps that reach them. The liveness carries
over from R to A because 3a changes no scratch or flag use or definition:
`substitute/3` replaces only the home operand of a `mov`, `movz*` or
`movs*`, and its inserted saves and restores, which take the live set of
their insertion point, move between callee-saved registers and save
slots. The 3a
checker already proved A is exactly that stream.

**Why the boundaries suffice.** Every path into a region comes through a
boundary: a label (any predecessor's end, which established equality of
everything live there), the line after a branch or call (that boundary's
region end), or function entry, where A and B are the same machine
state. Boundary lines are identical, so what they write lands in the
same place with equal values; in particular `rsp` is equal in A and B at
every instruction, so an asynchronous signal frame lands in the same
place. So at every region start, every live register is in fact equal in
A and B, which is what the shared `in` symbols assume, and a dead one is
not assumed equal. Within a region both streams execute the same paired
lines on values the checker proves equal, so each paired line computes
the same outputs and makes the same memory access. A `call` boundary
has equal arguments, memory and callee-saved registers on both sides, so
the callee behaves the same; the identical `call` line writes `res` to
the same caller-saved locations in both streams. Memory is equal except
for pushed return addresses, which differ between A and B; nanofil code
and the runtime never read them as data (an assumption: every `rip()`
operand the emitter produces is a data symbol). A collector or signal handler only
runs inside calls (polls are calls), and it reads only memory and
`lowers[]`, which are equal. Exceptions return through `leave`/`ret`,
boundaries like any other.

**Fallbacks and errors.** A setjmp function, or any line without
audited effects, keeps B = A. A failed check is an error, never a
silent fallback.

**Costs.** The checker is region-local symbolic execution, linear in the
function, plus eight bits per line in the shared liveness bitsets. It must not
raise the peak memory of `sqlite3.c` with `-O` (5.6 GB) by more than a
few percent; the measurement goes with the result.

**Fail-first fixtures** (`tests/regs_check.pl`), one per rule: a
forwarded read of a register redefined in between; a `movl` copy used at
64 bits; swapped `sub` operands; a different memory displacement or base
value; a deleted or added memory access; a scratch register live at a
region end left different (into a fail block, into a call, at `ret`);
flags read after a region start where they are dead; a read of a register
dead at region entry; a home register different at a label; an
immediate outside imm32 for `q`; `movq $0xffffffff` against `movq $-1`;
a retargeted `subq $16,%rsp` and a `jcc` with a different target (boundary
identity); a register operand swapped for a memory operand; `%ah`; an
8-bit write merged over different upper bits; `movl` against `movq`
into `%rdi` before a call.

Oracle reviewed this contract before implementation. Two blockers are
fixed in the text above: boundary lines were not required to be
identical (a retargeted `subq $16,%rsp` was accepted, leaving `rsp` 16
bytes off), and the `q` immediate rule did not match GNU as. The
should-fix items are folded in too: B's lines must be audited with A's
effect shape, partial writes merge per stream, both halves of every
compared register, preserved or undefined flags are not shared, and
liveness is computed by the checker, once per function.

#### Step 3b: result

`--registers=operands` (opt-in; bench mode `O-operands`) runs 3a, then
the rewrite in `amd64_regs.pl` ("Step 3b"), then the region checker
`check_operands/3` in `amd64_regs_check.pl`. The rewrite works one region
at a time: a forward pass propagates register and immediate copies into
later moves, source operands and addressing registers, but never replaces
a home register's name with a scratch one. Moves into dead scratch
registers are deleted. A scratch result copied into registers is written
into the first of them: `op …,%S; mov %S,%H` and
`mov X,%S; op Y,%S; mov %S,%H` become `op …,%H` and `mov X,%H; op Y,%H`.
The liveness is the shared `body_analysis/4` run, extended by the scratch
and flags bits (one run per function; `operand_lives/4` maps it to A).

`LZ4HC_countBack`'s loop head, 3a then 3b:

```
movl %r13d, %eax          movl %r13d, %ebx
movq %rax, %rbx           movl %r12d, %r10d
movl %r12d, %eax          subl %r13d, %r10d
movl %ebx, %ecx           cmpl $3, %r10d
subl %ecx, %eax           jle .LLZ4HC_countBack.L37
movq %rax, %r10
movl %r10d, %eax
cmpl $3, %eax
jle .LLZ4HC_countBack.L37
```

Fixtures: 50 `operand_case`s and their kin in `tests/regs_check.pl`,
covering every rule listed above plus those Oracle's review of the result
asked for. Each of 32 planted checker bugs fails at least one of them.
The implementation found two errors in the contract, both fixed in the
text above: `ret` uses `rcx`, and a shift does not read the flags for
liveness. The first was a miscompile the checker accepted
(`tests/c/prog/structs.c`); the second rejected identical streams. A rewrite
bug that dropped a line's effects (so copies were not invalidated) was
rejected by the checker, as it should be. Oracle's review of the result
found no blockers. It found the fixture gaps, now closed. It also found
that SSE arithmetic was modelled as writing the flags, now fixed.

Gate (7 trials, cpu 6), ratio to filcc -O2, time (instructions), with the
trials' range of time ratios:

| Workload | `O` (3a) | `O-operands` (3b) | overlap |
| --- | --- | --- | --- |
| zlib -6 | 3.18 (5.62) 3.12..3.26 | 2.96 (4.64) 2.93..2.99 | no |
| zlib -d | 2.52 (4.22) 2.45..2.56 | 2.47 (3.84) 2.36..2.48 | yes |
| bzip2 -9 | 2.63 (3.61) 2.62..2.64 | 2.43 (3.02) 2.43..2.44 | no |
| bzip2 -d | 4.08 (4.20) 4.07..4.09 | 4.16 (3.67) 4.15..4.17 | no, slower |
| lz4 -1 | 3.37 (22.69) | 3.25 (22.03) | yes |
| lz4 -9 | 5.49 (5.87) | 5.43 (5.55) | yes |
| lz4 -d | 5.47 (17.46) | 5.34 (16.88) | yes |
| lua int | 3.43 (3.24) | 3.42 (3.04) | yes |
| lua tab | 3.25 (3.14) | 3.23 (2.96) | yes |
| lua str | 1.67 (1.92) | 1.65 (1.80) | yes |
| sqlite | 2.41 (2.47) 2.40..2.45 | 2.27 (2.26) 2.26..2.28 | no |
| geomean | 3.22 (4.92) | 3.14 (4.49) | |

3b removes 9% of the dynamic instructions (geomean), up to 17% (zlib -6,
bzip2 -9), but only 2.5% of the time: the copies it deletes were cheap
(move elimination at rename), and what remains is dominated by the
stack-slot pointer traffic 3b leaves alone. bzip2 -d is 2% slower with
13% fewer instructions. One limitation is in the contract: a call uses
every scratch register, so a dead copy into `rcx`, `r8` or `r9` before a
call survives. Knowing the call's argument registers would need the
emitter to state them, which is a contract change.

Compile time as first landed: `lvm.i` 3.65 s → 4.71 s (+29%),
`sqlite3.c` 122.1 s → 141.7 s user (+16%). Peak memory for `sqlite3.c`
is unchanged at 5.58 GB. The checker is about a quarter of the backend's
time and the rewrite a fifth.

Most of the checker's cost was choicepoints, not work. `put_slot/4` had
clauses for both `r/16` and `x/8` under each index, and `operand_write/5`
chose its role with a disjunction, so each paired line left a choicepoint
behind. A function's walk kept them all, and with them every state it had
built. The checker took 0.66 s on all of `lvm.i`'s functions alone but
1.2 s inside the compiler, with the module live, which points at garbage
collection over the retained states. Splitting `put_xslot/4` off, writing the
roles as clauses, and reading registers by width through clause indexing
make the walk deterministic. An identical line also reuses A's effects
rather than auditing B's again, and the rewrite skips forwarding when
nothing is held. The output is byte-identical (snapshot, all modes).
Backend time on `lvm.i` (CPU s, SWI):

| | function | operands, before | operands, after |
| --- | --- | --- | --- |
| backend | 1.45 | 3.04 | 2.11 |
| `check_operands/3` | | 1.20 | 0.21 |
| rewrite | | 0.33 | 0.25 |

`sqlite3.c` with `-O` (user time, after the C thread's frontend work):
function 60.0 s, operands 72.2 s (+20%, was +46%: 72.8 s → 106.1 s
measured before it). Peak RSS is 2.93 GB in both modes.

bzip2 -d is slower with fewer instructions because of code layout, not
because of what 3b emits. `BZ2_decompress` is one function of about 40k
lines, and its loops' alignment decides how often the op cache misses.
In function mode alone, padding the function's start with `.skip N`
moves its cycles between 1.81G and 2.07G, tracking
`de_src_op_disp.decoder` (micro-ops from the legacy decoder). With 3b's
passes added one by one, cycles go 1.75G (function), 1.94G (forwarding),
1.98G (+ dead moves) and 1.83G (+ retargeting): each changes the layout.
With `.p2align 5` at the 123 targets of backward jumps (the loop heads),
function mode runs 1.81G and operands 1.76G, and both stay put under
the same padding. The gate measures layout luck in one large function
here. Aligning loop heads would be a small emitter change.

Measured on the whole gate at [`3d3d251`](https://github.com/mbrock/filnix/commit/3d3d25182318)
(cells default), with `.p2align 4` before every backward-jump target in
every translation unit against the same build without it, 9 trials:
geomean 2.97 (4.57) without it and 2.97 (4.58) with it. No workload's
ranges separate. zlib `-d` 2.06..2.10 against 2.02..2.06 touch; bzip2
`-d` 3.62..3.65 against 3.59..3.66 overlap; lz4 `-9` moves the other way
(4.06 to 4.11). It adds about 0.2% instructions as padding. Not adopted:
it only moves the layout noise.

A fresh gate run at [`9bcbb67`](https://github.com/mbrock/filnix/commit/9bcbb67ec04d)
(7 trials, cpu 6, same compiler output; the binaries were relinked) bears
this out. bzip2 -d is now 3.71 (3.67) in operands mode against 4.17
(4.20) for `O`, where it was 4.16 against 4.08:

| Workload | `O` (3a) | `O-operands` (3b) |
| --- | --- | --- |
| zlib -6 | 3.18 (5.62) 3.14..3.21 | 2.98 (4.64) 2.95..3.01 |
| zlib -d | 2.50 (4.22) 2.42..2.53 | 2.47 (3.84) 2.39..2.51 |
| bzip2 -9 | 2.61 (3.61) 2.60..2.62 | 2.41 (3.02) 2.41..2.42 |
| bzip2 -d | 4.17 (4.20) 4.14..4.17 | 3.71 (3.67) 3.69..3.75 |
| lz4 -1 | 3.40 (23.11) | 3.27 (22.43) |
| lz4 -9 | 5.67 (5.87) | 5.50 (5.55) |
| lz4 -d | 5.40 (17.48) | 5.28 (16.88) |
| lua int | 3.58 (3.24) 3.52..3.62 | 3.60 (3.04) 3.53..3.64 |
| lua tab | 3.50 (3.14) | 3.48 (2.96) |
| lua str | 1.67 (1.92) | 1.64 (1.79) |
| sqlite | 2.40 (2.47) 2.39..2.41 | 2.27 (2.26) 2.26..2.27 |
| geomean | 3.27 (4.92) | 3.14 (4.49) |

No workload is slower outside the trials' range (lua int overlaps), and
the compile cost is now +20% on `sqlite3.c`. Proposed: make
`--registers=operands` the `-O` default, keeping `function`, `stack` and
`local` selectable.

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

#### 4. Contract (approved; implemented as `--inline=small`, the `-O` default)

**What inlining buys, measured.** filcc's own `-O2` against
`-O2 -fno-inline`, user instructions: lz4 `-9` 2.84G / 5.19G, lz4 `-1`
0.15G / 0.37G, Lua int 1.18G / 1.91G, tab 0.96G / 1.45G, str 3.51G /
3.99G, bzip2 `-9` 4.67G / 4.76G, zlib `-6` 1.96G / 1.96G. Checks are
not where it pays. On bzip2 `-9`, filcc without inlining runs 299M
checks, against 230M with it and nanofil's 539M. Its per-function
counts line up with nanofil's:

| bzip2 `-9` function | filcc `-fno-inline` | nanofil `-O` |
| --- | ---: | ---: |
| `copy_input_until_stop` | 35M | 129M |
| `mainGtU` | 84M | 85M |
| `mainQSort3` | 45M | 77M |
| `mainSort` | 42M | 64M |
| `sendMTFValues` | 36M | 62M |
| `generateMTFValues` | 29M | 46M |

So item 6c's hypothesis was mostly wrong: the check gap is inside
functions, chiefly reloaded fields such as `s->strm->avail_in` (load
reuse across pointer loads). Inlining's gain is call overhead.

A prototype (`/tmp`, not committed) inlined static, non-variadic,
non-setjmp leaf callees of at most 120 pre-promotion instructions into
callers of at most 2000, two rounds, hoisting direct-only allocations
as below. Gate, 5 trials, ratio to filcc, time (instructions), `-O`
against the prototype: lz4 `-9` 4.10 (4.71) / 3.20 (3.83), lz4 `-1`
2.42 (13.17) / 2.11 (9.67), lz4 `-d` 3.20 (8.40) / 2.92 (6.74), Lua str
1.59 (1.71) / 1.56 (1.66), SQLite 2.08 (2.07) / 2.21 (2.11), the rest
within 0.04; geomean 2.45 (3.63) / 2.36 (3.39). lz4 `-9`'s checks went
from 157M to 189M (filcc 111M) while its instructions fell from 13.2G
to 10.0G. Without the caller cap, SQLite was 2.62: `sqlite3VdbeExec`'s
frame grew from 0x1510 to 0x1c10 bytes and its hot loop spread over
more slots. Lua int and tab do not change, because their hot helpers
(`luaH_getint`, ...) are extern. sqlite3.c at `-O`: 1:44 and 2.27 GB
without, 1:57 and 2.30 GB with.

**Where.** A middle-end pass `inline`, first in `o1`, on unchecked IR
before promotion. Everything after it, pizlonation, checked-IR
validation, check reuse, emission and the register checkers, sees
ordinary code; no checked-IR contract changes. `--inline=none|small`
and `NANOFIL_INLINE` select it; `none` is the reference path, and
without `-O` it is off. nanofil-cc maps `-fno-inline` and `-O0` to
`none`. The snapshot pins the mode.

**Callee eligibility.**

- Defined in the module with `local` linkage. Extern callees are
  excluded: a shared library's exported definition can be interposed
  at load time. This loses Lua's `luaH_*`; a later round can admit
  extern callees in executables (`-fno-semantic-interposition`, as clang
  does by default for non-PIC code).
- No `va_args` instruction: its argument snapshot belongs to its own
  entry. This also excludes generic-only fixed callees (byval or
  float-pair structs, x87 returns, more than 16 words), which use the
  same snapshot (*review*).
- At least one reachable `ret`, and strict SSA (`strict_ssa/3`): a join
  phi with no predecessors is invalid, and a non-strict callee would
  cost the whole caller its promotion (*review*).
- `noinline` is not kept by the frontend (`func/5` has no attribute
  field), so it is ignored, unlike filcc; honouring it is an IR change
  for the orchestrator to agree first (*review*).
- No `setjmp` or other returns-twice call (`setjmp_func/1`). A call to
  `longjmp` is an ordinary call and is fine.
- No tuple return (`rets`), no dynamic-size `alloc` (VLA, `alloca`), no
  allocation over 256 bytes.
- No recursion: callees are taken bottom-up from the module call graph
  restricted to defined functions; a function in a cycle, a self-call
  included, is never inlined. At most two rounds (depth 2).
- Size: at most 120 unchecked instructions (jumps counted). Indirect
  calls never inline: the callee is unknown.

**Caller eligibility.** Not a setjmp function: it keeps reference
selection, and inlined temporaries would be live across returns-twice.
Not in a call-graph cycle: inlining into a recursive caller grows every
recursive frame, so stack overflow would come at a smaller depth
(*review*). At most 2000 instructions, and growing by at most half its
size or 120 instructions, whichever is more (*amended*: exactly 1.5×
would forbid inlining into any caller under 240 instructions). Both
caps are on the caller's size before the first round (*amended*: per
round, the second round would grant another half). A variadic caller
is fine. Both amendments were accepted with the implementation.

**Transformation.** Split the calling block at the call. Copy the
arguments into renamed parameters, rename every temporary and label of
the callee with a fresh prefix, place its blocks right after the
calling block, turn each `ret(V)` into a jump to a join block whose phi
takes V, and move the original jump to the join block, renaming the
calling block to the join block in its successors' phis. Labels and
temporaries are fresh against both functions' names (as
`pizlonate:fresh_name`), not a fixed prefix, which can collide in IR
text (*review*). Source contexts follow: the callee's origin IDs, temps
and labels are renamed into the caller's records, `inst(L, I)` sites are
re-indexed after the split, and `site(jump(L))` moves to the join block;
the prototype dropped them, which opt.pl does not allow. Block order
keeps every callee loop's back edge an edge to an earlier block, so
pizlonation still polls every cycle; edges into and out of the inlined
body are forward and not polled, as a call is not.

**Allocations** (revised after review). The prototype hoisted a
callee's entry allocations to the caller's entry and reset them with
stores at the original point. Review showed that this is unsound and
counterproductive, reproduced under the interpreter:

- An integer store keeps the word's capability (abi-findings.md), and
  any 8-aligned word of a 16-aligned object can hold a pointer, padding
  included. `int b; *(char **)&b = p;` read back on a second call trapped
  `null_capability` without `-O` and returned 0 with the prototype.
- Its direct-only test ignored phis and jumps, so it hoisted an escaping
  `return &x`: two calls returned the same object (`ret 1`, not 0).
- The 8-byte null stores gave slots two widths, which promotion rejects,
  so `long` and `double` locals stopped promoting. That probably explains
  lz4 `-9`'s checks rising from 157M to 189M (not verified).

The contract therefore does not hoist. Instead promotion learns to take
a constant-size allocation in any block, not only the entry, whose
escape class (`escape:alloc_classes/2`, which sees phi, jump and call
uses) is `local` and whose slots pass `slots_ok`: the alloc instruction
counts as a store of 0 to every slot, and its block joins the
definition blocks for phi placement. Under strict SSA every access goes
through the latest execution's address, so this is exact on its own,
and `passes([inline])` without promote stays correct (each allocation
stays a fresh heap object per execution). A callee is inlined only if
each of its entry allocations either promotes that way or escapes; an
escaping one is a heap object inlined or not, while a non-escaping one
that could not promote would turn a local object into a per-call heap
allocation. Allocations keep their order relative to the caller's own,
so the 4096-byte local-storage budget is not taken first by inlined
objects. Promotion is shared code, so this part is its own commit with
its own refinement tests, before inlining. **Landed:** promote.pl now takes a constant-size
local alloc in any block (unit `promote_nonentry_allocs`: a fresh 0 per
pass of a loop, a pointer from an earlier pass trapping as null in a
promoted and in a too-small, unpromoted object, and an address merged
in a phi staying a distinct heap object per pass). No C input changes,
since the frontend puts every local in the entry block; the snapshot
differs only in two IR fixtures' `-O` outputs.

**Function identity.** The callee's function object, getter, generic
entry and alias are still emitted unchanged, so its address,
comparisons of function pointers and indirect calls are unaffected.
Dropping static functions left unreferenced is out of scope.

**Observation changes**, the review point:

1. *Check failures in inlined code.* Today nanofil reports the
   function containing the access: "semantic origin: get; check
   scheduled at: get / outer / main". filcc `-O2` without `-g` reports
   only the function the code ended up in ("semantic origin: main;
   check scheduled at: main"); with `-g` it lists "get (inlined) /
   outer (inlined) / main" from `filc_inline_frame` nodes
   (`num_lowers_ish == UINT_MAX`, filc_runtime.h:459-563), measured
   with a small test. Proposal (A): report as filcc `-O2` without `-g`
   does, the caller's frame only. (B), follow-up: emit inline-frame
   check origins from provenance, so nanofil reports what filcc `-g`
   does, without file and line. Review confirmed the layout and found
   what (B) costs: chains per inline path ending at both the `c` and
   `n` function origins (the pass keys them by `CanCatch`); check
   origins and fail blocks per (path, kind); per-path origin stores
   before calls and polls, getter origins and `unreachable` origins;
   and an inline path per instruction surviving every later pass.
   The collector reads `num_lowers` through the chain, so a malformed
   one is a GC crash, not a wrong message. Driving it from provenance
   would let metadata decide panic text, so it needs an IR path marker,
   a grammar change. (A) is described as "as filcc does for the calls
   it inlines", which is where both compilers agree.
2. *Traces through calls from inlined code* lose the inlined frame, as
   with filcc without `-g`: panics in a callee or in the runtime
   (getters, allocation), and `zstack_scan`, which returns the frames to
   user code (*review*).
3. *Frames*: recursive functions are neither inlined nor inlined into,
   so recursion depth before stack overflow is unchanged.
4. *No trap moves or changes kind.* Every access keeps its check
   (pizlonation runs after), and every block order keeps a poll on
   every cycle, since pizlonation polls by block index. Each allocation
   stays fresh at each execution.

**Validation.**

- Unit tests for each exclusion: extern, variadic, setjmp in callee and
  caller, tuple return, VLA, recursion (self and mutual), size caps,
  indirect calls.
- `-O` difftest refinement on everything it already runs, plus a
  fixture for each hazard:
  - a callee called in a loop that reads its local before writing it;
  - an object with alignment under 8 holding a pointer, read back on a
    later call, and an access in heap padding (the review's
    reproduction);
  - a returned local, also through a phi (`c ? &x : &y`), `if (&x)` and
    `ptoi`; called in a loop, comparing the two pointers in the program
    (`refines/2` keys pointers by offset);
  - `long`, `double` and struct-field locals still promoting after
    inlining (count allocations and local objects);
  - a generic-only (byval) callee, a callee with no `ret`, label and
    temporary collisions in IR text;
  - a phi successor of the calling block; void and valued returns; a
    callee with a loop;
  - both sides of the 120, 2000 and growth caps; a recursive caller;
    `passes([inline])` alone;
  - an inlined out-of-bounds access, its function lines compared with
    filcc `-O2`'s in a panic-text harness (progtest reduces every
    panic to "trap").
- Native: progtests and run-c under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`.
- Plants: no phi rename, admitting an escaping allocation to
  non-entry promotion, promoting without the alloc's zero, admitting
  recursion or setjmp callers, no growth cap, fixed-prefix names. Each
  must be caught.
- **Review.** Oracle reviewed this contract and the prototype: block
  placement, polls, function identity, GC roots and frame sizes, and
  (A) as the origin policy hold. Its two blockers, the store reset and
  the escape test, replaced the allocation design above; its other
  findings are marked *review*.
- Snapshot limited to `-O` outputs, the gate (no workload slower beyond
  its trial range, SQLite included), the ten checks, and sqlite3.c's
  `-O` compile within 25% of its time and memory.

#### 4: result (`--inline=small`, the `-O` default)

`src/inline.pl` is the pass, first in `o1(small)` (opt.pl);
`--inline=none|small` and `NANOFIL_INLINE` select it (main.pl), and
without `-O` it is off. nanofil-cc passes `--inline=none` for
`-fno-inline` and `-O0`. It is the `-O` default; `--inline=none` keeps
the uninlined path, which the bench's `O-noinline` mode and the Nix
check's `-O inline=none` difftests, ABI+GC run-c and progtests (GC
stress) run. The snapshot pins `--inline=none` in its four existing `-O`
modes and adds `I.`, frame cells with `--inline=small`.

Departures from the contract, none of them a safety rule (the first
two are now in the contract's caller rule):

- *Growth cap*: a caller may grow by half its size **or by 120
  instructions, whichever is more**. Exactly 1.5× forbids inlining
  anything into a caller under 240 instructions (wrappers, most
  `static` helpers' callers), where frame growth is negligible.
- Both caller caps, 2000 and the growth, are on the caller's size
  **before the first round**. A first version measured them per round,
  so round 2 granted another half; `inline_small` caught it (`k300`).
- In plain mode every callee alloc must promote: an unpromoted plain
  stack alloc would live until the caller returns.
- A callee label can be the join's base name: the join takes the first
  of `join`, `join_`, ... that no callee name and no caller name uses.
- Splits and callee records are collected while the blocks are walked
  and applied to the caller's records in one pass: rewriting the record
  list per inlined call was quadratic on SQLite's largest functions.
- difftest gives the inlined module twice the original's fuel: each
  inlined call adds a join block.
- `va_args` alone excludes a variadic callee (`variadic_func/1` is the
  same test).

**Panic origins** (decision (A)). Under `--inline=small` a check that
fails in inlined code reports the function the code ended up in, as
filcc `-O2` without `-g` does. Measured on an out-of-bounds read in
`get`, called from `sum`, called from `main`, all static but `main`:

| build | semantic origin | check scheduled at |
| --- | --- | --- |
| filcc `-O2` | `main` | `main` |
| nanofil `-O --inline=none` | `get` | `get`, `sum`, `main` |
| nanofil `-O --inline=small` | `main` | `main` |

The rest of the safety message (the pointer, "expected 4 bytes") is
the same. (B), inline frames as filcc `-g` reports them, stays a
follow-up that needs an IR path marker, a grammar change. progtest
reduces every panic to "trap", so this comparison is recorded here
rather than kept as a test.

**Tests.** Unit `inline_small`: eligible calls inline (a loop body
with a phi successor, a fresh zero per call in a loop, a returned local
through a phi and `ptoi`, depth 2, a name collision with the round's
prefix that the renamed body would redefine, a callee label `join`);
each exclusion keeps its call and leaves `users` unchanged (recursive,
variadic, extern, 300-byte and dynamic allocs, setjmp callee and
caller, no `ret`, recursive caller); both sides of the 120, 2000 and
growth caps; every run keeps its outcome under `passes([inline])` and
`o1(small)`. Unit `inline_contexts`: the exact sites after two inlined
calls in one block. `tests/c/inline.c`: static callees in loops with
`long`, `double` and struct locals, a returned local's address, void
returns and loops; a byval callee and a union local only local storage
takes stay calls. Plants, each caught: no phi rename, no zero for a
promoted alloc, admitting a recursive caller, a non-leaf callee, a
setjmp caller or callee, `va_args`, dynamic allocs; no growth cap,
per-round growth, each cap one higher; fixed-prefix names; no reapplied
split, a wrong shift. Two plants first survived and tightened the test:
dropping the leaf rule (the inlined recursive body still held one call,
hence the `users` equality), and fixed prefixes (the IR allows a
redefinition, so the collision now clobbers a value read after the
call).

**Gate** (5 trials, ratio to filcc, time (instructions); the `O`
binaries are 812a745's, whose C outputs the snapshot shows unchanged):

| workload | `-O` | `-O --inline=small` |
| --- | --- | --- |
| zlib -6 | 2.57 (4.21) | 2.60 (4.21) |
| zlib -d | 2.02 (3.38) | 2.04 (3.38) |
| bzip2 -9 | 2.07 (2.66) | 2.06 (2.66) |
| bzip2 -d | 3.62 (3.40) | 3.75 (3.40) |
| lz4 -1 | 2.42 (12.92) | 2.25 (10.71) |
| lz4 -9 | 4.07 (4.71) | 2.91 (3.71) |
| lz4 -d | 3.08 (8.32) | 2.88 (7.24) |
| lua int | 2.25 (2.49) | 2.25 (2.49) |
| lua tab | 2.09 (2.40) | 2.08 (2.40) |
| lua str | 1.58 (1.71) | 1.53 (1.64) |
| sqlite | 2.07 (2.07) | 2.07 (2.04) |
| geomean | 2.44 (3.62) | 2.34 (3.42) |

SQLite is unchanged (2.07..2.11 against 2.06..2.07): measuring the caps
on the pre-inlining size is what fixed the prototype's 2.08 → 2.21.
lz4 `-9` gains more than the prototype did (4.10 → 3.20 there). bzip2
`-d` is 4% slower over 11 trials (3.61 against 3.76) with the same
4.85G instructions. Its hot functions (`BZ2_decompress`,
`unRLE_obuf_to_output_*`) are the same size in both binaries, and only
compress-side functions and `main` grew. Legacy-decoder micro-ops rise
from 0.75–0.76G to 0.79G: this is the layout sensitivity measured under
3b, not inlined code. zlib's +1% is within its range.

**sqlite3.c `-O` compile**, under the 4 GB stack limit its builds use
(`NANOFIL_STACK_LIMIT`): `--inline=none` 90.6 s user, 1:37 wall,
1.46 GB peak RSS; `--inline=small` 105.0 s (+16%), 1:52, 1.46 GB.
Under SWI's default 1 GB limit both also finish, at 2.28 and 2.27 GB.
The
pass itself takes about 5 s; the rest is the 18% more blocks (66k to
78k) that later passes and the backend handle. Reaching that took three
changes to a first version that was quadratic and overflowed SWI's
default 1 GB limit with 200 MB live: per-call rewriting of the caller's
records (now one pass), linear ordsets for the module's 3,000 names,
the caller's names and the cycle search (now assocs; 17 s to 4.4 s
under the profiler), and the first round's garbage, which SWI's limit
counts as allocated (collected between rounds, as main.pl does between
stages; peak RSS was 2.14 GB without it).


**Default.** It became the `-O` default once the conditions held:
SQLite within its range, the compile within 25%, every other workload
faster or unchanged in instructions (bzip2 `-d`'s time is layout).

Not inlined yet, measured: `escape.pl` classes a `d` load as escaping,
so `double` and struct-with-`double` locals stay heap objects with or
without inlining (`mix` in `tests/c/inline.c` keeps three); that is a
promotion limit, not an inlining one. Lua's hot helpers are extern.

### 5. Pointer frame traffic — needs review

The original idea: keep `p` addresses, and then lowers, in registers
between safepoints. It is a **safety decision**: a lower held only in a
register is invisible to the collector. The proposed rule was that every
`call` is a safepoint, with no exemptions (polls, `filc_allocate`,
ensure-aux and the store-barrier slow path included: an exited thread's
frames are scanned, and a filcc callee may spill a callee-saved register
to the unscanned native stack), and that at each one every live
pointer's lower is in its `lowers[]` entry. Measurements after 3b change
the plan.

#### Where the frame traffic is now

Cachegrind on `-O --registers=operands` builds assembled with `-g`, each
`(%rbp)` access attributed through the emitter's frame layout (slot keys
per offset: `lower(…)` entries, `storage(pointer,…)` and pointer phi
shadows, scalar homes left in the frame). Share of all instructions:

| Workload | total | lowers ld | lowers st | addresses ld | addresses st | scalars ld+st | redundant loads in a region |
| --- | --: | --: | --: | --: | --: | --: | --: |
| zlib -6 | 9.11G | 8.4% | 6.2% | 7.4% | 4.9% | 6.8% | 10.3% (12.9%) |
| zlib -d | 0.75G | 8.0% | 6.3% | 7.1% | 4.9% | 19.2% | 14.6% |
| bzip2 -9 | 14.13G | 7.9% | 4.5% | 7.8% | 4.2% | 3.8% | 8.9% (13.1%) |
| bzip2 -d | 5.24G | 7.2% | 5.0% | 6.3% | 4.1% | 23.3% | 13.2% (15.9%) |
| lz4 -9 | 15.76G | 3.7% | 4.2% | 4.0% | 2.6% | 23.2% | 9.7% (9.9%) |
| lua int | 3.59G | 7.2% | 5.2% | 5.7% | 3.7% | 23.9% | 16.0% (17.9%) |
| lua tab | 2.90G | 7.4% | 5.4% | 5.9% | 3.9% | 22.8% | 16.4% |
| lua str | 5.39G | 5.1% | 6.0% | 5.0% | 3.5% | 1.8% | 5.3% |

"Redundant loads in a region" is an upper bound: loads of a frame word
already loaded or stored earlier in the same region (straight-line code
between labels, jumps and calls), whatever its class. In brackets, the
same if the jumps to check-fail blocks did not end a region.

Three findings:

- **Register pressure, not pointer class, is the limit.** Adding pointer
  address slots to 3a's candidates (scratch experiment; all outputs equal)
  *adds* instructions: zlib -6 −2.6%, bzip2 -9 +1.4%, bzip2 -d +3.5%,
  lz4 -9 +0.3%, lua int +0.3%. With seven allocatable registers, pointer
  homes displace scalar homes. A pointer needs two registers (address
  and lower). `luaV_execute` maps 211 of its 305 homes and
  `BZ2_decompress` 277 of 603; the scalar homes left in the frame are
  their 23–24%.
- **One excluded function is 23% of lz4 -9.** 3a maps none of
  `LZ4HC_InsertAndGetWiderMatch`'s 139 homes: the preflight rejects any
  function with an indexed frame operand, and the function computes
  `lea D(%rbp,%rax)` into local storage. Scalar homes left in the frame
  cost 3.58G of lz4 -9's 15.76G there. Item 3c below.
- **A tenth or more of all instructions reload a frame word in the same
  region.** Region-local forwarding of frame words needs no register
  across a call, so it adds no register pressure and no root decision.

So item 5 becomes two steps. 5a forwards frame words within regions,
which keeps `lowers[]` exactly as the reference has it at every boundary.
5b, pointers in registers across calls, waits until more registers are
free (live-range splitting or regional use of the scratch registers),
because today it loses.

#### 3c. Indexed frame operands

The only indexed `rbp` operands come from `local_check`
(`filc_amd64.pl`): `lea (8-Aux)(%rbp,%rax),%rdx` and
`lea -Payload(%rbp,%rax),%rax` after the range check, where `%rax`
holds the access's constant offset `Off`. The first proposal (accept an
indexed `lea` whose displacement misses every mapped home and save slot)
bounds nothing: the address is `rbp+D+X` for any X. Oracle's review
found that, and a simpler fix with no new trust. When `Off` is in range
and aligned, the emitter emits `lea (-Payload+Off)(%rbp)` and
`lea (8-Aux+Off)(%rbp)` after the same check (otherwise the success path
is unreachable and the indexed form stays). 3a's existing rule for a
non-indexed `lea` then sees the exact address, and the checker does not
change. Expected: most of lz4 -9's 23% in `LZ4HC_InsertAndGetWiderMatch`.
Cost: small, in the shared `filc_amd64.pl`; the snapshot changes where
locals are accessed. Checks and trap behaviour are unchanged.

#### 5a. Frame words: forwarding loads first

Oracle reviewed the contract below before implementation and found two
blockers in it. (1) The prologue's `lea -FrameBase(%rbp)`, published to
`thread->top_frame`, is a `lea` of a cell, so every function would fall
back. (2) Step 3 is false for the header words. `signal_pizlonator` tests
the stack limit before deferring a signal and, near it, panics with
`filc_thread_dump_stack`, which walks `parent` and dereferences
`origin` at an arbitrary instruction (filc_runtime.c:1795-1812,
2449-2452, 7015-7031). A B that used either word as scratch could make
the panic print from a B-chosen address. The rest of step 3 holds at the
pin: other threads scan this one's frames only while it is not entered
(soft handshakes and stop-the-world wait for that), nanofil code always
runs entered and exits only inside runtime calls, other signals are
deferred to pollchecks, and synchronous faults kill the process without
reading the frame.

So the first step is the smaller **5a-loads**. Cell stores stay paired
lines as in 3b (same order, equal values); only cell loads become moves,
which may disappear or be replaced by a register holding the cell's
symbolic value. Frame memory is then identical in A and B at every
instruction: no observer argument (step 3) is needed, nor region-end
comparison of cells. The only trust is 3a's: nothing but nanofil's own
`rbp`-relative operands reaches a cell within a region (the published
header pointer and `rsp`-relative red zone and argument areas
included). It targets exactly the measured "redundant loads" column.
Cells are listed by key class (`lower(…)`, `storage(scalar|pointer,…)`,
phi shadows, `thread`, `aux`, the `retbuf` pointer slot), never
`parent`/`origin`, locals, wide or save slots, and the checker verifies
they are 8-aligned and disjoint from each other, from locals, wide
slots, save slots and mapped homes. A cell's state is reset to the
shared start value at every region start; a paired 4-byte store writes
the low half and keeps each stream's high half; a non-GPR or odd-width
access of a cell makes the function keep cells as plain memory, and the
implementation reports how often. Fixtures: Oracle's list, plus the
ones below that apply to loads.

Dropping stores (the full contract below) is a second step, after
5a-loads is measured, with the header words excluded and step 3
reworded to name the stack-overflow panic as the one in-region reader.

#### 5a-loads: result

`--registers=cells` (opt-in; bench mode `O-cells`) is operands mode with
frame cells. The emitter lists the cells (`regs_mode/3` in
`filc_amd64.pl`: lowers[], the scalar and pointer pools, phi shadows,
thread, aux, retbuf and stack-aux roots) and the other frame ranges;
`check_operands/4` keeps stores paired and treats whole 32- and 64-bit
cell loads as moves of the cell's value, reset at every boundary. The
rewrite forwards a load to the register that still holds the cell
(`cell_forward/4`), then 3b's passes propagate the copy and delete it
where dead. 13 `cell_case` fixtures; each of 9 planted checker bugs
fails one. Static frame loads drop 16–35% on `lvm.i`, `decompress.i`,
`deflate.i` and `lz4hc.i`; the backend is 2–4% slower than operands
mode (a first version scanned the body per cell for `lea`s and was
+90% on `decompress.i`).

Gate after 3c (7 trials, cpu 6), ratio to filcc -O2, time (instructions):

| Workload | `O` | `O-cells` |
| --- | --- | --- |
| zlib -6 | 2.92 (4.61) 2.90..2.95 | 2.60 (4.36) 2.58..2.62 |
| zlib -d | 2.14 (3.61) 2.07..2.18 | 2.07 (3.48) 1.95..2.09 |
| bzip2 -9 | 2.43 (3.03) 2.42..2.43 | 2.14 (2.81) 2.13..2.15 |
| bzip2 -d | 4.12 (3.67) 4.11..4.13 | 3.69 (3.49) 3.67..3.70 |
| lz4 -1 | 3.42 (22.07) | 3.44 (21.97) |
| lz4 -9 | 4.32 (5.01) | 4.04 (4.90) 4.02..4.95 |
| lz4 -d | 5.23 (16.86) | 5.25 (16.80) |
| lua int | 3.62 (3.04) 3.51..3.88 | 3.46 (2.94) 3.33..3.46 |
| lua tab | 3.48 (2.96) 3.35..3.48 | 3.25 (2.83) 3.15..3.29 |
| lua str | 1.61 (1.79) | 1.57 (1.74) |
| sqlite | 2.28 (2.26) 2.27..2.30 | 2.14 (2.17) 2.14..2.16 |
| geomean | 3.06 (4.42) | 2.89 (4.26) |

Time improves more than instructions (−5.6% against −3.6%): the loads
removed were store-to-load forwards on the critical path. lz4 -1 and
-d are runtime-dominated (small `memcpy`, item 7) and unchanged. The
3c column here is `O` against the previous gate's `O-operands`: lz4 -9
5.50 (5.55) → 4.32 (5.01), zlib -d 2.47 → 2.14.

#### 5a, full: frame words in the region checker (dropped)

**Dropped, by decision of the orchestrating thread (October 2026), on the
measurement below. Do not reopen without a new measurement.**

**Measured ceiling, before writing the corrected contract: too small to
pursue.** Regions end at every label, jump and call (`boundary_line/2`
in `amd64_regs_check.pl`). With every cell compared at each boundary,
a cell store can be dropped only if a later store to the same cell in
the same straight-line stretch overwrites it first. In the cells-default
`-O` output at [`3d3d251`](https://github.com/mbrock/filnix/commit/3d3d25182318),
those stores are:

| Program | Share of `rbp` stores | Share of static instructions |
| --- | --- | --- |
| zlib | 2.8% | 0.30% |
| bzip2 | 3.8% | 0.50% |
| lz4 | 3.3% | 0.36% |
| Lua | 7.3% | 0.74% |

Repeated `origin` stores were the other target; they are excluded now.

Stores of cells that the function never reads again are 0.9–2.3% of
static instructions. That figure includes `lowers[]` roots, which must
stay. Dropping the rest would need cell liveness across boundaries, a
different contract in which the collector observes only `lowers[]` and
the stack-overflow panic only the header. Neither is proposed. The text
below is kept as the record of the first review; implementing it as
written is blocked by the two findings above 5a-loads.


*Contract written before the implementation, for review.*

A **cell** is an 8-byte frame word at an `rbp` displacement D listed by
the emitter: every plain slot of `layout/4` (scalar homes 3a left in the
frame, pointer address slots, phi shadows), every `lowers[]` entry, the
filc_frame's `parent` and `origin` words, and the thread and aux slots.
Not cells: local storage (payload and aux), wide slots, callee-save
slots, return buffers, and anything in a setjmp function (excluded, as
in 3a). The metadata gives the cells, and the checker verifies:

- D is 8-aligned, cells are disjoint, and no cell overlaps a save slot or
  a mapped home.
- Every `rbp`-relative operand that overlaps a cell is a whole access
  of that cell: `mem(D,rbp)` in a `mov` of 4 or 8 bytes, or in a paired
  line as an 8- or 4-byte source or destination at exactly D. Anything
  else overlapping a cell (a byte or word access, an indexed operand
  reaching it by its displacement, a `lea` of it) makes the function
  keep B = A for cells, that is, cells stay paired memory as in 3b.

**State.** Each stream's symbolic state gains a value per cell, two
32-bit halves like a general register. At every region start every
cell is `in(cell(D),H,shared)` in both streams. Cells are not dead or
live: all of them are compared at every boundary.

**Lines.** A *cell move* is a move (3b's definition) with a cell as
source or destination: `movq D(%rbp),%R` copies both halves into R,
`movl D(%rbp),%R` copies the low half and zeroes R's high half,
`movq %R,D(%rbp)` and `movq $I,D(%rbp)` (I in imm32, sign-extended) set
both halves of the cell, and `movl %R,D(%rbp)` or `movl $I,D(%rbp)` sets
the low half and *keeps* the high half (a memory store does not
zero-extend). Cell moves execute in their own stream, like register
moves, and may appear, disappear or differ. A paired line with a cell
operand must have the same cell at that position in both streams; as a
source it compares the cell's value at the operand's width, as a
destination it writes `res` into the cell in both streams, with 3b's
rules for widths. Every other memory operand is paired as in 3b and
never addresses a cell (below).

**Region end.** In addition to 3b's comparisons, A and B agree on both
halves of every cell at every boundary.

**Why the boundaries suffice.** 3b's argument gives equal registers,
equal non-cell memory and identical boundaries. For cells:

1. At function entry the frame is the same memory in both streams. At
   every later region start, the previous boundary compared every cell,
   so the shared start values are true.
2. Within a region, only rbp-relative operands of nanofil's own code
   touch a cell. Every other access goes through a pointer: checked
   accesses stay inside the bounds of the object they check, and no
   object's bounds cover a cell (local storage is laid out beside the
   cells, with exact bounds); the unchecked accesses nanofil emits
   address the thread, aux arrays and object headers, never the
   frame. This is the assumption 3a makes for homes, now for every
   cell.
3. Nothing else observes the frame within a region. The collector
   reads `lowers[]` and the frame header when it scans this thread's
   stack: at its own safepoints, which are calls, or from another thread
   while this one is exited, which happens only inside a call. Signal
   handlers are deferred to pollchecks, which are calls. Check failures
   leave through a jump (a boundary) into a block that calls the fail
   function. `ud2` and the stack-overflow jump are boundaries. So
   between boundaries a cell's memory may differ between A and B, but
   at every point where anything else can see it, it is equal.
4. Because cells are compared at every boundary, B keeps every
   `lowers[]` store A makes before a call, in time for the call: the GC
   sees the same roots at every safepoint as with the reference. This
   is not root reduction. A stale or missing lower is caught at the
   next boundary, not trusted.

**What it allows.** Within a region, B may replace a cell load by a
register that holds the cell's value (forwarding), drop a store that a
later store in the region overwrites before any boundary, and drop a
store of the value the cell already holds (for example a repeated
`origin` store). Across a boundary, nothing changes.

**Liveness.** The rewrite needs free registers to hold forwarded cell
values: scratch families dead over the stretch, from 3b's shared
liveness. The checker needs no cell liveness, since it compares every
cell.

**Costs.** One state entry per cell, built lazily: a cell gets an entry
when a region first touches it, and a region end compares only the
cells either stream touched since the region started; the others hold
the shared start value in both. That keeps the checker linear in the
function and leaves peak memory at 3b's. Expected yield: the
"redundant loads in a region" column is the upper bound, 5–16% of
instructions; the rewrite gets the part for which a scratch register is
free, plus dropped repeated stores. Cost: medium (checker extension and
a forwarding pass in the rewrite).

**Fail-first fixtures**, one per rule: a forwarded load of a cell stored
in between by another register; a cell store dropped before a call, a
`jcc` and a label (one each, a `lowers[]` entry among them); a `movl`
store forwarded as if it zero-extended the cell; a load forwarded from a
register clobbered in between; a cell accessed at a byte width, by an
indexed operand reaching it and by a `lea` of it (each must fall back to
B = A for cells); a cell overlapping a save slot or a mapped home in the
metadata; two overlapping cells.

#### 5b. Pointers in registers across calls (deferred)

Only after more registers are free. It needs the safepoint rule above,
plus two checker obligations: each live lower's `lowers[]` entry
symbolically equals its register at each safepoint, and lower material
never enters a home that item 3 treats as scalar.

#### 5b-1. Contract (approved; implemented opt-in as `--registers=flow`): cells across `jcc`s and labels

**Why this form.** The profile at `04c7e7c` (Where we are now) puts
pointer payloads and lowers at 16–30% of `-O`'s instructions. The reach
is in their loads: 5a-loads forwards a frame word from a register only
within a region, and every label and `jcc` ends a region, so each block,
and each access after a check, reloads the pointer and lower it checks. Measured on the final `.s`
with a forward must-analysis per function (scratch, not kept;
cachegrind counts per line), the loads of pointer and lower frame words
whose value is still, on every path, in the register that last loaded or
stored it, with no call or poll since (labels and `jcc`s not killing):

| Workload | pointer and lower loads | in that register | of which into that same register | share of all instructions (same register / any) | if calls did not kill |
| --- | --: | --: | --: | --: | --: |
| zlib -6 | 1.00G | 0.75G | 0.67G | 8.3% / 9.3% | 0.89G |
| zlib -d | 0.09G | 0.08G | 0.07G | 11.3% / 12.3% | 0.09G |
| bzip2 -9 | 1.25G | 0.67G | 0.62G | 5.3% / 5.7% | 0.91G |
| bzip2 -d | 0.50G | 0.30G | 0.28G | 6.4% / 6.8% | 0.38G |
| lz4 -1 | 0.01G | 0.003G | 0.001G | 0.3% / 0.9% | 0.01G |
| lz4 -9 | 0.78G | 0.35G | 0.25G | 2.6% / 3.6% | 0.47G |
| lz4 -d | 0.03G | 0.010G | 0.008G | 1.5% / 1.9% | 0.03G |
| lua int | 0.44G | 0.31G | 0.30G | 10.4% / 10.8% | 0.41G |
| lua tab | 0.33G | 0.25G | 0.24G | 10.9% / 11.5% | 0.32G |
| lua str | 0.37G | 0.20G | 0.15G | 3.1% / 4.2% | 0.33G |
| sqlite | 2.29G | 1.36G | 1.12G | 5.1% / 6.2% | 1.86G |

A load into the register that already holds the value is deleted; one
into another register becomes a move that forward/3 then propagates.
That needs no register allocation: the value is already there. Pointer
*homes* (registers holding addresses instead of frame slots) need the
registers the scalar homes use; 3d measured that adding them loses
(register pressure), and the hot functions use every allocatable
register somewhere. Moving lower stores from definitions to safepoints
changes when the root set holds an object, which is the invariant
Oracle declined to add for phi shadows (option B, item 9). So the first
step keeps every store and every root and forwards loads across `jcc`s
and labels.

Oracle's review (below) found that the checker also resets B's state at
every `jcc` fallthrough, so label facts alone reach much less than the
table. Rerun with each mechanism alone, the same loads as a share of all
instructions:

| Workload | label facts only | `jcc` continuation only | both |
| --- | --: | --: | --: |
| zlib -6 | 0.8% | 1.7% | 9.3% |
| zlib -d | 1.1% | 1.1% | 12.3% |
| bzip2 -9 | 0.6% | 2.0% | 5.7% |
| bzip2 -d | 1.1% | 2.1% | 6.8% |
| lz4 -1 | 0.0% | 0.0% | 0.9% |
| lz4 -9 | 1.6% | 0.4% | 3.6% |
| lz4 -d | 0.4% | 0.0% | 1.9% |
| lua int | 0.5% | 1.5% | 10.8% |
| lua tab | 0.7% | 1.7% | 11.5% |
| lua str | 0.9% | 0.5% | 4.2% |
| sqlite | 0.6% | 0.9% | 6.2% |

They are not additive: a block loads its pointer and lower before its
checks, each check ends in `jcc`s to its fail block, and the next
block's reload follows the last of them. A label fact can only be
established after that `jcc`, and the continuation alone stops at the
label. So 5b-1 is both, and the table's "both" column is its upper
bound.

**Mode.** Opt-in `--registers=flow`: temps mode with both rules below.
It becomes the `-O` default only after a gate run where it wins time and
compile time stays within budget. `stack`, `local`, `function`,
`operands`, `cells` and `temps` keep their streams, checker paths and
snapshot outputs; the snapshot gets one new mode for `flow`.

**Rule 1: `jcc` continuation (changes 3b's region rule, in `flow` only).**
A `jcc`'s fallthrough has one predecessor and the `jcc` writes nothing.
After `region_end/3` at a `jcc` (both streams agree on what is live, as
today), the walk continues with A's and B's states and the cell map
unchanged instead of `region_start/4`. Labels, `jmp`, calls, `ret` and
every other boundary reset as today. In the rewrite, regions span
`jcc`s: forwarding and `cell_forward/4`'s held map continue past them,
and dead-move deletion and retargeting treat each `jcc` as a merge
point whose live-out includes its `In` (the taken edge's needs).

**Rule 2: label facts (the certificate).** For each local label L of
the body, identified by its position in A (GNU numeric labels such as
`1` repeat; `target/3` resolves `1f`/`1b` by index, and so does every
fact lookup), the rewrite proposes Facts(L): pairs (R, D), register
family R holds the whole 64-bit value of cell D on entry to L. The
checker requires, before using them:

- *Well-formed:* at most one fact per family; each D a key of
  `valid_cells/3`'s map (a cell, and not addressed by any `lea`); each R
  a scratch family (`rax`, `rcx`, `rdx`, `rsi`, `rdi`, `r8`, `r9`), never
  `rbx`, `rsp`, `rbp` or `r10`–`r15`, which `region_end/3` compares at
  every boundary; R not live in A at L (`In` bit clear).
- *Complete edges:* no line of the body names L other than as a direct
  jump target (no `rip(L)` operand). Indirect jumps, `jmp` to a PLT
  symbol and calls into the body already make `successors/3` fail, so
  such a function is never allocated. Data outside the body does not
  name a body label (`.L<fn>.` naming); the contract relies on that.
- *Edge check:* at every jump to L (resolved by `target/3` on A's
  indices) and at the fallthrough into L, in B's state *before* the
  boundary and with the region's current cell map (not the reset one),
  each (R, D) in Facts(L) has `reg_get(R, SB) == cell_value(D, CS)`.
  Lines in state `none` are unreachable and make no edge.
- *Assumption:* at L, after `region_start/4`, B's R is set to
  `cell_value(D, empty)`, the cell's shared start value, which is the
  same symbol as A's and B's memory there.

Rule 1 lets a fact be established after a block's last check and lets a
label after a `jcc` fallthrough carry facts (the fallthrough is then an
ordinary edge with the continued state).

**Rewrite (untrusted).** The held map flows over the body's CFG: at each
label, the intersection of the maps on its incoming edges (a fixpoint
over back edges), killed by calls and every boundary the checker resets,
by writes to the register and by any write to the cell, minus families
live in A at L. A region's end liveness adds the facts of the label it
falls or jumps into (for a `jcc`, the taken target's), so the moves
that establish them stay. Before emitting, a must-analysis over the
final B reconfirms each label's facts and drops the ones it cannot, so
a rewrite bug costs a reload, not a build failure (`regs_asm` throws on
a failed check).

**Soundness.** Stores stay paired, so frame memory, `lowers[]`
included, is identical in A and B at every instruction. Rule 1 is exact
symbolic execution along the only edge into the fallthrough. For Rule
2, on every executed edge into L the checker proved R equal to the
cell's current content; nothing between an edge and its label writes
memory or R, so at L, R equals the cell, which is what the assumption
says. Induction over the executed trace, from function entry (shared
state, no facts). A call or poll resets B's registers, so no fact
survives one unless a load after it re-establishes it.

**GC.** No root changes, and nothing depends on when FUGC scans:
`lowers[]` holds the reference's values at every instruction. A register
holding a lower is a copy proven equal to its slot wherever B reads it.
The runtime writes `lowers[]` only in setjmp/longjmp, and setjmp
functions are not allocated; it writes `top_frame->origin` only inside
calls, and the origin is no cell. Signals are deferred to pollchecks,
which are calls. Oracle found no root or GC decision here.

**Expected yield.** An upper bound of 4–12% of instructions on nine
workloads (the "both" column; lz4 `-1`/`-d` 1–2%), most of it loads into
the register that already holds the value, which are deleted. Less where
a fact register is live in A at the label or a path writes it. Time less
than instructions: these loads hit L1. Letting facts cross calls would
add 5–40 points of these loads in Lua and SQLite; that is a later step
(5b-2, callee-saved registers and 3a's save rules), as is allowing
r10/r11 when they are not homes, which changes `region_end/3`'s
invariant and needs its own review.

**Cost.** Medium: Rule 1 is about three lines in the trusted walk plus
regions spanning `jcc`s in the rewrite; Rule 2 is the facts, their
well-formedness and edge checks, and the rewrite's fixpoint.
`sqlite3VdbeExec` (73k lines) bounds the compile cost; measured on
`sqlite3.c` against temps before it can be the default.

**Validation.**

- Checker fixtures (fail-first), refused unless marked:
  - a fact established on both predecessors (accepted); a loop-carried
    fact over a back edge without a poll (accepted) and with one;
  - one predecessor not holding the value; a store from another register
    to D on one path, with R holding the start symbol (B1's stale edge);
    a `movl` store to D on one path; a non-`mov` write to D (`add` to
    memory, `lock cmpxchg`); a call on one path;
  - a fact register live in A at L; a fact in `rbx` or `r10`–`r15`; two
    facts on one family; a fact on a non-cell or a `lea`'d word; L named
    by a `rip(L)` operand;
  - two labels `1` with different facts and a `jmp 1b`/`1f` checked
    against the wrong one;
  - a label after a `jcc` fallthrough with facts (accepted under Rule
    1); consecutive labels `L1: L2:` with facts on both;
  - a 32-bit load establishing a 64-bit fact with an unknown high half,
    and accepted where the cell's high half is a known 0;
  - Rule 1: a register written in the fallthrough and compared at the
    next boundary; flags across a `jcc` continuation.
- Plants in the checker, each caught by a fixture: skip the edge check;
  check edges against the reset cell map; key facts by name; skip the
  `rip(L)` rule; let facts survive a call; ignore A's liveness of R;
  reset at `jcc` in the checker but not the rewrite (a compile error).
  In the rewrite: no successor facts in end liveness (a compile error in
  difftest without the reconfirmation pass).
- Difftests of the fixtures, the filc IRs and `c/*.c` in `flow`,
  including a use-after-free across a label that must trap the same way;
  progtest and `run-c` under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`; the
  snapshot with only the new mode's outputs changed; the 13 nanofil
  checks plus nanofil-python; the gate with alternating trials; the
  profile rerun to confirm the loads moved.

**Review (Oracle, October 2026): sound with fixes, all folded in above.**
B1: the edge check must use the region's current cell map; checking
after the reset accepts a stale fact. B2: facts keyed by position, since
numeric labels repeat (the x87 sequences). B3: certificate
well-formedness (one fact per family, D a valid cell). B4: the checker
resets at every `jcc` fallthrough, so the rewrite must too, or Rule 1
must be adopted; Rule 1 was recommended and the label-only bound
measured above confirms it is needed. Its two items for the
orchestrating thread: Rule 1 changes 3b's region rule in the trusted
checker; freeing r10/r11 changes `region_end/3`'s invariant and is not
part of 5b-1.

#### 5b-1. Implementation (opt-in)

Approved by the orchestrating thread with both decisions: Rule 1 in
`flow` only (every other mode's checker keeps the same rule: the
snapshot's other six modes are identical), and `flow` the `-O` default
only after a gate win with separated ranges and at most +15% compile
time on `sqlite3.c`.

- *Checker* (`amd64_regs_check.pl`): `check_operands/5` takes `cells`
  (every existing caller, through `check_operands/4`) or `flow(Facts)`.
  `continued_jump/3` is Rule 1; `edge_facts/4` runs at every boundary
  before the reset, with the region's current cell map (B1);
  `label_facts/5` sets the fact registers after `region_start/4` and
  requires them dead in A. `fact_labels/2` admits a label only when it
  is defined once, is not numeric, and no line names it other than as a
  direct jump target (B2 and the `rip(L)` rule: facts on any other label
  are refused, so position keying is not needed). `well_formed_facts/4`
  checks one cell per scratch family and a valid, non-`lea`'d cell
  (B3).
- *Rewrite* (`amd64_regs.pl`, untrusted): regions span continued `jcc`s
  (their `In` joins the region's uses); `flow_facts/4` iterates the held
  map of `cell_forward/6` over the regions to a fixpoint (optimistic,
  at most 64 rounds, then no facts), meeting the incoming maps at each
  admitted label and dropping families live in A there; the end
  liveness of a region and the uses of its continued `jcc`s gain their
  targets' fact registers so the establishing moves stay (B4). The
  reconfirmation pass was not built: a wrong fact is a compile error
  (`regs_asm` throws), which the rewrite plant below shows.
- Two rewrite bugs found while validating, both refusals, not
  miscompiles: two cells proposed for one family (the checker's B3 test
  refused it; now one per family), and a label that may not carry facts
  starting its region from "top", which hid its edges from the meet
  (found on `sqlite3.c`; regression case `no_fact_label_region`, fails
  with the old rule). A third was cost only: the fixpoint compared held
  maps as assoc trees, which may differ for equal contents.

**Validation.** 31 checker cases in `tests/regs_check.pl`
(`flow_spec/4`), each also run with no facts and in `cells` mode to show
that the positives depend on their facts or on Rule 1: past a `jcc`
(accepted; refused in `cells`), into the taken target, into a label
that falls through from a `jcc`, past a `jmp`; facts on a jump, a
fallthrough, two edges, after a `jcc`, a loop back edge (accepted), a
loop with a poll, R clobbered on the fallthrough or the jump edge, a
call or poll between load and label, byte and dword writes to R, `movl`
and `add` to the cell, B1's stale symbol, consecutive labels, a 32-bit
load with a known-zero high half (accepted) and an unknown one, R live
in A, `rbx` and `r10`, two cells on one family, a non-cell, a `lea`'d
cell, a numeric label, a `rip`-named label, a label defined twice. Plants
(each restored; the unit suite fails on all but one):

| Plant | Cases that flip |
| --- | --- |
| Rule 1 widened to labels | `past_jcc_into_label`, `fact_live_register` |
| Rule 1 state carried into the taken target | `past_jcc_into_taken`, `fact_across_poll` |
| jump edges not checked (one incoming edge dropped) | `fact_clobbered_jump`, `fact_stale_symbol` |
| fallthrough edges not checked | 8 cases (clobber, call, poll, partial writes, cell writes) |
| facts kept across a call | `fact_across_call` |
| a 32-bit store preserves the 64-bit cell | `fact_movl_cell_store` |
| edge check against the reset cell map (B1) | 6 positive cases |
| facts keyed by name | `fact_numeric_label`, `fact_named_label`, `fact_twice_defined` |
| R's liveness in A at L ignored | none: redundant, `region_end/3` already compares a live R |
| rewrite: no successor facts in end liveness | 2 of 30 `c/*.c` difftests fail the check (compile errors) |

Difftests of the fixtures, filc IRs and `c/*.c`, `run-c` and progtest
under `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`, and the ensure-aux trace all pass
in `flow`. In `flow` and `temps` alike, the nine IRs that `nix/check.nix`
does not list for difftest (they need `run-c.sh`) fail to link. The
snapshot changes only the 593 new `W.` outputs; the other 4,744 are
identical. All 562 C inputs exit the same in `flow` as in `temps`. The
Nix check gained an `-O flow` block (difftest, ABI+GC, ensure-aux,
programs).

**Compile time** (`sqlite3.c`, one core each): `temps` 144.7 s, `flow`
165.3 s (+14.3%, within the +15% budget; 183 s before the fixpoint
fixes). Static frame loads into registers: 280,039 → 266,701 (−4.8%).

**Gate** (`run.py --modes ref,O,O-flow --trials 7`, cpu 6, load 2; ratio
to filcc -O2, time (instructions), min..max range):

| Workload | `-O` (temps) | `-O --registers=flow` | ranges |
| --- | --: | --: | --- |
| zlib -6 | 2.47 (4.08) | 2.49 (4.06) | overlap |
| zlib -d | 1.91 (3.20) | 1.90 (3.19) | overlap |
| bzip2 -9 | 1.99 (2.52) | 1.95 (2.48) | separated, flow faster |
| bzip2 -d | 2.38 (3.11) | 2.35 (3.09) | separated, flow faster |
| lz4 -1 | 2.10 (10.63) | 2.12 (10.54) | overlap |
| lz4 -9 | 2.66 (3.41) | 2.54 (3.40) | overlap |
| lz4 -d | 2.72 (7.19) | 2.77 (7.25) | overlap |
| lua int | 2.13 (2.35) | 2.07 (2.32) | separated, flow faster |
| lua tab | 1.98 (2.26) | 1.97 (2.24) | overlap |
| lua str | 1.51 (1.61) | 1.49 (1.61) | overlap |
| sqlite | 1.98 (1.99) | 1.94 (1.98) | separated, flow faster |
| geomean | 2.14 (3.27) | 2.12 (3.25) | |

Instructions fall 0.5–1.5%, far below the 4–12% bound. Flow wins time
with separated ranges on four workloads and loses on none with separated
ranges. Compile time is within budget, but the yield is too small to call
this a win, so `flow` stays opt-in. The annotated hot block of bzip2's
`copy_input_until_stop` shows why. The lower stays in `rcx` across the
checks, so Rule 1 works, but the address is reloaded from `-0x48(%rbp)`
into `rax` after every access, because `add $0x6c,%rax` turned `rax` into
the field address. No forwarding reaches that: the value is in no
register. Reaching it means giving the base its own register, which is
5b-2's register pressure question, not another rule (re-measured
below).

#### 5b, re-measured literally (after 5b-1)

The bound under 5b-1's contract (4–12% of instructions) came from a
scratch analysis that kept a register as holding a frame word until
the next move into it. An arithmetic write such as `add $0x6c,%rax`
after `mov -0x48(%rbp),%rax` did not count as a write, and the annotated
bzip2 block above is that case. Rerun with the value still in the
register taken literally, at `2ce8b0f`, on the final binaries' disassembly with callgrind's
per-instruction counts:

- any write to a register family at any width kills what it holds;
- a store that overlaps a frame word kills that word;
- a `lea` of a word excludes it;
- calls kill every register;
- the meet is the intersection over all predecessors.

The loads counted are 64-bit loads of frame words into general
registers in nanofil's functions. Each is attributed to the first
class that applies. Shares are of all instructions:

| Workload | still in that register, `-O` | frame-word loads, flow | still in that register, flow | in another register, flow | loaded before, in no register, flow | same, if calls kept callee-saved registers |
| --- | --: | --: | --: | --: | --: | --: |
| zlib -6 | 1.4% | 1.03G (13.0%) | 1.2% | 0.4% | 8.2% | 11.3% |
| zlib -d | 1.0% | 0.11G (17.3%) | 1.0% | 0.2% | 11.3% | 16.0% |
| bzip2 -9 | 1.3% | 1.18G (10.2%) | 1.0% | 0.2% | 4.3% | 7.4% |
| bzip2 -d | 1.7% | 0.64G (14.5%) | 1.5% | 0.2% | 9.1% | 12.5% |
| lz4 -1 | 0.7% | 0.02G (5.9%) | 0.1% | 0.0% | 0.8% | 5.7% |
| lz4 -9 | 1.7% | 0.95G (11.0%) | 1.1% | 0.7% | 3.9% | 8.1% |
| lz4 -d | 0.8% | 0.05G (9.4%) | 0.4% | 0.2% | 2.5% | 8.0% |
| lua int | 1.3% | 0.44G (15.5%) | 0.5% | 0.1% | 9.5% | 13.8% |
| lua tab | 1.3% | 0.33G (14.8%) | 0.6% | 0.2% | 9.7% | 13.2% |
| lua str | 0.9% | 0.45G (9.5%) | 0.6% | 0.7% | 3.5% | 7.7% |
| sqlite | 0.9% | 2.55G (12.0%) | 0.5% | 0.4% | 5.6% | 10.0% |

So forwarding had at most 0.7–1.7% to win, and flow takes 0.1–0.8
points of it. The 0.1–1.5% flow leaves are labels its facts do not
reach, which were not investigated further.

The large class is the last two columns: words loaded before and
unchanged in memory, but in no register. Here 2.5–11%, and up to 16%
counting calls. Forwarding cannot reach them. They need a register that
holds the value across the code that overwrites the one it was loaded
into, which is pointer homes. That is register allocation (5b-2, with
its GC root rules), and 3d measured that adding pointer homes to the
scalar ones loses to register pressure in the hot functions. These
loads also hit L1, so time gains are well below the instruction share.

**Decision:** no more 5b forwarding work; 5b-1 is the end of that line.
5b-2 stays deferred. If it is taken up, the last two columns bound it,
and it needs its own contract and review.

#### Punned union reads in promote (after 5b-1)

lz4's `LZ4_isLittleEndian` writes a union as a word and reads a byte, so
its alloc stayed memory in every inlined caller. Promote now treats an
unstored `b`/`h` load inside an `h`/`w` slot as the slot's value shifted
right by 8 × offset, then extended (promote.pl's header; fail-first test
`promote_punned_reads`). Gate after it (7 trials, cpu 6, idle), `-O`
time (instructions) ratio to filcc -O2: lz4 -9 2.66 (3.41) → 2.35 (3.07),
lz4 -d 2.72 (7.19) → 2.72 (6.82), lz4 -1 2.10 (10.63) → 2.22 (10.53)
(ranges overlap); the others are unchanged within noise. Geomean
2.14 (3.27) → 2.13 (3.22); `flow` 2.11 (3.20).

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

#### 6, measured (October 2026): the count of checks, not their length

Cachegrind on the `-O` build after 7a, with check sequences recognized
in the `.s` and filcc's counted at the address level (jumps to blocks
that call `filc_optimized_access_check_fail`):

| Workload | Check sequences, share of instructions | Borrow `jb`, share |
| --- | --: | --: |
| zlib -6 | 28.8% | 3.0% |
| zlib -d | 24.8% | 2.6% |
| bzip2 -9 | 37.1% | 3.8% |
| bzip2 -d | 24.5% | 2.5% |
| lz4 -9 | 10.5% | 1.1% |
| lz4 -d | 9.5% | 0.9% |
| lua int | 18.8% | 1.9% |
| lua tab | 19.9% | 2.0% |
| lua str | 16.0% | 1.5% |

- **The pin's own sequence is eight instructions:** `test lower; je;
  cmp lower,ptr; jb; mov -16(lower),u; add $-Size,u; cmp u,ptr; ja`
  (filcc -O2, staging pin). It does not hoist the null test or the upper
  load out of a loop with a poll. nanofil's is the same plus the borrow
  `jb` after `sub $Size`. The profile's earlier "four or five" was the
  hoisted form, which this pin does not produce; the yield estimated
  above from it was too high.
- **The gap is the number of checks.** bzip2 -9 runs 539M checks under
  nanofil `-O` against 230M under filcc. filcc inlines (`mainQSort3` and
  `mainSort` into `BZ2_blockSort`, `copy_input_until_stop` into
  `handle_compress`) and keeps struct fields in registers. nanofil
  checks every reload of `s->field`: `copy_input_until_stop` alone runs
  129M checks, against 41M in filcc's whole `handle_compress`.
- **Same-object checks.** A check whose lower repeats an earlier check's
  lower in the same label- and call-free stretch is 24% of checks in
  zlib -6, 26% in bzip2 -9, 9–14% in bzip2 -d and Lua, and 1% in lz4 -9.
  Skipping only their null tests saves 0–2% of instructions.

#### 6a. Contract: no borrow test after `upper − Size`

**Change.** `access_check//2` emits
`test %rcx,%rcx; jz F; cmp %rcx,%rax; jb F; mov -16(%rcx),%rdx;
sub $Size,%rdx; cmp %rdx,%rax; ja F`, followed by the write and
alignment tests unchanged. Only the `jb F` after `sub` goes, and only
when Size ≤ 16; a larger check keeps it, on every path. The
failure block, its arguments (`%rax`, `%rcx`), the origin, the order of
the remaining tests and the trap text are unchanged. This is the pinned
pass's own sequence. It is emitted where instruction selection is on
(the `local` selection, which every `-O` register mode except `stack`
uses). No `-O`, and `-O --registers=stack`, keep the borrow test byte
for byte, as the reference.

**Why the test is dead.** It fires only when `upper < Size`. The check
proves `lower ≤ ptr ≤ upper − Size`, which equals the runtime's
`ptr ≥ lower ∧ ptr < upper ∧ Size ≤ upper − ptr` when `upper ≥ Size`
(the bounds argument in 7a). Three facts give `upper ≥ Size`:
1. **Sizes.** Pizlonate's checks have Size ∈ {1, 2, 4, 8, 10}
   (`access_size_align/3`; 10 is `x`, a long double, whose 16-byte cell
   exists only for `va_arg`, which does not go through `access_check`).
   `check_reuse` only deletes checks whose proof subsumes them, and
   fused checks have offset 0, so neither widens a check. Checked-IR
   input may state any `0 < Size ≤ 2³¹−1` (`tests/filc/check-range.ir`,
   unit test `native_check_range`, the regression tests of 37ba5f5,
   which added the borrow test); those sizes keep the `jb`, so the
   argument needs only Size ≤ 16. `local_check` and the 7a filter have
   their own sequences, and the filter keeps its borrow test.
2. **Lowers.** A nonnull lower is the lower of a real object: lowers
   are created only by the runtime (allocation, globals, function and
   special objects, mmap objects) and are never forged, since integer
   to pointer gives a null lower (GIMSO). The object's header, `upper`
   at `-16(lower)` and `aux` at `-8(lower)`, sits in the 16 bytes below
   it, so `lower ≥ 16`. The check itself reads that header. This
   assumes, as the check already does, that the lower in `%rcx` is
   rooted: an unrooted lower could point into reused memory, which would
   be unsound with or without the `jb`.
3. **Upper.** `upper ≥ lower` for every object at every time. A free sets
   `upper = lower`, including a concurrent free on another thread; the
   racy read sees either value, and both satisfy it.

So for Size ≤ 16, `upper ≥ lower ≥ 16 ≥ Size`, and `upper − Size` cannot
borrow. The pin omits the borrow test more widely, for merged constant
ranges too (`s->a[0] + s->a[599]` becomes one check with `$-4800`,
FilPizlonator.cpp:4111-4116), on an unstated assumption; 6a relies only
on its own ≤ 16 bound, not on the pin. A null
lower is caught first by the unchanged `test`/`jz`.

**What does not change.** The check still runs before every access, as
in the reference. No check, poll or root is removed or moved. The
checked IR and its validator are untouched: this is instruction
selection inside one check.

**Validation.**
- **Fail-first unit test.** Under `-O`, a checked load of Size 1, 8 or
  10 has no `jb` after `sub`, and still has `test`/`jz` and `ja`;
  `check(0, 17, …)` and `check(0, 2147483647, …)` keep the `jb`. The
  reference sequence keeps it for every size.
- **Matrix, at sizes 1, 2, 4, 8 and 10.** Must pass: ptr = lower and
  ptr = upper − Size. Must trap with text byte-identical to the
  reference build: one past the end, Size − 1 bytes before the end,
  below lower, a freed object (upper = lower) and null.
  `check-range.ir` and `native_check_range` keep passing on every path.
- **Plants.** Emit `sub $(Size+16)` (caught by the must-pass cases);
  drop the `ja` instead of the `jb`; drop the `jb` for every size
  (caught by `check-range.ir`'s `wide(16)`).
- **Gates.** Snapshot changes only `-O` outputs. All Nix checks. The
  bench gate, where the expected yield is the borrow column above.

Expected yield: the borrow column, 1–4% of instructions.

**Review.** Oracle confirmed the runtime half at the pin: every nonnull
lower has a real 16-byte header below it (special, function, ordinary,
aligned and mmap objects, closures, the free singleton, nanofil's data
and function objects), and every write of upper keeps upper ≥ lower,
free and munmap included. It found two blockers, both fixed above:
checked-IR input reaches `access_check` with sizes up to 2³¹−1, which
the borrow test exists for (37ba5f5), and a long double access is 10
bytes, not 16. The size guard, the must-pass boundary cases, the
plant that drops the `jb` everywhere and the rooting assumption come
from its review.

**Result.** Implemented as `borrow_check//3` in `filc_amd64.pl`,
tested by unit `borrow_test_sizes` and `tests/checks.sh` (70 cases,
in `check.nix` by default and per registers mode); the three plants
were caught as stated (18 and 25 matrix cases, and `check-range.ir`).
Snapshot: 513 of 3312 outputs differ, all in the allocating `-O`
modes. Gate on swa, ratio to filcc, time (instructions), before → after:

| Workload | before | after |
| --- | ---: | ---: |
| zlib `-6` | 2.60 (4.36) | 2.57 (4.21) |
| zlib `-d` | 2.04 (3.48) | 2.05 (3.38) |
| bzip2 `-9` | 2.12 (2.78) | 2.04 (2.66) |
| bzip2 `-d` | 3.55 (3.49) | 3.66 (3.40) |
| lz4 `-1` | 2.42 (13.01) | 2.43 (12.90) |
| lz4 `-9` | 3.96 (4.77) | 3.91 (4.71) |
| lz4 `-d` | 3.19 (8.41) | 3.18 (8.39) |
| Lua int | 2.28 (2.54) | 2.26 (2.49) |
| Lua tab | 2.15 (2.46) | 2.11 (2.40) |
| Lua str | 1.58 (1.74) | 1.57 (1.71) |
| SQLite | 2.12 (2.13) | 2.09 (2.07) |
| geomean | 2.46 (3.70) | 2.44 (3.62) |

Instructions fall 0.2–4.3%, as estimated. bzip2 `-d`'s time rose
while its instructions fell, which is layout (the M7 noise floor).

#### 6b (not proposed)

**6b, null tests of a lower already tested in the stretch:** at most 2%.
With the `lower ≤ ptr` test and alignment, it is the sound spatial-only
subset of reuse (a capability's lower never changes). It needs
lower-equality facts across derived pointers in the emitter. Not worth
a contract now.

#### 6c, fewer checks: measured before the contract

The 24–26% "same lower" share above was measured over straight-line
stretches between labels and calls, keyed by where `%rcx` was loaded
from. With `-O` each field access has its own flight from the struct
pointer, so most of those checks are of one object but of *different*
fields. M7's reuse rule can only delete a check whose range an earlier
proof subsumes, and a new field always extends the range. Two
prototypes, measured with the gate (`O-reuse` builds, outputs byte for
byte as filcc's; instructions against today's `-O`):

| Workload | `-O` | 6c-1: offsets | 6c-1 + 6c-2: widening |
| --- | ---: | ---: | ---: |
| zlib `-6` | 8269M | −3.4% | −6.1% |
| zlib `-d` | 654M | 0.0% | −7.2% |
| bzip2 `-9` | 12421M | −1.0% | −5.1% |
| bzip2 `-d` | 4852M | −1.4% | −4.5% |
| lz4 `-1` | 396M | 0.0% | −0.2% |
| lz4 `-9` | 13376M | 0.0% | −0.1% |
| lz4 `-d` | 608M | −1.2% | −0.1% |
| Lua int | 2941M | 0.0% | −3.9% |
| Lua tab | 2313M | 0.0% | −3.6% |
| Lua str | 6014M | +0.2% | −0.3% |
| SQLite | 23052M | −1.3% | −3.2% |
| time geomean (ratio to filcc) | 2.44 | 2.46 | 2.43 |

- **6c-1, related pointers** ([m7.md, round 3](m7.md#related-pointers-round-3)):
  M7's rule, matching a check's pointer to an earlier proof's pointer
  when both are single-definition flights from one root with constant
  offsets, rather than only the same SSA pointer. The validator's
  safety rule does not change. Yield 0–3.4%; it needs `--checks=reuse`
  to become the `-O` default to do anything by default.
- **6c-1 result.** Implemented (m7.md round 3); `--checks=reuse` stays
  opt-in. Gate after it, 7 trials, ratio to filcc, time (instructions),
  `-O` against `-O --checks=reuse`: zlib `-6` 2.58 (4.21) / 2.58 (4.07),
  bzip2 `-9` 2.07 (2.66, 2.06..2.07) / 2.05 (2.63, 2.05..2.06), bzip2 `-d`
  3.77 (3.40) / 3.90 (3.35, separated, worse), lz4 `-9` 4.10 / 3.93 with
  identical instructions (layout; ranges overlap), SQLite 2.07 (2.07) /
  2.06 (2.05), the rest within 0.02; geomean 2.45 / 2.46. Reuse cuts
  instructions by up to 3.4% but wins time with separated ranges on no
  workload, which was the bar for making it the `-O` default.
- **6c-2, widening within a stretch: rejected** (prototype only). The
  first check of an object in an invalidator-free stretch is widened
  to cover the later fields, which 6c-1 then deletes. This is what the
  pin does (`$-4800`). It adds about 2–4% (table above). A trap then
  comes earlier in the block, before scalar stores that precede the
  failing access, and reports the first access rather than the failing
  one. That is the observation-contract change campaign.md says not to
  make, and 2–4% does not justify it; do not rediscover it.
- **The rest of the gap** is elsewhere. bzip2 `-9` runs 539M checks
  under `-O` against filcc's 230M, and 6c-1 plus 6c-2 remove about 75M
  of them. Per function (callgrind on filcc, cachegrind on nanofil),
  filcc's `handle_compress` runs 41M checks where nanofil's
  `copy_input_until_stop`, `add_pair_to_block` and
  `copy_output_until_stop` run 158M. filcc's `BZ2_blockSort` runs 92M
  and its `mainGtU` 30M, against nanofil's 245M in `mainQSort3`,
  `mainSort`, `mainSimpleSort` and `mainGtU`. Its `BZ2_compressBlock`
  runs 65M against nanofil's 129M in `sendMTFValues`,
  `generateMTFValues` and `bsW`. Each filcc function inlines the
  nanofil ones it is compared with. So the hypothesis, not yet
  measured, is that the rest comes from what a call boundary kills
  (inlining, item 4), from pointer fields reloaded per access
  (`s->strm->avail_in`, which needs load reuse), from merging across
  blocks, and from variable-index pairs like `block[i]`, `block[i+1]`.

#### 6d. Load reuse across pointer loads: measured, not proposed

The hypothesis under item 4 was that bzip2 `-9`'s check gap is
reloaded fields such as `s->strm->avail_in`, which removing the
repeated load (and with it its check) would reach. Measured on 539M
checks, it reaches almost none of them.

*Method* (scratch, not kept): bzip2 built with `-O`, its output and
12.42G instructions equal to the gate's, a symbol at every block label,
and callgrind's entry count for each block. For each block of the
checked IR, an analysis counts the checks that guard a load whose value
an earlier load or store of the same address still provides. Address
means the root pointer's value number plus a constant offset, with the
same type. A repeated load takes the earlier value's number, so
`s->strm->avail_in` chains. Facts cross plain forward edges, as M7's
check reuse does, and no poll edge. Calls, allocations, getters,
atomics and every other non-pure instruction kill all facts. The kill
rule for stores varies:

| stores kill | checks reached |
| --- | ---: |
| every fact (K1) | 0.0M (0%) |
| facts unless same root and disjoint bytes (K2) | 0.0M (0%) |
| as K2, pointer and scalar stores separately (K3, TBAA-like) | 11.0M (2.0%) |

All of K3's gain is in `copy_input_until_stop` (8.4M of 129M) and
`copy_output_until_stop` (2.6M). The block counts sum to the gate
binary's 539M checks.

*Why.* In the hot loops each field's first load is in the loop header.
Within an iteration, a store through another root (`s->block[i] = ch`)
kills `s->strm` under any rule that does not assume types. Across
iterations, the only way to remove the load is to hoist it and its
check to the preheader. filcc gets its `copy_input_until_stop` count
(35M without inlining) by check scheduling: one merged range check of
`s` at entry covers `s->nblock`, `s->nblockMAX` and the rest, which the
loop then reads unchecked. It still reloads and checks `s->strm` every
iteration. That is 6c-2's class, hoisting and merging that move a trap
earlier, which is rejected. K3's 2% needs a type-based alias rule,
and Fil-C has none: the pass drops `!tbaa`, and memory is bytes
(docs/ub.md, 6.5p7). So load reuse gets no contract. What remains of
the check gap is check scheduling, not reloads.

### 7. Small constant `memcpy` — needs review

An inline copy must preserve what `filc_memmove` does: null, bounds and
write checks on both pointers; copying aux for in-phase words, and
clearing the destination's aux where out of phase or partly overwritten;
aux allocation (an exit, so a safepoint) and the barrier. The smallest
safe version copies inline only when neither object has an aux pointer,
the runtime's "nothing to do" case, and calls the runtime otherwise.
Expected: 45% of lz4 `-d` and `-1`.

#### 7a. Contract: a filter in front of the unchanged call

The inline code is a *filter* placed before the existing call, not a
replacement for it. It either takes the fast path, when the runtime
would succeed and would do nothing for aux, or jumps to the call exactly
as `-O` emits it today. Every failure, every aux case, the barrier, aux
allocation and the panic text and origins stay the runtime's, reached
the same way. The only new claim is that the fast path's effect equals
the call's in the cases the filter admits.

**What the runtime does (pin, `filc_runtime.c`).** glibc's `memcpy` and
`memmove` (`pizlonatedFI28870___GI_memcpy`/`__GI_memmove` in
`libc.so.6666`) push a frame and call `zmemmove`, which reaches
`filc_native_zmemmove` and then `memmove_impl` (5659). Then:

1. `count == 0` returns.
2. A null object for either pointer goes to `memmove_fail`.
3. `CHECK_BOUNDS_FAST` (2376) runs on both pointers:
   `ptr >= lower`, `ptr < upper`, `count <= upper - ptr`.
4. `CHECK_WRITE_FAST` (2392) runs on the destination only:
   `flags & (READONLY | FREE | SPECIAL_MASK)`, mask `0x786`. The
   source gets no flag test. A freed object has size 0 (`upper =
   lower`), so step 3 already rejects it.
5. Below `FILC_MAX_BYTES_BETWEEN_POLLCHECKS`, `memmove_size_specialized`
   (5534) copies the bytes with `filc_memmove_small` (overlap-safe), with
   no exit and no poll.
6. It then reads both aux pointers and calls `memmove_aux_with_ptrs`.
   That does nothing when neither object has aux, or when only the
   source has aux and the offsets are out of phase.
7. The call returns `dst`.

**Scope.** The filter applies to `call(R, global(F), [arg(p,D), arg(p,S),
arg(l,const(N))])` under these conditions:
- F is `memcpy` or `memmove`. That includes `__builtin_memcpy` and
  `__builtin_memmove`, which `library_builtin/2` maps to them, and
  `__builtin___memcpy_chk` with size `(size_t)-1` when `__memcpy_chk`
  is undeclared (c_types.pl:1887-1892, 2122-2136).
- 1 ≤ N ≤ 16.
- No function in the module is emitted with symbol F. F is the
  assembler symbol, so asm labels and aliases count; a `gnu_inline`
  extern body emits nothing and does not count.
- The function is compiled with `-O`, and `--memcpy=call` is not given.

`--memcpy=call` is the new selectable reference. `nanofil-cc` passes it
for `-fno-builtin`, `-fno-builtin-memcpy`, `-fno-builtin-memmove` and
`-ffreestanding`.

Treating F as the standard function is the C library-reservation
assumption that clang makes: filcc lowers these calls to `llvm.memcpy`
and never calls libc's `memcpy` for them. An interposed `memcpy`
(`LD_PRELOAD`, or a definition in another translation unit) is no
longer called for small constant copies, as with filcc. `N = 0` and
other sizes keep the call.

**Sequence.** D is `(dp, dl)` and S is `(sp, sl)`. Only rax, rcx, rdx,
rsi, rdi, r8 and r9 are used: they are not allocatable, and the call
clobbers them anyway. r10 and r11 are allocatable, so the checker's
preflight rejects any stream that names them.

```
    test dl,dl ; jz slow
    cmp  dl,dp ; jb slow                 dp >= dl
    mov  -16(dl),u ; sub $N,u ; jb slow  upper >= N
    cmp  u,dp ; ja slow                  dp <= upper - N
    movabs $0x0786ffffffffffff,u
    test u,-8(dl) ; jnz slow             flags & 0x786, and aux pointer
    (the same for S, with mask $0x0000ffffffffffff: aux only)
    loads from sp, then stores to dp, at the offsets below
    R := D (if the result is used)
    jmp  done
slow:
    the call exactly as emitted today: origin store, arguments,
    call, exception test, result moves
done:
```

- **Bounds.** For N ≥ 1, `dp >= dl ∧ upper >= N ∧ dp <= upper − N` holds
  exactly when step 3 holds: `dp <= upper − N` gives `dp < upper` and
  `N <= upper − dp`. Conversely, step 3 gives `dp + N <= upper`, so
  there is no borrow. The test order is today's `access_check`.
- **Flags and aux in one read.** The word at `-8(lower)` holds the aux
  pointer in its low 48 bits (`FILC_OBJECT_AUX_PTR_MASK`;
  `PAS_ADDRESS_BITS` is 48) and the flags above them. The masked `test`
  is zero exactly when the destination's flags have none of
  READONLY | FREE | SPECIAL_MASK and its aux pointer is null; the
  source's mask tests only the aux pointer. `movabs` and `test q` are
  already audited, with defined flags (amd64_regs_check.pl:691-693,
  977-980). A `shl $16; jnz` form was rejected in review: `shl` leaves
  the flags shared only when its input flags are, and after the
  previous `jcc` they are not, so the region checker would fail the
  compile (`shift_keeps_flags` in tests/regs_check.pl).
- **Accepted set.** The filter accepts a subset of the cases where steps
  2–4 pass and step 6 is "nothing to do". It is stricter in one place:
  it requires the source to have no aux, even out of phase.
- **Copy.** Every load comes before any store, so overlap gives
  `memmove` semantics, as `filc_memmove_small` does.
  - N ∈ {1, 2, 4, 8}: one access of N bytes at offset 0.
  - N = 3: 2 bytes at 0 and 2 bytes at 1.
  - N ∈ {5, 6, 7}: 4 bytes at 0 and 4 bytes at N − 4.
  - N ∈ {9, …, 16}: 8 bytes at 0 and 8 bytes at N − 8.
  - All accesses are plain unaligned integer moves inside `[ptr, ptr +
    N)`, which the bounds test has just admitted.

**Why the fast path equals the call.** In the single-threaded case, the
call's observable effects under the filter are these:
- N payload bytes of D are replaced by S's N bytes as they were before
  the copy.
- No aux word is read or written.
- No allocation, exit, poll or barrier happens.
- The result is D.

The fast path has the same effects. Two things are lost:
- **The safepoint at the call.** Removing a poll does not change
  semantics, filcc inlines the same way, and nanofil polls every
  backward edge (pizlonate.pl:24-26), so no loop loses its safepoint.
- **The call's frame push and origin store.** These matter only to a
  panic stack trace during the copy. The fast path cannot panic through
  a Fil-C check, and the origin is per function, not per call site
  (filc_amd64.pl:833-840).

A hardware fault on mapped memory, such as SIGBUS reading a
file-backed mapping past EOF, happens on both paths, with different
stack traces.

**Races.** The runtime reads bounds before the copy and aux after it;
the filter reads both before the copy. With concurrency, the fast path
is exactly a checked N-byte integer load from S followed by a checked
N-byte integer store to D. nanofil already emits that sequence for
`*(uN *)d = *(uN *)s` under the same check. So the fast path adds no
reachable state.
- **A concurrent pointer store to D** that installs D's aux after the
  filter reads it leaves that word with our bytes and the other
  thread's capability. That is the intval/capability tearing already
  allowed for an integer store racing a pointer store
  (`gimso_semantics.md` "Simplified Rules"). Accesses through the torn
  pointer are still checked against a real object's bounds.
- **A concurrent pointer store to S** after the filter's read: the
  copy carries bytes without lowers, as if the copy ran first.
- **A concurrent free** after the bounds test: the copy still
  completes, as the runtime's own note at `memmove_size_specialized`
  allows ("still safe to finish the memcpy"). Free does not unmap, and
  with no safepoint in the fast path the lower stays rooted. `munmap`
  of an mmap object remaps the range as anonymous read-write memory
  (filc_runtime.c:9930-9977), so neither path faults.
- **Aux before the copy has precedent.** filcc's own inline copy reads
  the aux base before it copies (`accessDataForOperand` before
  `RealMemmove`, FilPizlonator.cpp:7671-7672, 7882-7885).
- **No atomic boxes.** With aux null at the filter's read, no word of
  either object was in atomic mode then. A later atomic store races as
  it would with an integer access.

**Frame and checker.**
- D and S are heap or global lowers. Non-escaping locals cannot reach a
  call; they escape and become heap allocations, and no native stack
  address becomes a lower (campaign.md, M5). So the inline accesses
  cannot touch frame cells. That is 3a's existing trust, that only
  `%rbp`-relative operands reach the frame; nothing new.
- The sequence is part of the reference stream R, so the register
  allocator and the region checker treat it like any other code. Its
  internal labels and jumps are ordinary CFG edges. `slow` keeps the
  call, so the call is still a boundary on that path.
- Every opcode it uses (`test`, `cmp`, `sub`, `shl`, `mov`, `testw`
  with a memory operand, and `jcc`) needs an audited entry in the
  checker's effect table. Any that is missing is added with a fixture.

**Review.** Oracle checked every claim against the pin and found no hole
in the accepted set, the bounds equivalence or the race argument. One
blocker, the `shl` step above, is fixed. The text fixes are folded in:
the register list, scoping by symbol and the `_chk` route, panic
identity only against `--memcpy=call`, the hardware-fault caveat, and
the extra fixtures. glibc's `memcpy` and `memmove` were checked by
disassembling `libc.so.6666` at the pin: each pushes a frame, calls
`zmemmove`, and returns `dst` in `rdx`/`rcx`. `nanofil-cc` does not
parse `-fno-builtin` yet; mapping it to `--memcpy=call` is part of the
change.

**What is not claimed.** The filter does not inline any aux case, does
not change failure behaviour, and does not inline sizes above 16 or
non-constant sizes. A wider version that copies aux words inline, as
the pass's `emitOptMemmove` does with `FinishMemmoveSmall1–5`, needs
its own contract.

**Validation.**
- **Fail-first unit test.** `-O` on `memcpy(d, s, 8)` emits no call on
  the fast path and keeps the call on `slow`; `--memcpy=call` and
  non-`-O` keep today's output.
- **Runtime matrix (`tests/memcpy_small.c`, a difftest).** Run it
  against `--memcpy=call` and filcc. It covers:
  - N = 1…16, each with dst and src misaligned by 0–7 and overlapping
    in both directions;
  - null dst or src, one past the end, one byte too long, a pointer
    below lower, a read-only dst (string literal), a freed dst or src;
  - dst with aux (holds a pointer) in and out of phase, src with aux in
    and out of phase, and copying a pointer through `memcpy` then
    dereferencing it;
  - a defined `memcpy` in the module, which must be called;
  - `-fno-builtin`.

  Also covered:
  - `__builtin___memcpy_chk(d, s, 8, (size_t)-1)`, with and without
    `__memcpy_chk` declared;
  - a function as source, `(char *)main`, and `malloc(0)`;
  - a read-only string literal as source, which stays on the fast path;
  - a global holding pointers as destination;
  - a used result (`p = memcpy(...); p[n]`), including its bounds;
  - exact overlap `d == s`;
  - N = 0, N = 17 and a variable N, which keep the call;
  - an allocated function whose D and S live in callee-saved registers;
  - the pointer-through-`memcpy` case under `FUGC_SCRIBBLE` and
    `FUGC_VERIFY`.

  Output, panic text and exit status must be byte-identical to
  `--memcpy=call`. Against filcc, success output must match and a
  failing case must panic; the texts differ, because filcc's inline
  check fails through `filc_optimized_access_check_fail` and the
  runtime through `memmove_fail`.
- **Checker fixture.** The real filter sequence in an allocated function
  is accepted by `check_operands/4`. A planted `shl`/`jnz` variant, or
  one naming r10, is rejected.
- **Gates.** Snapshot changes are limited to `-O` default outputs that
  contain small constant copies. All Nix checks pass, and the bench
  gate covers lz4 `-1` and `-d`.

#### 7a: result

Implemented as contracted: `copy_filter`/`copy_join` actions around an
eligible call (`small_copy/5` in `filc_abi.pl`), expanded by
`copy_filter//7` in `filc_amd64.pl` when the copy choice is `inline`, the
`-O` default (`--memcpy=call|inline`, `NANOFIL_MEMCPY`). Without `-O`,
and in setjmp functions, the output is unchanged: the snapshot differs in
20 of 3306 outputs, all `-O` (5 programs in each of the four pinned `-O`
modes).

Tests:
- **Unit test `small_copy_filter`.** The filter appears in an allocated
  function, which the region checker accepts. Call mode, 17 bytes and a
  module defining `memcpy` keep only the call. It fails without the
  change.
- **`tests/memcpy.sh`.** 14 failing cases (dst or src with aux,
  read-only dst, freed dst or src, out of bounds on each side, null dst
  or src lower, a function as source, `malloc(0)`, the result's bounds),
  each at N = 1, 8, 9 and 16. Every case must give byte-identical stdout,
  stderr and status under `-O` and `-O --memcpy=call`, pids and
  addresses aside, and must trap exactly when filcc's build traps. It
  runs in the Nix check by default and under every `--registers` mode.
- **`tests/c/prog/memcpy-small.c`**, a progtest against filcc, also
  under GC stress. It covers every N from 1 to 16 at every pair of
  misalignments, copying and overlapping memmove in both directions
  (`d == s` included). It also covers pointers copied through `memcpy`,
  a global holding pointers as destination, holders made by a
  clang-built companion and copied whole and in part, a string-literal
  source, the result's bounds, and N = 0, 17, a variable N and
  `__builtin___memcpy_chk`.

Planted bugs:

| Plant | Caught by |
| --- | --- |
| Destination mask without the aux bits | `dst-aux` at all four sizes (the pointer survives where the runtime clears it) |
| Source mask 0 | `src-aux` and progtest (the copied pointer loses its capability) |
| Destination mask without READONLY and FREE | `readonly` at all four sizes |
| Each store right after its load | progtest, 790 overlapping moves wrong |
| `mov; shl $16; jnz` in place of the masked test | the region checker rejects it ("register operand translation check failed") |
| A copy register in r10 | the unit test |

A destination mask without the SPECIAL bits is not observable: special
objects have upper = lower, so the bounds test sends them to the call
first. The runtime has the same redundancy, and the bits stay as the
contract states.

filcc's own inline check, for a memcpy source below its lower,
panics through a failed assertion in `filc_optimized_access_check_fail`
("Should not be reached") rather than a safety error. That is a panic all
the same; `memcpy.sh` counts it as a trap.

Gate (7 trials, cpu 6), ratio to filcc -O2, time (instructions). `O-call`
is `-O --memcpy=call`, the previous default:

| Workload | `O-call` | `O` |
| --- | --- | --- |
| zlib -6 | 2.60 (4.36) | 2.60 (4.36) |
| zlib -d | 2.05 (3.48) 2.01..2.34 | 2.11 (3.48) 2.10..2.12 |
| bzip2 -9 | 2.14 (2.81) | 2.14 (2.81) |
| bzip2 -d | 3.56 (3.49) 3.55..4.02 | 3.73 (3.49) 3.72..3.76 |
| lz4 -1 | 3.37 (21.92) 3.15..3.42 | 2.44 (13.00) 2.18..2.53 |
| lz4 -9 | 4.03 (4.90) 4.00..5.19 | 3.93 (4.77) 3.89..3.94 |
| lz4 -d | 5.15 (16.82) 4.96..5.26 | 3.14 (8.50) 2.96..3.26 |
| lua int | 3.43 (2.94) | 3.43 (2.94) |
| lua tab | 3.23 (2.83) | 3.26 (2.83) |
| lua str | 1.60 (1.75) | 1.57 (1.75) |
| sqlite | 2.14 (2.17) | 2.13 (2.16) |
| geomean | 2.87 (4.26) | 2.67 (3.81) |

lz4 `-d` halves its instructions and lz4 `-1` loses 40%. zlib `-d` and
bzip2 `-d` run the same instruction counts and move by layout, as
before (item 3b's note on bzip2 -d).

### Where scalar frame traffic remains, and split float pools

Measured after 7a (cachegrind on the `-O` build with `as -g`, each `.s`
line's count joined with the class of the frame slot it touches, from
nanofil's own layout). Shares are of each workload's executed
instructions:

| Workload | Scalar homes left in the frame (with phi shadows) | Mostly in | Homes shared with `d` temps | Pointer address and lower slots |
| --- | --: | --- | --: | --: |
| bzip2 -d | 23.8% | `BZ2_decompress` 21.6% | – | 18.6% |
| lz4 -9 | 10.7% | `LZ4HC_InsertAndGetWiderMatch` 10.4% | – | 14.7% |
| zlib -6 | 6.1% | `longest_match` 5.5% | – | 22.3% |
| bzip2 -9 | 2.1% | `mainSort`, `mainQSort3` | 1.3% | 18.6% |
| lua int | 2.8% | `luaV_execute` | 16.0% | 19.7% |
| lua tab | 3.0% | `luaV_execute` | 15.6% | 20.1% |

Lua's 16% was in `luaV_execute`'s three hottest pooled scalar slots.
Each held hundreds of `w`/`l` temporaries and a few `d` ones (Lua
numbers), and one float alias makes a home ineligible (M6's rule, which
the checker keeps). So the allocating modes (`--registers=function`,
`operands`, `cells`) now lower with split pools:
`frame_slots:temp_slots/9` gives `s` and `d` temporaries a float pool,
and frame cells include it. The reference layout (no `-O`,
`--registers=stack` and `local`) keeps shared pools and is unchanged.
The snapshot differs in 75 of 3312 outputs, all in the three allocating
`-O` modes. Unit test `split_float_pools` fails when split pools behave
as shared.

Gate (7 trials, cpu 6), ratio to filcc -O2, time (instructions);
`O-memcpy` is `-O` after 7a:

| Workload | `O-memcpy` | `O` |
| --- | --- | --- |
| zlib -6 | 2.60 (4.36) | 2.60 (4.36) |
| zlib -d | 2.12 (3.48) | 2.07 (3.48) |
| bzip2 -9 | 2.14 (2.81) | 2.13 (2.78) |
| bzip2 -d | 3.74 (3.49) | 3.68 (3.49) |
| lz4 -1 | 2.40 (13.03) | 2.35 (13.03) |
| lz4 -9 | 3.94 (4.77) | 3.95 (4.77) |
| lz4 -d | 3.14 (8.41) | 3.15 (8.41) |
| lua int | 3.45 (2.94) 3.42..3.45 | 2.28 (2.54) 2.25..2.30 |
| lua tab | 3.29 (2.83) 3.21..3.30 | 2.15 (2.46) 2.10..2.16 |
| lua str | 1.59 (1.74) | 1.58 (1.73) |
| sqlite | 2.13 (2.16) | 2.15 (2.13) |
| geomean | 2.68 (3.81) | 2.46 (3.70) |

What is left for live-range splitting is the first two rows' pressure
and calls: `BZ2_decompress` keeps 22–26 homes live at once, and
`LZ4HC_InsertAndGetWiderMatch` keeps homes live across calls to small
functions, which item 4 removes. Pointer slots, at 15–22% everywhere, are
item 5b's.

### 3d. Live-range splitting: webs, not edge moves

#### Measured first (October 2026, after inlining became the default)

`bench/profile/split.py` estimates two ways of giving the homes 3a
leaves in the frame registers, on the marked build. One caveat applies
to every profile of the marked build: its marker labels come before the
stack check and split every region, so `allocated_stream/4` excludes
every function from 3a, and 3b and cells do nothing either. The marked
build is the stack reference with `-O`'s other passes. That is what an
allocator starts from, but cells already forward some of these loads in
`-O`, so the yields below overstate the gain. The estimate also models
homes approximately: it finds them by `%rbp` offset rather than from the
metadata, tracks whole words rather than halves, and leaves out
noreturn calls. It ranks the options; it does not predict the result. Both estimates and coverage.py's
colour by executed instructions (cachegrind), callee-saved registers for
values live across a returning call, and `r10`/`r11` for the others.
They admit only whole moves of a home, 3a's rule.

- **Whole homes** is what 3a does: one register for a home's whole life.
- **Loops** splits at natural loops of backward jumps, outermost first.
  Each loop colours the leftover homes it references with registers no
  home occupies inside it. A home pays one move per execution of each
  entry and exit edge it is live across, which is an upper bound, and is
  kept only if its traffic in the loop is larger.
- **Webs** splits each home into its webs: the connected parts of its
  live range, joined along the CFG edges it is live across. Webs are
  coloured instead of homes. A web needs no moves, because its home is
  dead wherever it meets another web.

| Function (workload) | Scalar home traffic | Whole homes | Loops | Webs | Homes → webs |
| --- | --: | --: | --: | --: | --: |
| `BZ2_decompress` (bzip2 -d) | 1.742G, 35% of the function | 47% | 48% (0 moves) | 59% | 559 → 5049 |
| `LZ4HC_InsertAndGetWiderMatch` (lz4 -9) | 3.774G, 49% | 70% | 68% (0.004G moves) | 84% | 152 → 663 |
| `longest_match` (zlib -6) | 2.163G, 35% | 92% | 84% | 93% | 40 → 185 |
| `luaV_execute` (lua int) | 1.032G, 29% | 99% | 99% | 100% | 220 → 4769 |
| `mainGtU` (bzip2 -9) | 0.894G, 33% | 84% | 36% | 98% | 21 → 368 |
| `mainSort` (bzip2 -9) | 0.675G, 34% | 82% | 98% | 99% | 58 → 557 |

On this build the loop estimate starts without 3a's whole-function
homes, so it loses to them where traffic lies outside loops (`mainGtU`).
Its assignments needed almost no edge moves. What they found is the same thing webs find, less completely. `frame_slots` packs
unrelated short-lived temporaries into a few hot slots (a median of 2
webs per home, up to thousands of webs in a large function), and 3a's
one register per slot cannot use a register that is free only where one
of those temporaries lives. Values that cross loop boundaries are not
the limit in any of these functions.

So item 3d is webs. Splitting with edge moves is item 3e and is
deferred. The loop estimate above colours only homes a loop references,
so it never spills a value that lives through a loop unused, and that
is the main thing edge moves buy. Counted directly in `BZ2_decompress`:
its four largest loops (2281 to 8654 instructions) have no homes live
through them unreferenced. Its third-hottest loop (245 instructions,
0.91G Ir) has 19 such homes and references only 7, and those 7 carry
0.19G of scalar traffic. A 92-instruction loop (0.23G Ir) has 18. Their
entries are rare, so spilling around them is nearly free. The ceiling
for 3e on bzip2 -d is therefore those loops' traffic, about 0.2–0.25G
(4%), on top of webs. 3e needs moves, landing pads for critical edges
and a checker that accepts inserted lines. It comes after 3d's result,
if the gate still shows the gap.

**Expected yield.** This is traffic moved from frame slots to registers,
over whole homes. It is an upper bound, because the estimate colours by
the real execution counts and the allocator by loop depth:

| Workload | Traffic moved | Share of the workload's instructions |
| --- | --: | --: |
| bzip2 -d | +0.20G | 3.4% |
| lz4 -9 | +0.53G | 4.0% |
| bzip2 -9 | +0.23G | 1.4% |
| zlib -6 | +0.02G | 0.2% |
| lua int | +0.01G | 0.2% |

That is less than bzip2 -d's 24% suggested. 41% of `BZ2_decompress`'s
scalar traffic (0.72G, about 12% of bzip2 -d) stays in the frame under
webs too. Most of it is pressure in the large loops, with a median of 21
homes live at once against 7 allocatable registers and none of them
unreferenced. Splitting cannot fix that part (3e reaches the small inner
loops, above). Memory operands for frame homes
(`addl -8(%rbp), %eax`, which removes the load but not the access) or
more allocatable registers would be needed, and both are instruction
selection.

Instructions barely move when a slot move becomes a register move. 3a's
lesson is that the gain is time: it cut the geomean 15% with flat
instructions, because store-to-load forwarding chains through frame
slots bound IPC. 3b's operand rewrite then folds many of the new
register moves. Expect a few percent of time on bzip2 -d and lz4 -9 and
nothing elsewhere. bzip2 -d's time is also layout-sensitive (step 3b's
result), so the result is judged against a padding sweep. At
`0230f1d` (`-O`, cells and inlining), `.skip N` before `BZ2_decompress`
for N = 0, 16, …, 112 gives the same 4.851G instructions (±0.0001G) and
cycles from 1.652G to 1.757G (6%), the median of 5 trials each, on cpu 6.
Legacy-decoder micro-ops move with them, from 0.76G to 0.88G. A
change inside that band is layout. To count as a gain, webs must move
the whole band.

Gate at `0230f1d` (7 trials, cpu 6, median ms, instructions): `-O`
against `-O --inline=none` is lz4 -9 488 against 639 (10.52G against
13.37G), lua str 398 against 416, sqlite 1360 against 1378, and equal
within noise elsewhere. This is the baseline 3d is measured against.

#### First: a home per temporary (`--registers=temps`), no checker change

The webs come from `frame_slots` pooling unrelated temporaries into one
home, the same kind of cause as the float pools. So before any new
trusted analysis, the layout stops pooling them: `temp_slots/9` with
pools `own` gives each `w`/`l` temporary its own home. 3a's per-home
allocation and checker then see each temporary's live range as a home,
and 3b and cells run unchanged. Only the layout changes, and it is not
trusted. The reference layout (no `-O`, `stack`, `local`) and the other
allocating modes keep their pools, and the snapshot's 4032 existing
outputs are byte-identical. The new `T.` mode adds 576.

Four versions were measured. bzip2 -d is the hard case: one function
of 55k instructions, bound by the op cache, whose cycles track
legacy-decoder micro-ops in every variant.

1. *Every temporary its own home.* This cut instructions everywhere
   (geomean 3.42 → 3.27), but bzip2 -d ran slower (gate 3.74 → 4.07,
   with a padding band of 1.70–1.91G against base's 1.65–1.76G).
   `BZ2_decompress`'s frame grew from 5.5 KB to 25.6 KB, and with 22
   values live at once, many homes stay in that frame, spread across
   it.
2. *A cap of 1024 own homes per function* kept `BZ2_decompress` pooled,
   but cost Lua its gain: `luaV_execute` is over the cap, and it gains
   because nearly every home gets a register, so its large frame is
   never touched.
3. *Two lowerings, frame-resident homes pooled.* If more than 256
   homes stay in the frame, the function is lowered again with those
   pooled, as split pools them, and placed first, near `%rbp`. This
   fixed bzip2 -d (band 1.65–1.81G against base's 1.59–1.82G, 4.550G
   instructions against 4.851G). But the homes that got a register
   kept their own slots, never touched, so frames grew 3.7× across
   bzip2 (`sendMTFValues` 0.9 → 20.5 KB), and deep recursion would
   reach the stack-overflow trap sooner. This version shipped opt-in in
   `d20067b`.
4. *Two lowerings, grouped by register (kept).* The second lowering
   pools every temporary by where the first allocation put it: those
   left in the frame together (placed first), and those given a
   register together with the others given the same register. Same-
   register temporaries never interfere, so 3a gives each shared home
   that register again. The frame then holds about one home per
   register in use plus the pooled remainder, as in cells mode. The
   first lowering only proposes the map (`regs_asm/6`'s map mode: 3a's
   allocator, no check, no operand rewrite), because its lines are
   dropped. Only the second, emitted stream is checked, by 3a's checker
   and 3b's, unchanged. Functions with at most 16 scalar homes (128
   bytes) keep one lowering and their own homes.

Frames under 4, across bzip2's main files: 31.9 KB in total against
29.6 KB for cells (1.08×; version 3 was 109 KB), median 208 against 160
bytes. `BZ2_decompress` is 5584 bytes against 5552, and bzip2 -d keeps
its instruction drop (4.559G).

Recursion depth before the stack-overflow trap (8 MiB stack, to 1%):

| Program | filcc -O2 | `-O` (cells) | `-O --registers=temps` |
| --- | --: | --: | --: |
| small recursive function (`1 + f(n - 1)`) | 173,056 | 74,240 | 65,024 (0.88×) |
| recursive function with ~20 temporaries | 65,024 | 34,560 | 34,560 (1.00×; 17,280 with a 256-home threshold) |
| Lua, Lua-level recursion | 499,712 | 499,712 | 499,712 |
| Lua, recursion through `pcall` (C) | 196 | 196 | 196 |

Lua's limits are its own (`LUAI_MAXSTACK`, and the C-call count), not
the machine stack. The small function is under the 16-home threshold:
its frame grows from 96 to 112 bytes. The threshold bounds any
function's growth at 128 bytes.

Gate (7 trials, cpu 6), ratio to filcc -O2, time (instructions), with
the trials' range of time ratios:

| Workload | `O` | `O-temps` | ranges |
| --- | --- | --- | --- |
| zlib -6 | 2.59 (4.21) 2.56..2.62 | 2.44 (4.02) 2.41..2.46 | apart |
| zlib -d | 2.04 (3.38) 2.01..2.25 | 1.96 (3.22) 1.94..1.98 | apart |
| bzip2 -9 | 2.06 (2.66) 2.05..2.12 | 1.99 (2.53) 1.99..2.00 | apart |
| bzip2 -d | 4.04 (3.40) 4.04..4.07 | 3.81 (3.19) 3.79..3.84 | apart |
| lz4 -1 | 2.27 (10.69) 2.16..2.33 | 2.22 (10.64) 2.15..2.29 | overlap |
| lz4 -9 | 2.99 (3.71) 2.89..3.01 | 2.56 (3.37) 2.53..2.69 | apart |
| lz4 -d | 2.77 (7.24) 2.72..2.92 | 2.76 (7.18) 2.70..2.91 | overlap |
| lua int | 2.26 (2.49) 2.25..2.67 | 2.14 (2.35) 2.12..2.15 | apart |
| lua tab | 2.09 (2.40) 2.09..2.13 | 1.99 (2.26) 1.98..2.04 | apart |
| lua str | 1.51 (1.63) 1.45..1.54 | 1.50 (1.61) 1.48..1.55 | overlap |
| sqlite | 2.06 (2.04) 2.05..2.11 | 1.98 (1.99) 1.98..1.99 | apart |
| geomean | 2.35 (3.41) | 2.24 (3.27) | |

bzip2 -d flipped against version 3's gate (3.66 → 3.78 there): `O`'s
binary, relinked, drew a worse layout (4.04), with the same instruction
count. That function's time is link layout, as above.

The instruction drop matches or exceeds the webs estimate (lz4 -9:
0.97G against 0.53G estimated; bzip2 -d: 0.30G against 0.20G), because
3b then folds the new register moves too.

**Costs.**

- *Compile.* `sqlite3.c`, user time, each run alone: cells 106.5 s,
  temps 138.3 s (+30%). By threshold: 0 homes 143.2 s, 16 138.3 s, 256
  126.2 s (but 2× depth loss on the 20-temporary function). The second
  lowering costs a backend pass on each function above the threshold.
  An explicit collection before every second lowering cost 4×, so it
  is done only for functions with more than 1024 homes.

  Then three cuts, each leaving every output byte-identical (the
  snapshot's modes, `sqlite3.c` in cells and temps). They are measured
  in `perf stat` user instructions, because user time on this compile
  varies by up to 8% between identical runs, and instruction counts by
  under 1%:

  1. Map mode runs only the allocation: no preflight, allocated stream,
     successors or check, since its stream is dropped. It also analyses
     only the lines a home can depend on: labels, control flow, calls,
     `lea` and lines with a memory operand. Every other line falls
     through and touches no home, so home liveness, interference, loop
     depths and references are unchanged; only the scratch and flags
     bits differ, and the allocation masks them off.
  2. The second lowering reuses the first's fused blocks and live
     ranges (`temp_slots/9` with pools `own(Groups, Ranges)`). The groups
     change only which slots the ranges share, and building the ranges
     was 6.3 s of the 7.0 s of frame layout.
  3. `body_analysis` and the allocator's references find the homes an
     access overlaps by 8-byte word (`halves/5`), not by an assoc lookup
     per byte offset. This is shared code, so cells gains too.

  | `sqlite3.c -O` | instructions | user (pinned, alone) |
  | --- | --: | --: |
  | cells at `77c1c56` | 1,749G | 106.5 s |
  | temps at `77c1c56` | 2,320G | 138.3 s |
  | cells now | 1,655G | 107 s |
  | temps now | 1,954G | 125 s |

  Temps is now 1.18× cells by instructions (1.17× by time), and 1.12×
  the cells compile at the start of this work. What remains is temps'
  own: the map pass, about 16 s (selecting the own lowering 3.2 s, line
  effects 1.4 s, the allocation 11 s), and the second lowering, 0.5 s.
  The map pass's cost is spread over all 1374 two-lowering functions
  (`sqlite3VdbeExec` is 2.3 s; the largest seven are 4.7 of 22 s). So
  the threshold is not the lever. Skipping the second lowering when it
  could save at most 16 homes against the split pools gave 1,977G
  against 1,986G at the time; thresholds of 24 and 32 homes gave 1,956G
  and 1,938G.
- *Memory.* With the 4 GB stack limit the `sqlite3.c` builds above
  use, peak RSS is 2.28–2.39 GB for temps against 1.46 GB for cells.
  (After cut 3, cells reads 1.83 GB with the same output and fewer
  instructions.) Under the default 1 GB limit, which the Nix checks
  use, cells at `77c1c56`, cells now and temps all peak at 2.28 GB and
  finish. So the difference is how far SWI lets its stacks grow between
  collections, not live state temps would have to re-key: garbage
  collection takes 7.1 s in temps against 6.5 s in cells. Temps fits the
  default stack.
- *Trust.* Nothing new is trusted. The map-only first pass is a layout
  choice whose lines are never emitted.

Fail-first: unit test `own_scalar_homes` fails when own pools behave as
split, and when `own(Groups)` ignores the groups; `temps_frame` (the
~20-temporary function's frame is no larger than cells') fails when the
second lowering is skipped. Under `-O --registers=temps` the difftests
and progtests pass, and one Nix check configuration runs them.

What remains for 3d (webs with a new checker) is the part temps cannot
reach without the frame growth: functions where pressure leaves many
homes in the frame. The second lowering pools those again, so
`BZ2_decompress` keeps 3a's limits there.

#### Temps as the `-O` default

Approved after the compile cuts above, as 1.17–1.18× today's cells and
1.12× the cells the budget was set against, with memory within the
default stack. `-O` now selects `--registers=temps`. `--registers=cells`
stays selectable. The snapshot's existing `-O` modes keep their explicit
`--registers` (cells in C. and I.), so their outputs are unchanged, and
T. guards temps. `nix/check.nix` runs one configuration on
`-O --registers=cells`, and the gate has an `O-cells` mode.

Gate on the switch (7 trials, cpu 6), ratio to filcc -O2, time
(instructions), with the trials' range of time ratios:

| Workload | `O` (temps) | `O-cells` |
| --- | --- | --- |
| zlib -6 | 2.43 (4.02) 2.38..2.48 | 2.60 (4.21) 2.54..2.61 |
| zlib -d | 1.92 (3.22) 1.80..1.95 | 2.02 (3.38) 1.93..2.06 |
| bzip2 -9 | 2.00 (2.53) 1.98..2.00 | 2.06 (2.66) 2.05..2.06 |
| bzip2 -d | 3.73 (3.19) 3.72..3.81 | 3.54 (3.40) 3.52..3.57 |
| lz4 -1 | 2.20 (10.63) 2.18..2.31 | 2.16 (10.70) 2.12..2.32 |
| lz4 -9 | 2.67 (3.37) 2.53..2.72 | 2.94 (3.71) 2.91..3.50 |
| lz4 -d | 2.81 (7.29) 2.72..2.89 | 2.83 (7.33) 2.74..3.17 |
| lua int | 2.12 (2.35) 2.12..2.14 | 2.26 (2.49) 2.25..2.26 |
| lua tab | 1.99 (2.26) 1.99..2.00 | 2.10 (2.40) 2.10..2.12 |
| lua str | 1.49 (1.63) 1.47..1.53 | 1.48 (1.64) 1.47..1.51 |
| sqlite | 1.99 (1.99) 1.98..2.00 | 2.06 (2.04) 2.05..2.08 |
| geomean | 2.24 (3.28) | 2.31 (3.42) |

bzip2 -d is the exception: 0.29G fewer instructions but slower in this
link, the reverse of the earlier gate (3.81 against 4.04). That function's
time follows its layout, not its instruction count (3d's padding
bands).

#### CPython's interpreter frame (measured for the next item)

CPython (`nanofil-python`, a1a5306) needs a 256 MB stack for
`test_isinstance`'s recursion, because `_PyEval_EvalFrameDefault`'s frame
is far larger than clang's 3,640 bytes. Measured on `Python/ceval.c`
preprocessed as `nanofil-cc` does (`-std=gnu23`, so `NANOFIL_STD=c23`),
by frame key, in bytes, with each kind's lower words counted with it:

| Frame part | plain | `-O --registers=stack` | `-O` (cells) | `-O --registers=temps` |
| --- | --: | --: | --: | --: |
| pointer pool (slots + lowers) | 1,486 + 1,486: 23,776 | 150 + 150: 2,400 | 2,400 | 2,400 |
| phi shadows (slots + pointer lowers) | 106 + 23: 1,032 | 295 + 172: 3,736 | 3,736 | 3,736 |
| local objects (64, with aux words and alignment) | — | 3,072 | 3,072 | 3,072 |
| stack-aux roots of those objects | — | 512 | 512 | 512 |
| scalar and float pools | 32 | 56 | 56 + 24 | 104 + 24 |
| callee-saved registers | — | — | 40 | 40 |
| header, thread, aux | 32 | 32 | 32 | 32 |
| **frame** | **24,880** | **9,808** | **9,872** | **9,920** |

Plain, the frame is the pointer pool: 1,486 pointer temporaries, each
with its lower word. `-O` removes 90% of them. It also places 64 heap
allocations in the frame as M5's local objects (zeroed payload and aux,
a stack-aux root each, within M5's 4096-byte per-function budget), and
its control flow has 295 phis against 106, 172 of them pointers against
23. What fills the `-O` frame is pointers and objects, not scalars:
shadows 38%, local objects and their roots 36%, the pointer pool 24%,
scalars 1%.

Temps' pooling neither helps nor hurts: its first lowering's 6,605 own
scalar homes (52,840 bytes) pool back to 13 homes, 48 bytes more than
cells' 7. The levers are elsewhere:

- *Phi shadows* each have a slot of their own, never shared, with a
  lower word for a pointer phi. Pooling shadows whose copies' lifetimes
  are disjoint, as the pointer pool already is, would address the
  largest part. A shadow's lower is a GC root, so this changes what the
  frame's roots are, and it needs review before implementation.
- *Local objects* are kept whole in the frame, payload and aux, with a
  stack-aux root each, and their storage is never reused. Clang turns
  most such objects into SSA values. Splitting an object whose fields
  are only loaded and stored whole into temporaries, or sharing storage
  between objects whose lifetimes are disjoint, would be middle-end
  work under M5's local-object contract, and needs its own review.
- *The pointer pool* is shared by liveness already.

A CPython workload would be the gate's most realistic interpreter. It
costs a nanofil build of CPython per mode (280 objects), against about
a minute for each of today's workloads. Candidates are a recursion-
heavy script and the `python.sh` workload's scripts, timed against the
filcc build that `nanofil-python` already makes. This is not added yet.

#### Contract (webs; approved, held while temps is measured)

**Mode.** `--registers=webs` is opt-in: frame cells (the current `-O`
default) with webs in place of whole homes. It becomes the default only
after a gate run where it wins time. `function`, `operands` and `cells`
keep their fixed maps, their checker and their snapshot outputs
unchanged.

**Allocator (untrusted, `amd64_regs.pl`).** It works from the shared
`body_analysis/4` liveness of the candidate homes:

- A home's webs are the connected components of the lines where one of
  its halves is live, or where the line accesses it. Two lines are
  joined along each CFG edge into a line where the home is live-in.
- Home eligibility stays 3a's, per home: a w/l home that is 8 apart
  from every other home and save slot, whose address no `lea` takes,
  and whose every access in the function is a substitutable move (3a's
  `substitute/3`). This matches the checker's preflight exactly (a
  `lea` has no memory effect, so a per-web rule would miss it, and a
  rejection is a compile error, not a fallback). Only the colouring is
  per web.
- A web of an eligible home is a candidate when it is not live at the
  function's entry and no 32-bit store in it leaves the high half
  live.
- Two webs interfere when one is written while the other is live, 3a's
  rule at web granularity. A web live across a returning call gets a
  callee-saved register.
- Webs are coloured greedily by loop-weighted references, as 3a colours
  homes.
- The output is the reference body with each access of a coloured web
  substituted by its register (`substitute/3` with a one-home map), plus
  3a's saves after the stack check and restores before every `leave`,
  for each callee-saved register any web uses.
- No other line is inserted. There are no moves and no new labels.

**Checker (trusted): value locations, not a map.** A new validator in
`amd64_regs_check.pl` that needs neither webs nor liveness. That keeps
the web computation and the colouring out of the trusted base: a wrong
partition can only produce a stream that the checker rejects.

1. *Shape.* The proposal pairs line for line with the reference body.
   Each line is identical to its reference line, or is that line with
   one home operand replaced by an allocatable register of the same
   width (`substitute/3` with a one-home map, for any allocatable
   register). 3a's preflight applies unchanged: the reference names no
   allocatable register and has no indexed `%rbp` operand, no `lea`
   takes the address of a substituted home or save slot, no line
   touches a save slot, nothing before the stack check is a label, a
   transfer or an access to a substituted home, and setjmp functions
   admit only identity. Two of 3a's `valid_map/3` rules apply too.
   They are not part of its preflight, and the checker must state
   both:
   - *Homes.* Every substituted home is an 8-byte home of the
     metadata, every description of it is `w` or `l`, and it is 8 apart
     from every other home and every save slot. Otherwise a write to
     one home's register would leave a reference write to an
     overlapping home's slot unaccounted for.
   - *Saves.* The saves are exactly `save(R, S)` for each callee-saved
     R that some substituted line names, in `callee_saved/1` order,
     with valid_map's slot conditions (integer, negative, 8-aligned,
     distinct, outside every home). They come right after the stack
     check, the matching restores come before every `leave`, and every
     `leave` is followed by `ret` (`allocated_stream/4`). The
     proposal must equal the stream rebuilt from the reference, the
     per-line substitutions and these saves.
2. *State.* At every point, for each location X (the home's slot, or
   one of `rbx`, `r12`–`r15`, `r10`, `r11`), the set of halves (home,
   low or high) whose reference value X holds. At entry every slot holds
   its own home's halves and no register holds anything. The analysis
   runs forward over the proposal's CFG. That CFG must be complete, as
   for 3a: every jump names a label of the body or the stack-overflow
   exit, and no line falls off the end. States meet at labels by
   intersection, unvisited blocks start at top, and the analysis
   iterates to a fixed point.
3. *Transfer.* For a line that writes bytes of home H at location X
   (the substituted register, or the slot for an unsubstituted access):
   - Halves the write covers: X holds them, and no other location does.
   - Halves the write only partly covers: X keeps each one only if it
     held it before, since the other bytes are unchanged in both
     streams. No other location holds them.
   - A 32-bit write to a register zeroes its high half, so X no longer
     holds H's high half. A 32-bit store to the slot keeps it.
   - A register write also takes from X every other home's halves.
   - Halves the write does not touch are unchanged in every location
     (for example H's high half under a byte write to its register).

   A `call` takes everything from `r10` and `r11`, and a restore takes
   everything from its register. No other line can change a home slot
   or an allocatable register (shape and preflight).
4. *Obligation.* Every read of a half of home H at location X requires
   X to hold that half before the line: a substituted read from the
   register, or an unsubstituted read from the slot.
5. *Why it suffices.* Lines that are identical in both streams read
   identical operands. The exceptions are home reads, and the
   obligation makes those equal. So by induction along any execution
   path, every non-home location (scratch registers, flags, non-home
   memory, control) is equal in both streams at every corresponding
   point. The must-analysis' fixed point covers loops. The callers'
   registers are restored before every `leave` (the *Saves* rule).
   Homes do not escape, the same trust as 3a, and no reference line
   touches a save slot. So the only state that differs is home slots,
   save slots and allocatable registers, and nothing outside the
   function reads the first two.

The validator accepts every fixed-map stream that 3a's checker accepts:
a fixed map is one web per home. A unit test runs it on 3a's outputs for
the regs fixtures and a corpus. It replaces nothing yet: the fixed-map
modes keep their checker.

**3b and cells.** `operand_lives/4` assumes A is the reference with
substitutions and saves inserted, and a webs stream is exactly that. The
operand rewrite and `check_operands/4` therefore run unchanged; neither
reads the map (`region_end` compares `rbx` and `r10`–`r15` at every
boundary whatever the map). Cells are unchanged too. `regs_mode/3` lists
every scalar slot as a cell, mapped homes included, and `valid_cells`
excludes only locals, wide and save slots. So the slot webs of a split
home are cells, which is sound because cells compare A against B. This
corrects 5a's text, which says cells stay apart from mapped homes. No
code does that, and none needs to.

**No new runtime or GC assumption.** Only `w`/`l` homes move, as in
3a. Pointer payloads, lowers and every GC-visible word stay where they
are. No trap, check or call changes. The runtime assumptions are 3a's:
callees preserve callee-saved registers, only `%rbp`-relative operands
reach homes, homes do not escape, and `instruction_effects/2` is
audited. The trusted code does grow by this validator, which replaces
3a's checker in this mode. Under `--checks=reuse`, later accesses rely
on M7 check evidence about values that live in homes, so a validator
bug there would be a memory-safety bug and not only a wrong result.
That is why its fixtures follow 3a's in full.

**Validation.**

- Fail-first fixtures for the validator, each rejected and each failing
  when its rule is removed:
  1. Another home written into the same register between H's write and
     its read.
  2. H written in `rbx` on one arm and `r12` on the other, then read
     from `rbx` after the join. The meet must intersect.
  3. A `movl` to H's register, then a `movq` read of H. The high half
     is zeroed.
  4. H in `r10` across a call.
  5. A read of H's slot after its last write went to a register (a
     stale slot).
  6. A loop whose back edge carries H in the slot while the head reads
     it from `rbx`. The fixed point must not start from "held".
  7. A byte store to H's slot, then a read from its register.
  8. A substituted home whose address a `lea` takes.
  9. A substitution in a setjmp function.
  10. A substitution that is not of the same width.
  11. A callee-saved register used but not saved, and a save missing
      a restore before one of two `leave`s.
  12. A substituted home overlapping another home or a save slot, and
      one with a `d` description.
  13. A read from a register at entry with no write before it.
  14. A byte write to H's register, then a read of H's slot.
  15. 3a's rejecting fixtures for the rules webs keeps (a `movq`
      immediate outside imm32, a call to a body label, a write before
      the stack check), run against the new validator.
- Accepted fixtures: the same home in two registers in disjoint webs, a
  web left in the slot between two register webs, and every 3a
  fixed-map fixture.
- Fail-first allocator tests (unit, through the public `regs_asm/6`):
  a pooled slot whose two temporaries need different registers gets two
  webs, where whole homes gives it none; and a home with a `lea` in one
  web stays in its slot in every web, rather than failing the check.
- Snapshot: every existing output identical, plus a new `W.` mode for
  `-O --registers=webs`. Difftests, progtests and one Nix check
  configuration run under webs, and then all twelve checks.
- Gate: `O` against `O-webs`, 7 trials. A `.skip N` sweep before
  `BZ2_decompress`, N from 0 to 112 in steps of 16, runs in both modes,
  with cycles, instructions and legacy-decoder micro-ops
  (`de_src_op_disp.decoder`). If webs moves the whole cycle band down,
  that is a gain. If the bands overlap, only the instruction count
  moved.
- Compile time: `sqlite3.c` with `-O --registers=webs` within 10% of
  `-O` (105.0 s user, 1.46 GB peak RSS). Over budget, the allocator caps
  the webs it colours per function. That is a choice of the untrusted
  allocator; the checker is unchanged.

### 8. A cheap middle end

Constant folding and propagation, local value numbering of pure
operations, and dead-code removal on unchecked IR, validated by the
existing refinement checks. Expected: small and unmeasured; constant
moves are 3–11% today, partly removed by immediate operands (M6) and
item 3. Last because the profile shows little to gain yet.

#### 8: result (`--simplify=full`, the `-O` default)

Re-profiled at `2f960d1` first. The shares were still those of
`04c7e7c` (checks 16–40%, pointer temps and lowers 18–30%, calls
11–14% and 36–41% in lz4 `-1`/`-d`, selection 4–16%, copies 4–14%,
ops 4–19%). Of the user's four candidates:

- **Inlining what the inliner refused.** `2ce8b0f`'s punned-union
  promotion already inlines lz4's `LZ4_isLittleEndian` chain. What lz4
  still called was `LZ4_NbCommonBytes`: 105 instructions, over the
  size limit, but 17 once its `isLittleEndian` branches fold. So this
  needed folding inside the inliner, and it is part of item 8.
- **Strength reduction.** Multiplies, unsigned divides and remainders
  by 2^k are rewritten here (one rule each); indexed addressing is the
  backend's and stays open.
- **Copies and zero extensions.** An `ext` of a value that is already
  narrow (a narrow load or extension, the `fits/2` table) becomes a
  copy, and copies of constants propagate.

`src/simplify.pl` runs after `copy`, before `local_storage`, on each
strict-SSA function without `setjmp`:

1. A dominator-tree walk folds constants through interp.pl's own
   `alu/4` (so folding is the interpreter's arithmetic). It applies
   identities, strength reduction, booleans and negated compares, and
   drops narrow `ext`s. It numbers pure operations, scoped to the
   dominator subtree (a pointer plus a constant only within its
   block, below), and folds constant branches. Up to three rounds
   run while a branch folds.
2. Unreachable blocks are pruned and trivial phis removed (copy.pl's
   substitution and `copy_reps`).
3. Dead pure definitions and phis are removed. Loads, stores, calls,
   allocations, divisions that can trap, and getter copies of globals
   never are.
4. Blocks merge: an empty block is bypassed, and a block is appended to
   its only `goto` predecessor. Joins with phis and over 64 edges are
   left alone, which keeps the pass linear.

With `--simplify=full`, inlining's second round takes callees that are
already promoted, copied and simplified (`inline_simplified`,
inline.pl's `prepared/3`). That is what inlines `LZ4_NbCommonBytes`.

**Safety.** The pass sees unchecked IR, before pizlonation. It removes
or shares only pure operations, so no check, trap or trap reason
changes. Polls are placed afterwards by pizlonation's rule (every edge
to an earlier block), so every cycle still polls. The Oracle review
found one blocker: a stale merge entry produced an invalid source
context when merges ran out of block order. It was fixed with a
regression test. Three large-function costs were also fixed: a
quadratic dead-phi scan, bypasses into large joins, and a phi chain
bounded at depth 1000. Validation: difftest refinement over every suite
corpus (fixtures, `gen.pl` seeds 1–4, backend, float, `filc/*.ir`,
`c/*.c`) with `NANOFIL_SIMPLIFY=full`; progtest, also under GC stress;
ABI+GC. The Nix check runs the difftest, ABI+GC and program steps once
more under `-O --simplify=full`. The default output is
snapshot-identical.

**One rule came from measurement.** With every pure operation numbered,
bzip2 `-d` ran 3.11× instead of 2.40×: 4.43G → 4.09G instructions,
but 1.08G → 1.39G cycles. Disabling numbering alone restored the cycles
(on `decompress.c` alone: 1.074G, against 1.293G with numbering). Only
numbering a pointer plus a constant mattered. The likely reason
(not traced to single moves) is that sharing field addresses in
`BZ2_decompress` keeps pointers and their capabilities live across its
state machine. The hottest instructions became frame-slot moves, and
store-to-load forwards fell from 317M to 190M while failed forwards
rose from 51M to 76M. Recomputing such an address costs one add, which
the backend folds into the access.

Two rules were tried. Never numbering a pointer plus a constant (s3)
gave `decompress.c` alone 1.071G cycles and 4.32G instructions, and it
fixed bzip2 `-d` on the gate (3.14 → 2.36). But it gave back part of
the other workloads' gain (Lua int 1.81 → 1.94, bzip2 `-9` 1.75 →
1.83; geomean 2.01 against 2.04). Numbering it only within its block
(s4, adopted) keeps the local sharing. `decompress.c` drops to 4.21G
instructions, and its cycles stay at `-O`'s. On a 3-trial gate while
swa was loaded, s4 was at or below s3 on every workload, 2.09 (2.89)
against 2.13 (2.91); `-O` was 2.28 (3.21) in that run.

**Gate.** Quiet (7 trials, cpu 6) for `-O` and the first two rules; the adopted
rule (s4) only in the 3-trial run while swa was loaded, so its time
column is noisier and its absolute ratios run higher (that run's `-O`
geomean was 2.28 (3.21), not 2.14). Time (instructions) against filcc
`-O2`:

| Workload | `-O` | all numbered | s3: never p+const | s4: p+const in block (loaded) |
| --- | --: | --: | --: | --: |
| zlib -6 | 2.45 (4.08) | 2.27 (3.84) | 2.37 (3.98) | 2.79 (3.92) |
| zlib -d | 2.01 (3.18) | 1.93 (3.02) | 1.89 (3.03) | 1.87 (3.03) |
| bzip2 -9 | 1.98 (2.52) | 1.75 (2.31) | 1.83 (2.38) | 1.93 (2.33) |
| bzip2 -d | 2.42 (3.11) | 3.14 (2.87) | 2.36 (2.99) | 2.54 (2.92) |
| lz4 -1 | 2.19 (10.84) | 2.24 (10.44) | 2.11 (10.45) | 2.47 (10.22) |
| lz4 -9 | 2.41 (3.07) | 2.15 (2.65) | 2.09 (2.65) | 2.36 (2.65) |
| lz4 -d | 2.69 (6.82) | 2.62 (5.36) | 2.59 (5.37) | 2.71 (5.35) |
| lua int | 2.14 (2.35) | 1.81 (1.81) | 1.94 (1.87) | 1.78 (1.87) |
| lua tab | 2.03 (2.26) | 1.74 (1.78) | 1.85 (1.82) | 1.72 (1.82) |
| lua str | 1.49 (1.61) | 1.43 (1.53) | 1.45 (1.54) | 1.51 (1.53) |
| sqlite | 1.97 (1.99) | 1.88 (1.92) | 1.90 (1.94) | 1.80 (1.93) |
| geomean | 2.14 (3.23) | 2.04 (2.87) | 2.01 (2.92) | 2.09 (2.89); loaded `-O` 2.28 (3.21) |

The instruction columns do not depend on load. s4's are within 1% of
"all numbered" except Lua (1.87 against 1.81) and bzip2 `-d` (2.92
against 2.87). In the loaded run s4's time geomean is 0.92× that of
`-O`; in the quiet runs s3's is 0.94× and all-numbered's 0.95×.

`inline_simplified` is worth its cost. Without it (plain inlining,
then simplify) the geomean was 2.05 (2.93), against 2.02 (2.87) with
it. lz4 `-d` falls from 6.39× to 5.36× the instructions. lz4hc's
`LZ4_count`, `countBack` and `countPattern` are still calls; their
caller `LZ4HC_InsertAndGetWiderMatch` is probably over the growth
limit (not checked).

**Profile** (`bench/profile.py` with s3's rule, billions of instructions, `-O` →
`-O --simplify=full`): zlib `-6` 8.03 → 7.82, bzip2 `-9` 11.79 →
11.12, bzip2 `-d` 4.45 → 4.28, lz4 `-9` 8.79 → 7.60, lz4 `-d` 0.49 →
0.39, Lua int 2.78 → 2.22, tab 2.18 → 1.76, str 5.35 → 5.12, SQLite
21.73 → 21.34. The savings come from selection (lz4 `-9` 1.31 → 1.06,
Lua int 0.44 → 0.25), ops (bzip2 `-9` 2.29 → 1.93, Lua int 0.52 →
0.31) and copies (lz4 `-9` 1.24 → 0.90, Lua int 0.26 → 0.13). Checks
are unchanged except in lz4 `-d` (0.06 → 0.03), whose newly inlined
callees' accesses fold or disappear (not traced per access).

**Compile time.** `-O cc sqlite3.i` on one core takes 124.4 s user
without simplify and 125.8 s with it (+1%). The pass costs 7.1 s of the
middle end's time on sqlite3.ir, and `inline_simplified` 1.1 s more.
Less code reaches the backend, which wins most of that back. On lz4.c,
3.2 s becomes about 4.4 s.

**The `-O` default** (decided by the orchestrating thread, after the
opt-in commit): 6–8% of time and 10% of instructions on the gate, for
about 1% more compile time on SQLite, and less on lz4.c (40.0G
instructions to compile against 40.6G without it). `--simplify=none`
stays selectable (NANOFIL_SIMPLIFY=none), and the Nix check keeps its
difftest, ABI+GC and program steps under `-O --simplify=none`. The
snapshot spells out `--simplify=none` for its `-O` modes, so those
outputs and plain mode's stay identical. The zlib, bzip2, Lua and
SQLite checks pass in every configuration with it on.

### 9. Phi shadows shared by position (frame size) — contract (approved, A)

Measured first (`_PyEval_EvalFrameDefault`, item 3d's CPython table):
phi shadows are 38% of the `-O` frame, 295 shadow slots and 172 shadow
lowers (3,736 bytes), because every phi has a shadow of its own. Its
6,078 blocks have at most 7 phis each, and at most 4 pointer phis.
Shadows shared by their phi's position in its block would need 11 slots
(88 bytes), and the frame would go from 9,920 to about 6,270 bytes.

**What a shadow is.** An edge into a block with phis is the parallel
copy `edge_moves//4` (filc_amd64.pl): `phi_reads//3` stores each
incoming value into its phi's `shadow(D)` (and, for a pointer phi, the
value's lower into `lower(shadow(D))`); then `phi_writes//2` loads each
shadow into its phi's home `tmp(D)` (and `lower(tmp(D))`); then the
edge's pollcheck, if it has one, and the jump. A shadow is written and
read only there. Between an edge's first shadow store and its last
shadow load there is no call, poll or other safepoint, and no access to
another block's shadows.

**The change, layout only.** In the allocating modes (`function`,
`operands`, `cells`, `temps`), a block's phis are numbered in phi order
within three classes: `int` (`w`, `l`), `p` and `float` (`s`, `d`). The
`i`-th phi of class `C` in its block uses the plain slot
`shadow_slot(C, i)`, and the `i`-th pointer phi also uses the root
`lower(shadow_slot(p, i))`. Only a temporary that is a phi destination
once in its function shares. The IR allows a temporary to be defined
more than once (ir.pl), so a phi destination in two blocks would need
two positions under one name; it keeps a shadow of its own, as every
phi does now. (Long double phis are rejected by validation.) Each
function then has, per class, as many shadow slots as its largest block
has sharing phis of that class, and as many shadow roots as its largest
block has sharing pointer phis. `frame/6` (filc_abi.pl) adds
`shadow(D) -> shadow_slot(C, i)` and `lower(shadow(D)) ->
lower(shadow_slot(p, i))` to the frame's aliases, as `tmp(N) ->
storage(...)` already are. It shares only when the function has no
setjmp sites and its pools are not `shared` (stack and local layouts
use `shared`), since a placement cannot undo a frame already built.
Emission is unchanged: it stores to and loads from `shadow(D)`, and the
layout resolves the alias. The reference layout is unchanged and
selectable: no `-O`, `-O --registers=stack` and `local` keep one shadow
per phi, byte-identical. A function that calls setjmp keeps one shadow
per phi too. Its snapshot payload names each shadow key, and
setjmp/longjmp copy all of the frame's lowers by index; sharing would
stay consistent there, but excluding these functions is simpler.

**Why the parallel copy is preserved.** Two phis of one block have
different slots: different classes, or different indices within a
class, or (a phi destination defined more than once) a shadow of their
own. So an edge copy's stores never overwrite each other, and each load
reads its own phi's incoming value, as now. Incoming values are read
from homes (`tmp(E)`, `lower(tmp(E))`), never from shadows, so swaps,
self-loops and a phi fed by another phi of its block behave as today.
Each phi has one pair per predecessor (ir.pl's `valid_phi`), so every
load in a copy follows its store in the same copy. Phis of different
blocks may share a slot. A shadow's value is live only from its store
to the load in the same edge copy, and copies are never interleaved: a
branch with copies on both arms emits them one after the other,
`branch(v, L, L)` included. So a later edge's store never meets a live
value.

**GC roots: kept, fewer, never a non-lower.** Shared shadow lowers stay
in the root area (`lowers[]`), zeroed at entry by `zero_roots` with the
rest before the frame is pushed, and are counted in the origins' root
count, which is the frame's own `length(Roots)`. FUGC marks the object
of each non-null `lowers[i]` below the count (filc_runtime_inlines.h),
and requires nothing else of a root slot between safepoints. Stack-aux
roots are found from the end of the array (`end = num_lowers -
has_setjmps`, `begin = end - num_stack_auxes`, filc_runtime.h), and the
shadow roots come before them, so fewer shadow roots only move that
suffix. A shadow root is
written only by `phi_read(p, ...)`, from the incoming pointer's lower
(`lower_reg_load//3`: the value's lower slot, or 0 for a constant). So
every root word is always null or a lower this frame stored. At the
pollcheck after an edge copy, the shared root holds the same lower as
the phi's own `lower(tmp(D))`. At any other safepoint it may hold a stale
lower from an earlier copy, as today's per-phi shadow roots do, since
none is ever cleared. The frame may keep fewer stale objects alive than
before, never different kinds of words. The `shadow_slot(C, i)` words
themselves, a pointer's address word included, are plain frame words,
never roots, as the shadow words are now.

Not proposed (B): taking shadow lowers out of the root area entirely,
since no safepoint separates their store and load. That is a root
reduction. It would rely on three things: no safepoint between a
shadow lower's store and its load, FUGC scanning a running thread's
frame only at its safepoints, and the object being reachable from some
other root at every safepoint. That is the principle clang's Fil-C uses
for values in registers, but no checker verifies the first: a later
helper call inside a phi copy would break it silently. It would save 4
root words (32 bytes) in CPython's frame. Oracle's review recommends A;
B would first need a mechanical check that no call falls inside an edge
copy, and its own review.

**The no-safepoint condition is checked, not argued.** `edge_moves//4`
builds each edge's parallel copy and refuses to emit it unless every
line is a move: `mov`, `movabs` of an immediate, or `lea` of a
rip-relative address. Any call, poll, helper, trap or jump inside a copy
is a compile error ("a phi copy contains a possible safepoint"), in
every mode, so a later change cannot put a safepoint between a shared
shadow's store and its load without being stopped. The register checker
then sees the copy's moves, and it refuses a scratch register for a
shadow live across a call (`shadow_across_poll` in
tests/regs_check.pl).

**What the checkers see.** Nothing new is trusted. The register
checker and frame cells work by slot offset. A shared shadow slot is
one home whose classes are its phis' classes. Separating the classes
keeps each home eligible exactly when its phis are (only `w`/`l` homes
are); a mixed integer and float slot would be refused by the checker,
which requires every class of a home to be `w`/`l`, not miscompiled.
`placed_lines` lists each shared shadow slot once, with the union of its
classes, grouping its phis by offset. Cells are already deduplicated by
offset. A `w` and an `l` phi sharing a slot leave only a `w` value's
dead high half behind, as uninitialized frame words do now.
`own_frame_limit` counts only scalar storage, so temps mode's threshold
is unaffected.

**Validation.**
- Fail-first unit test (`shared_shadows`): a function with two
  phi blocks has as many shadow slots as its larger block, not the sum.
  It fails when the layout gives every phi its own shadow. It also
  asserts that the origin's root count, `zero_roots(N)` and the placed
  `lowers[]` agree.
- Fail-first fixture: one temporary as a phi destination in two blocks,
  beside another phi in each, so the two positions differ. Plant:
  share it anyway. The difftest must fail.
- A plant for each exclusion, each caught: dropping the
  multiply-defined-destination exclusion, and dropping the setjmp
  exclusion. If a plant gives correct code, the report says so, and
  says which test catches the layout change.
- A plant of a call inside an edge copy, refused by the checked
  condition above.
- Fail-first difftest and progtest with swaps (`a, b = b, a` phis in a
  loop), a pointer phi whose incoming value is another phi of the same
  block, `branch(v, L, L)` into a phi block, and a selected branch whose
  arms enter two phi blocks that share slots. Plant: number all of a
  block's phis 0. The tests must fail, then pass once the plant is
  reverted. They run in all five allocating modes (`function`,
  `operands`, `cells`, `temps` and the `-O` default), not only `-O`.
- A register-checker fixture where a shared shadow is mapped to `r10`
  or `r11` on an edge that has a poll.
- GC stress: `run-c.sh gc pointer-effects` and progtests under
  `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`, with pointer phis on polled back
  edges, and a function with both nonescaping locals (stack-aux roots)
  and pointer phis, since fewer shadow roots move the stack-aux suffix.
- Snapshot: only the allocating `-O` modes' outputs (F., P., C., I.,
  T.) change; `cc`, `compile`, O. and `local` outputs are byte-identical.
- The ten-workload gate (instructions should not move; frame offsets
  shrink), bzip2's and SQLite's frames, the 14 Nix checks, and CPython
  (`nanofil-python`, on chapel): `_PyEval_EvalFrameDefault`'s frame,
  and the recursion depth of `test_isinstance`'s
  `test_infinitely_many_bases` case at a fixed stack, before and after.

**Review (Oracle, October 2026): sound with fixes; A, not B.** It
confirmed from the code that the edge copy has no safepoint inside, that
the GC needs root words to be null or lowers and nothing more, that the
origins' count and the stack-aux suffix stay consistent, and that the
setjmp exclusion is sufficient. Its one blocker was a phi destination
defined in two blocks, now excluded from sharing above. Its validation
additions are in the list above.

#### 9: result

Implemented as written (`efd378c`). Frames under `-O` (temps), before
and after:

| Frames | before | after |
| --- | --: | --: |
| CPython `_PyEval_EvalFrameDefault` | 9,920 | 6,272 |
| bzip2's 108 functions: total / median / largest | 31,872 / 208 / 5,584 | 23,568 / 192 / 1,296 |
| SQLite's 3,130 functions: total / median / largest | 794,080 / 224 / 5,504 | 685,376 / 208 / 1,488 |

bzip2's output is byte-identical, and so is everything outside the
allocating `-O` modes: 347 of the snapshot's 4728 outputs differ, all
in F., P., C., I. and T.

CPython's test_isinstance case (test_infinitely_many_bases:
`__getattr__` calling `self.assertEqual` through C), levels reached
before the stack-overflow trap. Since `5d084c76f` the check's interpreter
runs on a 256 MB fiber, which ignores `ulimit -s`, so the after build was
measured with that fiber's size patched to the same 8 and 16 MB that bound
the before build's main stack:

| Stack | before | after |
| --: | --: | --: |
| 8 MB | 650 | 940 |
| 16 MB | 1,310 | 1,880 |

That is 1.45× deeper, about 12.8 KB per level before and 8.9 KB after.
The 4,997 levels the test reaches before Python's RecursionError need
about 64 MB before and 45 MB after, so 256 MB has room either way.

Gate after sharing (7 trials, cpu 6), ratio to filcc -O2, time
(instructions), with the trials' range of time ratios:

| Workload | `O` (temps) | `O-cells` |
| --- | --- | --- |
| zlib -6 | 2.48 (4.08) 2.39..3.50 | 2.51 (4.20) 2.47..2.56 |
| zlib -d | 1.91 (3.20) 1.84..1.96 | 2.02 (3.39) 1.90..2.04 |
| bzip2 -9 | 1.99 (2.52) 1.98..1.99 | 2.06 (2.66) 2.05..2.32 |
| bzip2 -d | 2.39 (3.11) 2.38..2.40 | 2.73 (3.44) 2.73..2.74 |
| lz4 -1 | 2.12 (10.62) 2.05..2.22 | 2.11 (10.71) 2.08..2.25 |
| lz4 -9 | 2.67 (3.41) 2.54..2.68 | 3.05 (3.69) 3.03..3.05 |
| lz4 -d | 2.86 (7.29) 2.81..2.93 | 2.89 (7.34) 2.81..2.94 |
| lua int | 2.13 (2.35) 2.13..2.13 | 2.29 (2.49) 2.28..2.29 |
| lua tab | 1.99 (2.26) 1.98..2.00 | 2.15 (2.40) 2.14..2.53 |
| lua str | 1.51 (1.62) 1.48..1.55 | 1.50 (1.63) 1.47..1.52 |
| sqlite | 1.97 (1.99) 1.96..1.98 | 1.98 (2.04) 1.97..1.98 |
| geomean | 2.15 (3.27) | 2.26 (3.42) |

Most rows are within noise of the switch's gate. bzip2 -d is the
exception, and most of the geomean's change from 2.24: 3.73 to 2.39
under temps and 3.54 to 2.73 under cells, while its instruction ratios
barely move (3.19 to 3.11, 3.40 to 3.44). Its time follows its layout
(3d), and BZ2_decompress's frame, the 5,584-byte largest, shrank most.

The plants, each restored afterwards:

- Numbering every phi of a block 0: the shadows.ir difftest fails
  (`swaps` and `twice` return other values), and so does
  `shared_shadows`.
- No sharing at all: `shared_shadows` fails.
- Dropping the multiply-defined-destination exclusion: the compile
  refuses `twice` (duplicate `shadow(t)` keys in the layout), so the
  difftest and `shared_shadows` fail.
- Dropping the setjmp exclusion: `shared_shadows` fails, on the layout.
  The code stays correct: `run-c.sh setjmp` and the setjmp progtests
  pass under GC stress. As Oracle found, setjmp/longjmp copy all of the
  frame's lowers by index, and the snapshot of a dead shadow is
  harmless, so this exclusion is for simplicity, not safety.
- A call in `phi_writes`: every compile with a phi is refused ("a phi
  copy contains a possible safepoint").
- `shadow_across_poll` expected to pass: the register checker refuses
  it, so the regs_check test fails.

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

`--registers=function` (or `NANOFIL_REGISTERS=function`) landed opt-in
and became the `-O` default after the gate below; without `-O` the stack
reference stays the default, and `-O --registers=stack` (the gate's
`O-stack` mode, also run by the Nix checks) gives the earlier `-O`. A
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
of the largest files rises from 2.9–3.8 s (`-O --registers=local`) to
4.4–4.6 s, 20–50% more.

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

### Function registers as the `-O` default, and SQLite in the gate

With `-O` now meaning function registers, the gate in one run (filcc
pinned, SQLite added):

| Workload | `O-stack` (old `-O`) | `O-local` | `O` |
|---|--:|--:|--:|
| zlib -6 text | 4.41 (5.68) | 4.22 (5.62) | 3.21 (5.62) |
| zlib -d text | 3.14 (4.33) | 2.96 (4.23) | 2.67 (4.22) |
| bzip2 -9 text | 3.36 (3.70) | 3.10 (3.62) | 2.64 (3.61) |
| bzip2 -d text | 6.05 (4.30) | 5.72 (4.19) | 4.09 (4.20) |
| lz4 -1 random | 3.61 (23.29) | 3.61 (23.48)* | 3.32 (23.36)* |
| lz4 -9 text | 6.36 (5.91) | 5.68 (5.81)* | 5.47 (5.87) |
| lz4 -d text | 5.87 (17.49) | 5.81 (17.53)* | 5.36 (17.46) |
| lua int | 3.80 (3.43) | 3.69 (3.21)* | 3.33 (3.24) |
| lua tab | 3.75 (3.32) | 3.64 (3.13)* | 3.35 (3.14) |
| lua str | 1.77 (1.93) | 1.73 (1.91)* | 1.67 (1.93) |
| sqlite | 2.67 (2.48) | 2.65 (2.46)* | 2.41 (2.47) |
| geomean | 3.82 (5.02) | 3.67 (4.92) | 3.23 (4.93) |

bzip2 `-d` with `-O` takes 4.09× filcc against 5.54× off.

Compile time is the cost. `sqlite3.c` (FTS5 on, preprocessed, `-O`)
compiles in 73 s with `--registers=stack`, 92 s with `local` and 122 s
with `function` (5.6 GB peak), so the register pass and its checker are
about 40% of that compile: +33% over `local`, +67% over `stack`, in line
with +20–50% on the bench programs' largest files.
The register pass recomputed each line's instruction effects several
times and ran a whole liveness pass to check the CFG; sharing them cut
its backend time on `lvm.c` from 4.3 s to 2.8 s (local: 1.5 s), with
the same output.

Where `-O`'s instructions go now, by shape (`bench/profile/shapes.py`
over callgrind; frame traffic is now mostly pointer payloads and lowers):

| Workload | frame loads + stores | home ↔ scratch moves | constants | control |
|---|--:|--:|--:|--:|
| lua int | 43% | 9% | 5% | 12% |
| zlib -6 | 28% | 23% | 3% | 16% |
| bzip2 -d | 41% | 17% | 2% | 13% |
| lz4 -9 | 43% | 10% | 3% | 11% |
| sqlite | 29% | 9% | 3% | 15% |

Step 3b (register operands) targets the home ↔ scratch moves; the frame
traffic left is pointer material, item 5.

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
