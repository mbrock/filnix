# Representative routine evaluation

The compiler-backed prototype reaches roughly the same decoder throughput
as a C implementation using checked `memcpy` operations. Its table-entry
leaf is somewhat slower than that C version, and the pointer-linked walk
is about even. These results support retaining C lowering and extending
the semantic model before implementing another assembler backend.

This is an evaluation of three small routines, not a zstd benchmark.
The raw [2026-09-05 results](measurements/2026-09-05.json) include every sample,
hardware-counter record, source hash, tool path and executed command.
`evaluate.py` reproduces the build, correctness gates and measurements;
the Nix check runs its correctness-only mode and retains C, assembly,
objects, disassembly, callers and a build manifest under `evaluation/`.

## Compared programs and contracts

| Variant | Implementation |
|---|---|
| `filc-c` | Bytewise C reference, compiled with Fil-C |
| `filc-memcpy` | C reference using checked four-byte `memcpy` reads/writes |
| `plain` | Prolog translation with grouping and condition simplification disabled |
| `groups` | Read grouping enabled; original flag formulas |
| `conditions` | Direct comparisons enabled; individual reads |
| `optimized` | Both Prolog transformations enabled |
| `upstream` | Unmodified, pinned upstream SaRCAsm |
| `native-c` | Bytewise C compiled with native GCC |
| `native-asm` | Original assembly, assembled and called natively |

All Fil-C variants use compiler/runtime and SaRCAsm revision
`4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c`. The measured Prolog executable
was packaged from Filnix commit `8195b2d3ced017d75f1cbe5afa573bd7f7f325d8`;
the evaluation sources and assembly inputs are additionally identified by
SHA-256 in the result. Native builds use the flake's GCC 14.3.0 and binutils
2.44. C uses `-O2`, separate translation units and no LTO. Fil-C assembly
emission also uses `-fno-addrsig`.

The inputs are the existing table-entry, decoder and node-walk examples.
Upstream needs `#! load ptr` / `#! store ptr` in place of `#! ptr`, and the
table fixture's two instructions on one line must be split. The adapter
checks the six pointer-access shapes and verifies equal normalized
instruction effects after reversing the annotation spelling and ignoring
source-line numbers. No instruction is removed or substituted.

Pinned upstream requires natural alignment for these integer accesses;
the prototype permits unaligned integers. Every Fil-C variant passes 16,384
aligned table cases, null/freed/bounds failures, the decoder reference and
19 decoder/node-walk failure modes. The prototype and C variants also pass
unaligned table cases and all 10,240 decoder cases per test variant. Upstream
passes the 768-case aligned intersection across three alias layouts, plus
exact boundaries and 520 node walks; an unaligned table access is recorded
as an expected alignment rejection. Native variants run valid-input gates.

All timed inputs are aligned, within bounds and free of address overflow.
The prototype retains explicit offset-overflow guards; the C references
do not implement that additional trap contract. The bytewise C version is
useful as an oracle but is a poor performance baseline for this decoder.
The packed C version is necessary to assess what ordinary checked C can do.

## Measurement method

The host is an AMD Ryzen 9 7950X3D with 32 logical CPUs. Measurements ran on
CPU 1, whose SMT sibling is CPU 17 and whose shared L3 is 96 MiB. The host
remained shared: sampled one-minute load averages ranged from 14.19 to 21.57.
Affinity prevents migration, not contention or frequency changes.

Each routine is called through the same separately compiled caller. The
table workload cycles over 64 entries. The decoder processes either 64 or
65,536 input bytes into four times as much output. Inputs use the fixed seed
42 and contain symbols 0..63; correctness tests separately cover malformed
symbols and aliasing. The walk traverses 4,096 separately allocated nodes
in a cycle, using a stride of 179 through their allocation order.

Allocation, initialization, 64 warmup calls and final output checking occur
outside the timed region. Timings include calls and their common caller
bookkeeping; each decoder invocation resets state and checks final cursors.
Iteration counts are calibrated once against packed C, then held equal
across variants. Nine interleaved rounds rotate a seeded variant order so
each variant occupies each position once. Tables report median wall time
per lookup, input byte or node. The JSON also records ranges and paired
within-round ratios to each C reference.

Two additional counter rounds run in opposite orders. `perf stat` starts
disabled; a FIFO enable/disable acknowledgement protocol encloses the
workload rather than process startup, allocation or warmup. The counters
cover the main thread, with a small control/clock boundary overhead. All
recorded counters ran at 100% without multiplexing; no CPU migrations were
recorded. Counter samples are separate executions from the timing samples.

## Runtime results

Nanoseconds per lookup, input byte or node; lower is faster:

| Variant | Table lookup | Decoder, 64 bytes | Decoder, 65,536 bytes | Node walk |
|---|---:|---:|---:|---:|
| Bytewise Fil-C C | 2.782 | 8.876 | 8.646 | 3.833 |
| Packed Fil-C C | 2.212 | 2.119 | 1.885 | 3.879 |
| Prolog, neither transformation | 3.236 | 2.712 | 2.414 | 3.823 |
| Prolog, grouping only | 2.527 | 2.135 | 1.959 | 3.820 |
| Prolog, conditions only | 3.202 | 2.521 | 2.318 | 3.798 |
| Prolog, both | 2.405 | 2.056 | 1.879 | 3.821 |
| Upstream SaRCAsm | 3.545 | 4.328 | 3.711 | 4.186 |
| Native bytewise C | 1.189 | 1.826 | 1.781 | 1.576 |
| Native original assembly | 1.290 | 0.634 | 0.567 | 1.618 |

The optimized large decoder's range was 1.852–2.001 ns/input byte, versus
1.822–2.144 for packed C and 3.547–4.094 for upstream. Its median paired
ratio to packed C was 1.001. The leaf's paired ratio was 1.100, and its
range overlaps packed C's; the walk's ratio was 0.993. Small differences
within those overlapping ranges should not be treated as stable wins.

Read grouping provides the main improvement over the unoptimized Prolog
translation. Direct condition lowering removes the extra comparison and
substantially reduces mispredictions for the valid symbol 63, but these
timings do not isolate a consistent speedup from that change alone. The
four Prolog versions of the walk have no meaningful optimization difference
and give a useful indication of timing noise. The native bytewise C decoder
is also slower than native assembly; it is not a competitive native-C ceiling.

Mean main-thread counters per input byte for the large decoder:

| Variant | Instructions | Branches | Branch misses | Cycles |
|---|---:|---:|---:|---:|
| Bytewise C | 202.103 | 52.021 | 0.0027 | 40.398 |
| Packed C | 45.026 | 13.005 | 0.0006 | 8.926 |
| Prolog, neither | 59.064 | 15.022 | 0.0101 | 11.593 |
| Prolog, grouping only | 47.059 | 13.021 | 0.0101 | 9.618 |
| Prolog, conditions only | 59.031 | 15.006 | 0.0008 | 10.813 |
| Prolog, both | 47.031 | 13.006 | 0.0007 | 11.186 |
| Upstream | 86.048 | 20.010 | 0.0011 | 17.400 |

Instruction counts support the grouping result: the optimized prototype
is close to packed C and executes about half as many instructions as
upstream here. Cycle counts vary more; the optimized counter runs do not
beat grouping-only despite their lower branch-miss count. Neither source
instruction counts nor a single counter run establish a general speedup.

## Code size and frontend cost

Fast-entrypoint bytes, including cold blocks but excluding getters and
signature bridges:

| Variant | Table | Decoder | Walk |
|---|---:|---:|---:|
| Bytewise Fil-C C | 160 | 1498 | 333 |
| Packed Fil-C C | 103 | 1220 | 333 |
| Prolog, neither | 247 | 1305 | 298 |
| Prolog, grouping only | 153 | 1250 | 298 |
| Prolog, conditions only | 247 | 1304 | 298 |
| Prolog, both | 153 | 1251 | 298 |
| Upstream | 248 | 1720 | 376 |
| Native original assembly | 29 | 96 | 39 |

Packed C and the optimized Prolog decoder both reserve 152 stack bytes
plus saved registers; upstream reserves 136. Frame size alone does not
predict its larger instruction count or lower throughput. Prolog's leaf
still carries offset guards absent from the packed C leaf. Native code and
Fil-C code also have different ABI, capability and polling obligations.

Across three interleaved frontend trials for the combined three-function
input, Prolog emission to C took median 470–478 ms. End-to-end assembly
emission took 519–530 ms; upstream assembly emission took 57.8 ms. These
are tool-invocation costs, including startup. The Prolog command runs
Fil-C-built Trealla, while packaged upstream uses native minilute/Luau, so
this comparison does not isolate language or algorithm cost. Profiling the
frontend and comparing equivalent interpreter builds should precede claims
about the reason for the difference.

## Reproduction and next scope

From the repository root:

```sh
nix build .#checks.x86_64-linux.sarcasm-prolog -o result-prolog-check
nix build .#sarcasm-prolog -o /tmp/prolog-eval-tool
nix build .#filcc -o /tmp/prolog-eval-cc
nix build .#sarcasm -o /tmp/prolog-eval-upstream
python3 experiments/sarcasm-prolog/evaluate.py \
  --translator /tmp/prolog-eval-tool/bin/sarcasm-prolog \
  --filcc /tmp/prolog-eval-cc/bin/clang \
  --sarcasm /tmp/prolog-eval-upstream/bin/sarcasm \
  --out /tmp/prolog-evaluation --cpu 1
```

The runner accepts `--cc`, `--assembler`, `--nm`, `--objdump` and `--perf`
to select exact tools; the raw JSON records the pinned paths used above.
`--check-only` runs builds and correctness gates without timings or perf.
When perf is unavailable, normal timings still run and the reason is saved.
All subprocesses have timeouts. Use an available CPU on the machine being
measured; the recorded affinity and topology describe this run only.

The next semantic slice should be a bounded bit-reservoir routine using
variable shifts, with widths, count masking and flag preservation specified
before adding opcodes. It can use one stream, explicit bounds and the same
checked C backend. Profile frontend phases alongside that extension; the
half-second cost is already visible on a small input.

A read-only inventory of pinned zstd 1.5.7's
[`huf_decompress_amd64.S`](https://github.com/pizlonator/fil-c/blob/4867f1179f1c3dbe5484ec0f98c2fcc7d401e50c/projects/zstd-1.5.7/lib/decompress/huf_decompress_amd64.S)
shows why a full port is a larger task: BMI2 `shlx`/`shrx`, `bsfq` with its
zero-input behavior, 8/16-bit stores, `%ah` reads, pointer subtraction and
differences, `mulq`'s paired outputs, conditional moves, additional registers,
stack traffic and four interdependent streams. Macro expansion and
preprocessing also precede the existing parser. Variable shifts are one
useful prerequisite, not a promise that the rest of that routine is accepted.
No package default changes and no revival of the parked zstd port follow
from these measurements.
