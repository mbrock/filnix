# zstd with SaRCAsm

The experimental `zstd-sarcasm` package enables zstd 1.5.7's two x86-64
BMI2 Huffman decoder loops through SaRCAsm. The default zstd continues to
use its C decoders. LLVM, the runtime, and the default assembler are unchanged.

```sh
nix run .#zstd-sarcasm -- --version
nix build .#checks.x86_64-linux.zstd-sarcasm
```

## What was needed

`patches/sarcasm-zstd.patch` teaches the pinned SaRCAsm to parse
semicolon-separated statements emitted by zstd's preprocessor macros. It
preserves quoted strings, `#` comments, annotation bodies, `lock;` prefixes,
and original line numbers. The same change is on the `coro` branch of
[mbrock/fil-c](https://github.com/mbrock/fil-c), with upstream-style tests.
The pinned SaRCAsm already allows unaligned ordinary integer accesses while
keeping pointer and atomic alignment checks.

`patches/zstd-sarcasm.patch` ports the two loops:

- Declare `void(ptr)` entrypoint signatures and mark pointer loads/stores.
- Replace the push/pop state layout with equivalent fixed frames, which
  SaRCAsm virtualizes. The decoder's arithmetic and loop structure remain.
- Replace `%ah` stores with a shift and `%al` store, avoiding an unsupported
  high-byte register alias.

The variant selects its own patched assembler with `--filc-resource-dir`.
This keeps experimentation downstream of LLVM and avoids rebuilding the
compiler/runtime or changing other packages' assembler.

The upstream zstd patch's inline loop-alignment suppression remains in place.
Re-enabling these layout hints is a separate compiler-inline-assembly issue,
not necessary to enable the standalone Huffman loops.

## Independent compression fix

zstd 1.5.7's `ZSTD_selectAddr` uses pointer-returning inline assembly that
Fil-C rejects at runtime. `ZSTD_DISABLE_ASM` does not disable this helper.
The failure reproduced with the previously cached default zstd on a
low-alphabet random input at compression level 3.

`patches/zstd-pointer-select.patch` selects the existing C conditional for
Fil-C in both variants. The baseline smoke test now exercises this case.
This is independent of the Huffman assembly experiment.

## Validation

The Nix check covers:

- Semicolon parsing, `#` comments, annotations, quoted text, lock prefixes, and
  access width/alignment selection.
- Unaligned integer accesses, preserved pointer loads, and traps for
  out-of-bounds loads/stores, read-only writes, and misaligned pointer loads.
- 200 comparisons of the X1/X2 assembly loops with zstd's C loops, using
  varied tables and bitstreams with unaligned input/output. It compares
  output bytes, input/output positions, bit containers, and returned pointer
  usability. These direct loop tests require BMI2, unlike the dispatched CLI.
- Missing capabilities and out-of-bounds reads/writes trap inside each loop.
- 36 compression/decompression round trips between native and Fil-C zstd,
  spanning six input patterns and compression levels 1, 3, and 9.

## Initial performance result

On the development host, a deterministic 1 MiB input drawn from 16 symbols
was compressed at level 3. Each timing decoded that frame 100 times using
the same library and context, switching `ZSTD_d_disableHuffmanAssembly`
between the assembly and C paths. Five alternating measurements gave:

| Decoder | Median time for 100 MiB |
|---|---:|
| SaRCAsm | 0.226 s |
| Fil-C C | 0.153 s |

The safe assembly was about 47% slower on this workload. This is an initial
measurement, not a general performance result. It establishes working safe
assembly, but does not justify changing the default.
The benchmark source is `tests/zstd-sarcasm-bench.c`.

To repeat it:

```sh
nix build .#filcc -o result-cc
nix build '.#zstd-sarcasm^out' -o result-zstd
nix build '.#zstd-sarcasm^dev' -o result-zstd-dev
result-cc/bin/clang -O2 -Iresult-zstd-dev/include \
  tests/zstd-sarcasm-bench.c -Lresult-zstd/lib \
  -Wl,-rpath,"$(readlink -f result-zstd)/lib" -lzstd -o /tmp/zstd-bench
/tmp/zstd-bench
```

## Profiling the regression

On 2026-09-05, profiling the same workload on an AMD Ryzen 9 7950X3D,
pinned to CPU 5, reproduced the regression. Three alternating runs of
2,000 MiB each had median decoder times of 5.166 seconds for SaRCAsm and
3.613 seconds for C: 43% slower. The host was shared with other workloads;
these timings are not an isolated-machine throughput claim.

A separate hardware-counter run, with all counters active 100% of the
time, measured the following for 2,000 MiB. Counters include the process's
one-time input generation and compression as well as decompression.

| Counter | SaRCAsm | Fil-C C |
|---|---:|---:|
| User instructions | 95.20 billion | 64.71 billion |
| User cycles | 22.78 billion | 16.46 billion |
| User branches | 17.71 billion | 11.23 billion |
| User branch misses | 52.13 million | 51.87 million |
| Task CPU time | 5.047 s | 3.613 s |

The 47% instruction increase and 58% branch increase are much larger than
the 0.5% increase in branch misses. This points toward executing more code,
rather than misprediction, as the main problem.

Separate `cycles:u` profiles at 999 Hz over 5,000 MiB locate 60.34% of the
assembly run's cycles in the X2 Huffman assembly loop, versus 42.80% in
the C loop. Multiplying these shares by each profile's estimated total
cycles suggests the assembly Huffman function costs about twice as much.
The common sequence decoder accounts for approximately the same absolute
cycles in both runs. X1 is not exercised significantly by this input.

Disassembling the actual packaged library reveals two concrete differences:

1. **Three checks per table entry instead of one.** The original assembly
   reads the four-byte entry with a two-byte load and two one-byte loads:

   ```asm
   movzwl 0(%dtable,%rax,4), %r8d
   movzbl 2(%dtable,%rax,4), %r15d
   movzbl 3(%dtable,%rax,4), %eax
   ```

   SaRCAsm emits a capability-null test, lower-bound check, and upper-bound
   check separately for every load. In the packaged X2 function the first
   such sequence spans addresses `0x2be38f` through `0x2be45b`.
   The C source copies `HUF_DEltX2 const entry = dtable[index]`. Its generated
   code checks a four-byte extent once, then performs the same three loads
   (`0x25d588` through `0x25d5c5`). Subsequent checks can also omit the
   already-established non-null test. The difference is check reuse, not
   an unchecked C path or a single combined machine load in the C version.

2. **More stack traffic and larger generated code.** The assembly X2
   function is 17,512 bytes with a 904-byte frame, versus 6,705 bytes and
   520 bytes for C. The assembly repeatedly spills effective addresses and
   reloads table bases, output pointers, and bit containers. About 25% of
   its function-local cycle samples land on stack `mov` instructions and
   26% on comparisons. Instruction samples can skid, so those percentages
   are clues, not independent causal cost measurements.

Over 99% of the assembly function's samples fall in the inner decode/reload
region. Flag save/restore instructions receive under 0.1%; its large
prologue and root initialization are not the dominant cost on this input.

The most direct experiment would replace each three-load table lookup with
one checked 32-bit load and register extraction of the three fields. This
preserves the four-byte entry access and should remove two checks, although
extra shifts and changed register pressure could offset some gain. A more
general SaRCAsm improvement would coalesce proven-compatible access checks,
with appropriate invalidation across calls or capability changes.

Register allocation is a second candidate: the pinned assembler's
`sarcasm.luau` computes spill costs from static def/use counts without loop
frequency weighting. Giving hot-loop uses more weight, and rematerializing
cheap effective addresses instead of spilling them, are plausible next
experiments. Neither improvement has been measured here. Both can be tried
in the package-local assembler without rebuilding LLVM.

The benchmark accepts a decoder and iteration count for profiling:

```sh
perf stat -e task-clock,cycles:u,instructions:u,branches:u,branch-misses:u \
  -- taskset -c 5 /tmp/zstd-bench asm 2000
perf record -o /tmp/zstd-asm.data -e cycles:u -F 999 \
  -- taskset -c 5 /tmp/zstd-bench asm 5000
perf report -i /tmp/zstd-asm.data --stdio --no-children
perf annotate -i /tmp/zstd-asm.data --stdio \
  --symbol pizlonatedFIP1065_HUF_decompress4X2_usingDTable_internal_fast_asm_loop
```

Repeat with `c`, a separate data file, and the symbol ending in
`fast_c_loop`. Profiling worked without sudo on this host. The original
profiles, counters, and disassembly are in `/tmp/filnix-zstd-perf/` on the
development host; that directory is temporary, not a repository artifact.
