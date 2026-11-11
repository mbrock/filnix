# SARCASM flag snapshots in zstd and libjpeg-turbo

The LAHF/SAHF patch does not change zstd's Huffman decoder code or the
libjpeg-turbo experiment's SIMD objects. Their timing differences are noise,
not a speedup from this patch. Neither filnix's main branch nor its toolchain
pins change in this experiment.

## The builds isolate one assembler commit

`default.nix` uses the staging compiler and runtime pinned at
`18b6663a2785c8eba6cc2a544a7711e19fc448c7`. The old assembler is
`9b7584cea1fa0faf52ffec67859d3b7342919783`. The new assembler is its single
child, `5bf5b21eda6258062cbec43ec5e8f03fe8207983`. Both receive the same
existing semicolon-parser backport needed by zstd's macros.

The experiment starts from filnix `ec452b78f72c3055bf0830c6f4dee08b63d50faf`.
It reuses `ports/zstd-sarcasm.nix`'s assembly adaptation and the fixtures in
`tests/zstd-sarcasm*`. The earlier work is described in
[`docs/zstd-sarcasm.md`](../../docs/zstd-sarcasm.md) and began in commits
`1dede322` and `c7ea6826`.

All four zstd 1.5.7 variants compile C with the same Fil-C toolchain and
optimization settings. `base` disables standalone assembly. `before` and
`after` assemble the annotated Huffman loops with the old and new assembler.
`yolo` assembles zstd's original uninstrumented loops with GNU as. Its
benchmark-only C forwarders use `zunsafe_fast_call` and reconstruct returned
input/output pointers with their original capabilities. This control is
unchecked and is not a proposal to ship it.

## zstd's generated machine code does not change

The complete `.text` sections of the old and new `libzstd.so.1.5.7` are
byte-identical, with SHA-256
`91ce9dc0a167d2655c5cc292654b69825b7ea4a56eddeedeb9a5b3f9e51f7961`.
Neither decoder emits flag snapshots. This patch cannot improve those loops.
The earlier profiling report instead identified redundant table-access
checks and spills.

`run.py` benchmarks compression and decompression at levels 1, 3, and 9.
It uses the earlier fixture's deterministic 16-symbol LCG input, repeated
four times to make 4 MiB, and the sorted concatenation of zstd's `.c` and
`.h` files, totaling 5,231,666 bytes. The repeated input permits long-distance
matches at some levels; the original 1 MiB fixture below avoids that change.

These are medians of five rotating-order rounds on one shared KVM orb,
pinned to logical CPU 2 of an Intel Xeon family 6, model 106, nominally
2.60 GHz. CPU 3 is its SMT sibling. Local builds and suites finished before
timing. The VM host was not reserved. `zstd -bLEVEL -i1` times each operation
for at least one second and reports its best internal sample. The harness
now uses `-q` to emit the final rates without progress updates.

### Decompression throughput

All values are decimal MB/s. The C and yolo columns still use Fil-C for C
code; yolo is not a fully native build.

| Input | Level | Old SARCASM | Patched SARCASM | C, no assembly | Unchecked/yolo |
| --- | ---: | ---: | ---: | ---: | ---: |
| 16 symbols, 4 MiB | 1 | 347.5 | 356.1 | 888.4 | 2110.7 |
| 16 symbols, 4 MiB | 3 | 1068.9 | 1057.5 | 1816.6 | 2262.4 |
| 16 symbols, 4 MiB | 9 | 1016.2 | 1021.3 | 1065.8 | 1278.4 |
| zstd source | 1 | 551.7 | 541.3 | 654.3 | 678.2 |
| zstd source | 3 | 570.2 | 572.6 | 583.8 | 560.0 |
| zstd source | 9 | 655.9 | 652.4 | 686.7 | 643.3 |

### Compression throughput

Compression does not use the standalone Huffman decoder assembly. These
measurements are controls, not expected beneficiaries of the patch.

| Input | Level | Old SARCASM | Patched SARCASM | C, no assembly | Unchecked/yolo |
| --- | ---: | ---: | ---: | ---: | ---: |
| 16 symbols, 4 MiB | 1 | 277.1 | 279.5 | 274.3 | 272.5 |
| 16 symbols, 4 MiB | 3 | 223.5 | 215.6 | 222.4 | 214.8 |
| 16 symbols, 4 MiB | 9 | 65.9 | 67.4 | 59.7 | 66.6 |
| zstd source | 1 | 188.9 | 187.4 | 182.7 | 183.9 |
| zstd source | 3 | 137.4 | 138.6 | 132.7 | 138.5 |
| zstd source | 9 | 29.2 | 29.9 | 27.7 | 28.0 |

The five-run full range divided by the median spans 1.4–44.2% for
decompression and 1.8–44.1% for compression across these rows. Old/new
decompression medians differ by −1.9% to +2.5%, despite identical code.
These noisy samples do not support fine-grained comparisons between C and
yolo where the rates are close.

### The original 1 MiB fixture still favors C

The existing `tests/zstd-sarcasm-bench.c` compresses one deterministic 1 MiB
16-symbol input at level 3, then repeatedly decodes the same frame with
output validation. Five rotating-order rounds of 2,000 decodes gave:

| Decoder | Median seconds for 2,000 MiB | Full range / median |
| --- | ---: | ---: |
| Old SARCASM | 6.940 | 4.7% |
| Patched SARCASM | 7.086 | 6.7% |
| C, no assembly | 4.066 | 6.8% |
| Unchecked/yolo | 3.054 | 7.6% |

Patched SARCASM takes 1.74× as long as C on this fixture. Compile the existing
harness against `before.dev`'s headers and `before.out`'s shared library,
then select each variant with `LD_LIBRARY_PATH=LIBRARY/lib` and run
`taskset -c 2 /tmp/zstd-bench asm 2000`. The harness prints `SaRCAsm` for the
enabled path even when the selected library is the C-only or yolo build;
the library selection determines which decoder actually executes.

## The JPEG experiment retains full flag snapshots

`build-jpeg.sh` reuses `experiments/libjpeg-turbo-sarcasm`'s NASM conversion,
signatures and source patches. It uses the same staging C compiler as zstd
and varies only the assembler. All 27 SIMD object files are byte-identical
before and after. The hot `jdcolor-avx2` source contains `sfence`, which the
assembler classifies as unknown. `transform.luau` assigns unknown
instructions an all-bits flag-use mask, so the new emitter correctly keeps
full pushf/popf snapshots. The generated color-conversion assembly retains
294 snapshot pairs in each build.

`run-jpeg.py` uses libjpeg-turbo 3.1.4's own `tjbench` on deterministic
2048×2048 smooth and textured RGB inputs, quality 90, 4:2:0 subsampling.
It rotates old/new/C order for five rounds, with two seconds per operation
and a 0.2-second warmup, on the same CPU 2. The C control sets
`JSIMD_FORCENONE=1`. Values are megapixels/s.

| Image | Operation | Old SARCASM | Patched SARCASM | C, no SIMD |
| --- | --- | ---: | ---: | ---: |
| Smooth | Compress | 94.85 | 93.36 | 45.20 |
| Smooth | Decompress | 79.71 | 79.65 | 68.36 |
| Textured | Compress | 44.14 | 45.48 | 25.07 |
| Textured | Decompress | 43.20 | 43.85 | 38.54 |

The five-run full ranges are 1.6–7.9% of their medians. Old/new medians
differ by −1.6% to +3.0%, again with unchanged assembly. A separate carry-loop
positive control emits eight pushf/popf pairs before and eight LAHF/SAHF
pairs after, confirming that the assembler override is effective.

The explicit safe-assembly consumers found in filnix are packaged
`openssl-sarcasm`, experimental `zstd-sarcasm`, and this libjpeg-turbo
experiment. Default OpenSSL uses native forwarders, default libjpeg-turbo
uses SIMDe, and GMP, Nettle and libgcrypt disable their assembly backends.
Inline compiler assembly is not automatically a SARCASM consumer.

## The focused zstd checks and bounded upstream suites pass

Both old and patched builds pass the existing strict SARCASM check:
200 direct X1/X2 comparisons, parser/access tests, expected missing-capability
and bounds traps, and 36 native/Fil-C round trips each. The yolo build also
passes 36 cross-codec round trips against the no-assembly build. No CLI
benchmark reports a checksum failure.

The patched build additionally passes zstd's upstream `fuzzer -i100` and
`zstreamtest -i100`, including their startup unit tests. Their decisive
output is `100 fuzzer tests completed` and `101 fuzzer tests completed`.
This is a bounded run, not zstd's entire CLI suite or a long fuzz campaign.

Both JPEG builds pass 330/332 upstream tests. They retain the same two
documented float-progressive checksum failures:
`cjpeg-shared-3x2-float-prog-cmp` and
`djpeg-shared-3x2-float-prog-cmp`. Encoded JPEG bytes and decoded pixels are
identical before/after for both benchmark images.

## Reproduction

Run these commands from this branch in a fresh work directory. No toolchain
pin needs to move.

```sh
expr=experiments/zstd-fast-flags/default.nix
nix build --impure -f "$expr" beforeCheck afterCheck upstreamAfter --no-link -L
python3 experiments/zstd-fast-flags/run.py /tmp/zstd-flags-cli
bash experiments/zstd-fast-flags/build-jpeg.sh /tmp/zstd-flags-jpeg
# The JPEG build script returns nonzero for the two documented test failures.
python3 experiments/zstd-fast-flags/run-jpeg.py /tmp/zstd-flags-jpeg
```

Keep the no-assembly zstd default. The next zstd experiment should target
table-check coalescing or spills. For JPEG, explicitly modeling `sfence`'s
flag effects is a separate assembler change worth reviewing before another
performance experiment; it is not part of this patch or this harness.
