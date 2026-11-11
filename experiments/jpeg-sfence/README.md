# JPEG with flag-neutral SFENCE

Explicitly modeling SFENCE speeds up JPEG decompression by 2.23× on the smooth image and 1.47× on the textured image. Compression does not materially change. This experiment changes no main-branch toolchain pin.

The comparison isolates one assembler change. Both builds use the same C compiler, runtime and parser patch. The baseline already uses LAHF/SAHF for arithmetic flags, and the new commit adds only the SFENCE classification and regression coverage.

| Component | Revision |
| --- | --- |
| Baseline assembler | [5bf5b21e](https://github.com/mbrock/fil-c/commit/5bf5b21eda6258062cbec43ec5e8f03fe8207983) |
| Patched assembler | [1f869d1c](https://github.com/mbrock/fil-c/commit/1f869d1c15a797876c1ac3287eaf599a4e1cc8b3) |
| Staging C compiler and runtime | [18b6663a](https://github.com/mbrock/fil-c/commit/18b6663a2785c8eba6cc2a544a7711e19fc448c7) |
| Fil-C branch | `sarcasm-jpeg-flag-neutral` |

## JPEG throughput

These are medians of five rotating-order rounds of libjpeg-turbo 3.1.4's `tjbench`, in megapixels/s. Each operation runs for two seconds after a 0.2-second warmup. Inputs are the earlier experiment's deterministic 2048×2048 RGB images, at quality 90 with 4:2:0 subsampling. The C control sets `JSIMD_FORCENONE=1`; it still uses Fil-C.

| Image | Operation | Baseline | SFENCE patch | Ratio | C, no SIMD |
| --- | --- | ---: | ---: | ---: | ---: |
| Smooth | Compress | 94.81 | 95.40 | 1.006× | 43.46 |
| Smooth | Decompress | 80.91 | 180.26 | 2.228× | 69.35 |
| Textured | Compress | 44.57 | 44.69 | 1.003× | 24.66 |
| Textured | Decompress | 43.38 | 63.56 | 1.465× | 37.80 |

All timings use the same shared KVM orb and logical CPU 2 as the earlier zstd/JPEG experiment: Intel Xeon family 6, model 106, nominally 2.60 GHz. CPU 3 is its SMT sibling. Builds and suites finished before timing; the host is not reserved. Full range divided by median was 3.75%/5.24% for baseline/patched smooth decompression and 10.12%/2.13% for textured decompression. Compression ranges were 5.43–13.80%, so its sub-1% median differences are noise. The C control's ranges were 3.22–11.68%. Encoded JPEG bytes and decoded pixels match before/after for both inputs.

## Only SFENCE was unknown

The inventory covers all 25 nonempty converted SIMD source units. The other two assembly objects are the existing C-fallback stubs for `jidctflt-sse2` and `jchuff-sse2`. Every unknown instruction was SFENCE: 28 sites, seven each in `jdcolor-avx2`, `jdcolor-sse2`, `jdmerge-avx2`, and `jdmerge-sse2`. There are no remaining unknown instructions in these inputs after the patch. No other instruction classification changed.

Disassembly of all 27 assembly objects confirms these counts. The four affected objects change, and the other 23 remain byte-identical.

| Static instruction count | Baseline | SFENCE patch |
| --- | ---: | ---: |
| pushf | 1182 | 20 |
| popf | 1178 | 16 |
| SFENCE | 28 | 28 |
| pushf/popf pairs in the four affected objects | 1162 | 0 |
| pushf/popf pairs in all assembly objects | 1178 | 16 |

Four additional pushf instructions read the direction flag for checked string operations without restoring it. They are not save/restore pairs. The remaining 16 pairs are unchanged in the two downsampling objects, where checked string operations still need them. The hot AVX2 color-conversion object drops from 294 pairs to zero.

## Review and checks preserve the fence

Oracle found no soundness blocker in the actual classifier change. It confirmed that SFENCE neither reads nor writes flags or general-purpose registers, that the assembler retains the fence in order, and that invalid operands and prefixes still reject. Unknown instructions otherwise remain conservative.

The expanded arithmetic-flags fixture passes all four runner modes, including all 131,072 byte add/sub combinations and the existing independent carry/overflow chains. Generated FIP bodies retain both fences around the checked load, use LAHF/SAHF and SETO where needed, and contain no full flag snapshots. A dead-flags store case retains exactly one SFENCE between its stores and emits no snapshots. Independent compilations reject `sfence %rax`, `sfence (%rax)`, `lock sfence`, and `rep sfence` with the expected diagnostics.

Both JPEG builds run all 332 tests and pass 330. The same two documented float-progressive checksum comparisons fail in each: `cjpeg-shared-3x2-float-prog-cmp` and `djpeg-shared-3x2-float-prog-cmp`. There are no new JPEG test failures.

The broader `filc/run-tests --filter '^sarcasm-'` run selects 1113 cases: 1112 pass and `sarcasm-fp-bf16-att` fails with SIGILL. That fixture requires AVX512 in its manifest rather than the existing AVX512BF16 guard. Its old/new generated assembly is identical, and the baseline binary also fails with SIGILL on this CPU. This unrelated test-guard issue remains unchanged.

## Reproduction

Run from the filnix experiment branch in a fresh work directory. The build script deliberately returns nonzero for the two existing checksum failures, after running both suites.

```sh
expr=experiments/jpeg-sfence/default.nix
nix build --impure -f "$expr" oldAssembler newAssembler --no-link -L
bash experiments/zstd-fast-flags/build-jpeg.sh /tmp/jpeg-sfence "$PWD/$expr"
taskset -c 4 python3 experiments/zstd-fast-flags/run-jpeg.py /tmp/jpeg-sfence
```

The measurements initially used a local source override. The pinned package above installs byte-identical SARCASM modules and reproduces the same generated regression assembly. No PR was opened, no main branch was updated, and no experimental binaries were published to a cache.
