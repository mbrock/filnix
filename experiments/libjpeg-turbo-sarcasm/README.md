# libjpeg-turbo's x86-64 SIMD through SaRCAsm

This experiment builds libjpeg-turbo 3.1.4 for Fil-C with its hand-written
x86-64 NASM SIMD (SSE2 and AVX2) assembled by SaRCAsm. The packaged
libjpeg-turbo port uses a different approach: the Arm Neon intrinsics
translated by SIMDe (`patches/libjpeg-turbo-simde-neon.patch`).

```sh
experiments/libjpeg-turbo-sarcasm/run.sh .amp/in/sarc-run
```

## Pipeline

SaRCAsm reads GNU as input; libjpeg-turbo is written for NASM.
`run.sh` points CMake's `CMAKE_ASM_NASM_COMPILER` at `filc-nasm`, which:

1. preprocesses each file with `nasm -E -D__FILC__`, expanding NASM macros;
2. converts the result with `nasm2gas.py` to GNU as Intel syntax;
3. assembles it with Fil-C clang, whose `.s` assembler is SaRCAsm.

The converter's output assembles with GNU as to the same instructions and
`.rodata` bytes as NASM's output for all 27 files, apart from equivalent
encodings (NASM shortens `mov r64, imm` to `mov r32, imm`).

Beyond syntax, the converter adds what SaRCAsm needs:

- Signatures on function labels and direct calls, derived from `jsimd.h`
  (`sigs.txt`).
- `#! load ptr` on every 8-byte GPR load and `#! store ptr` on every 8-byte
  GPR store. In these kernels those are the `JSAMPARRAY`/`JSAMPROW` row
  pointers.
- Constant folding of NASM's macro arithmetic (`[(r11) + (1) * 8 * (2)]`),
  which SaRCAsm's Intel parser rejects.
- Push/pop pairs after the prologue become moves through SaRCAsm
  pseudo-registers (`%fil_s0`, ...). SaRCAsm models pushes as frame slots and
  cannot follow a register redefined between its push and its pop, as the
  colour converters' per-row saves do.
- `.rept` data is expanded (see "SaRCAsm issues").

Source changes (`libjpeg-turbo-sarcasm.patch`, applied after the port patch):

- `jchuff-sse2.asm`: the byte emitter stores `bh`, a high-byte register that
  SaRCAsm's bounds-check rewrite cannot combine with REX registers. It now
  shifts `rbx` by 8 and stores `bl`.
- `jdmrgext-{sse2,avx2}.asm`: `jsimd_h2v2_merged_upsample_*` builds a
  `JSAMPIMAGE` on its stack and passes its address to the h2v1 kernel. Under
  `__FILC__` it allocates the array with SaRCAsm's `.alloca` instead
  (spelled `FILC_ALLOCA` in NASM).
- `jsimd.c`: the float IDCT and Huffman encoder SIMD are disabled under
  Fil-C (below); `jpeg_nbits.c` then defines `jpeg_nbits_table` for the C
  Huffman encoder.

## Results

330 of 332 libjpeg-turbo tests pass. The two failures compare 3x2 float
progressive output: the float forward DCT is the SSE assembly while the
float inverse DCT falls back to C, a combination neither `FLOATTEST8`
expectation describes. The SaRCAsm build's `cjpeg -dct float` output is
byte-identical to native NASM libjpeg-turbo's, progressive and baseline.

Two kernels still use C: `jidctflt-sse2.asm` and `jchuff-sse2.asm` walk a
pointer through a stack workspace (`add rdi, 128` in a loop;
`lea rdi, [rdi + rcx * 2]`). SaRCAsm's `#! stack buffer` by-address
annotations should cover this, but the float IDCT's workspace sits below an
`lea rsp, [r15 - 288]` that SaRCAsm's frame model does not count as
allocated, and the encoder's walk was rejected as a read of an `rsp` save.
`stackbufs.txt` holds the attempted annotations.

libtiff inspect-plus-decode (median ms, `.amp/in/tiffbench`-style 2048x2048
strip images, 2026-10-15, shared cloud host):

| libjpeg-turbo | smooth JPEG | textured JPEG |
|---|---:|---:|
| native, NASM SIMD | 10.1 | 29.5 |
| native, no SIMD | 23.4 | 47.1 |
| Fil-C, C | 84.4 | 119.0 |
| Fil-C, SIMDe Neon (packaged) | 32.2 | 62.5 |
| Fil-C, SaRCAsm AVX2 | 65.3 | 92.9 |

The SaRCAsm build is about twice as slow as the SIMDe build. Half its
samples are in `jsimd_ycc_rgb_convert_avx2`, and most of those are spent
checking constant-table loads such as `vpaddw PW_ONE(%rip), ...`. Each
expands to two `lea`s, spills, `pushf`/`popf`, a null test and both bound
compares, although the object, its size and the offset are all known when
assembling. Clang's Fil-C pass hoists or removes the equivalent checks in
the SIMDe build. Statically discharging in-bounds rip-relative accesses to
read-only same-file data would remove most of this overhead.

## SaRCAsm issues found

The first two are fixed upstream after 0.686 (pizlonator/fil-c#336 and
#337), which the staging toolchain includes (check: `staging-sarcasm-fixes`). With the second fix the
reproducer is rejected at compile time instead of miscompiled. The
experiment still uses the release toolchain, where `.rept` is expanded by
`nasm2gas.py` and the merged upsampler uses `.alloca`.

1. **`.rept` in data is silently dropped.** A `.rept` block in `.rodata`
   produced an 8-byte zero object, and the labels inside it were left
   undefined, so the failure surfaced only at link time. Other
   unsupported directives are rejected.
2. **Pointers stored into an escaping frame are lost.**
   `repro/escaping-frame.s` stores two pointers into its frame with
   `#! store ptr`, takes the frame's address with `lea rdi, [rsp]`, and
   passes it to C. The C side reads the string's bytes instead of the
   pointers, with no capability, and traps. The README describes escape
   promotion for this shape. The failure is safe, but the program is
   wrong.

   ```sh
   cc=$(nix build --no-link --print-out-paths .#filcc)/bin/clang
   s=$(nix build --no-link --print-out-paths .#sarcasm)
   d=experiments/libjpeg-turbo-sarcasm/repro
   $cc --filc-resource-dir=$s -c $d/escaping-frame.s -o esc.o
   $cc $d/escaping-frame-main.c esc.o -o esc && ./esc
   ```

3. **Constant-table accesses are checked at run time** (see Results).
