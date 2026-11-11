# SARCASM flag snapshots

This experiment measures cheaper flag saves in SARCASM and their effect on
OpenSSL 3.6.5. The patch is on `mbrock/fil-c` branch `sarcasm-fast-flags`, at
`7cafb5c30f5f126b38105cf179537d0244b313c3`. It does not change either main branch
or filnix's toolchain pin.

The experimental assembler requires LAHF/SAHF support in 64-bit mode
(CPUID.80000001H:ECX[0]). It has no runtime feature dispatch for this requirement.

## The assembler uses the existing liveness analysis

SARCASM already omits flag saves when its per-flag CFG analysis finds no live
flags. The patch passes that analysis's mask to x86 code generation instead of
reducing it to a boolean. Live arithmetic flags use `lahf` and `sahf`. When OF
is live, `seto %al` saves it and `addb $127,%al` restores it before `sahf`.
The allocator sees RAX as a scratch register and keeps program values clear of
it. The saved virtual value may spill or survive a runtime call.

DF-live and unknown masks still use the full RFLAGS stack round-trip. The
string-operation DF probe and explicit input flag-stack operations are unchanged.
ARM64 output is unchanged for the two flag fixtures compared here.

## Real Montgomery assembly gets faster

These are medians of three alternating before/after rounds on one Linux orb
with an Intel Xeon family 6, model 106 CPU at a reported 2.60 GHz. Each native
benchmark process was pinned to logical CPU 2. Other validation work ran on
the orb during measurement, so these are local measurements rather than
isolated-machine performance guarantees.

| Workload | Before | After | Speedup |
| --- | ---: | ---: | ---: |
| Extracted `bn_add_words` assembly | 35.79 ns/word | 3.86 ns/word | 9.27× |
| Extracted `bn_sub_words` assembly | 33.48 ns/word | 3.77 ns/word | 8.88× |
| Library `bn_mul_mont`, 17 limbs | 8,530.82 ns/call | 2,224.93 ns/call | 3.83× |
| Library `bn_mulx4x_mont`, 32 limbs | 40,511.01 ns/call | 7,564.13 ns/call | 5.36× |
| RSA-2048 signing | 475.0 ops/s | 839.9 ops/s | 1.77× |
| RSA-2048 verification | 1,279.3 ops/s | 6,286.7 ops/s | 4.91× |

The extracted loops are the fixtures in `../ct-bn-add`, not the implementations
linked into this OpenSSL port. The port's `x86_64-gcc.c` patch selects the C
fallbacks for `bn_add_words` and `bn_sub_words` under `__FILC__`. Their measured
medians were 0.88 → 0.91 ns/word and 1.02 → 1.11 ns/word respectively. They
show no speedup from changing the assembler.

The library contains SARCASM-compiled Montgomery, Montgomery gather/scatter,
RSAZ, elliptic-curve, AES, GHASH, ChaCha/Poly1305, SHA and Keccak assembly,
among other modules. CPU dispatch chooses which implementations run.
The direct Montgomery calls above establish the executed assembly paths:
17 limbs selects the general multiplication path, while the second test calls
the BMI2/ADX helper directly. Both come from `crypto/bn/asm/x86_64-mont.pl`.
Its `.Linner` loop loads memory between `addq` and `adcq`, and its ADX loops
interleave `adcx` and `adox` with checked accesses. Disassembly confirms that
their inserted flag saves use `lahf`/`sahf` after the patch. RSA helper dispatch
was not traced individually.

`bench.c` links the actual `libcrypto.a`. It checks the add/sub results and
returned carry with independent C arithmetic. Its Montgomery reference uses
schoolbook multiplication modulo \(2^{64n} - 1\), for which the Montgomery factor
is 1. It times 100,000 calls on 512-word add/sub buffers and 20,000 calls for
each Montgomery path. RSA uses `openssl speed -elapsed -seconds 3 rsa2048`;
the table uses the first RSA signing/verification row.

## Correctness and poison checks pass

The rebuilt OpenSSL's complete enabled suite reported:

```text
All tests successful.
Files=353, Tests=4569, 559 wallclock secs
Result: PASS
```

A redundant verbose suite run in a copied build tree reached its 600-second
timeout without an assertion failure. The full-suite pass above came from the
completed Nix build, not from treating that incomplete rerun as successful.

The SARCASM checks passed 31 existing x86 test cases in normal, stop-the-world,
and rage/scribble/verify GC modes. The extended flag test checks all 131,072
byte add/sub operand combinations and all four input CF/OF combinations in
interleaved ADCX/ADOX chains. The ADCX/ADOX part is CPUID-gated on other hosts.
Two ARM64 flag fixtures emitted identical assembly before and after.

An independent Python program checked the results of 176 extracted add/sub
runs. These covered empty inputs, carries and borrows across multiple words,
and randomized operands. Both attempts to access memory beyond the buffers
produced a Fil-C safety panic.

A scratch build forced every loop poll to call `filc_pollcheck_slow`. Six
add/sub cases still matched the reference results when the saved flags spilled
to the stack across that returning runtime call.

Zegarmistrz with `../ct-memcmp/zegarmistrz-keep-taint.patch` poisoned both secret
operands with 0x4c: cannot-branch, cannot-index and cannot-var-time-op. All 12
extracted constant-time runs were clean, and all six branchy controls were
caught. The real-library add, sub, general Montgomery and ADX Montgomery
checks were also clean before and after, with independently checked results.
The poison-check mode does not collect timing data while operands are tainted.
These are executed checks, not a proof of constant time on physical hardware.

## Rebuild without changing the toolchain pin

From the filnix root, the expression builds the remote assembler commit and
uses it only for this OpenSSL build. The `after` derivation retains the port's
full test suite. Building it can take several minutes.

```sh
expr=experiments/sarcasm-fast-flags/default.nix
before=$(nix build --impure -f "$expr" before.out --no-link --print-out-paths)
after=$(nix build --impure -f "$expr" after.out --no-link --print-out-paths)
filcc=$(nix build .#filcc-staging --no-link --print-out-paths)/bin/clang
as experiments/ct-memcmp/zeg.s -o /tmp/fast-flags-zeg.o
zlib=$(nix eval --raw .#legacyPackages.x86_64-linux.pkgsFilc.zlib.outPath)
for version in before after; do
    eval 'library=$'"$version"
    "$filcc" -O2 -g -yolo-assembler \
        experiments/sarcasm-fast-flags/bench.c /tmp/fast-flags-zeg.o \
        "$library/lib/libcrypto.a" -L"$zlib/lib" -lz -ldl -pthread \
        -o "/tmp/fast-flags-$version"
    taskset -c 2 "/tmp/fast-flags-$version" bench
done
```

The benchmark's direct ADX call requires BMI2 and ADX. For poison checking,
run each benchmark binary as `zegarmistrz --no-core BINARY check 0x4c` using
the keep-taint emulator built by the neighboring experiment.
