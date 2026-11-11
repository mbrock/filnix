# How zegarmistrz works

Memory safety keeps a bad pointer from reading someone else's secret. Constant-time cryptography has to keep a secret from steering your own program: which branch it takes, which cache line it touches, and how many cycles an instruction spends on its operands. A cipher can be completely memory-safe and still hand its key to anyone measuring time.

**zegarmistrz** (*watchmaker* in Polish, [`projects/zegarmistrz`](https://github.com/pizlonator/fil-c/tree/deluge/projects/zegarmistrz) in Filip Pizlo's Fil-C repository) is a user-mode Linux x86-64 emulator built to catch those leaks directly on compiled binaries. Programs mark secret buffers with [[poison]] bits; the emulator propagates taint through registers, flags, memory and AVX-512 masks, and stops with a core dump the instant a secret reaches a branch, a memory address or a variable-time instruction. Filip wrote it after watching Valgrind struggle with modern x86-64 SIMD: masked vector loads, gather and scatter, and `VPCOMPRESS` / `VPEXPAND` all need per-lane and mask-aware tracking rather than ad-hoc binary patching.

This page explains the basic idea, why Fil-C and OpenSSL have a special relationship because of it, how the eight poison bits work, and what happens when we move the exact same rules into nanofil's Rocq model ([poison.md](poison.md) has the technical report and proofs).

## Why memory safety is not constant time

Here are two ways to write the `SubBytes(AddRoundKey)` step of AES on a 16-byte block (`rocq/spikes/sbox.c`). Both take a plaintext block `in`, xor each byte with the round key `rk`, and replace the byte through the 256-entry AES `sbox` table:

```c -O
static const unsigned char sbox[256] = {
  0x63, 0x7c, 0x77, 0x7b, 0xf2, 0x6b, 0x6f, 0xc5, 0x30, 0x01, 0x67, 0x2b, 0xfe, 0xd7, 0xab, 0x76,
  0xca, 0x82, 0xc9, 0x7d, 0xfa, 0x59, 0x47, 0xf0, 0xad, 0xd4, 0xa2, 0xaf, 0x9c, 0xa4, 0x72, 0xc0,
  0xb7, 0xfd, 0x93, 0x26, 0x36, 0x3f, 0xf7, 0xcc, 0x34, 0xa5, 0xe5, 0xf1, 0x71, 0xd8, 0x31, 0x15,
  0x04, 0xc7, 0x23, 0xc3, 0x18, 0x96, 0x05, 0x9a, 0x07, 0x12, 0x80, 0xe2, 0xeb, 0x27, 0xb2, 0x75,
  0x09, 0x83, 0x2c, 0x1a, 0x1b, 0x6e, 0x5a, 0xa0, 0x52, 0x3b, 0xd6, 0xb3, 0x29, 0xe3, 0x2f, 0x84,
  0x53, 0xd1, 0x00, 0xed, 0x20, 0xfc, 0xb1, 0x5b, 0x6a, 0xcb, 0xbe, 0x39, 0x4a, 0x4c, 0x58, 0xcf,
  0xd0, 0xef, 0xaa, 0xfb, 0x43, 0x4d, 0x33, 0x85, 0x45, 0xf9, 0x02, 0x7f, 0x50, 0x3c, 0x9f, 0xa8,
  0x51, 0xa3, 0x40, 0x8f, 0x92, 0x9d, 0x38, 0xf5, 0xbc, 0xb6, 0xda, 0x21, 0x10, 0xff, 0xf3, 0xd2,
  0xcd, 0x0c, 0x13, 0xec, 0x5f, 0x97, 0x44, 0x17, 0xc4, 0xa7, 0x7e, 0x3d, 0x64, 0x5d, 0x19, 0x73,
  0x60, 0x81, 0x4f, 0xdc, 0x22, 0x2a, 0x90, 0x88, 0x46, 0xee, 0xb8, 0x14, 0xde, 0x5e, 0x0b, 0xdb,
  0xe0, 0x32, 0x3a, 0x0a, 0x49, 0x06, 0x24, 0x5c, 0xc2, 0xd3, 0xac, 0x62, 0x91, 0x95, 0xe4, 0x79,
  0xe7, 0xc8, 0x37, 0x6d, 0x8d, 0xd5, 0x4e, 0xa9, 0x6c, 0x56, 0xf4, 0xea, 0x65, 0x7a, 0xae, 0x08,
  0xba, 0x78, 0x25, 0x2e, 0x1c, 0xa6, 0xb4, 0xc6, 0xe8, 0xdd, 0x74, 0x1f, 0x4b, 0xbd, 0x8b, 0x8a,
  0x70, 0x3e, 0xb5, 0x66, 0x48, 0x03, 0xf6, 0x0e, 0x61, 0x35, 0x57, 0xb9, 0x86, 0xc1, 0x1d, 0x9e,
  0xe1, 0xf8, 0x98, 0x11, 0x69, 0xd9, 0x8e, 0x94, 0x9b, 0x1e, 0x87, 0xe9, 0xce, 0x55, 0x28, 0xdf,
  0x8c, 0xa1, 0x89, 0x0d, 0xbf, 0xe6, 0x42, 0x68, 0x41, 0x99, 0x2d, 0x0f, 0xb0, 0x54, 0xbb, 0x16
};

void subbytes_table(unsigned char *out, const unsigned char *in,
                    const unsigned char *rk) {
  for (int i = 0; i < 16; i++)
    out[i] = sbox[in[i] ^ rk[i]];
}

void subbytes_ct(unsigned char *out, const unsigned char *in,
                 const unsigned char *rk) {
  for (int i = 0; i < 16; i++) {
    unsigned int idx = in[i] ^ rk[i];
    unsigned int acc = 0;
    for (int j = 0; j < 256; j++) {
      unsigned int mask = -(unsigned int)(idx == (unsigned int)j);
      acc |= mask & (unsigned int)sbox[j];
    }
    out[i] = (unsigned char)acc;
  }
}
```

Both functions are completely memory-safe. Every index `in[i] ^ rk[i]` lies between `0` and `255`, inside the 256-byte `sbox` object; Fil-C's [[capability]] checks pass every time, and neither function can ever panic.

Yet `subbytes_table` leaks the key. A 256-byte table spans four 64-byte L1 cache lines. Which cache line `c: sbox[in[i] ^ rk[i]]` pulls in depends on the top two bits of `c: in[i] ^ rk[i]`. After a handful of blocks with known plaintext or ciphertext, an attacker sharing a core or timing responses recovers `rk` (Daniel J. Bernstein's 2005 cache-timing attack on OpenSSL AES). `subbytes_ct` avoids that by touching every byte `sbox[0]` through `sbox[255]` in fixed order and selecting the matching one with a bitwise mask `0xFFFFFFFF` or `0x00000000`.

Three hardware channels dominate these leaks:

- **Memory addresses**: indexing a table or picking between two buffers with a secret (`c: table[secret]`), which leaves a footprint in data caches and TLBs.
- **Control flow**: branching or jumping on a secret (`if (secret & 1)`), which changes instruction timing, instruction cache lines and branch-predictor state.
- **Variable-time instructions**: feeding a secret to an instruction whose latency depends on its operand values, such as integer division (`DIV`, `IDIV`) or floating-point square root.

> In nanofil's Rocq model those two questions sit side by side over the same [[machine]]. Campaign 3's [valid_no_unchecked] proves a validated module never makes an [[unchecked]] access; Campaign 7's [never_panics] proves a program never hits a [[trap]]; and [Poison.v](../rocq/spikes/Poison.v) asks whether two runs with different secrets emit the exact same trace of branches, checks, addresses and variable-time operands ([prun_ct_sound]).

## Fil-C's OpenSSL trilemma

In ordinary C, serious cryptographic libraries do not trust the compiler to keep `subbytes_ct` branchless. An optimizing pass is well within C's abstract machine if it recognizes `c: mask = -(idx == j)` and turns it back into a conditional jump. So OpenSSL writes its core ciphers, field arithmetic and Montgomery ladders in assembly (generated by Perl scripts, *PerlAsm*), using hardware instructions such as `AESENC`, `VPSHUFB` (bit-sliced VPAES) and `ADCX`/`ADOX`.

For Fil-C ([filc.md](filc.md)), raw assembly is a problem. Fil-C's [[gimso|GIMSO]] guarantee rests on instrumenting every pointer operation in LLVM IR so that capabilities in the [[aux]] allocation stay in lockstep with addresses. Hand-written `.s` files bypass LLVM IR completely. That gives Fil-C three ways to build OpenSSL, and filnix has packaged all three:

```diagram
no-asm: C source ─▶ FilPizlonator ─▶ memory-safe, timing leaks return
zunsafe: C wrapper ─▶ zcheck ─▶ native .s ─▶ fast, unsafe inside asm
SaRCAsm: PerlAsm #! ─▶ sarcasm ─▶ capability-checked constant-time asm
```

| Build | In filnix | Memory safety | Constant time | What happens |
|---|---|---|---|---|
| `no-asm` | `ports/openssl.nix` on non-x86 | Full GIMSO | Lost | OpenSSL drops `AESENC` and `VPAES` and falls back to C tables and compiler-generated branches. |
| `-yolo-assembler` (`zunsafe`) | [`ports/openssl.nix`](https://github.com/mbrock/filnix/blob/main/ports/openssl.nix) (3.5.7) | Checked only at C boundary | Only where OpenSSL's asm is | C forwarders (`aes_asm_forward.c`) call `zcheck_readonly` / `zcheck` on the outer buffers and jump via `zunsafe_fast_call` into uninstrumented `.s` files. |
| `SaRCAsm` (`SARCASM=1`) | [`ports/openssl-sarcasm.nix`](https://github.com/mbrock/filnix/blob/main/ports/openssl-sarcasm.nix) (3.6.5) | Full GIMSO, no `-yolo-assembler` | Preserved where asm is constant-time | PerlAsm scripts emit `#!` capability directives (`#! void(ptr, ptr, int)`, `#! load ptr`, `#! global ptr`); Fil-C's safe assembler checks every access in assembly. |

Two surprises came out of building `zegarmistrz` and testing OpenSSL under it:

1. **Even OpenSSL's x86-64 assembly is not all constant-time.** When `AES-NI` and `SSSE3` (`VPAES`) are unavailable — or masked off through `OPENSSL_ia32cap` — OpenSSL falls back to its generic scalar x86-64 assembly (`crypto/aes/asm/aes-x86_64.pl`), which still indexes a lookup table by secret bytes. That is the exact bug Filip's Discord screenshot caught: `tainted (cannot-index) value used as address index` inside `_aes_encrypt_compact`.
2. **Fil-C's own bounds checks add branches.** Under Fil-C, a pointer check lowers to `cmp` and `jb`/`ja` against the object's [[lower]] and upper bounds. If a pointer's address `sbox + secret` carries a secret offset, Fil-C's bounds [[check]] branches on that address *before* the load ever runs — even when the check always passes!

`SaRCAsm` solves memory safety for OpenSSL's assembly without giving up `AESENC` or `VPAES`, and `zegarmistrz` checks the timing side that memory safety alone never promises.

## Eight bits in memory, three bits in flight

`zegarmistrz` tracks two things: a sparse byte map over guest memory, and a 3-bit taint tag on every register, flag word and SIMD mask.

```diagram
┌─────────────────────────────────────────┐
│ bit 7: clear-var-time-op-on-store (0x80)│   sanitized by clean store
│ bit 6: cannot-var-time-op         (0x40)│   blocks DIV, IDIV, FP
├─────────────────────────────────────────┤
│ bit 5: clear-index-on-store       (0x20)│   sanitized by clean store
│ bit 4: clear-branch-on-store      (0x10)│   sanitized by clean store
├─────────────────────────────────────────┤
│ bit 3: cannot-index               (0x08)│   blocks memory addresses
│ bit 2: cannot-branch              (0x04)│   blocks Jcc, switch, call*
├─────────────────────────────────────────┤
│ bit 1: cannot-store               (0x02)│   redzone: faults on write
│ bit 0: cannot-load                (0x01)│   redzone: faults on read
└─────────────────────────────────────────┘ ← 1 byte of poison shadow
```

Bits `0` and `1` are **access redzones**, like AddressSanitizer's: touching a `cannot-load` or `cannot-store` byte faults immediately. The other six bits govern **secret taint**:

- **`cannot-branch` (`0x04`)** forbids the value from driving control flow: conditional jumps (`Jcc`), indirect jumps and calls, `LOOP`/`JCXZ` counters, and `SYSCALL` arguments. Conditional moves (`CMOVcc`) and `SETcc` do *not* fault — instead, they fold the condition flags' taint into the destination register, because both arms execute without branching.
- **`cannot-index` (`0x08`)** forbids the value from appearing in any effective address (`[base + index*scale + disp]`, `XLAT`, string instructions, gather/scatter indices) or `SYSCALL`. Crucially, x86's `LEA` does *not* touch memory: `LEA` never faults on `cannot-index`, and simply propagates taint to the resulting register.
- **`cannot-var-time-op` (`0x40`)** forbids the value from entering an instruction whose cycle count depends on data. A command-line flag `--var-time-op=` picks how conservative to be:
  - `known` (default): `DIV`, `IDIV`, x87/SSE scalar divides and `SQRT`, BCD (`AAM`), and floating-point arithmetic;
  - `plausible`: adds integer `MUL`/`IMUL`, `BSF`/`BSR`, `LZCNT`/`TZCNT`/`POPCNT`, variable-count shifts on older cores, `CMPXCHG`, `CRC32`;
  - `everything`: anything outside Intel's DOIT (Data Operand Independent Timing) constant-time set.

Why keep `cannot-branch` and `cannot-index` orthogonal instead of using a single `secret` bit, as Valgrind's `ctgrind` does? Because diagnostics and partial annotations need them apart. Marking a secret key `cannot-index` alone tests strictly for cache-timing table lookups even in code that makes benign secret-dependent branches; marking a value `cannot-branch` alone tests strictly for control-flow leaks.

> When you want *full* constant-time security, you must set all three bits together (`0x4C`, [taint_all] in Rocq). [Poison.v](../rocq/spikes/Poison.v) proves a small constructive counterexample, [index_only_allows_implicit_addr_leak]: if a secret is marked `cannot-index` *without* `cannot-branch`, the program `if (secret == 0) p = q0; else p = q1; *p` branches on `secret` without faulting and then dereferences clean pointers `q0` or `q1` at two different addresses! Only `cannot-branch` + `cannot-index` together close both direct and implicit address leaks.

### Propagation, zeroing idioms, and store sanitization

Through ALU operations, taint combines by bitwise OR (`t1 | t2`), with one hardware-accurate exception: self-cancelling idioms such as `XOR EAX, EAX`, `SUB RAX, RAX` and `PXOR XMM0, XMM0` produce a constant zero regardless of the register's old bits, so `zegarmistrz` clears the destination's taint to clean ([is_zero_idiom] in Rocq).

Memory stores distinguish two kinds of poisoned locations using the `clear-*-on-store` bits (`0x10`, `0x20`, `0x80`):

- **Sticky poison** (`cannot-branch` *without* `clear-branch-on-store`): storing clean data into the slot does *not* clear its poison. Reading the slot back taints the clean data. Tests use this to model an untrusted or permanently secret region that cannot be sanitized by overwriting.
- **Clear-on-store poison** (`cannot-branch | clear-branch-on-store`): storing a *tainted* value to normal scratch memory (such as spilling a register to the stack) sets both the taint bit and its matching `clear-*-on-store` bit. Later, when the stack slot is reused for a *clean* variable, the clean store sees `clear-*-on-store` and clears the taint bit so unrelated code does not false-fault.

> Formalizing `mem_note_store` in Rocq uncovered a subtle bug in `zegarmistrz`'s C++ implementation (`src/mem.cpp`): when a *second* tainted value was stored to a slot that already carried `CLEAR_X_ON_STORE` from an earlier tainted spill, an inverted `if` branch cleared `CANNOT_X` instead of keeping it set ([buggy_double_store_toggles]). Every odd spill left the stack slot tainted; every even spill silently laundered the secret! In [Poison.v](../rocq/spikes/Poison.v), [note_store_byte] makes tainted stores monotone and idempotent ([note_store_idempotent]) while keeping clean-store sanitization ([note_store_clean_sanitizes]) and sticky redzones ([note_store_sticky_launders]).

## Moving the watchmaker into nanofil's Rocq model

In `zegarmistrz`, a program runs on **one** concrete input — say an all-zero plaintext and an all-zero key marked `0x4C` (`cannot-branch | cannot-index | cannot-var-time-op`). Why should one clean test run convince anyone about the other 2²⁵⁶ − 1 keys?

Because every place where two runs with different keys could diverge in their observable behavior is guarded by a taint check:

```diagram
sbox.c  two AES SubBytes functions, table lookup and masked scan
  │ nanofil -O
  ▼
SboxCode.v  checked nanofil IR, validated by sbox_valid
  │ pstep (pol_strict, taint_all on in and rk)
  ▼
subbytes_ct_ref_runs  one concrete 0^16 run finishes cleanly in 61,815 steps
  │ prun_ct_sound (2-run relational noninterference)
  ▼
subbytes_ct_constant_time  all 2^512 input/key pairs emit the exact same trace
```

In [Poison.v](../rocq/spikes/Poison.v), we pair nanofil's operational semantics ([Semantics.step]) with a shadow poison state [pstate] that tracks byte poison on [m_bytes], capability taint on [m_aux], and `(address_taint, cap_taint)` pairs on every [[flight-pointer|flight pointer]] in the [[ssa|SSA]] environment:

- **[[flight]]** (`v30 = flight add (address sbox, offset) (lower sbox)`) is nanofil's `LEA`: it computes pointer arithmetic without touching memory, so just like `zegarmistrz`'s `LEA` it never faults on `cannot-index` and carries the offset's taint into `v30`'s address taint.
- **[[check]]** (`chk2 = check [0; 1; read; 1] v30`) is Fil-C's bounds check. Under [pol_strict] (`pol_check_branches = true`), it checks `cannot-branch` on `v30`'s address, matching native x86-64 emission (`cmp + jb/ja`). Under [pol_erased] (`pol_check_branches = false`), representing code whose checks Campaign 5's optimizer has proved redundant and removed, `check` does not branch.
- **[[raw-access|raw_load / raw_store]]** checks `cannot-index` on the pointer's address taint and `cannot-load` / `cannot-store` on the target bytes, then propagates byte taint (and `m_aux` capability taint for pointer loads and stores).

Running both functions from `sbox.c` in [PoisonSbox.v](../rocq/spikes/PoisonSbox.v) reproduces every native `zegarmistrz` behavior step for step — and then proves what an emulator alone cannot:

| Function | Poison on `rk` | Policy | Outcome in `PoisonSbox.v` | Why |
|---|---|---|---|---|
| `subbytes_table` | `taint_index` (`0x08`) | `pol_strict` | `PTrap CannotIndex` at step 20 ([subbytes_table_traps_cannot_index]) | `Flight` taints `v30`'s address; `Check` at step 19 passes (`t_branch = false`); `RawLoad` faults on `cannot-index`. |
| `subbytes_table` | `taint_branch` (`0x04`) | `pol_strict` | `PTrap CannotBranch` at step 19 ([subbytes_table_traps_cannot_branch]) | Fil-C's `Check` branches (`cmp + jb/ja`) on `sbox + (in[0] ^ rk[0])` one step *before* `RawLoad`. |
| `subbytes_table` | `taint_branch` (`0x04`) | `pol_erased` | `PDone RetVoid` ([subbytes_table_erased_branch_misses]) | With bounds checks discharged, no branch depends on `rk`; `cannot-branch` alone misses a pure table lookup. |
| `subbytes_table` | `taint_index` (`0x08`) | `pol_erased` | `PTrap CannotIndex` at step 20 ([subbytes_table_erased_index_traps]) | `RawLoad` still catches the secret-indexed table access after check erasure. |
| `subbytes_ct` | `taint_all` (`0x4C`) | `pol_strict` | `PDone RetVoid`, universal trace equality ([subbytes_ct_constant_time]) | Every branch, `Check`, and address uses only loop counters `i` and `j`; [prun_ct_sound] lifts the single `0^16` run to all 2⁵¹² pairs of 16-byte inputs and keys. |

One concrete tainted execution in `vm_compute`, combined with [prun_ct_sound], turns dynamic taint checking into a universal constant-time proof over every secret key. [Poison and constant time in Rocq](poison.md) walks through the exact definitions, leakage model, coupling invariant and proofs.
