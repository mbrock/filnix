# Poison and constant time in Rocq

November 2026. The technical report and primer for [[poison]] semantics
over nanofil's checked IR, pairing Filip Pizlo's
[`projects/zegarmistrz`](https://github.com/pizlonator/fil-c/tree/deluge/projects/zegarmistrz)
emulator with nanofil's Rocq model ([formal.md](formal.md)).
[zegarmistrz.md](zegarmistrz.md) introduces the ideas for a general
reader; this document records the exact state space and propagation
rules of `zegarmistrz`, the bug our formalization found in its store
sanitizer, the two spikes in `rocq/spikes` ([Poison.v](../rocq/spikes/Poison.v)
and [PoisonSbox.v](../rocq/spikes/PoisonSbox.v)), OpenSSL's three
assembly regimes under Fil-C, and how poison lifts to Campaign 7's
[[iris|Iris]] logic and user glibc.

## Zegarmistrz's state and rules, from source

`zegarmistrz` (`pizlonator/fil-c`, `projects/zegarmistrz/src/`) is a
user-mode Linux/x86-64 ELF emulator whose guest virtual addresses equal
host virtual addresses (`memcpy` fast path), with every memory access,
control transfer and ALU op routed through a byte-granular poison map
(`g_poison` in `mem.cpp`) and per-register `Taint` tags (`cpu.h`,
`decode_exec.cpp`).

### Client request ABI and `libpizlo` integration

Guest code talks to the emulator by calling the magic address
`0x1410141014101410` (`RDI = op`, `RSI = ptr`, `RDX = size`,
`RCX = flags`), intercepted before fetch in `decode_exec.cpp`:

- `op = 0`: probe (`RAX = 0` inside `zegarmistrz`, `SIGSEGV` natively);
- `op = 1`: `mem_poison_range(emu, ptr, size, flags)` (ORs `flags & 0xff` into `[ptr, ptr + size)`);
- `op = 2`: `mem_unpoison_range(emu, ptr, size)` (erases entries in `[ptr, ptr + size)`).

Under Fil-C, calling a forged integer function pointer `0x1410141014101410`
from C would fail Fil-C's function [[capability]] check (`NotAFunction`).
`libpizlo` therefore exposes native runtime helpers in
`libpas/src/libpas/filc_runtime.c` (`filc_native_is_in_zegarmistrz` and
`filc_native_zegarmistrz_client_request`, wrapped as
`z_is_in_zegarmistrz` and `z_zegarmistrz_poison` / `z_zegarmistrz_unpoison`
in `<stdfil.h>`), checking the buffer's capability first with
`filc_check_write` before issuing the magic call from native runtime code.

### Memory poison bits and value taint

Each byte in `g_poison` holds an 8-bit mask (`mem.h`), while values in
flight carry three booleans:

| Bit | Mask | Name | Where it lives | Effect |
|---|---|---|---|---|
| 0 | `0x01` | `POISON_CANNOT_LOAD` | memory only (sticky) | Any load overlapping the byte faults (`mem_check_load`). |
| 1 | `0x02` | `POISON_CANNOT_STORE` | memory only (sticky) | Any store overlapping the byte faults (`mem_check_store`). |
| 2 | `0x04` | `POISON_CANNOT_BRANCH` | memory & `Taint` | Faults on `Jcc`, `JMP r/m`, `CALL r/m`, `RET` target, `LOOP`/`JCXZ`, and `SYSCALL` args. |
| 3 | `0x08` | `POISON_CANNOT_INDEX` | memory & `Taint` | Faults on effective-address `base`/`index` of loads, stores, atomics, `XLAT`, gather/scatter, and `SYSCALL` args. |
| 4 | `0x10` | `POISON_CLEAR_BRANCH_ON_STORE` | memory only (sticky) | Clean store clears bit 2 (`CANNOT_BRANCH`). |
| 5 | `0x20` | `POISON_CLEAR_INDEX_ON_STORE` | memory only (sticky) | Clean store clears bit 3 (`CANNOT_INDEX`). |
| 6 | `0x40` | `POISON_CANNOT_VAR_TIME_OP` | memory & `Taint` | Faults when an instruction classified under `--var-time-op=` consumes the value. |
| 7 | `0x80` | `POISON_CLEAR_VAR_TIME_OP_ON_STORE` | memory only (sticky) | Clean store clears bit 6 (`CANNOT_VAR_TIME_OP`). |

Instruction-level rules verified in `decode_exec.cpp` and `syscall.cpp`:

- **Orthogonality (`0x04` vs `0x08`).** `check_branch_taint` inspects
  only `cannot_branch`; `ea_full` inspects only `cannot_index`. `LEA`
  computes its address with `ea_no_index_check`, propagating
  `base_taint | index_taint` into the destination GPR without faulting.
- **Flags and branchless selection.** `CMP`, `TEST` and arithmetic set
  `cpu.flags_taint = a | b`. `Jcc` checks `flags_taint.cannot_branch`,
  whereas `CMOVcc` and `SETcc` do *not* fault: `SETcc` writes a byte
  with `flags_taint`, and `CMOVcc` merges `flags_taint | dst_taint | src_taint`
  (even on the untaken arm, preventing untaken-arm secret laundering).
- **Hardware zeroing idioms.** Same-register `XOR r, r`, `SUB r, r`,
  `SBB r, r` (when `flags_taint` is clean), `PXOR`/`VPXOR x, x, x`,
  `PSUB* x, x` and `XORPS`/`VXORPD` clear the destination's taint to
  `Taint{}` regardless of prior taint.
- **Variable-time hierarchy (`--var-time-op=`).** `known` (default)
  flags `DIV`/`IDIV`, `AAM`, x87 ops and scalar/packed FP `DIV`/`SQRT`
  and arithmetic; `plausible` adds integer `MUL`/`IMUL`, `BSF`/`BSR`,
  `LZCNT`/`TZCNT`/`POPCNT`, variable shifts, `CMPXCHG` and `CRC32`;
  `everything` flags anything outside Intel's DOIT list.
- **SIMD masks and `XMMValue` granularity.** AVX-512 opmask registers
  `k0`–`k7` carry `k_taint[8]`. Masked memory ops check `cannot_branch`
  when fault suppression depends on `k` (or merge `k_taint` into loaded
  elements), and `VPCOMPRESS*`/`VPEXPAND*` propagate `k_taint` because
  active mask bits shift lane positions. One implementation limitation
  exists in `cpu.h`: `XMMValue` currently keeps one `Taint` for the
  whole 64-byte ZMM register rather than per-byte taint, so inserting a
  tainted scalar lane taints sibling lanes (`tests/poison_compress_expand.c`
  faults early at its lane-0 setup load at line 44 rather than at the
  `VPEXPANDQ` test at line 70).

### The `mem_note_store` repeated-store clearing bug

In `src/mem.cpp` (lines 290–357), `mem_note_store` updates `g_poison`
after storing a value with taint `t`. When `t` is clean, lines 294–324
clear any `POISON_CANNOT_X` whose matching `POISON_CLEAR_X_ON_STORE` bit
is set. When `t` is non-empty, however, lines 331–351 invert the branch:

```cpp
if (cb) {
    if (old & POISON_CLEAR_BRANCH_ON_STORE)
        nu &= ~(uint8_t)POISON_CANNOT_BRANCH;
    else
        nu |= (uint8_t)(POISON_CANNOT_BRANCH |
                        POISON_CLEAR_BRANCH_ON_STORE);
}
```

The first secret spill into clean stack memory sets both the branch taint
bit and its clear-on-store flag. When a second secret is spilled to the
same stack slot, the inverted branch sees that clear-on-store flag and
clears the branch taint while leaving the clear-on-store flag set. Every
subsequent secret spill to that slot hits the same branch and leaves the
slot untainted. Overwriting a branch-tainted slot with an index-only
secret also skips the branch check and leaves stale branch taint behind.

[PoisonModel.v](../rocq/theories/logic/PoisonModel.v) and
[PoisonLogic.v](../rocq/theories/logic/PoisonLogic.v) model both the
unpatched C++ update and the repaired monotone update, proving the
repeated-store counterexamples alongside idempotence, clean-store
sanitization, and sticky redzone preservation:

```rocq
Definition note_dim (stored old_taint old_clear : bool) : bool * bool :=
  if stored then (true, true)
  else (if old_clear then false else old_taint, old_clear).

Definition note_store_byte (t : taint) (old : poison_byte) : poison_byte :=
  let (nb, cb) := note_dim (t_branch t) (t_branch (pb_taint old)) (pb_clear_branch old) in
  let (ni, ci) := note_dim (t_index t) (t_index (pb_taint old)) (pb_clear_index old) in
  let (nv, cv) := note_dim (t_vartime t) (t_vartime (pb_taint old)) (pb_clear_vartime old) in
  mkPoisonByte (pb_no_load old) (pb_no_store old) cb ci cv (mkTaint nb ni nv).
```

- [note_store_idempotent]: `note_store_byte t (note_store_byte t old) = note_store_byte t old`.
- [note_store_clean_sanitizes]: when `pb_clear_branch old = true`, `note_store_byte taint_bot old` clears `t_branch`.
- [note_store_sticky_launders]: when `pb_clear_branch old = false`, `note_store_byte taint_bot old` preserves `t_branch` (`poison_launder_branch.c`).
- [buggy_double_store_toggles] and [buggy_third_store_stays_clean]: both the second and third `taint_branch` stores to `pb_clean` under `note_store_byte_buggy` leave `t_branch = false`.

## Mapping poison onto nanofil IR (`Poison.v`)

In native Fil-C, a pointer in registers is two GPRs (`intval` and
[[lower]]) and a pointer in memory splits across payload bytes and the
[[aux]] allocation (`filc.md`). Under native `zegarmistrz`, tainting an
8-byte payload slot taints `intval`, while the aux slot has its own
bytes. Nanofil's [[core-subset|core IR]] makes that split first-class:
a pointer word is `WPtr (mkPtr addr cap)`, memory has [m_bytes] and
[m_aux], and pointer arithmetic ([Flight]), bounds checks
([Check], [HalfCheck], [Renew], ...) and raw memory accesses
([RawLoad], [RawStore], [RawLoadPointer], [RawStorePointer]) are
distinct instructions.

### Word taint, shadow state and policy

[Poison.v](../rocq/spikes/Poison.v) pairs each IR [[word]] class with a
[word_taint] and each machine [config] with a shadow [pstate]:

```rocq
Record taint : Type := mkTaint {
  t_branch : bool;
  t_index : bool;
  t_vartime : bool
}.

Inductive word_taint : Type :=
| WTInt (t : taint)
| WTPtr (t_addr : taint) (t_cap : taint)
| WTLimit (t_cap : taint) (t_len : taint).

Record poison_policy : Type := mkPolicy {
  pol_vartime : vartime_mode;
  pol_check_branches : bool
}.
```

`pol_check_branches` captures the interaction between Fil-C's bounds
checks and `zegarmistrz`:

- **`pol_check_branches = true`** ([pol_default], [pol_strict]):
  every capability check ([Check], [HalfCheck], [Renew],
  [RenewHull], [SpanTest], [RenewIf], [CheckLimit]) faults with
  `CannotBranch` if the checked pointer's address or capability carries
  `t_branch` (or if its capability carries `t_index`, since natively the
  check reads `upper` from `[lower - 16]`). This matches native
  `zegarmistrz` on `filcc` and `nanofil` binaries, where checks lower to
  `cmp + jb/ja` (`EmitInst.v`).
- **`pol_check_branches = false`** ([pol_erased]): models IR after
  static check elimination ([m7.md](m7.md), Campaign 5), where proven
  checks emit no runtime branch.

### Step rules and erasure

[tstep] advances [pstate] alongside [Semantics.step], and [pstep]
combines them so poison checks run *before* the underlying step (a
branch or division on a poisoned value faults as `PTrap` even if the
underlying operation would have trapped or divided by zero):

| IR form | Fault condition in [tstep] | Result taint |
|---|---|---|
| `Let d k (Sub \| Xor) [Tmp x; Tmp x]` | none ([is_zero_idiom]) | `WTInt taint_bot` |
| `Let d k o args` (scalar ALU / `Cmp`) | `op_checks_vartime pol o k && t_vartime (join_taints ts)` | `WTInt (join_taints ts)` (`Cmp` lowers to `cmp + setcc + movzbl` in `EmitOps.v`, never a branch!) |
| `Let d P (Add \| Sub) [pv; ov]` | none | `WTPtr (taint_join ta toff) tc` |
| `Flight d o args lw` | `op_checks_vartime pol o L && t_vartime ta` (never faults on `t_index`, matching `LEA`!) | `WTPtr ta tc` |
| `Check` / `SpanTest` / `HalfCheck` / `Renew` | when `pol_check_branches`: `t_branch ta \|\| t_branch tc \|\| t_index tc` | preserves `(ta, tc)` (or `WTInt taint_bot` for `SpanTest`) |
| `RawLoad t off [av]` | `t_index ta`, `(pol_check_branches && ...)`, `mem_no_load` (`PoisonLoad`) | `WTInt (mem_load_taint pm addr sz)` |
| `RawLoadPointer es off [av]` | `t_index ta \|\| t_index tc`, `(pol_check_branches && ...)`, `mem_no_load` | `WTPtr (mem_load_taint pm addr 8) (ps_aux addr)` |
| `RawStore w off v av` | `t_index ta`, `(pol_check_branches && ...)`, `mem_no_store` (`PoisonStore`) | updates `ps_mem` via [note_store_byte] (and `ps_aux` for `Wp`) |
| `JBranch v t1 t2` | `t_branch tv` (`CannotBranch`) | enters chosen block, substituting [phis_tenv] |
| `Alloc` / `free` | `t_branch \|\| t_index` on size or freed pointer | unpoisons `[base, base + size)` on fresh allocation |

Every non-faulting [pstep] erases directly to [Semantics.step]
([pstep_erases]): poison tracking never changes what any instruction
computes.

> Why can `CannotIndex` alone (`0x08`) not guarantee constant-time memory
> addresses? [index_only_allows_implicit_addr_leak] constructs a
> 4-block function that branches on a secret `s` marked `taint_index`
> (`t_branch = false`), jumps to `L0` or `L1`, and loads from two
> distinct clean addresses `a0 <> a1`. Both runs pass [pstep] without
> trapping, yet emit different load addresses! Sound constant-time
> noninterference requires all three taint bits ([taint_all]).

## Two-run constant-time noninterference (`prun_ct_sound`)

To state what a clean poisoned run *proves*, [Poison.v](../rocq/spikes/Poison.v) defines an
explicit IR-level leakage observation [leak_of] emitted at each step:

- control-flow steps emit the entered block (`LeakEnter`), jump target
  (`LeakGoto`), branch outcome and target (`LeakBranch`), direct call
  callee (`LeakCall`), or return (`LeakRet`);
- memory accesses ([RawLoad], [RawLoadPointer], [RawStore],
  [RawStorePointer]) emit the access kind, effective address and byte
  width (`LeakMem Read addr sz`, `LeakMem Write addr sz`);
- allocation and `free` emit the allocation request or freed word
  (`LeakAlloc`, `LeakFree`);
- scalar `Let` steps whose opcode is classified as variable-time under
  `pol` emit the exact operand words (`LeakVarTime o xs`);
- when `pol_check_branches pol = true`, [Check], [SpanTest],
  [HalfCheck] and [Renew] emit the checked principal pointer
  (`LeakCheck o p`), while [Flight] and the remaining check forms emit
  `LeakPure` (their operand taints are still guarded in [tstep]).

> [leak_of] is an IR-level leakage model, matching CompCert-CT and
> Jasmin's constant-time semantics. Two boundaries sit outside it: first,
> `prun_ct_sound` ranges over deterministic `PNext`/`PDone` traces (heap
> allocations in `PFresh` require an allocator that chooses equal bases
> on equal allocation histories, as `InterpRuntime` does); second,
> preserving IR leakage down to machine code requires the backend not to
> lower branchless IR ops into branches — true of nanofil's `EmitOps.v`,
> which emits integer `Cmp` as `cmp + setcc + movzbl` rather than `Jcc`.

Two configurations `c1` and `c2` satisfy the coupling relation
`[ct_rel] c1 c2 ps` when they sit at the same program point with equal
regions, local frames and fuel, and **every** temporary, byte of
[m_bytes] or capability of [m_aux] on which `c1` and `c2` disagree
carries [taint_all] in `ps`. Single-step soundness ([pstep_ct_sound])
and terminal soundness ([pstep_ct_done]) induct to [prun_ct_sound]:

```rocq
Theorem prun_ct_sound : forall pol ge steps c1 c2 ps o1 ots tr,
  pol_check_branches pol = true ->
  ge_free ge = free_res ->
  ct_rel c1 c2 ps ->
  (o1 = RetVoid \/ o1 = OutOfFuel \/ exists w, o1 = Ret w) ->
  prun pol ge steps c1 ps = PDone o1 ots ->
  prun_trace pol ge steps c1 ps = Some tr ->
  prun_trace pol ge steps c2 ps = Some tr.
```

Read operationally: if **one** concrete execution `(c1, ps)` with secret
inputs marked [taint_all] finishes cleanly without hitting `PTrap`,
then **every** secret-related configuration `c2` runs through the exact
same sequence of control points, passes the exact same Fil-C capability
checks, touches the exact same memory addresses, and emits the exact
same leakage trace `tr`.

## The AES S-box spike (`PoisonSbox.v`)

`rocq/spikes/sbox.c` implements both `subbytes_table` and `subbytes_ct`
over the 256-byte FIPS-197 S-box. `rocq/spikes/code.sh` compiles
`sbox.c` with `nanofil -O --inline=none` and checks that
[SboxCode.v](../rocq/spikes/SboxCode.v) matches the compiler's current
output. [PoisonSbox.v](../rocq/spikes/PoisonSbox.v) decodes the module,
checks `[sbox_valid] : valid sbox_module = Some true`, and proves both the
negative table-lookup faults and universal constant-time noninterference
for `subbytes_ct`.

### Matching native `zegarmistrz` on `subbytes_table`

We compiled `sbox.c` natively with `nanofil -O` + `filcc` and ran it
under the patched `zegarmistrz` binary alongside `PoisonSbox.v`:

1. **`rk` poisoned `0x08` (`taint_index`) under `pol_strict`**:
   natively, Fil-C's bounds check on `sbox + (in[0] ^ rk[0])` passes,
   and the `movzbl` load faults with
   `tainted (cannot-index) value used as address index`. In Rocq, step
   19 (`Check`) steps to `PNext` ([subbytes_table_check_passes_on_index_only])
   and step 20 (`RawLoad`) returns `PTrap CannotIndex`
   ([subbytes_table_traps_cannot_index]).
2. **`rk` poisoned `0x04` (`taint_branch`) under `pol_strict`**:
   natively, `zegarmistrz` faults *inside* Fil-C's bounds check with
   `tainted (cannot-branch) value used in branch condition`. In Rocq,
   step 19 (`Check`) returns `PTrap CannotBranch`
   ([subbytes_table_traps_cannot_branch]).
3. **Check erasure (`pol_erased`, `pol_check_branches = false`)**:
   once redundant checks on `sbox + (0..255)` are discharged, branch-only
   poison (`0x04`) runs all 16 iterations to `PDone RetVoid []` without
   noticing the cache-timing table lookup
   ([subbytes_table_erased_branch_misses]), whereas `taint_index`
   (`0x08`) still traps at step 20 ([subbytes_table_erased_index_traps]).

### Universal 2⁵¹²-pair constant time for `subbytes_ct`

In `subbytes_ct`, the inner loop (`L27` → `L28`) scans `j = 0 .. 255`:

```prolog
% Block L28 of subbytes_ct in SboxCode.v (nanofil -O)
let(tmp(v36), w, cmp(eq, w), [tmp(v24), tmp(pr.3)]),
let(tmp(v37), w, neg, [tmp(v36)]),
let(tmp(v40), p, copy, [global(sbox)]),
let(tmp(v42), l, ext(sw), [tmp(pr.3)]),
flight(tmp(v43), add, [address(tmp(v40)), tmp(v42)], lower(tmp(v40))),
let(tmp(chk2), a, check(0, 1, read, 1), [tmp(v43)]),
let(tmp(v44), w, raw_load(ub, 0), [tmp(chk2)]),
let(tmp(v45), w, and, [tmp(v37), tmp(v44)]),
let(tmp(v46), w, or, [tmp(pr.2), tmp(v45)])
```

`v24` (`in[i] ^ rk[i]`) carries [taint_all]. `cmp(eq, w)` compares
`v24` with `pr.3` (`j`) without branching (`WTInt taint_all`); `neg`,
`and` and `or` propagate `taint_all` into the accumulator `pr.2`;
meanwhile `v43`, `chk2` and `v44` use only `pr.3` (`taint_bot`). After
256 iterations, `L30` stores the tainted byte into `out[i]` (`out`'s
address uses only `i`, `taint_bot`).

Running `vm_compute` on the single all-zero input `(zero_bytes, zero_bytes)`
takes 61,815 steps ([subbytes_ct_ref_runs]), and [prun_ct_sound]
lifts that single witness to every pair of 16-byte inputs and round keys:

```rocq
Theorem subbytes_ct_constant_time :
  exists tr,
    sbox_ct_ref_trace = Some tr /\
    forall (inp1 rk1 inp2 rk2 : Z -> Z),
      prun_trace pol_strict sbox_ge sbox_ct_steps (sbox_ct_cfg inp1 rk1) sbox_ct_ps = Some tr /\
      prun_trace pol_strict sbox_ge sbox_ct_steps (sbox_ct_cfg inp2 rk2) sbox_ct_ps = Some tr.
```

On the FIPS-197 Appendix B 128-bit test vector, [subbytes_table_fips197]
and [subbytes_ct_fips197] confirm both implementations produce the
exact Round-1 `SubBytes(AddRoundKey)` state
`[0xd4; 0x27; 0x11; 0xae; 0xe0; 0xbf; 0x98; 0xf1; 0xb8; 0xb4; 0x5d; 0xe5; 0x1e; 0x41; 0x52; 0x30]`.

## OpenSSL, user glibc, and Iris (`PoisonLogic.v`)

### How Fil-C's three OpenSSL builds fit

1. **`no-asm` C OpenSSL**: compiles directly to IR; `Poison.v`'s rules
   apply directly and reject T-table lookups (`CannotIndex`) and secret
   branches (`CannotBranch`).
2. **`-yolo-assembler` (`ports/openssl.nix`, 3.5.7)**: C forwarders such
   as `aes_asm_forward.c` run `zcheck_readonly(in, 16)` and
   `zcheck(out, 16)` in Fil-C, then cross `zunsafe_fast_call` into
   opaque native `.s` code. At the IR level, `zunsafe_fast_call` is an
   external boundary: neither Campaign 3's memory safety nor `Poison.v`
   can see inside it, which is why dynamic `zegarmistrz` testing on the
   assembled binary caught `_aes_encrypt_compact`'s scalar table lookup.
3. **`SaRCAsm` (`ports/openssl-sarcasm.nix`, 3.6.5, `SARCASM=1`)**:
   OpenSSL's PerlAsm scripts emit `#!` capability directives (`#! void(ptr, ptr, int)`,
   `#! load ptr`, `#! global ptr`), keeping capability safety end-to-end
   without `-yolo-assembler`. Extending nanofil's inline/safe-asm
   contracts ([asm-fixed.md](asm-fixed.md)) with taint summaries
   (`AESENC` / `VPSHUFB` propagate operand taint cleanly without
   `CannotIndex` or `CannotBranch`) lets IR-level constant-time proofs
   compose across `SaRCAsm` primitives.

### User glibc and the `zsys_` boundary

In the user-glibc campaign ([zsys.md](zsys.md), [glibc-ir.md](glibc-ir.md)),
`Poison.v` extends across `libpizlo`'s system-call boundary with two
small additions to `ExternalCalls.v`:

- **Pointer/length check on syscalls**: matching `zegarmistrz`'s
  `syscall_arg_taint` (`syscall.cpp`), every `zsys_*` contract requires
  its syscall number, pointer arguments and buffer lengths to have
  `t_branch = false` and `t_index = false` (passing secret *bytes*
  inside a buffer to `zsys_write` on an encrypted socket is allowed;
  passing a secret *address* or *length* faults).
- **Taint sources**: `zsys_getrandom(buf, n, flags)` or reading a key
  file marks `[buf, buf + ret)` with `pb_secret taint_all` in `ps_mem`.
  Note that user glibc's `strlen` and `memcmp` loop until a byte matches
  and branch on that comparison — so calling `strlen` or `memcmp` on a
  `taint_all` buffer rightly faults with `CannotBranch`, forcing
  constant-time `CRYPTO_memcmp` instead!

### Heap proofs in Iris

[PoisonModel.v](../rocq/theories/logic/PoisonModel.v) contains the operational
semantics and two-run soundness proofs. The old spike import path re-exports
that model, so the AES and memcmp examples keep their existing statements.
[PoisonLogic.v](../rocq/theories/logic/PoisonLogic.v) adds an [[iris|Iris]]
logic for heap-using programs without changing Heap.v, Language.v, Logic.v,
or their clients.

A byte can hold a secret even when its address is public. The proof tracks
both its value and the restrictions on using it, with separate records for
ordinary memory and [[aux]] capability taints. Both records agree with
physical memory. Reads can borrow a share of that ownership; writes must
own the entries they change and preserve every other entry. Allocation
clears byte poison and capability taint throughout the new object. Free
ends the right to access the object, even if a proof retains its byte records.

Helper calls must carry restrictions along with values, including when a
caller resumes after a return. The logic supplies rules for helper calls,
bounds [[check]] and [[renew]] instructions, [[flight]] address arithmetic,
byte and 8-byte word accesses, and aligned pointer accesses with [[aux]]
capability taint. It also covers bounded and unbounded heap allocation,
free, arithmetic, `Select`, block entry, public branches, and returns. More
general rules establish a read, write, allocation, or pure step directly
from the machine. Closed IR functions are supported; external contracts,
variadic calls, raw calls, and argument snapshots are not yet modeled.

[PoisonHeap.v](../rocq/theories/programs/PoisonHeap.v) proves both a small
byte-scratch kernel and a [[validator]]-accepted module over an 8-byte heap
cell. The validated kernel checks every pointer before accessing memory,
advances its input cursor with [[flight]], runs a recursive `Select` loop
over any 32-bit length, reads back the tainted 8-byte cell, frees it, and
returns zero. Separate negative lemmas show that a secret branch and a
secret address are rejected.

The same Hoare triple yields reachable-state memory safety, poison-fault
freedom, and `never_panics` with input key uniqueness proved automatically.
One safe run also transfers allocator readiness to any secret-related
memory and yields equal finite leakage traces together with equal public
return values under the deterministic runtime driver. These traces describe
IR control flow, addresses, and modeled variable-time operations. They do
not establish native hardware timing or trace equality under independently
scheduled collectors.

[CtLt.v](../rocq/theories/programs/CtLt.v) follows OpenSSL's
`constant_time_lt` from C through nanofil's optimized IR to an Iris proof.
It proves poison-fault freedom, machine panic freedom, and equal finite
leakage traces for any two pairs of secret integers. The return mask stays
secret and may differ between the runs. A compiled branch-based control
fails the poison rules. The page explains the helper-call proof and separates
IR constant-time behavior from functional correctness and native timing.
