# OpenSSL's CRYPTO_memcmp three ways: unchecked, SaRCAsm and nanofil

This experiment takes one small piece of hand-written constant-time
assembly and asks what each route to running it under Fil-C keeps. The
kernel is `CRYPTO_memcmp` from OpenSSL 3.6 (`crypto/x86_64cpuid.pl`), 24
instructions that compare two buffers without branching on their bytes.
Beside it is a control, `leaky_memcmp`, which has the same contract but
leaves at the first difference.

The three routes are:

- **unchecked**: the assembly as `as` assembles it, called from Fil-C with
  `zunsafe_fast_call`. This is what `-yolo-assembler` gives: the original
  instructions and no memory safety.
- **SaRCAsm**: the same file through Fil-C's assembler, which keeps each
  instruction and puts Fil-C's checks before each memory access.
- **nanofil**: a translation of the assembly into nanofil's IR, written by
  hand, which nanofil then checks, optimizes and prints as new assembly.
  The original instructions are not kept. This is the re-emit route; no
  model of x86 is involved.

```sh
./run.sh [WORKDIR]               # everything below except the Rocq check
./poison.sh POISON.v [WORKDIR]   # the Rocq check; see "The poison spike"
```

## The files

| File | What it is |
| --- | --- |
| `memcmp.s` | `CRYPTO_memcmp` as perlasm prints it, renamed `ct_memcmp`, and `leaky_memcmp`. Each label has a SaRCAsm signature (`#! int(ptr,ptr,size_t)`), which plain `as` reads as a comment, so one file serves two builds. Each instruction is numbered. |
| `memcmp.ir` | The hand translation. Each IR instruction cites the number of the machine instruction it stands for. |
| `drive.ir` | Two functions that allocate buffers and call the kernels, with 21 `run` lines, so that nanofil's interpreter, its native code and the Rocq model can run the IR. |
| `harness.c` | A Fil-C program that calls the kernels of whichever build it is linked with, and poisons the buffers under zegarmistrz. |
| `zeg.s` | The zegarmistrz client request, as unchecked assembly. |
| `zegarmistrz.nix` | zegarmistrz from upstream Fil-C at `9b7584ce`; filnix does not package it. |
| `MemcmpPoison.v`, `poison.sh` | The checked module of `memcmp.ir` under the poison spike. |

## Results

`run.sh` builds the unchecked and SaRCAsm kernels and two nanofil ones
(without and with `-O`), and compares them.

| | unchecked | SaRCAsm | nanofil | nanofil `-O` |
| --- | --- | --- | --- | --- |
| Results on 19 cases | same | same | same | same |
| A length of 4096 on 16-byte buffers | reads past the end and returns 1 | Fil-C panic | Fil-C panic | Fil-C panic |
| `ct_memcmp` under zegarmistrz, buffers poisoned | clean | clean | clean | clean |
| `leaky_memcmp` under zegarmistrz, buffers poisoned | caught: cannot-branch | caught: cannot-branch | caught: cannot-branch | caught: cannot-branch |
| The author's instructions are the ones that run | yes | yes, with checks between them | no | no |
| Instructions in `ct_memcmp` | 24 | 159 | 288 | 192 |
| `ct_memcmp` on 4096 bytes, ns per byte | 0.7 | 2.6 | 6.4 | 3.3 |
| The module is judged valid by the Rocq validator | no | no | yes | yes |
| A theorem about every secret | no | no | yes, with the spike | yes, with the spike |

Under zegarmistrz every byte of both buffers is poisoned cannot-branch,
cannot-index and cannot-var-time-op, and each build runs three cases for
each kernel: the 16-byte path, the byte loop on buffers that differ, and
the byte loop on equal buffers. All 12 `ct_memcmp` runs finish with the
right answer, and all 12 `leaky_memcmp` runs stop with "tainted
(cannot-branch) value used in branch condition" inside the kernel. The
Fil-C checks that SaRCAsm and nanofil add do not trip the emulator: they
branch on pointers and bounds, which are public, and never on a loaded
byte. The instruction counts are of the assembled function, without
alignment padding. The timings are from one orb and are steady to about
5% between runs.

The IR itself passes nanofil's own checks, without and with `-O`:

- `tests/difftest.sh`: the interpreter and the native code agree on all 21
  runs, including the runs whose length passes the end of a buffer, which
  trap.
- `rocq/scripts/agree.sh`: the extracted Rocq model agrees with the
  interpreter on all 21.
- `rocq/scripts/valid.sh` and `gate.sh`: the extracted validator and
  `ir:valid_module/1` reach the same verdicts, and the checked module is
  valid.

## What the IR could not say directly

The translation took one IR instruction per machine instruction where the
IR had one. These are the places where it did not.

- **Flags.** `cmp` followed by `je` becomes a `cmp` value and a `branch`.
  Where an arithmetic instruction sets the zero flag (`or` at 12, `dec` at
  20), the IR needs a separate `cmp(ne, l)` against 0.
- **Conditional move.** The IR has no select. `cmovnz %rdx, %rax` at 13
  became `cmp(ne, l)` only because its two operands are the constants 0
  and 1. A `cmov` between two computed values has no direct translation
  that is free of branches.
- **Partial registers.** `%r10b` and `%al` are written as whole `l` values
  loaded with `load(ub)`. That is right here because the entry `xor`
  zeroes the upper bits and nothing else writes them. A general rule has
  to track the upper bits.
- **Memory operands.** `xor (%rsi), %r10` is a load and then an `xor`.
  `lea 1(%rdi), %rdi` is an `add` at class `p`.
- **Registers.** A register becomes a new temporary at each write, with
  phis at the loop head. `mov $1, %rdx` at 9 reuses the length register for
  a constant, which the IR does not need to notice.
- **Zeroing.** `xor %rax, %rax` is the constant 0, so instructions 1, 2
  and 9 have no IR instruction of their own.

This kernel has no carry chain, rotate, byte swap, wide multiply, vector
instruction or stack frame, so it says nothing about those. The IR's
operations (`Syntax.v`'s `op`) have none of them either.

## What the checks do and do not show

The hand translation is the weak link. Nothing here proves that
`memcmp.ir` computes what `memcmp.s` computes; the 19 cases of the
harness's table are the only comparison. A planted mistake shows it:
changing the second load of the 16-byte path from offset 8 to offset 7
passes `difftest.sh`, `agree.sh`, `valid.sh` and `gate.sh`, since the IR is
still a valid module that all three of nanofil's executions agree on. Only
the table catches it (`16 16 -1: ct 1` where the assembly gives 0).

On the re-emit route that weakness is about the answer, not about safety.
The assembly is not what runs, so a wrong translation cannot read out of
bounds, and it cannot leak through a branch that the poison rules would
see. It can only compute something other than `CRYPTO_memcmp`, which is
what OpenSSL's own tests are for.

nanofil chooses its own instructions. Where the assembly has `cmovnz`,
nanofil's code has `cmp`, `setne` and `movzbl`. The constant-time argument
for the nanofil builds therefore has two parts: the IR does not branch or
index on a secret, which the poison spike proves below, and nanofil's
backend does not add a secret-dependent branch when it prints that IR,
which nobody has proved. The zegarmistrz runs are the evidence for the
second part on this kernel.

## zegarmistrz needs natives the pinned runtime lacks

`zegarmistrz.h` reaches the emulator from Fil-C through natives
(`zegarmistrz_poison` and others under `__FILC__`) that the pinned runtime
(`lib/filc-staging.json`) does not have, so a Fil-C program that includes
the header does not link. `zeg.s` is the body of the header's
`zegarmistrz_client_request` as unchecked assembly, and `harness.c` calls
it with `zunsafe_fast_call`. That needs `-yolo-assembler` for the harness,
while `memcmp.s` is compiled separately so that the SaRCAsm build still
checks the kernel.

## The poison spike

`nanofil/rocq/spikes/Poison.v` gives zegarmistrz's poison rules to nanofil's
checked IR and proves `prun_ct_sound`: two runs that differ only in fully
tainted data have the same leak trace, if the first returns without a
poison fault. It is not on `main` yet. `poison.sh` was run against the
file as it stood in the thread finishing it on 2026-11-11 (sha256
`135618772abf…`, 3040 lines, which compiles in five minutes with no axiom),
and should be run again when the spike lands.

`MemcmpPoison.v` runs the checked module nanofil `-O` makes of `memcmp.ir`
through the spike's `prun`, under its strictest policy, on two buffers
whose every byte carries all three taints:

- `ct_memcmp` returns the right answer on the three cases above, and the
  answer carries the taint (`PDone (Ret (WInt 1)) [WTInt taint_all]`).
- `leaky_memcmp` stops with `PTrap CannotBranch`, on equal buffers too.
- `ct_memcmp_trace_is_public`: if `ct_memcmp` returns on some contents of
  the two buffers, then on any other contents its leak trace (its
  branches, the addresses and widths of its accesses, the pointers its
  checks read) is the same one. This holds for any buffer size and length.
  With the two runs above, the trace is fixed for a length of 16 and for
  the byte loop at a length of 32.

The theorem is about the IR's leak trace, as the spike defines it. It is
not about the machine code or about time.

## Is a lifter worth building?

A small one is, and a general one is not yet.

The case for it is that the hand step was mechanical. Every gap above has
a fixed rule, the two places that took judgment (the `cmov` and the byte
registers) would fall to a select and to masks that `-O` removes, and the
result is the only route with a theorem about every secret instead of a
test on the inputs someone tried. A lifter would remove the labor and the
transcription mistakes. It would not remove the question of whether the IR
computes what the assembly did, which stays a testing question on the
re-emit route.

The case against a general one is the vocabulary and the cost. OpenSSL's
assembly exists for carry chains (`adc`, `adcx`, `adox`, `mulx`), AES-NI,
carry-less multiply and wide vectors. The IR has no carry, no select and
none of those instructions, and nanofil's backend would not pick them.
Even on this integer kernel the re-emitted code is 1.3 times slower than
SaRCAsm's and 5 times slower than the original. For that code SaRCAsm,
which keeps the instructions, remains the way to ship it.

So the next step that this experiment supports is a lifter for the integer
subset this kernel used (moves, loads, `lea`, the bitwise and arithmetic
operations, `cmp`, `dec`, conditional jumps on the zero flag), driven by
the effect table of the Prolog prototype (`experiments/sarcasm-prolog`),
with this directory's table and emulator runs as its test. A select in the
IR should come with it. Carry chains and vectors should wait until the IR
has them for C's sake.
