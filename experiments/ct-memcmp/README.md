# OpenSSL's CRYPTO_memcmp: unchecked, through SaRCAsm, and through nanofil

This experiment takes one small piece of hand-written constant-time
assembly and asks what each route to running it under Fil-C keeps. The
kernel is `CRYPTO_memcmp` from OpenSSL 3.6 (`crypto/x86_64cpuid.pl`), 24
instructions that compare two buffers without branching on their bytes.
Beside it is a control, `leaky_memcmp`, which has the same contract but
leaves at the first difference.

The three routes are:

- **unchecked**: `as` assembles the file, and Fil-C code calls the result
  with `zunsafe_fast_call`. The original instructions run, and nothing
  checks their memory accesses. Fil-C's `-yolo-assembler` option gives
  this.
- **SaRCAsm**: Fil-C's assembler assembles the same file. It keeps each
  instruction and puts Fil-C's checks before each memory access.
- **nanofil**: the assembly is rewritten as nanofil's IR, which nanofil
  then checks, optimizes and prints as new assembly. The original
  instructions are not kept. This is the re-emit route, and it involves
  no model of x86. The IR comes from the assembly in two ways: a
  translation written by hand (`memcmp.ir`), and a small lifter that
  reads `memcmp.s` (`lift/`).

```sh
./run.sh [WORKDIR]      # everything below except the Rocq check
./poison.sh [WORKDIR]   # the Rocq check; see "The poison spike"
```

## The files

| File | What it is |
| --- | --- |
| `memcmp.s` | `CRYPTO_memcmp` as perlasm prints it, renamed `ct_memcmp`, and `leaky_memcmp`. Each label has a SaRCAsm signature (`#! int(ptr,ptr,size_t)`), which plain `as` reads as a comment, so one file serves two builds. Each instruction is numbered. |
| `memcmp.ir` | The hand translation. Each IR instruction cites the number of the machine instruction it stands for. |
| `lift/asm.pl`, `lift/table.pl`, `lift/lift.pl` | The lifter: a reader for the assembly, the effect table, and the translation to IR. `swipl lift/lift.pl memcmp.s` prints the lifted IR. |
| `drive.ir` | Two functions that allocate buffers and call the kernels, with 21 `run` lines, so that nanofil's interpreter, its native code and the Rocq model can run the IR. |
| `harness.c` | A Fil-C program that calls the kernels of whichever build it is linked with, and poisons the buffers under zegarmistrz. |
| `zeg.s` | The zegarmistrz client request, as unchecked assembly. |
| `zegarmistrz.nix` | zegarmistrz from upstream Fil-C at `9b7584ce`; filnix does not package it. |
| `zegarmistrz-keep-taint.patch` | A change to the emulator's store rule; see "The emulator misses one leak". |
| `MemcmpPoison.v`, `poison.sh` | The checked modules of `memcmp.ir` and of the lifted IR under the poison spike. |

## Results

`run.sh` builds six kernels and compares them. Two are the unchecked and
SaRCAsm ones. nanofil makes two from the hand translation and two from
the lifted IR, in each case one without `-O` and one with it.

| | unchecked | SaRCAsm | nanofil | nanofil `-O` | lifted | lifted `-O` |
| --- | --- | --- | --- | --- | --- | --- |
| Results on 19 cases | same | same | same | same | same | same |
| A length of 4096 on 16-byte buffers | reads past the end and returns 1 | Fil-C panic | Fil-C panic | Fil-C panic | Fil-C panic | Fil-C panic |
| `ct_memcmp` under zegarmistrz, buffers poisoned | clean | clean | clean | clean | clean | clean |
| `leaky_memcmp` under upstream zegarmistrz | caught | caught | caught | caught | missed | caught |
| `leaky_memcmp` when a tainted store keeps its taint | caught | caught | caught | caught | caught | caught |
| The author's instructions are the ones that run | yes | yes, with checks between them | no | no | no | no |
| Instructions in `ct_memcmp` | 24 | 159 | 288 | 192 | 314 | 204 |
| `ct_memcmp` on 4096 bytes, ns per byte | 0.7 | 2.7 | 6.8 | 3.3 | 9.5 | 3.7 |
| The module is judged valid by the Rocq validator | no | no | yes | yes | yes | yes |
| A theorem about every secret | no | no | yes | yes | yes | yes |

Under zegarmistrz every byte of both buffers is poisoned cannot-branch,
cannot-index and cannot-var-time-op, and each build runs three cases for
each kernel: the 16-byte path, the byte loop on buffers that differ, and
the byte loop on equal buffers. `run.sh` does this under two builds of the
emulator, which the next section explains. All 36 `ct_memcmp` runs finish
with the right answer. A `leaky_memcmp` run that is caught stops with
"tainted (cannot-branch) value used in branch condition" inside the
kernel. The Fil-C checks that SaRCAsm and nanofil add do not trip the
emulator: they branch on pointers and bounds, which are public, and never
on a loaded byte. The instruction counts are of the assembled function,
without alignment padding. The timings are from one orb and are steady to
about 5% between runs.

Each IR passes nanofil's own checks, without and with `-O`:

- `tests/difftest.sh`: the interpreter and the native code agree on all 21
  runs, including the runs whose length passes the end of a buffer, which
  trap.
- `rocq/scripts/agree.sh`: the extracted Rocq model agrees with the
  interpreter on all 21.
- `rocq/scripts/valid.sh` and `gate.sh`: the extracted validator and
  `ir:valid_module/1` reach the same verdicts, and the checked module is
  valid.

The lifted IR gives the hand translation's outcome on each of the 21 runs.

## The emulator misses one leak

Upstream zegarmistrz catches `leaky_memcmp` in five of the six builds. In
the unoptimized lifted build it lets all three runs finish. The cause is
the emulator's rule for stores (`mem_note_store` in `src/mem.cpp`). A
tainted store sets the taint bit and the clear-on-store bit of the bytes
it writes. A tainted store to bytes that already carry the clear-on-store
bit clears the taint bit, so the second tainted store to one stack slot
leaves the slot clean. nanofil without `-O` keeps every temporary in a
stack slot, so its code stores tainted values to the stack where the
other builds keep them in registers. Which store cleans the byte in this
build has not been traced. The evidence that the store rule is the cause
is that changing only that rule makes the miss go away.

`zegarmistrz-keep-taint.patch` makes a tainted store always set the taint.
With it the emulator catches all 18 `leaky_memcmp` runs and still passes
all 18 `ct_memcmp` runs. `nanofil/docs/zegarmistrz.md` describes the same
store rule as a bug that the Rocq formalization found, and the poison
spike's `note_store_byte` keeps the taint. The Rocq check below catches
`leaky_memcmp` in the lifted IR without help, because it applies the rules
to the IR and not to stack slots.

## What the IR could not say directly

The translation took one IR instruction per machine instruction where the
IR had one. These are the places where it did not. The lifter applies the
same rules.

- **Flags.** `cmp` followed by `je` becomes a `cmp` value and a `branch`.
  Where an arithmetic instruction sets the zero flag (`or` at 12, `dec` at
  20), the IR needs a separate `cmp(ne, l)` against 0.
- **Conditional move.** When the hand translation was written the IR had
  no select, and `cmovnz %rdx, %rax` at 13 became `cmp(ne, l)` only
  because its two operands are the constants 0 and 1. The IR now has
  `let(tmp(D), K, select, [C, X, Y])`, which gives X when C is not 0 and Y
  otherwise and is printed as `test` and `cmovne`. The lifter translates
  every conditional move to it. The hand translation is left as it was.
- **Partial registers.** `%r10b` and `%al` are written as whole `l` values
  loaded with `load(ub)`. The hand translation relies on the entry `xor`
  having zeroed the upper bits. The lifter does not reason about that: a
  byte write to a register that holds a 64-bit integer keeps the other 56
  bits with an `and` and an `or`.
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

## The lifter

`lift/lift.pl` reads the integer subset of x86-64 that `memcmp.s` uses and
prints unchecked IR for each function that has a SaRCAsm signature. It is
about 740 lines of Prolog in three files.

The lifter is driven by an effect table in the format of the Prolog
SaRCAsm prototype (`experiments/sarcasm-prolog/effects.pl`). A row says
which registers an instruction reads and writes, which memory it
accesses, what it does to the flags, and where control goes. The
prototype is frozen and its table is used as it is. Of the 37
instructions in `memcmp.s`, 26 are looked up in the prototype's table.
The other 11 use rows that `lift/table.pl` adds for forms the prototype
lacks: byte registers, a memory source for `xor`, `or` and `cmp`, `dec`,
`neg` and the conditional move.

From the rows the lifter builds the IR as follows.

- A register is a temporary named after the register and the source line
  that wrote it. Each block starts with a phi for every register that has
  one type on every way in, and phis that nothing uses are removed.
- A register holds a pointer, a 64-bit integer, or an integer of which
  only the low byte is defined. Reading more than a register holds is an
  error, so a register that is read before it is written is refused. The
  lifter refuses 32-bit registers.
- The zero flag is remembered as the two values whose difference it
  tests, and becomes a `cmp` where a branch or a conditional move reads
  it. It does not cross a block boundary. Only `e` and `ne` are
  translated.

Nothing in the lifter has to be trusted for memory safety, because
nanofil inserts the checks afterwards and validates the result. A wrong
row gives a wrong answer and never an unchecked access. A planted mistake
shows that the comparison with the hand translation can see a wrong
answer: swapping the two operands of the conditional move in `lift.pl`
makes the lifted IR differ from the hand translation on 5 of the 21 runs.

The lifter does not lift a conditional move between two pointers.
`select` is an integer operation at width `w` or `l`, and a capability
does not survive a pointer that is turned into an integer, selected and
turned back.

## What the checks do and do not show

The step from assembly to IR is the weak link. Nothing here proves that
`memcmp.ir` or the lifted IR computes what `memcmp.s` computes. The
evidence is that two translations made independently agree on 21 runs,
and that all six builds agree on the 19 cases of the harness's table. A
planted mistake in the hand translation shows what nanofil's own checks
miss: changing the second load of the 16-byte path from offset 8 to
offset 7 passes `difftest.sh`, `agree.sh`, `valid.sh` and `gate.sh`, since
the IR is still a valid module that all three of nanofil's executions
agree on. Only the table catches it (`16 16 -1: ct 1` where the assembly
gives 0).

On the re-emit route that weakness is about the answer, not about safety.
The assembly is not what runs, so a wrong translation cannot read out of
bounds, and it cannot leak through a branch that the poison rules would
see. It can only compute something other than `CRYPTO_memcmp`, which is
what OpenSSL's own tests are for.

nanofil chooses its own instructions. The constant-time argument for the
nanofil builds therefore has two parts: the IR does not branch or index
on a secret, which the poison spike proves below, and nanofil's backend
does not add a secret-dependent branch when it prints that IR, which
nobody has proved. The zegarmistrz runs are the evidence for the second
part on this kernel, and the previous section shows that the emulator can
miss a leak in unoptimized code.

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
poison fault. `nanofil/docs/poison.md` describes it. `poison.sh` compiles
the file as it is in this tree, which takes about two and a half minutes,
and then checks the hand translation and the lifted IR in turn.

The spike's rule for `select` gives the result the join of the taints of
its three operands and records no branch. zegarmistrz treats `cmov` the
same way.

`MemcmpPoison.v` runs the checked module nanofil `-O` makes of each IR
through the spike's `prun`, under its strictest policy, on two buffers
whose every byte carries all three taints. The same file checks both
modules, and neither check rests on an axiom. The lifted module contains
one `select`.

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

## Is a wider lifter worth building?

The small lifter did what the hand translation suggested it would. It
reads the assembly that OpenSSL ships, and its output passes every check
the hand translation passes, including the theorem about every content of
the buffers, with no change to the proof script. The step from assembly
to IR took judgment in two places by hand (the `cmov` and the byte
registers), and both are now fixed rules.

The lifter did not change two things. Whether the IR computes what the
assembly did is still a testing question on the re-emit route. The
re-emitted code is still slower: with `-O` the lifted kernel takes 1.4
times as long as SaRCAsm's and 5.7 times as long as the original.

A wider lifter is worth building one instruction family at a time, when
there is a kernel that needs the family and the IR can say it. The table
is cheap to extend: this kernel needed 11 added rows. The IR is what
limits it. OpenSSL's assembly exists for carry chains (`adc`, `adcx`,
`adox`, `mulx`), AES-NI, carry-less multiply and wide vectors. The IR has
no carry and none of those instructions, and nanofil's backend would not
pick them. For that code SaRCAsm, which keeps the instructions, remains
the way to ship it.

The next kernel that would teach something is a carry loop such as
`bn_add_words`. A carry can be written in today's IR as an unsigned
comparison of the sum with an operand, which nanofil prints as `setb` and
not as a branch, so the lifter could translate `adc` and `sbb` without a
new instruction. That would show how much the missing carry costs and
whether the poison rules accept the result. Vectors and AES-NI should
wait until the IR has them for C's sake.
