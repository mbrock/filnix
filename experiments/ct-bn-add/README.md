# OpenSSL's bn_add_words: a carry loop through the lifter

`../ct-memcmp` lifted OpenSSL's `CRYPTO_memcmp` from assembly to nanofil's
IR, and ended by asking what a carry loop would cost, since the IR has no
carry. This experiment answers that for `bn_add_words` and `bn_sub_words`
from OpenSSL 3.6 (`crypto/bn/asm/x86_64-gcc.c`). They add and subtract two
numbers of n 64-bit words with `adc` and `sbb`, and return the last carry.
Beside them is a control, `leaky_add_words`, which computes the same sums
and sets the carry with two branches.

The experiment runs each kernel in four builds, as `../ct-memcmp` does.
The first calls the assembly unchecked. The second assembles the same
file with SaRCAsm, which keeps the instructions and adds Fil-C's checks.
The other two take the IR that `../ct-memcmp/lift/lift.pl` lifts from the
file and compile it with nanofil, without `-O` and with it. This
experiment has no hand translation, adds no instruction to the IR, and
involves no model of x86.

```sh
./run.sh [WORKDIR]      # everything below except the Rocq check
./poison.sh [WORKDIR]   # the Rocq check; see "The poison spike"
```

## The files

| File | What it is |
| --- | --- |
| `bn_add.s` | The three kernels, each with a SaRCAsm signature (`#! size_t(ptr,ptr,ptr,size_t)`) and each instruction numbered. |
| `drive.ir` | Three functions that allocate the buffers and call the kernels, with 21 `run` lines, so that nanofil's interpreter, its native code and the Rocq model can run the lifted IR. |
| `harness.c` | A Fil-C program that calls the kernels of whichever build it is linked with, and poisons the operands under zegarmistrz. |
| `BnAddPoison.v`, `poison.sh` | The checked module of the lifted IR under the poison spike. |
| `pushf.c` | A measurement of what saving the flags costs this loop; see "Why SaRCAsm is slow on this loop". |

OpenSSL does not have these loops in an assembly file. Each is nine
instructions of inline assembly inside a C function whose count is an
`int`. `bn_add.s` is a transcription: it gives the inline assembly the
registers a compiler could give it, and writes the C around it as six
more instructions. Those six use 64-bit registers and a `size_t` count,
because the lifter refuses 32-bit registers.

## Results

| | unchecked | SaRCAsm | lifted | lifted `-O` |
| --- | --- | --- | --- | --- |
| Results on 18 runs | same | same | same | same |
| A count of 5 on 4-word buffers | not checked | Fil-C panic | Fil-C panic | Fil-C panic |
| `bn_add_words` and `bn_sub_words` under zegarmistrz, operands poisoned | clean | clean | clean | clean |
| `leaky_add_words` under upstream zegarmistrz | caught | caught | missed | caught |
| `leaky_add_words` when a tainted store keeps its taint | caught | caught | caught | caught |
| Instructions in `bn_add_words` | 15 | 135 | 226 | 154 |
| `bn_add_words` on 512 words, ns per word | 0.5 | 45 | 11 | 4.8 to 5.5 |
| `bn_sub_words`, ns per word | 0.5 to 0.7 | 45 | 11 to 12 | 4.7 to 6.4 |
| `leaky_add_words`, ns per word | 1.4 | 3.5 to 4.3 | 13 | 3.8 |
| The module is judged valid by the Rocq validator | no | no | yes | yes |
| A theorem about every operand | no | no | yes | yes |

The 18 runs are the runs of `drive.ir` that return: sums with no carry, a
carry out of every word, a carry that enters a word whose own sum does not
wrap, a count of 0 and a count of 1. Every build prints what nanofil's
interpreter returns for the lifted IR, so on these runs the lifted IR
computes what the original assembly computes. The other three runs have a
count past the end of the buffers, and the three checked builds stop with
a Fil-C panic.

Under zegarmistrz every byte of both operands is poisoned cannot-branch,
cannot-index and cannot-var-time-op, and each build runs three cases for
each kernel under two builds of the emulator: sums with no carry, a carry
that ripples through every word, and carries in some words. All 48
`bn_add_words` and `bn_sub_words` runs finish with the right answer. The
timings are three runs on one orb, and a range is given where they differ by
more than 5%.

The lifted IR passes nanofil's own checks, without and with `-O`:
`tests/difftest.sh`, `rocq/scripts/agree.sh`, `rocq/scripts/valid.sh` and
`gate.sh`, on all 21 runs. Its outcomes with `-O` are its outcomes
without.

## The carry in the IR

`adc (%rdx,%r8,8), %rax` becomes five IR instructions and a phi. The lifter
writes the sum as two additions, and the carry out as two unsigned
comparisons, since either addition can wrap and at most one does:

```prolog
let(tmp(t_32), l, add, [tmp(rax_31), tmp(m_32)]),           % a[i] + b[i]
let(tmp(rax_32), l, add, [tmp(t_32), tmp(cf_ladd_loop)]),   % ... + carry in
let(tmp(cf1_36), l, cmp(ult, l), [tmp(t_32), tmp(rax_31)]), % the first sum wrapped
let(tmp(cf2_36), l, cmp(ult, l), [tmp(rax_32), tmp(t_32)]), % the second sum wrapped
let(tmp(cf_36), l, or, [tmp(cf1_36), tmp(cf2_36)])          % carry out
```

`sbb` is the same with subtractions and with each comparison testing
whether the subtrahend is the larger. The carry goes round the loop as a
phi named `cf`. The lifter makes the two comparisons where the carry is
next needed, which here is the end of the block, and makes none for a
carry that nothing reads.

The machine code that nanofil makes of this has no branch on a secret.
nanofil prints each unsigned comparison as `cmp` and `setb`. The
`bn_add_words` it prints with `-O` has two `setb` and no `adc`, and its
conditional jumps test only the count and the bounds of the three
buffers.

The loop depends on `lea` and `dec` leaving the carry alone between one
`adc` and the next. The lifter learns that from the effect table, whose
rows say which flags an instruction reads, sets and preserves. The table
is in the format of the Prolog SaRCAsm prototype
(`experiments/sarcasm-prolog/effects.pl`), which is frozen and is used as
it is. Of the 47 instructions in `bn_add.s`, 34 are looked up in the
prototype's table. The other 13 use rows that the lifter adds for `adc`,
`sbb`, `add` with a memory source, `sub` of two registers, `dec`, and
`lea` on a register that holds an integer.

## Why SaRCAsm is slow on this loop

SaRCAsm's `bn_add_words` takes 45 ns for each word, 90 times the original
and 8 to 9 times the lifted code with `-O`. In `CRYPTO_memcmp` the order
was the other way round: SaRCAsm's code was 1.4 times as fast as the
lifted code.

SaRCAsm keeps `adc`, so the carry flag has to survive from one iteration
to the next, and the checks SaRCAsm puts before each memory access change
the flags. It therefore wraps a check in `pushf; pop` and `push; popf`
where the flags are live. The loop of `bn_add_words` has four such pairs:
one around each of its three memory accesses and one around a test at the
head of the loop. `bn_sub_words` has four as well. `leaky_add_words` has
none, because no check sits between an instruction that sets the carry
and the branch that reads it, and it runs at the lifted code's speed.

`pushf.c` measures the saves alone. It is the original loop, without any
check, in three versions: as it is, with four `pushf` and `popf` pairs in
each iteration, and with four pairs of `lahf` and `sahf` that save the
same flags.

| The original loop | ns per word |
| --- | --- |
| as it is | 0.5 to 0.8 |
| with four `pushf` and `popf` pairs | 43 to 45 |
| with four `lahf` and `sahf` pairs | 6.4 to 6.7 |

The four `pushf` and `popf` pairs account for the whole of SaRCAsm's 45 ns.
The `lahf` version suggests that SaRCAsm could keep the carry about seven
times more cheaply; that version is a measurement of the saves, and has
not been tried in SaRCAsm.

nanofil does not have this cost because it does not keep a flag across an
instruction. The carry is an ordinary value in a register.

## The emulator misses the same leak

Upstream zegarmistrz catches `leaky_add_words` in the unchecked, SaRCAsm
and lifted `-O` builds, and lets all three runs of the unoptimized lifted
build finish. This is the miss `../ct-memcmp` found for `leaky_memcmp`,
and it has the same cause. nanofil without `-O` stores the loaded word to
a stack slot and later stores the condition computed from it to the same
slot, and the emulator's store rule clears the taint of a slot at the
second tainted store to it. With `../ct-memcmp/zegarmistrz-keep-taint.patch`
the emulator catches all 12 `leaky_add_words` runs and still passes all 24
runs of the two constant-time kernels. `run.sh` checks both halves, so it
fails when upstream fixes the rule.

## The poison spike

`poison.sh` runs the checked module nanofil `-O` makes of the lifted IR
through `prun` of `nanofil/rocq/spikes/Poison.v`, under its strictest
policy, with every byte of both operands carrying all three taints.
`nanofil/docs/poison.md` describes the spike. Nothing in `BnAddPoison.v`
rests on an axiom.

- `bn_add_words` returns the right carry on the three cases above, and
  `bn_sub_words` on four words that all borrow. The carry is as tainted as
  the operands (`PDone (Ret (WInt 1)) [WTInt taint_all]`).
- `leaky_add_words` stops with `PTrap CannotBranch`, on sums with no carry
  too.
- `bn_add_words_trace_is_public` and `bn_sub_words_trace_is_public`: if
  the kernel returns on some contents of the two operands, then on any
  other contents its leak trace is the same one. This holds for any buffer
  size and count. One tactic proves both.

The theorems are about the leak trace of the IR as the spike defines it.
They are not about the machine code or about time. The comparisons that
compute the carry are operations on tainted values, which the poison
rules allow because they record no branch and no address.

## What the checks do and do not show

Nothing proves that the lifted IR computes what `bn_add.s` computes. There
is no hand translation to compare with here, so the evidence is the 18
runs on which the lifted builds and the original assembly agree. A planted
mistake shows what that comparison is worth. If the lifter leaves out the
second comparison of `adc`, the IR still passes `difftest.sh`, `agree.sh`,
`valid.sh` and `gate.sh`, because it is a valid module that nanofil's
three executions agree on. `run.sh` then fails at the first native run in
which a carry enters a word whose own sum does not wrap:

```
FAIL: unchecked add 4 4 -1 0 1 -1: 14003818205313896716, not 14003818205312896713
```

As in `../ct-memcmp`, that weakness is about the answer and not about
safety, because the assembly is not what runs.

## What the IR could not say directly

- **Add with carry.** One `adc` is two additions, two comparisons and an
  `or`. The IR has no operation that gives a sum and its carry together.
- **32-bit registers.** OpenSSL's count is an `int`, and compiled C around
  hand-written loops uses 32-bit registers freely. The lifter refuses
  them, so `bn_add.s` has 64-bit stand-ins for the C.
- **Inline assembly.** OpenSSL's source for these loops is a C file, not
  an assembly file with signatures, so the lifter read a transcription.
- **Scaled index.** `(%rsi,%r8,8)` is a `shl` and an `add` at class `p`,
  written again at each of the three accesses.

## What this says about a wider lifter

An integer carry chain lifts with no new IR instruction, and every check
that passed for `CRYPTO_memcmp` passes for it, including the theorem about
every operand. The lifted code with `-O` is about 10 times slower than
the original loop, against 5.7 times for `CRYPTO_memcmp`. It is faster
than SaRCAsm's on this loop only because of how SaRCAsm saves the flags.

The next kernel in the same file is `bn_mul_add_words`, and it stops at
the IR. It needs the high half of a 64-bit product (`mulq`), and the IR's
`mul` gives the low half only. A multiply that gives the high half would
be a new instruction with its own row in the model, the validator and the
backends, which is worth adding when C needs it and not for the lifter
alone. `adcx` and `adox` would not need one: they are two carries, and
the lifter already keeps a carry as a value. Vectors and AES-NI remain out
of reach, as `../ct-memcmp` says.
