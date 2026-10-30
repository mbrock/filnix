# Fixed-register inline asm (B1): contract (reviewed)

The frontend thread measured the 17 survey packages that inline asm
blocks. filcc passes through a single instruction that has no operand in
its text and works only on fixed registers, such as `cpuid`, `xgetbv`,
`rdtsc`, the fences and `pause`. That wins libblake3, pcre2,
util-linux, physfs and fstrm now. B1 lets nanofil do the same. It runs
native code inside checked functions, so this contract comes before any
code and goes to Oracle for review, as rounds 1–5 of M7 did.

## Scope

filcc's validator (`validateSafeInlineAsm`, FilPizlonator.cpp 8933–11494
in `filc-staging-ref-src`) is general. It knows about 200 mnemonics,
checks each explicit operand's role, and requires every register an
instruction writes to be declared. B1 takes only one corner of it:

| Mnemonic | Reads | Writes (32-bit, upper half zeroed) | filcc's coverage rule (lines) | Flags |
| --- | --- | --- | --- | --- |
| `cpuid` | eax, ecx | eax, ebx, ecx, edx | each written register is an output or clobber (10521–10546) | none |
| `xgetbv` | ecx | eax, edx | ecx is an input; eax and edx are outputs, not clobbers (10548–10566) | none |
| `rdtsc` | — | eax, edx | eax and edx are outputs or clobbers (10644–10660) | none |
| `rdtscp` | — | eax, ecx, edx | eax, ecx and edx are outputs or clobbers (10662–10682) | none |
| `lfence`, `sfence`, `pause` | — | — | none (9300–9330) | none |
| `mfence` | — | — | none | none |

In every case filcc requires that the line has no operands: "X takes no
operands". None of these instructions sets flags, so filcc requires no
`cc` clobber (11489). None of them accesses memory. `cpuid` and the
`rdtsc` pair are never privileged. Some can still fault:
- `cpuid` under `ARCH_SET_CPUID`, which Fil-C allows (filc_runtime.c
  13163), raises #GP;
- `rdtsc` and `rdtscp` under `PR_SET_TSC` (12247) raise #GP;
- `xgetbv` with an invalid ecx raises #GP;
- `xgetbv` with OSXSAVE clear, and `rdtscp` on a CPU without it, raise
  #UD.

#GP is SIGSEGV and #UD is SIGILL. Fil-C makes both uncatchable
(`is_unsafe_signal_for_handlers`, 525–536; `sigaction`, 9043), so the
process dies, as it does under filcc.

## The term

One new instruction, a statement because it defines up to four
results:

    asm_fixed(M, Ins, Outs)

| Part | Rule |
| --- | --- |
| `M` | one of `cpuid`, `xgetbv`, `rdtsc`, `rdtscp`, `lfence`, `sfence`, `pause`: an atom, never text |
| `Ins` | `R-V` for exactly the registers M reads, in the order a, b, c, d. Each V is a `w` operand (a `w` temporary or a constant) |
| `Outs` | `R-tmp(T)` for a subset of the registers M writes, in order, each R at most once. Each T is defined here as a `w` temporary |

`mfence` is the existing `fence` instruction, emitted as `mfence` and
already supported by every pass, the interpreter, both backends and the
register checker. The frontend lowers asm `"mfence"` to it. `fence` is
at least as strong as the asm in every respect, including clang's
treatment of a `memory` clobber.

Text, constraints and clobbers stay in the frontend. The emitter prints
an instruction from its own table for M, so no source text reaches the
assembler. Effects come from M, not from the declared clobbers, so a
wrong clobber list cannot make the emitter keep a value in a register M
writes.

### Operands are scalars only

Every V and T is class `w`. The validator rejects `p`, so no pointer
and no capability reaches the asm or comes out of it. It also rejects
`l`, `s`, `d` and `x`. Fil-C keeps capabilities out of band, and an
integer carries none. A program may pass `(uintptr_t)ptr` as an input,
which is an integer. An output turned back into a pointer has no
capability, as with any int-to-pointer cast in Fil-C.

All operands are 32-bit because M reads only the low 32 bits of its
inputs and every write of M zero-extends.
- If the C operand is 64-bit, the frontend truncates an input and
  zero-extends an output. That is exactly what the hardware does with
  `rax` under clang.
- For an 8- or 16-bit C operand, the frontend truncates the output, as
  clang does.

### What the frontend does with the rest (acceptance, owned there)

- Only a template that filcc accepts, split at `\n` and `;` and
  trimmed of `" \t\r\v\f"`, with exactly one nonblank line whose
  lowercased mnemonic is in the table and which has no operands.
- Constraints: only the letters a, b, c and d (and `S` and `D`, which no
  mnemonic in B1 reads or writes), digit ties, and the prefixes `=`,
  `+` and `&`. Clobbers: only the ones filcc's validator accepts.
- filcc's coverage rules apply as in the table. A form that filcc
  turns into a run-time error keeps filcc's reason
  (`asm_runtime_reason`). A form that filcc accepts and B1 cannot
  express is refused at compile time, never miscompiled.
- A tied (`"0"`) or `+` operand is an input to that register and an
  output from it. An input to a register that M does not read is
  dropped, after its value has been evaluated as C requires. An output
  from a register M does not write equals the tied input, or is refused
  when untied, because its value would be unspecified.
- A register that M reads but no input names gets `const(0)`. In
  filcc it holds whatever the register allocator left there, which is
  unspecified, so 0 is a refinement. Examples are libblake3's cpuid
  without ecx and fftw's `"+a".."+d"` cpuid, whose b and d inputs are
  dropped.
- Clobbers that filcc accepts but that name nothing M writes are
  accepted and dropped. Examples are `memory`, `cc` and named GPRs such
  as nettle's `%r10`; M has no other effects. An sp, bp or segment
  clobber stays filcc's run-time error. filcc's "cc clobber is missing"
  refusal never applies, since none of these mnemonics sets flags.
- C operands are integers only. float and double are refused at
  compile time.
- A pass-through tie on a register M does not write, such as `"+S"`
  with cpuid or `"+c"` with xgetbv, keeps the full C value. It never
  goes through the 32-bit operand.
- A `_Bool` output takes bit 0, as clang's i8-to-i1 truncation does,
  not `!= 0`.
- filcc's pointer refusals (`asm_runtime_reason`) come before B1's
  acceptance.
- Agreed with the frontend thread (T-01a17e04-9a23-7050-9a91-9536214f8bee)
  against every measured B1 site:
  - cpuid: fftw `"+a".."+d"`, libblake3, physfs, and pcre2 and
    util-linux's tied forms;
  - xgetbv: flac, fftw, libblake3, and libdeflate, whose `=d` before
    `=a` the frontend reorders;
  - rdtsc: fftw, rhash;
  - mfence (fstrm) and pause (quickjs).
- B1 acceptance extends the frontend's tier-A line model. A single line
  that passes becomes `asm_fixed`. Anything else filcc passes through
  is refused at compile time.
- `volatile` does not matter. B1 asm is never deleted, merged or moved
  (below). clang may delete or merge a non-volatile asm, and keeping
  it is a refinement.

## Validator (ir.pl)

`asm_fixed(M, Ins, Outs)` is valid in both the plain and the checked
stage iff M is in the table, Ins names exactly M's read registers in
order with `w` values, and Outs names distinct registers in order that
M writes, each defining a `w` temporary. Strict SSA covers the results:
`cfg:inst_def` gives each output, and `cfg:inst_uses` each input
temporary. A missing `inst_uses` clause would fail open: simplify's
dead code would delete the inputs' definitions. A missing `inst_def`
clause would let frame_slots start an output's interval at its first
use, so a temporary sharing its slot could be overwritten at the asm. It is not `evidence_preserving` (rounds 1–5): every check
fact dies at it. That is conservative, since it can neither free nor
change bounds, but B1 does not need its facts.

## Middle end

The pattern is `fence`, which every pass already treats as ordered:
- **Ordered.** No pass deletes it, merges two of them or moves it. No
  load, store, atomic, call or other `asm_fixed` moves across it in
  either direction. It is kept even when no result is used.
- **Inputs and outputs.** Its results are ordinary definitions. Its
  inputs are uses that substitution (simplify, copy) may rewrite.
- **Inlining.** It may be inlined and duplicated along with its function.
- **Locals.** Promoted and local-storage locals are not memory that it
  orders, since no other thread can see them.

Today ordering holds because no pass moves memory operations at all;
`fence` gets no special treatment. simplify keeps it because
`removable/1` covers only pure `let`s. The test that guards this is
therefore "each pass keeps every `asm_fixed`, in order", not a
particular reordering.

Clauses that must be added, since without them the asm's effects
silently disappear (Oracle):
- `cfg:inst_uses` and `cfg:inst_def`;
- `simplify:inst_subst`;
- `copy:inst_reps` and `copy:temp_classes`;
- `filc_abi:inst_dest`;
- `filc_amd64:cache_temp_class`;
- `ir:valid_inst` and the definition-class checks;
- `interp:inst_result`;
- `inst//N` in amd64.pl and filc_amd64.pl.

These defaults are already right for it:
- `promote:inst_renamed`;
- `pizlonate:checked_insts`;
- `filc_abi:lower_inst`;
- `inline:renamed_temps`;
- `escape:inst_event`, safe only because operands are `w`.

## Emission (filc_amd64.pl and amd64.pl)

    movl <V_a>, %eax      ; each input, from its slot, home or constant
    movl <V_c>, %ecx
    asm_fixed(M)          ; one line in the stream (below)
    movl %eax, <T_a>      ; each output, into its slot or home
    movl %edi, <T_b>      ; cpuid's b result arrives in %edi
    ...

The line `asm_fixed(M)` prints as M's table entry. For `cpuid`:

    movq %rbx, %rsi
    cpuid
    movl %ebx, %edi
    movq %rsi, %rbx

For the others it is just the instruction. `rbx` is callee-saved, and
under `--registers=temps` (the `-O` default) it may hold a home. The
save and restore keep both the caller's `rbx` and that home.
`%rsi` and `%rdi` are scratch inside one IR instruction, like
`%rax`–`%rdx`. In the reference stream, no scratch register holds a
value at an IR instruction boundary. The `-O` step-3b rewrite does carry
scratch contents across boundaries within a region (amd64_regs.pl
`forward`, `cell_forward`, `dead_move`), so the line must end such a
region (below). Roots never live in registers: FUGC scans frame lowers,
not native registers.

### Register allocator and checker

The line is the non-`ins` term `asm_fixed(M)`, not `ins(M, none, [])`.
The checker's operand pairing (`paired/7`) takes register effects only
from operand roles and `implicit/4`, never from
`instruction_effects/2`. So an `ins` line with no operands would look
register-neutral, and a 3b rewrite that forwards a stale rcx or rsi
across cpuid, or drops its input move, would be accepted. (This was
Oracle's blocker on the first draft, which modelled it on `mfence`.) As
a non-`ins` line:

- **Region boundary.** `boundary_line/2` treats it as one, as it does a
  call. Nothing is forwarded across it, the reference and allocated
  lines must be equal (`LA == LB`), and `region_end` compares the live
  inputs.
- **Liveness.** `extra_use_def` treats it like `call`: it uses every
  scratch register, so `dead_moves` can never delete an input move
  (Use ∪ 127), and it defines the registers M writes.
- **Effects.** `amd64_contract:instruction_effects/2` gets one audited
  entry per M, used by the stack cache and by liveness:

| M | Reads | Writes | Flags | Memory | Control |
| --- | --- | --- | --- | --- | --- |
| `cpuid` | rax, rcx | rax:32, rcx:32, rdx:32, rsi:64, rdi:32 | write | none | next |
| `xgetbv` | rcx | rax:32, rdx:32 | write | none | next |
| `rdtsc` | — | rax:32, rdx:32 | write | none | next |
| `rdtscp` | — | rax:32, rcx:32, rdx:32 | write | none | next |
| `lfence`, `sfence`, `pause` | — | — | preserve | none | next |

The flags entries are conservative: nothing reads flags across an IR
instruction.

- **No named register.** The line names no register, so the reference
  stream still names no allocatable register outside the prologue.
- **Trusted table.** cpuid's entry says rbx is preserved, which only the
  save and restore make true. A unit test checks the printed expansion,
  and a native test checks a value homed in rbx across the cpuid, with
  the emitted asm showing the home is really there.
- **Hardening.** The checker rejects any audited effect that writes an
  allocatable register (rbx, r10–r15) outside home moves and calls.
  Homes are never in rax–rdx, rsi or rdi, and this makes the table
  unable to clobber one even if it were wrong.
- **Not a call.** r10 and r11 are untouched.

## No memory, poll or GC interaction

- **Memory.** None of the instructions reads or writes memory, so no
  object, header, frame slot or shadow is touched. The fences order
  this thread's memory accesses, the same accesses the native code makes
  under filcc. `pause` is a hint.
- **Poll and GC.** It is not a safepoint, and it neither enters nor
  exits the runtime. FUGC is concurrent and needs this thread only at
  polls, and none is added or removed. It touches no pointer: operands
  are `w`, and the scratch registers it writes hold no root at an
  instruction boundary. Store barriers and allocation are unaffected.
- **Signals.** Fil-C runs handlers at polls, so a signal during cpuid
  waits like any other. A #GP from `xgetbv` or `rdtsc` kills the
  process, as it does under filcc.
- **Stack.** It does not push, pop or touch `rsp` or `rbp`, uses no red
  zone, and needs no alignment.

## Interpreter (interp.pl) and difftest

- **The fences and pause** are no-ops. The interpreter runs one thread
  in program order, where they change nothing.
- **`cpuid`, `xgetbv`, `rdtsc`, `rdtscp`** stop the run with a new
  outcome, `unknown(asm(M, InVals))`, carrying the input values so a
  pass that changes cpuid's leaf fails validation.
  - `call_outcome_result/5` passes it out of a callee.
  - `outcome_text/2` prints it.
  - Without these clauses, a cpuid in a callee would throw "interpreter
    found no outcome" and abort the difftest file.
  - It is not a thrown error: a throw ("cannot interpret") would abort
    the whole difftest file.
  - It is not a symbolic value either. The interpreter is relational,
    so a branch on an unconstrained result would take one arm and report
    an integer result that native code need not match.
- **difftest.** `comparable/2` does not accept `unknown(_)`, so
  difftest lists such a run as "not comparable", with its outcome, and
  compares the file's other runs.
- **Pass validation.** Before and after the middle end, the outcome
  `unknown(asm(M, InVals))` before a pass accepts only the same outcome
  after it (`refines/2` compares by equality). Everything after a run's
  first cpuid goes unvalidated by the interpreter. Ordering keeps the asm, and all behaviour before it, in place, so
  a pass that changes the path to the asm fails validation.
- **Coverage for functions difftest cannot compare.** Native tests
  compare nanofil's binary with filcc's build of the same C program on
  the same machine (progtest, with `FUGC_SCRIBBLE`/`FUGC_VERIFY`):
  - cpuid leaf 0's maximum leaf and vendor string;
  - leaf 1 and leaf 7.0's feature bits;
  - `xgetbv(0) & 7` when OSXSAVE is set;
  - that two `rdtsc` reads, with `lfence` and `rdtscp` around them,
    do not decrease;
  - a `pause`/`sfence` loop;
  - every C operand width;
  - tied and `+` forms;
  - under `-O`, values live across cpuid in `rbx`, r12–r15, r10 and
    r11, homes that the test arranges with live values around a call.

## Tests and plants (planned)

- **Unit, validator.**
  - Accept every row of the table.
  - Reject:
    - an unknown M;
    - `mfence` as `asm_fixed`;
    - a `p`, `l` or `d` operand;
    - a missing read input, an extra one, or one in the wrong order;
    - an output from a register M does not write;
    - two outputs from one register;
    - a non-`w` result.
- **Unit, emitter.**
  - cpuid's printed lines, with rbx restored after the instruction.
  - The effect entry for each M.
  - The checker accepts a temps-mode stream with a home in rbx across
    cpuid.
- **Interpreter.**
  - The no-op forms return the reference value.
  - The others stop with `unknown(asm(M))`.
  - difftest reports such a run as not comparable and still compares
    the file's other runs.
- **Native.** The progtest program above, with and without `-O`, under
  `FUGC_SCRIBBLE=1 FUGC_VERIFY=1`, against filcc.
- **Unit, checker.** A temps stream that forwards a stale rcx or rsi
  across `asm_fixed(cpuid)`, or drops its eax input move, is rejected.
- **Unit, passes.** Each pass keeps every `asm_fixed`, in order. simplify
  keeps the pure `let`s that define its inputs.
- **Unit, interpreter.** A cpuid in a callee gives `unknown(asm(cpuid,
  [L, S]))`, and difftest lists it.
- **Plants.** Each must be caught:
  1. cpuid without the rbx save (native: an asserted home in rbx);
  2. the b result read from `%ebx` after the restore (native: vendor string);
  3. the effect table omitting rsi or rdi, or rdtscp's rcx write
     (checker unit test: a value forwarded across the line);
  4. cpuid's entry omitting the rcx read (checker unit test: the subleaf
     move is kept);
  5. the validator accepting `p`;
  6. the validator accepting an output from an unwritten register;
  7. the interpreter running cpuid as a no-op (unit: outcome);
  8. a missing `inst_uses` clause (simplify unit test above);
  9. a missing `call_outcome_result` clause (callee unit test above);
  10. a pass dropping an `lfence` or `pause` (each pass keeps it).

## Review

Oracle reviewed the first draft. The core argument held: operands are
`w` only, there is no memory access and no safepoint, homes are never
in rax–rdx, rsi or rdi, and the cpuid save and restore are correct. Its
blocker was that a line with no operands, modelled on `mfence`, hides
cpuid's register effects from the checker while `-O` forwards scratch
values across IR boundaries; the line is now a region boundary with
call-like liveness. Its should-fixes were:
- the interpreter outcome's plumbing and input values;
- the fail-open clause list;
- the frontend's float, wide-tie and `_Bool` cases;
- the fault facts above;
- plants that the planned tests would not have caught.

All are folded in above.
