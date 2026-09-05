# A small Prolog SaRCAsm experiment

This is an independent, deliberately restricted assembly frontend hosted
by Fil-C-built Trealla. It is not a replacement for upstream SaRCAsm.

The experiment accepts annotated x86-64 AT&T assembly, parses it with DCGs,
describes instruction effects, tracks typed values and flags through basic
blocks, validates edge transfers, groups compatible reads, and emits C.
Fil-C then lowers that C to assembly.
The installed command emits assembly by default:

```sh
nix run .#sarcasm-prolog -- experiments/sarcasm-prolog/examples/table-entry.s > /tmp/table-entry.s
nix run .#sarcasm-prolog -- --emit-c experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --emit-ir experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --emit-effects experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --explain experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --no-coalesce --emit-c experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --emit-ir experiments/sarcasm-prolog/examples/branches.s
nix run .#sarcasm-prolog -- --emit-checks experiments/sarcasm-prolog/examples/checks.s
nix run .#sarcasm-prolog -- --verify-checks --emit-c experiments/sarcasm-prolog/examples/checks.s
nix run .#sarcasm-prolog -- --linear --emit-c experiments/sarcasm-prolog/examples/table-entry.s
nix build .#checks.x86_64-linux.sarcasm-prolog
```

The emitted assembly already uses the Fil-C ABI. Assemble it with ordinary
GNU `as`, then link the object with Fil-C; feeding it back through SaRCAsm
would attempt a second translation. `-fno-addrsig` makes this compiler
output consumable by GNU `as`.

## The slice

`examples/table-entry.s` performs the three reads used in a zstd X2 table
lookup: a 16-bit sequence, an 8-bit bit count, and an 8-bit output length.
It returns their packed four-byte value. This is a table lookup example,
not a Huffman decoder or a benchmark of zstd.

Without grouping, its C representation has three `memcpy` reads. With
grouping, it has one four-byte read and register extractions. Each access
retains its source line and destination value, and the plan records the
original ordered loads served by each read. The packaged assembly for the
grouped example contains a single 32-bit data load.

`--emit-effects` shows source-located register, memory, flag, control-flow
and trap effects before register lowering. `--explain` records the read
planner's actual choices. For this example it reports:

```text
line 6: read v(0) selects 4 bytes [0,4); source lines [6,6,7]
  address: pointer param(0,reg(rdi)), index view(param(0,reg(rsi)),64), scale 4
  8 bytes rejected: line 8: binary(shl) is an ordering barrier
  4 bytes accepted: same pointer/index/scale, exact adjacent ranges, original order
```

The two instructions on line 6 account for its repeated source location.
Both inspection modes require valid input and a validated access plan.

## Responsibilities

| File | Responsibility |
|---|---|
| `parser.pl` | Character and token DCGs, source lines, assembly syntax and constant-expression trees |
| `effects.pl` | Finite instruction catalogue, normalized actions, typed register effects, memory, flags, control flow and traps |
| `ir.pl` | Signature assumptions, initialized-register/type checks, register-to-value mapping and action lowering |
| `flags.pl` | Branch conditions, flag dependencies and value availability |
| `cfg.pl` | Blocks, typed value lowering and independent edge-transfer validation |
| `dataflow.pl` | Finite type/flag fixed point and local inductive obligation checker |
| `accesses.pl` | Read-group proposals, decision traces and an independent structural validator |
| `check-model.pl`, `check-reuse.pl`, `check-validator.pl` | Protection requirements, bounded witness search and independent certificate validation |
| `target.pl` | Architecture selection; explicit rejection for AArch64/arm64 and unknown targets |
| `x86_64.pl` | Little-endian extraction and unsigned integer semantics expressed as Fil-C C |
| `x86-flags.pl`, `x86-cfg.pl` | Flag computation, branches and simultaneous typed edge assignments in C |
| `report.pl` | Prolog inspection output, grouping explanations and source-located diagnostics |
| `main.pl` | CLI, pass sequencing and output selection |
| `tests.pl`, `effects-tests.pl` | Parser, effect catalogue, normalized semantics, access plans and decision traces |
| `pointer-tests.pl` | Pointer-copy type propagation, derived addresses and aliased operands |
| `store-tests.pl` | Write effects, immediate ranges, preserved registers and ordering barriers |
| `pointer-memory-tests.pl` | Pointer annotations, typed memory effects and register/value flow |
| `dataflow-tests.pl` | Cycles, first-iteration facts, missing predecessors and resource exhaustion |
| `check-tests.pl`, `check-runtime.c`, `check-safety.py` | Protection certificate mutations, native/C comparisons and conditional failure behavior |
| `protection-probe.py`, `protection-probe*.c` | Compiler check scheduling inspection and lifetime tests |
| `cfg-tests.pl`, `edge-swap-test.pl` | Joins, unavailable flags, malformed edges and an executable cyclic assignment |
| `diagnostic-tests.py` | Malformed-source fixtures and CLI inspection modes |
| `generated-tests.py`, `branch-generated-tests.py`, `loop-generated-tests.py`, `native_oracle.py` | Deterministic scalar/branch comparisons against native x86-64 execution |

The [semantic contract](SEMANTICS.md) defines the effect terms, value rules,
assumptions and runtime obligations. The effect relation accepts ground
instructions; `instruction_form/2` enumerates the finite supported forms.

The parser handles labels, selected directives, signature annotations
(`#!` or `;!`), comments, semicolon-separated instructions, quoted strings,
registers, base/index/scale addressing, decimal/octal/hexadecimal integers,
and expressions with parentheses, unary signs, addition, subtraction and
multiplication. Syntax outside the accepted grammar fails. Parsing a
directive does not imply that lowering accepts it.

The executable subset has `unsigned long(ptr)` and
`unsigned long(ptr, unsigned long)` signatures, with a pointer in `%rdi`
and an optional integer in `%rsi`. It supports ordinary integer loads,
32/64-bit integer moves and stores, addition, bitwise operations, immediate shifts,
comparisons, conditional/direct branches, and return. A 64-bit register
copy preserves either an integer or a pointer;
`leaq` derives a pointer from a pointer base, optional integer index and
nonnegative displacement. Registers are mapped to distinct values after
each write;
32-bit writes zero-extend, arithmetic wraps, and shift counts are masked.
The pointer argument remains pointer-typed in generated C.

Branch conditions use actual flag values. All incoming paths must supply a
flag before a branch can read it. Pointer joins preserve whichever pointer
the incoming edge selects, including its capability. Read grouping stays
inside each block. The previous straight-line frontend remains available
with `--linear` for differential testing.

Backedges and loop-carried values are supported. Analysis terminates over
a finite domain; source programs may still contain nonterminating loops.
The test loops have explicit bounds. Calls, stack manipulation, SIMD,
atomics, and partial 8/16-bit register writes remain unsupported.
Unsupported instructions fail explicitly. AArch64 is a deliberately failing
target boundary, not an x86 fallback.

Pointer loads and stores use `movq` with a trailing `#! ptr` annotation
(`;! ptr` also works):

```asm
movq (%rdi), %r8       #! ptr
movq %r8, 8(%rdi)      #! ptr
```

These operations access an eight-byte-aligned pointer slot and preserve
Fil-C's capability metadata. A pointer store requires a pointer source;
the annotation does not turn an integer register into one. Without the
annotation, memory-source/destination `movq` remains an integer operation.

## Grouping and its limits

The optimizer proposes a partition of consecutive loads into reads of
1, 2, 4 or 8 bytes. It groups only adjoining byte ranges with the same
pointer value, index value and scale. It stops at any intervening scalar or pointer
operation or store. It cannot move reads across a store, even when the
address expressions differ. Pointer loads and stores also separate read
groups; the planner never replaces a typed pointer access with an integer
read. A block boundary also ends a read group.

The validator independently matches the plan against the original ordered
IR, verifies address identities and exact contiguous coverage, and rejects
missing, reordered or mismatched operations. Validation requires ground
terms and successful completion. It uses no tabling, negation-based
inference of safety, or mutable fact database.

This is a structural validation pass, not a formal verification of the
compiler. Parsing, instruction semantics and emission still need to be
correct. Also, these are *read groups*, not authorization to emit unchecked
machine accesses: every resulting C read is still instrumented by Fil-C.
A bug in grouping could change results or trap behavior even though the
compiler continues to enforce memory safety.

The input contract permits ordinary nonvolatile, nonatomic reads and
unobserved intermediate register values. A grouped read may trap before an
individual later read would have trapped. Negative displacements are
rejected in this slice. Effective offsets must fit `PTRDIFF_MAX` without
multiplication or addition overflow; generated guards trap otherwise.
This intentionally excludes assembly that relies on address wraparound.

`--emit-checks` reports advisory certificates for prior covering reads,
including forward joins where every predecessor satisfies the obligation.
`--verify-checks` validates them while emitting unchanged C. Stores, pointer
operations and cyclic edges are conservative barriers. The analysis retains
offset guards and never authorizes unchecked emission. [CHECK_REUSE.md](CHECK_REUSE.md)
describes the proof boundary, rejection tests and measured compiler behavior.

## Validation and next steps

The Nix check runs Prolog tests, builds both grouped and ungrouped assembly,
assembles it with GNU `as`, links a Fil-C C caller, and checks 32,000 lookup
cases per variant against an independent bytewise reference. It also
checks unaligned inputs, scalar arithmetic and changing index values.
Negative cases exercise null capabilities, out-of-bounds reads in both
variants, and offset overflow. Unsupported architectures must fail without
producing assembly.

The effect table covers all 61 accepted instruction forms. Fifty-one
malformed-source fixtures check failure reasons and source lines. A
deterministic generator exercises 181 small programs, comparing 46,336
return values and full memory buffers in four variants (block/linear frontend,
each with grouping on/off) against the original assembly executed natively. This oracle does not reuse the Prolog rules or
C emitter. Subprocess execution is bounded. The check output retains the
generated sources, case descriptions, binaries and result streams, along
with the original example's C and assembly, for inspection.

Another 525 programs test branches, including all 16 conditions, signed and
unsigned comparisons, parity/carry/overflow, flag replacement and preservation,
and flag joins. Native execution agrees on 134,400 return/full-buffer
outcomes per grouped/ungrouped variant. `examples/branches.s` additionally
checks 4,096 selections, stores and swaps per variant with real Fil-C
pointer slots. Seven failure modes exercise both arms, including a pointer
whose address was changed while retaining the wrong capability, after a
successful access to the other object. Null, freed, out-of-bounds and
read-only selections still fail.

`examples/pointers.s` copies a pointer, derives an indexed pointer with
`leaq`, copies it again and performs the table lookup. Another 32,000 cases
per variant compare this against a C reference. Null, freed and missing
capabilities, crossing the allocation boundary and offset overflow must
still fail after copying or deriving a pointer. The check retains its
generated C so the pointer representations can be inspected directly.

`examples/stores.s` includes overlapping 32/64-bit reads and writes, checked
against a bytewise C reference in 8,000 cases per variant. Failed-store
tests cover read-only memory, missing/freed capabilities, allocation
boundaries and offset overflow. Whole-buffer comparisons include untouched
bytes, so a correct return value cannot hide an incorrect store.

`examples/pointer-memory.s` loads, copies, stores and dereferences pointers,
including pointers back to their own slots. Fil-C callers check 16,384
indexed reads, 2,048 round trips and 256 self references per variant.
Fifteen failure modes per variant cover pointer alignment, slot/pointee
bounds and lifetime, read-only destinations, and real addresses rebuilt
byte by byte without a capability. A separate overwritten-slot case checks
that changed address bits cannot escape the original capability's bounds.

`examples/decoder.s` is a bounded table decoder with input/output cursors
and a status result. It agrees with a bytewise C reference in 10,240 cases
per variant, including five layouts where buffers can overlap. Another 55
native loop programs compare 14,080 complete outcomes per variant; a bounded
node walk checks capabilities across different objects. Nineteen failure
modes cover later iterations, pointer backedges and partial table entries.
[DECODER.md](DECODER.md) gives the format, contract and assembly findings.

The tests intentionally cross the actual allocation boundary: Fil-C rounds
small allocations up, so `malloc(3)` is not a reliable four-byte-read
failure fixture.

The [development plan](PLAN.md) turns the next steps into ordered milestones,
with implementation boundaries, acceptance criteria, and explicit decisions
before adding a direct assembly backend. Milestones 1–5 are
complete: explicit effects, pointer operations and stores, blocks and
branches, a bounded decoder loop, and the check-reuse investigation.
The backend decision and representative performance evaluation are next.
The remaining milestones describe
planned extensions, not currently supported input.
