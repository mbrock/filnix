# A small Prolog SaRCAsm experiment

This is an independent, deliberately restricted assembly frontend hosted
by Fil-C-built Trealla. It is not a replacement for upstream SaRCAsm.

The first complete slice accepts annotated x86-64 AT&T assembly, parses it
with DCGs, tracks scalar register values, groups compatible reads, checks
the proposed grouping, and emits C. Fil-C then lowers that C to assembly.
The installed command emits assembly by default:

```sh
nix run .#sarcasm-prolog -- experiments/sarcasm-prolog/examples/table-entry.s > /tmp/table-entry.s
nix run .#sarcasm-prolog -- --emit-c experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --emit-ir experiments/sarcasm-prolog/examples/table-entry.s
nix run .#sarcasm-prolog -- --no-coalesce --emit-c experiments/sarcasm-prolog/examples/table-entry.s
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

## Responsibilities

| File | Responsibility |
|---|---|
| `parser.pl` | Character and token DCGs, source lines, assembly syntax and constant-expression trees |
| `ir.pl` | Supported instruction semantics, register-to-value mapping, read-group proposals and a separate validator |
| `target.pl` | Architecture selection; explicit rejection for AArch64/arm64 and unknown targets |
| `x86_64.pl` | Little-endian extraction and unsigned integer semantics expressed as Fil-C C |
| `main.pl` | CLI, pass sequencing, error reporting and output selection |
| `tests.pl` | Parsing, supported semantics, and acceptance/rejection of access plans |

The parser handles labels, selected directives, signature annotations
(`#!` or `;!`), comments, semicolon-separated instructions, quoted strings,
registers, base/index/scale addressing, decimal/octal/hexadecimal integers,
and expressions with parentheses, unary signs, addition, subtraction and
multiplication. Syntax outside the accepted grammar fails. Parsing a
directive does not imply that lowering accepts it.

The executable subset has `unsigned long(ptr)` and
`unsigned long(ptr, unsigned long)` signatures, with a pointer in `%rdi`
and an optional integer in `%rsi`. It supports ordinary integer loads,
32/64-bit integer moves, addition, bitwise operations, immediate shifts,
and return. Registers are mapped to distinct values after each write;
32-bit writes zero-extend, arithmetic wraps, and shift counts are masked.
The pointer argument remains pointer-typed in generated C.

No branches, calls, stack manipulation, stores, pointer loads, pointer
copies, SIMD, atomics, or partial 8/16-bit register writes are supported.
Unsupported instructions fail explicitly. AArch64 is a deliberately failing
target boundary, not an x86 fallback.

## Grouping and its limits

The optimizer proposes a partition of consecutive loads into reads of
1, 2, 4 or 8 bytes. It groups only adjoining byte ranges with the same
pointer value, index value and scale. It stops at any intervening scalar
operation. It does not move reads across calls, stores, branches, or other
observable effects; those instructions are not yet in the executable subset.

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

## Validation and next steps

The Nix check runs Prolog tests, builds both grouped and ungrouped assembly,
assembles it with GNU `as`, links a Fil-C C caller, and checks 32,000 lookup
cases per variant against an independent bytewise reference. It also
checks unaligned inputs, scalar arithmetic and changing index values.
Negative cases exercise null capabilities, out-of-bounds reads in both
variants, and offset overflow. Unsupported architectures must fail without
producing assembly. The check output retains generated C and assembly for
inspection.

The tests intentionally cross the actual allocation boundary: Fil-C rounds
small allocations up, so `malloc(3)` is not a reliable four-byte-read
failure fixture.

The [development plan](PLAN.md) turns the next steps into ordered milestones,
with implementation boundaries, acceptance criteria, and explicit decisions
before adding loops or a direct assembly backend. Start with milestone 1;
the current passing spike is the baseline, not evidence that the proposed
extensions are already supported.
