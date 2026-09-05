# Semantic contract

This document covers the current x86-64 subset with control flow. The compiler
accepts annotated assembly and produces Fil-C C, then delegates machine
code, capabilities, GC roots and the calling convention to Fil-C. The
observable results are the function's integer return value and permitted
memory reads and writes; source registers and arithmetic flags are internal state.

## Instruction actions and effects

`sp_effects:instruction_effects(+Instruction, -Semantics)` accepts a ground
instruction AST from the parser. It either produces a normalized action
and its effects or rejects the instruction. It does not infer input types
from how a register happens to be used. `instruction_form/2` enumerates the
61 supported forms independently of a particular function or register
state.

For example, `movzwl 2(%rdi,%rsi,4), %eax` has this description:

```prolog
semantics(
  load(address(register(rdi,64),register(rsi,64),4,2),2,register(rax,32)),
  effects(
    registers(
      [read(register(rdi,64),pointer),read(register(rsi,64),integer)],
      [write(register(rax,32),integer,zero_extend(64))]),
    memory([access(read,
      address(register(rdi,64),register(rsi,64),4,2),2,alignment(1),ordinary,integer)]),
    flags(reads([]),defined([]),cleared([]),undefined([]),
          preserved([cf,pf,af,zf,sf,of])),
    control(next),
    may_trap([address_overflow,invalid_read])))
```

`register(rax,32)` denotes the `%eax` view of `%rax`. The load reads two
bytes and zero-extends the integer into that view; its write also clears
the upper 32 bits of `%rax`. `alignment(1)` permits unaligned byte addresses.
`ordinary` excludes volatile and atomic access semantics. The trap list
names outstanding runtime obligations, not checks the analysis has proved.

`--emit-effects` wraps each description in `located(Line, Semantics)` and
groups them by function. `ir.pl` resolves the typed reads against the
current register state, lowers the action, and applies its declared writes.
Each write creates a fresh value identity, so changing an index register
changes the address identity seen by subsequent passes.

For a 64-bit register copy the read requirement is `read(Source,value)`
and the write is `write(Destination,same_type_as(Source),replace)`. This
rule accepts either an integer or a pointer and preserves its static type.
Lowering resolves that constraint using the source's old value. The rule
cannot turn integer bits into a pointer. A 32-bit copy remains integer-only.

## Where the facts come from

| Fact | Source and enforcement |
|---|---|
| `%rdi` initially holds a pointer; optional `%rsi` holds an integer; result is an integer | Signature annotation, checked against the supported function signatures |
| An operand reads an integer or a pointer of a particular width | Instruction effect rule, checked against initialized register state by lowering |
| Integer width, zero extension, address scale and access size | Normalized instruction semantics |
| Two loads use the same pointer/index values and adjoining byte ranges | Ordered IR and independent access-plan validation |
| A block input is initialized with a coherent type, or a flag is available | Every reachable predecessor's state and the virtual entry, checked by `dataflow.pl` |
| An edge transfers the right typed values to its original target | Independent edge validator against recorded typed exit states |
| Offset arithmetic does not wrap and fits `PTRDIFF_MAX` | Explicit guards in generated C |
| An accessed capability is live, covers the access and permits a write when requested | Fil-C instrumentation and runtime |

Annotations cannot manufacture a capability. The backend keeps the pointer
parameter pointer-typed, and every access remains a Fil-C memory operation.
The structural validator trusts the original IR produced by lowering; it
checks a transformation of that IR, not the correctness of the parser,
instruction model or emitter.

## Value rules and accepted forms

All scalar values are unsigned bit patterns. A read of a 32-bit register
view takes its low 32 bits. Every supported 32-bit destination write
zero-extends to the full register, including a shift whose masked count is
zero. A 64-bit write replaces the full register. Reads use the old values
before any destination write, including when source and destination alias.

| Forms | Action |
|---|---|
| `movzbl`, `movzwl`, memory-source `movl`/`movq` | Read 1/2/4/8 bytes in little-endian order; zero-extend the loaded integer |
| Register-source `movq` | Copy the complete typed value, preserving a pointer and its capability or an integer |
| Register-source `movl`, immediate-source `movl`/`movq` | Copy an integer into the destination width |
| Register/immediate-source `movl`/`movq` with a memory destination | Store the low 4/8 bytes of an integer in little-endian order; write no register |
| `leaq` with a memory-address operand and 64-bit destination | Derive a pointer from a pointer base, optional integer index, scale and nonnegative displacement; perform no memory access |
| Register/immediate-source `addl`/`addq` | Add modulo the destination width |
| Register/immediate-source `andl`/`andq`, `orl`/`orq`, `xorl`/`xorq` | Bitwise operation in the destination width |
| Immediate-source `shll`/`shlq`, `shrl`/`shrq` | Logical shift by the immediate modulo 32/64; discard bits beyond the destination width |
| Register/immediate-source `cmpl`/`cmpq`, `testl`/`testq` | Compute subtraction/AND flags from destination and source; write no register |
| `jmp Label` | Transfer control to a named block in the same function |
| `je`, `jne`, `jb`, `jae`, `jbe`, `ja`, `jl`, `jge`, `jle`, `jg`, `js`, `jns`, `jo`, `jno`, `jp`, `jnp` | Read the specified condition's flags and choose the named target or fallthrough block |
| `ret` | Return the integer in `%rax` through the Fil-C ABI |

Move immediates range from `-2^(W-1)` to `2^W-1`, interpreted modulo the
destination width `W`. Arithmetic, bitwise and comparison immediates range
from `-2^31` to `2^32-1` for 32-bit operations, or `-2^31` to `2^31-1`
for 64-bit operations
(the latter sign-extend). Shift immediates must be in `[0,255]` before
masking. The supported scale factors are 1, 2, 4 and 8; displacements are
nonnegative unsigned 64-bit constants. Larger effective offsets can still
fail the runtime guards.

Pointer copies and offsets have distinct `pointer_copy` and
`pointer_offset` operations in the value IR. Both produce pointer-typed C
temporaries. Inputs are read before the destination is overwritten, so
`leaq (%rdi,%rsi,4),%rsi` uses the old integer `%rsi` and then makes `%rsi`
a pointer. Returning that pointer as an integer or using it for integer
arithmetic is rejected; an explicit later integer write can change its type.

The initial `leaq` subset deliberately rejects negative displacements,
integer-only address arithmetic, pointer-valued indices and address
wraparound. It uses the same checked offset calculation as memory accesses.
Overflow can trap at pointer derivation even before a dereference; bounds
and liveness remain obligations of any later memory access. Copying a
pointer does not prove those obligations or change its capability.

Integer stores declare `access(write,Address,Bytes,alignment(1),ordinary,integer)`
and possible `address_overflow` or `invalid_write` failures. The source must
be an integer, even for `movq`; pointer stores require an explicit
annotation. Store immediates use the same ranges as
arithmetic immediates, including sign extension for the 64-bit form.

The backend evaluates the source into a width-specific C integer and uses
`__builtin_memcpy` to support unaligned destinations. Its destination cast
removes C's `const` qualifier from the address helper's result; it cannot
grant write permission to a read-only capability. Fil-C still checks each
write. Static integer/pointer types describe allowed source operations,
not an assertion that C integer values or integer-written memory have no
Fil-C metadata. In particular, integer writes must not be treated as proof
that an existing slot's capability has been erased.

## Pointer memory and annotations

`movq Address,%register #! ptr` loads a pointer, and
`movq %register,Address #! ptr` stores one. The annotation must follow the
instruction on the same physical line; `;! ptr` is equivalent. The DCG
produces `instruction(movq,Operands,ptr)`. Naked annotations, annotations
on directives, other opcodes, immediate sources and register-only copies
are rejected. Register copies already preserve their source type.

The pointer load writes a pointer register value; the pointer store reads
a pointer register and writes no register. Both declare a memory access
with width 8, `alignment(8)`, `ordinary` ordering and `pointer` value type.
Permission, width, alignment and value type are separate fields. The
backend asserts that its C pointer size and alignment match this layout.

The value IR has distinct `pointer_load` and `pointer_store` operations.
The C backend dereferences pointer-typed slots, leaving both the address
word and its invisible capability to Fil-C. It does not load an integer
and reinterpret it to reconstruct a capability. Fil-C checks slot bounds,
alignment and write permission; any later dereference separately checks
the loaded pointer's own capability. A pointer value need not address an
eight-byte-aligned pointee when the later access is an ordinary byte load.

Annotations specify access semantics, not a proof of valid memory. An
integer-only slot can yield non-null address bits with a null capability,
and a loaded pointer can refer to a freed object. Both remain unusable for
an invalid dereference. A slot that previously held a pointer may retain
that capability after bytewise integer writes; changing its address bits
does not expand the original bounds. The tests cover these cases using
real live addresses, rather than relying on unmapped-address faults.

All pointer loads/stores are ordering barriers for the read planner. They
are never grouped with ordinary integer reads, because that would need a
separate argument about capability metadata as well as byte coverage.

`ret` is a function-level action here. Its physical stack read and stack
pointer adjustment belong to the backend's calling convention, not the
source-level memory-effect list. Stack instructions remain unsupported.

## Arithmetic flags

Effects partition the six arithmetic flags into defined, cleared,
undefined and preserved sets. Branches declare the flags their condition
reads. They preserve all flags for subsequent blocks.

| Operation | Defined | Cleared | Undefined | Preserved |
|---|---|---|---|---|
| Load, store, move, LEA, return, jump/branch, shift with masked count 0 | — | — | — | CF, PF, AF, ZF, SF, OF |
| ADD, CMP | CF, PF, AF, ZF, SF, OF | — | — | — |
| AND, OR, XOR, TEST | PF, ZF, SF | CF, OF | AF | — |
| Shift with masked count 1 | CF, PF, ZF, SF, OF | — | AF | — |
| Shift with larger masked count | CF, PF, ZF, SF | — | AF, OF | — |

These classifications follow the instruction descriptions in the
[Intel instruction-set reference](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
The supported 32/64-bit shifts mask counts below the operand width.

`flags.pl` binds each defined or cleared flag to its producing instruction.
`x86-flags.pl` computes the flag bits with unsigned width-limited arithmetic:
carry/borrow, signed overflow from sign-bit relations, auxiliary carry,
low-byte even parity, zero and sign. CMP computes destination minus source;
TEST computes their AND. Undefined flags have no usable value. A zero-count
shift retains previous flag identities; changing a compared register with
MOV does not change the comparison's captured operands. C arithmetic cannot
overflow a signed temporary in these recipes.

| Conditions | Expression (the second condition is the inverse) |
|---|---|
| E / NE | ZF |
| B / AE | CF |
| BE / A | CF or ZF |
| L / GE | SF differs from OF |
| LE / G | ZF or (SF differs from OF) |
| S / NS | SF |
| O / NO | OF |
| P / NP | PF |

Flags are initially unavailable. A consumer of an unavailable or undefined
flag fails at the source line, including OF after a shift greater than one.
The C helper may compute deterministic bits for undefined flags, but those
bits never enter the usable flag state. Flags are internal values; their
physical machine-register state is not promised across the function ABI.

After graph and access validation, `conditions.pl` may replace one of the
first five pairs of conditions above with a direct comparison if every
referenced flag has the same local CMP producer. The proof names that
producer; the validator independently matches the original formula to the
comparison's signedness, relation, width and captured operands. It also
requires unchanged entry, blocks, operations and outgoing edges. Merely
finding a nearby CMP is insufficient. A later MOV does not change the
captured operands; a later ADD replaces the relevant flag identities.
Block-parameter flags and mixed producers retain the original formula.

Unsigned comparisons use width-specific casts. Signed ordering uses the
equivalent unsigned ordering after toggling both operands' sign bit, avoiding
out-of-range signed casts and signed overflow. Equality uses unsigned bits.
The rewrite introduces no memory accesses or offset calculations and removes
no protection. `--no-simplify-conditions` retains the original flag formula
as a selectable reference; it is independent of `--no-coalesce`.

## Blocks, joins and edges

Labels and terminators form explicit blocks. Adjacent labels alias one
block. Targets must name a label inside the same function; conditional
branches need a fallthrough block, and falling out of a function is
rejected. Cycles need not terminate at runtime.
Unknown opcodes, duplicate labels, unresolved targets and malformed block
structure are rejected before reachability filtering. Unreachable blocks
then contribute no values and produce no code.

`dataflow.pl` computes a finite fixed point before any value lowering.
Each register carries a nonempty set of possible types: integer, pointer,
or uninitialized. Each flag carries a nonempty subset of defined/undefined.
A synthetic entry edge supplies signature types, uninitialized remaining
registers and undefined flags, including when a backedge targets block zero.
Joins union these possibilities. Instruction writes replace the affected
type; a typed copy transfers its source's possibilities. Defined/cleared
flags become defined, undefined flags become undefined, and other flags
retain their state. Read requirements are enforced after convergence.

The worklist starts at entry and queues successors whenever an exit state
changes. Known states only grow in this finite domain. With nine supported
register roots and six flags, there are at most 39 facts per block, so
39 times the block count bounds successful state updates. Reaching the
budget before convergence throws an error; no partial result is emitted.
A source loop can run forever while its compilation analysis terminates.

A separate checker verifies local inductive obligations without running
the worklist again. States must cover the entry state and **all** predecessor
outputs, and each output must cover its instruction effects applied to its
input. Every domain is nonempty and contains only allowed values. These
obligations permit conservative overapproximations but cannot omit a real
path or manufacture first-iteration initialization from a backedge. The
graph, entry signature and instruction-effect transfer remain trusted.

At a join, possible register types accumulate across predecessors. A value
is usable only if every predecessor supplies the same type: all integers
produce an integer block parameter, all pointers a pointer block parameter.
A missing value remains unavailable; incompatible types remain a conflict.
An unconditional overwrite may replace either before any read. A flag is
available only if every predecessor supplies it. Entry has no flags, so it
cannot establish a flag merely by having no earlier block.

Pointer parameters may select different objects or different derived
addresses. Each incoming edge copies the complete typed pointer; its
capability travels with its address. The join does not union bounds or
establish protection for any access. A successful check on one predecessor
does not authorize an access on another. Every actual access still goes
through Fil-C.

An edge lists typed simultaneous assignments to the target's block
parameters. The C emitter saves every source in a temporary before
overwriting any destination. This handles cyclic swaps of both integers
and pointers; an executable self-edge assignment test covers that staging
and is complemented by executable source loops.

The independent edge validator compares the proposed graph with recorded
typed exit states and original terminators. It checks groundness, block
identity and order, unchanged bodies and conditions, original targets,
parameter count, destination/type, and the exact outgoing value for each
register or flag. It does not call the edge-construction predicates or
repeat the worklist search. It trusts the lowering and recorded state;
this validates edge construction, not the entire dataflow analysis.
Read grouping runs separately inside each validated block.

`--linear` retains the earlier straight-line lowering as a differential
reference. It shares instruction/value semantics but has no block analysis,
edge assignments or flag consumers; branches fail explicitly.

## Read-group proposals and validation

The planner greedily tries supported widths 8, 4 and 2 larger than the
original load. Each candidate must cover an exact prefix of adjoining
loads with the same pointer identity, index value and scale. It cannot
split a load or cross another operation. Stores are unconditional barriers;
different address expressions are not sufficient evidence of non-aliasing.
If no candidate works, it retains
the original width. `--no-coalesce` retains every individual load.

`plan/4` returns decisions containing the first load's value and line,
chosen width, covered source lines and each attempted candidate's outcome.
Rejections name changed address components, gaps, split loads or ordering
barriers. This trace comes from the actual search, and `--explain` renders
it only after validation succeeds.

The validator has its own coverage calculation and does not call the
planner's candidate or compatibility predicates. It checks groundness,
original-prefix identity, address components, supported widths, exact
contiguous coverage, displacement-range overflow and unchanged remaining
operations. Missing, reordered or substituted operations cannot disappear
inside an accepted group. This is structural validation, not a formal proof
of the whole compiler.

A read group permits a single wider **checked** C read and extraction of
its component integers. It establishes neither bounds nor liveness and
does not authorize unchecked machine instructions. The input contract
permits ordinary nonvolatile, nonatomic reads and unobserved intermediate
register state. A group may trap earlier than a later individual read
would have trapped. Stores retain their original order and separate read
groups. No read group crosses a block boundary. Calls remain unsupported.

## Evidence and next extension

Protection analysis is separate from read grouping. An advisory certificate
names a prior checked read, the exact pointer/capability and index identities,
range, permission, alignment, and every intervening operation/edge. All
incoming paths must reach the witness without invalidation. Stores, pointer
operations, unknown effects and edges belonging to cycles are barriers.
Effective-offset guards remain obligations even when byte coverage follows.
The independent validator checks the supplied certificate without repeating
witness search. Exhaustion and exceptions return no partial analysis result.

These statements concern normal continuation of a **modeled checked read**;
LLVM might eliminate that read before instrumentation. A certificate is
therefore not evidence that a real machine guard remains. `--emit-checks`
and `--verify-checks` leave every C access unchanged. [CHECK_REUSE.md](CHECK_REUSE.md)
specifies the obligations, conservative limits and actual compiler evidence.

The Nix check combines a complete instruction-form table, negative effect
and access-plan tests, source-located malformed-input fixtures, native
differential execution of deterministic small programs, and Fil-C runtime
failure tests. Native comparisons cover valid memory; allocation-boundary,
null-capability and offset-overflow tests exercise failures separately.
These tests increase confidence in the implementation without replacing
its contract or proving it complete.

Milestones 1–7 are complete. The bounded decoder's contract and assembly
inspection are in [DECODER.md](DECODER.md). [EVALUATION.md](EVALUATION.md)
records the performance evidence and contract differences with the C and
upstream comparisons. [PLAN.md](PLAN.md) selects the next bounded scope.
