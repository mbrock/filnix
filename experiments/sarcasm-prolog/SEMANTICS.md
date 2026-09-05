# Semantic contract

This document covers the current straight-line x86-64 subset. The compiler
accepts annotated assembly and produces Fil-C C, then delegates machine
code, capabilities, GC roots and the calling convention to Fil-C. The
observable results are the function's integer return value and permitted
memory reads; source registers and arithmetic flags are internal state.

## Instruction actions and effects

`sp_effects:instruction_effects(+Instruction, -Semantics)` accepts a ground
instruction AST from the parser. It either produces a normalized action
and its effects or rejects the instruction. It does not infer input types
from how a register happens to be used. `instruction_form/2` enumerates the
30 supported forms independently of a particular function or register
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
      address(register(rdi,64),register(rsi,64),4,2),2,alignment(1),ordinary)]),
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
| Offset arithmetic does not wrap and fits `PTRDIFF_MAX` | Explicit guards in generated C |
| An accessed capability is live and covers the memory access | Fil-C instrumentation and runtime |

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
| `leaq` with a memory-address operand and 64-bit destination | Derive a pointer from a pointer base, optional integer index, scale and nonnegative displacement; perform no memory access |
| Register/immediate-source `addl`/`addq` | Add modulo the destination width |
| Register/immediate-source `andl`/`andq`, `orl`/`orq`, `xorl`/`xorq` | Bitwise operation in the destination width |
| Immediate-source `shll`/`shlq`, `shrl`/`shrq` | Logical shift by the immediate modulo 32/64; discard bits beyond the destination width |
| `ret` | Return the integer in `%rax` through the Fil-C ABI |

Move immediates range from `-2^(W-1)` to `2^W-1`, interpreted modulo the
destination width `W`. Arithmetic/bitwise immediates range from `-2^31` to
`2^32-1` for 32-bit operations, or `-2^31` to `2^31-1` for 64-bit operations
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

`ret` is a function-level action here. Its physical stack read and stack
pointer adjustment belong to the backend's calling convention, not the
source-level memory-effect list. Stack instructions remain unsupported.

## Arithmetic flags

Effects partition the six arithmetic flags into defined, cleared,
undefined and preserved sets. No accepted instruction reads a flag.

| Operation | Defined | Cleared | Undefined | Preserved |
|---|---|---|---|---|
| Load, move, LEA, return, shift with masked count 0 | — | — | — | CF, PF, AF, ZF, SF, OF |
| Add | CF, PF, AF, ZF, SF, OF | — | — | — |
| AND, OR, XOR | PF, ZF, SF | CF, OF | AF | — |
| Shift with masked count 1 | CF, PF, ZF, SF, OF | — | AF | — |
| Shift with larger masked count | CF, PF, ZF, SF | — | AF, OF | — |

These classifications follow the instruction descriptions in the
[Intel instruction-set reference](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html).
The supported 32/64-bit shifts mask counts below the operand width.

The descriptions do **not** compute flag values. C lowering drops flags
because the accepted subset cannot observe them; it does not promise their
preservation across the function ABI. Before accepting a branch or another
flag consumer, implement flag values, their dependencies and control-flow
joins as described in [milestone 3](PLAN.md#3-introduce-basic-blocks-and-conditional-control-flow).

## Read-group proposals and validation

The planner greedily tries supported widths 8, 4 and 2 larger than the
original load. Each candidate must cover an exact prefix of adjoining
loads with the same pointer identity, index value and scale. It cannot
split a load or cross a scalar operation. If no candidate works, it retains
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
would have trapped. Calls, stores, branches and other observable effects
remain outside this subset.

## Evidence and next extension

The Nix check combines a complete instruction-form table, negative effect
and access-plan tests, source-located malformed-input fixtures, native
differential execution of deterministic small programs, and Fil-C runtime
failure tests. Native comparisons cover valid memory; allocation-boundary,
null-capability and offset-overflow tests exercise failures separately.
These tests increase confidence in the implementation without replacing
its contract or proving it complete.

Pointer-preserving copies and the initial `leaq` subset are implemented.
Integer stores are next, followed by annotated pointer loads/stores in a
separate slice. Specify their permission, width, alignment and ordering
effects before extending lowering; see
[milestone 2](PLAN.md#2-add-straight-line-pointer-operations-and-stores).
