# A guide to nanofil's IR and NFB bytecode

**nanofil** is a C compiler written in Prolog that targets [Fil-C](https://fil-c.org/)'s memory-safe x86-64 ABI, paired with a machine-checked model in Rocq. Unlike an ordinary C compiler, where memory-safety checks are either absent or emitted implicitly during code generation, nanofil makes every safety check and pointer invariant an explicit term in its intermediate representation (IR).

That design lets three tools share a single contract:

1. **The compiler** ([`src/`](../src/)) lowers C to an *unchecked* IR, optimizes it, translates it into a *checked* IR where every bounds check, capability projection, and garbage-collector safepoint is explicit ([`pizlonate.pl`](../src/pizlonate.pl)), optionally reuses check evidence ([`check_reuse.pl`](../src/check_reuse.pl)), validates the result ([`ir.pl`](../src/ir.pl)), and emits Fil-C x86-64 assembly ([`filc_amd64.pl`](../src/filc_amd64.pl)).
2. **The relational interpreter** ([`interp.pl`](../src/interp.pl)) executes any IR module at any stage and distinguishes a normal Fil-C runtime panic (`trap(Reason)`) from a compiler bug where a raw access ran without valid check coverage (`unchecked(Reason)`).
3. **The Rocq model and backend** ([`rocq/theories/`](../rocq/theories/), [`rocq/backend/`](../rocq/backend/)) transcribe the checked IR's syntax ([`Syntax.v`](../rocq/theories/Syntax.v)), small-step semantics ([`Semantics.v`](../rocq/theories/Semantics.v)), and validator ([`Validate.v`](../rocq/theories/Validate.v)), prove that no validated module ever executes an unchecked access ([`Soundness.v`](../rocq/theories/Soundness.v)'s [valid_no_unchecked]), and compile the checked IR to assembly in Gallina.

Historically, the only concrete syntax for a nanofil module was canonical Prolog terms (`module(Items)`). **NFB** (*nanofil bytecode*, specified in [`nfb.md`](nfb.md) and implemented in [`nfb.pl`](../src/nfb.pl), [`NfbTerm.v`](../rocq/backend/NfbTerm.v), and [`Nfb.v`](../rocq/backend/Nfb.v)) gives that same IR a canonical binary representation: a flat stream of little-endian 32-bit words inside a sectioned container.

This guide introduces nanofil's IR from the ground up, explains how its checked stage enforces Fil-C's memory safety, walks through how NFB encodes a module into 32-bit words using real examples from the test corpus, and shows how the Prolog and Gallina implementations fit together.

## Part I: How the nanofil IR Works

### Where the IR sits in the pipeline

When `nanofil cc` compiles a C translation unit, the program passes through two stages of the same IR grammar before becoming x86-64 assembly:

```diagram
C source (.c / .i)
  │  c_pp, c_lex, c_parse, c_types, c_lower
  ▼
Unchecked IR         load(T), store(W, V, A), call, add/sub on p ...
  │  ir:valid_module/1
  │  opt:optimize/3  (-O: inline, promote, copy, simplify, local_storage)
  ▼
Unchecked IR (optimized)
  │  pizlonate:pizlonate_module/2
  ▼
Checked IR           check, raw_load, raw_store, flight, check_function, poll(L) ...
  │  check_reuse     (--checks: reuse, renew, half_check, span_test, limit ...)
  │  ir:valid_module/1
  │  filc_abi, frame_slots, filc_amd64, amd64_regs
  ▼
GNU as assembly (.s)
```

Both unchecked and checked modules use the grammar defined in [`ir.pl`](../src/ir.pl). They are ground Prolog terms—logic variables never appear inside an IR module—and can be written either as text ([`ir_text.pl`](../src/ir_text.pl)) or as NFB binary files (`.nfb`).

### Modules and top-level items

A module is a single term `module(Items)` whose elements are four kinds of top-level items:

| Item term | Meaning |
| --- | --- |
| `func(Name, Linkage, Ret, Params, Blocks)` | A function definition. `Name` is a symbol atom; `Linkage` is `export`, `local`, or `weak`; `Ret` is a return class, `void`, or `tuple([K1, K2])`; `Params` is a list of `param(K, tmp(D))`; `Blocks` is a non-empty list of basic blocks, entry block first. |
| `data(Name, Linkage, Align, DataItems)` | A static data object (or constructor/destructor table entry or weak extern declaration) aligned to `Align` bytes (a power of two from `1` to `4096`). |
| `alias(Name, Linkage, Target)` | A symbol alias (`export` or `weak`) for another function or data object `Target` defined in the same module. |
| `context(Name, Records)` | Optional provenance metadata ([`provenance.pl`](../src/provenance.pl)) recording which C declarations and typed AST nodes produced each temporary and instruction. Ignored by validation, interpretation, and code emission. |

A `data` item's `Linkage` controls where it lives and how it is linked:

- `export`, `local`, `weak`: writable data (`.data` / `.bss`).
- `ro(export)`, `ro(local)`, `ro(weak)`: read-only data (`.rodata`); attempting a write through a capability to a `ro(...)` object traps with `readonly`.
- `tls(export)`, `tls(local)`: thread-local storage; each thread gets its own instance initialized from `DataItems` when it first takes the symbol's address.
- `init(ctor, Priority)` or `init(dtor, Priority)`: a constructor or destructor entry run before `main` or at exit (`Priority` is `0..65535` or `none`), holding a single `item(p, sym(F, 0))` naming a function `F` in the module.
- `extern(weak)` with `DataItems = []`: declares an undefined external symbol as weak so `global(Name)` evaluates to a null pointer if no linked object defines it.

Inside a `data` item, `DataItems` is a list of initializer directives:

| Data item | Bytes | Meaning |
| --- | --- | --- |
| `item(W, const(N))` | `width_bytes(W)` (`1`, `2`, `4`, `8`, or `10`) | Integer or float bit-pattern `N` at store width `W` (`b`, `h`, `w`, `l`, `s`, `d`, `x`). |
| `item(b, str(Chars))` | `length(Chars)` | Raw byte array, one one-character atom per byte (`0..255`). |
| `item(l, sym(S, Off))` | `8` | Plain mode only: the 64-bit address `S + Off`. |
| `item(p, sym(S, Off))` | `8` | Fil-C mode only (must be 8-byte aligned inside the object): a pointer to `S + Off` carrying `S`'s capability in the object's aux table. |
| `zero(N)` | `N` | `N` zero bytes. |

### Modes: `plain` vs. `filc`

Every module has a mode inferred from the vocabulary it uses (`ir:module_mode/2`):

- **`plain` mode** uses only 32- and 64-bit integers (`w`, `l`) and 32- and 64-bit IEEE floats (`s`, `d`). Memory addresses are 64-bit integers (`l`), and [`amd64.pl`](../src/amd64.pl) compiles the module to ordinary System V x86-64 assembly.
- **`filc` mode** is entered as soon as a module mentions the pointer class `p`, an 80-bit extended float `x`, a `tuple([K1, K2])` return, read-only/TLS/init/weak linkages, pointer-only operations (`ptoi`, `itop`, `flight`, `check`, ...), or a call to an external symbol not defined in the module. Addresses are `p` values (pointers paired with capabilities).

### Value classes and operands

Every temporary, parameter, and operation result has a single-letter **class**:

| Class | Width | Stage / Mode | Meaning |
| --- | --- | --- | --- |
| `w` | 32-bit | both | 32-bit integer (unsigned range `0 .. 2^32 - 1`, two's complement signed). |
| `l` | 64-bit | both | 64-bit integer (also the address class in `plain` mode). |
| `s` | 32-bit | both | IEEE 754 binary32 float (`float`); constants hold its unsigned 32-bit pattern. |
| `d` | 64-bit | both | IEEE 754 binary64 float (`double`); constants hold its unsigned 64-bit pattern. |
| `x` | 80-bit | `filc` | x87 80-bit extended float (`long double`); never a parameter, call argument, return value, or phi. |
| `p` | 64-bit addr + cap | `filc` | Flight pointer: a 64-bit address (`intval`) paired with a Fil-C capability (`lower`). |
| `a` | proof | `checked`, `filc` | Proven address: a pointer or named local cleared by a bounds/rights/alignment check. |
| `f` | proof | `checked`, `filc` | Proven function: a `p` value cleared by `check_function` for an immediately following `raw_call`. |

Sub-word memory accesses use narrow specifiers rather than separate register classes:

- **Store widths (`W`)**: `b` (1 byte), `h` (2 bytes), or a value class `w`, `l`, `p`, `s`, `d`, `x`.
- **Load and extension types (`T`)**: `sb` / `ub` (signed/unsigned byte), `sh` / `uh` (signed/unsigned 16-bit halfword), `sw` / `uw` (signed/unsigned 32-bit word), or a full class `l`, `p`, `s`, `d`, `x`. A narrow load sign- or zero-extends into a `w` or `l` destination.

An instruction operand (`Value`) is always one of three ground terms:

- `tmp(Name)`: a temporary register identified by a ground term `Name` (such as `tmp(v0)`, `tmp('pr.1')`, or `tmp(0)`).
- `const(Integer)`: an integer literal (or IEEE bit pattern when read at class `s`, `d`, or `x`; `const(0)` at class `p` is a null pointer with no capability).
- `global(Symbol)`: the address of a function or data symbol `Symbol`. In `filc` mode, `global(S)` is only read by `let(tmp(D), p, copy, [global(S)])` (which calls `S`'s symbol getter to obtain its flight pointer) or as the direct callee of `call(Res, global(S), Args)`.

### Functions, blocks, phis, and temporaries

A function `func(Name, Linkage, Ret, Params, Blocks)` is a control-flow graph of basic blocks:

```prolog
block(Label, Phis, Insts, Jump)
```

Every block has three strictly ordered regions:

1. **`Phis`**: a list of `phi(tmp(D), K, [PredLabel - Value, ...])` nodes. When control enters `Label` from `PredLabel`, every phi in `Phis` reads its corresponding `Value` simultaneously and binds `tmp(D)` at class `K`. The first block in `Blocks` is the **entry block** and must have `Phis = []`. Every predecessor that can jump to `Label` must appear once in each phi's pair list.
2. **`Insts`**: a flat list of non-branching instructions executed sequentially.
3. **`Jump`**: a single terminator that ends the block:
   - `goto(Target)`: unconditional jump.
   - `branch(V, TargetTrue, TargetFalse)`: jump to `TargetTrue` if `V` (of class `w` or `l`) is nonzero, else `TargetFalse`.
   - `ret(V)`: return a single value `V` matching `Ret`.
   - `rets([V1, V2])`: return a two-word struct (`Ret = tuple([K1, K2])`, where each `Ki` is `l`, `p`, `s`, or `d`).
   - `ret`: return from a `void` function.
   - `unreachable`: trap immediately if reached.

Each `Target` in `goto` or `branch` is either a block label `L` or `poll(L)`. On a `poll(L)` edge, after evaluating the destination block's phi inputs and before executing its instructions, the thread performs a Fil-C **pollcheck** (a garbage-collector and signal safepoint).

#### Temporaries and dominance (almost-SSA)

Frontend-generated IR is in strict Static Single Assignment (SSA) form: every parameter and instruction defines a fresh temporary `tmp(D)`. However, the IR grammar and validator (`ir:definitions_dominate/3`) actually enforce a slightly broader rule:

- Parameters in `Params` must have distinct names and may never be redefined by any instruction.
- No block may define the same temporary twice in its `Phis`.
- Every use of `tmp(U)` in a reachable block (and every phi input along an edge from a reachable predecessor) must be **dominated** by at least one definition of `tmp(U)`.

Thus, `ir.pl` permits a temporary to be defined more than once, provided some definition dominates every use. Several hand-written validator fixtures in the corpus—such as `rocq/tests/interval.ir`, `rocq/tests/dominance.ir`, and `tests/fixtures/memory.ir`—deliberately redefine a temporary to test dominance and liveness boundaries. When check-reuse passes reason about pointer provenance across blocks, they restrict their proofs to `single_definitions/3`, the subset of temporaries defined only once in the function.

### The instruction set

Instructions fall into two categories: `let(tmp(D), K, Op, Args)`, which computes `Op` on `Args` and binds `tmp(D)` of class `K`, and standalone instructions (`store`, `call`, `flight`, `local_alloc`, ...).

#### Operations inside `let(tmp(D), K, Op, Args)` (both stages)

| Operation `Op` | Result `K` | Arguments `Args` | Semantics |
| --- | --- | --- | --- |
| `add`, `sub` | `w`, `l`, `s`, `d`, `x`, `p` | `[K, K]`, or `[p, l]` for `p` | Integer/float addition or subtraction; in unchecked `filc` mode, pointer offset arithmetic. |
| `mul`, `div` | `w`, `l`, `s`, `d`, `x` | `[K, K]` | Multiplication, signed integer division, or IEEE float division. |
| `udiv`, `rem`, `urem`, `and`, `or`, `xor` | `w`, `l` | `[K, K]` | Unsigned division, signed/unsigned remainder, bitwise logic. |
| `sar`, `shr`, `shl` | `w`, `l` | `[K, w]` | Arithmetic right shift, logical right shift, left shift (shift count is class `w`). |
| `neg` | `w`, `l`, `s`, `d`, `x` | `[K]` | Two's complement or IEEE negation. |
| `copy` | any `K` | `[K]` | Value copy; `let(tmp(D), p, copy, [global(S)])` calls symbol `S`'s getter. |
| `cmp(Cond, K1)` | `w` or `l` (`w` if `K1` is float) | `[K1, K1]` | `1` if the comparison holds, else `0`. Integer `Cond`: `eq`, `ne`, `sle`, `slt`, `sge`, `sgt`, `ule`, `ult`, `uge`, `ugt`. Float `Cond`: `eq`, `ne`, `le`, `lt`, `ge`, `gt`, `o` (ordered), `uo` (unordered). |
| `ext(T)` | `l` for `sw`/`uw`; `w` or `l` for `sh`/`uh`/`sb`/`ub`; `d` or `x` for `s`; `x` for `d` | `[w]`, `[s]`, or `[d]` | Sign/zero-extend narrow integer from low bits of `w`, or widen float (`s -> d`, `s -> x`, `d -> x`). |
| `truncd`, `truncx` | `s` (`truncd`); `s` or `d` (`truncx`) | `[d]` or `[x]` | Narrow float precision. |
| `stosi`, `stoui`, `dtosi`, `dtoui`, `xtosi`, `xtoui` | `w`, `l` | `[s]`, `[d]`, or `[x]` | Convert float to signed (`*tosi`) or unsigned (`*toui`) integer, truncating toward zero. |
| `swtof`, `uwtof`, `sltof`, `ultof` | `s`, `d`, `x` | `[w]` or `[l]` | Convert signed or unsigned 32/64-bit integer to float. |
| `cast` | `w`, `s`, `l`, `d` | `[s]`, `[w]`, `[d]`, `[l]` | Bitwise reinterpretation between `w` and `s` (32-bit) or `l` and `d` (64-bit). |
| `ptoi`, `itop` | `l` (`ptoi`), `p` (`itop`) | `[p]` or `[l]` | Extract 64-bit integer address from pointer (`ptoi`), or construct pointer with `none` capability from integer (`itop`). |
| `alloc(Align)` | `l` (`plain`) or `p` (`filc`) | `[l]` (byte size) | Allocate zeroed object aligned to `Align` (`4 .. 4096`) with fresh capability. |
| `load(T)` | class of `T` | `[Addr]` | Unchecked stage (or `plain` mode): load `T` from `Addr`. |
| `atomic_load(p)` | `p` | `[p]` | Unchecked stage: sequentially consistent atomic pointer load (`filc_load_ptr_atomic`). |
| `cas(T)` | class of `T` | `[K, K, p]` (`Expected`, `New`, `Addr`) | Unchecked stage: sequentially consistent atomic compare-exchange (`T` in `l`, `sw`, `uw`, `sh`, `uh`, `sb`, `ub`, `p`). |
| `va_args`, `va_arg` | `p` (`va_args`), any (`va_arg`) | `[const(N)]` or `[p]` | Variadic argument snapshot cursor at fixed-prefix byte offset `N` (`va_args`), and advancing load through a `va_list` (`va_arg`). |
| `setjmp(Kind)` | `w` | `[p, w]` (`Buf`, `SaveMask`) | `setjmp`, `'_setjmp'`, or `sigsetjmp`. |

#### Checked-stage operations and standalone instructions

When `pizlonate:pizlonate_module/2` lowers an unchecked Fil-C module to the **checked stage**, implicit pointer operations are replaced by explicit check and access forms:

| Checked form | Defines | Meaning |
| --- | --- | --- |
| `let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P])` | `tmp(Q)` : `a` | Trap unless `P`'s capability allows `Rights` (`read` or `write`) on `[P+Lo, P+Hi)` and `P+Lo` is `Align`-aligned (`1`, `2`, `4`, `8`, or `16`). |
| `let(tmp(Q), a, check_ahead(Lo, Hi, Rights, Align, AHi), [P])` | `tmp(Q)` : `a` | Check `[P+Lo, P+Hi)` where `[Lo, AHi)` covers the immediate access and `[AHi, Hi)` is anticipated for an inevitable downstream access. |
| `let(tmp(Q), a, renew(Lo, Hi, Rights, Align), [Q1, P])` | `tmp(Q)` : `a` | Renew dominating heap proof `Q1` for pointer `P` at a known constant offset: checks only temporal flags (not freed, and not read-only on write). |
| `let(tmp(Q), a, renew_hull(Lo, Hi, Rights, Align), [QL, QH, P])` | `tmp(Q)` : `a` | Renew `P` using the bounding interval hull of two dominating heap proofs `QL` and `QH` of the same object. |
| `let(tmp(Q), a, half_check(Bound, Lo, Hi, Rights, Align), [Q1, P])` | `tmp(Q)` : `a` | Test only the `upper` or `lower` bound (plus temporal flags), relying on dominating proof `Q1` for the other bound. |
| `let(tmp(G), w, span_test(Lo, Hi), [P])` | `tmp(G)` : `w` | Non-trapping range check: evaluates to `1` if `P` is a live object whose bounds contain `[P+Lo, P+Hi)`, else `0`. |
| `let(tmp(Q), a, renew_if(Lo, Hi, Rights, Align), [P, G])` | `tmp(Q)` : `a` | Check `P` where a passing `span_test` guard `G` discharges the bounds check when `G == 1`. |
| `let(tmp(U), l, limit(Size), [P])` | `tmp(U)` : `l` | Non-trapping snapshot of `P`'s capability and bounds for `Size`-byte accesses, consumed only by `check_limit`. |
| `let(tmp(Q), a, check_limit(Lo, Hi, Rights, Align), [P, U])` | `tmp(Q)` : `a` | Check `P` against snapshot `U` taken from a pointer with the same capability `lower`. |
| `let(tmp(Q), a, check_local(Name, Off, Bytes, Rights, Align), [])` | `tmp(Q)` : `a` | Prove `[Off, Off+Bytes)` lies within the exact size of invocation-local stack object `Name`. |
| `let(tmp(F), f, check_function, [P])` | `tmp(F)` : `f` | Trap unless `P` carries a function capability at its exact callable address. |
| `let(tmp(D), K, raw_load(T, Off), [Q])` | `tmp(D)` : `K` | Non-pointer load of `T` at proven address `Q + Off` (`T` cannot be `p`). |
| `let(tmp(D), p, raw_load_pointer(Off, Effects), [Q])` | `tmp(D)` : `p` | Load a pointer at `Q + Off` executing the ordered protocol `Effects`. |
| `let(tmp(D), K, raw_cas(T, Off), [Q, Exp, New])` | `tmp(D)` : `K` | Atomic compare-exchange at proven address `Q + Off`. |
| `raw_store(W, Off, V, Q)` | none | Non-pointer store of `V` (width `W` ≠ `p`) at proven address `Q + Off`. |
| `raw_store_pointer(Off, V, Q, Effects)` | none | Store pointer `V` at `Q + Off` executing the ordered protocol `Effects`. |
| `raw_call(Res, F, Args)` | `0`, `1`, or `2` temps | Indirect call to proven function `F` (of class `f`). |
| `flight(tmp(D), Op, Args, Lower)` | `tmp(D)` : `p` | Construct a pointer `p` from 64-bit unsigned address math (`Op` in `copy`, `add`, `sub`; each arg is an `l` value or `address(P)`) and capability `Lower` (`none` or `lower(P)`). |
| `touch(tmp(Q))` | none | Consume proof `tmp(Q)` without reading or writing memory (the checked form of `access(Rights, A, Size, Align)`). |

Finally, the remaining standalone instructions can appear in either stage (except `store` and `atomic_store`, which pizlonation replaces in Fil-C modules):

- `store(W, V, A)` and `atomic_store(p, V, A)`: unchecked memory stores.
- `fence`: sequentially consistent memory fence (`mfence`).
- `access(Rights, A, Size, Align)`: unchecked full-width vector check (pizlonates to `check` + `touch`).
- `local_alloc(Name, Size)`, `local_load(tmp(D), K, T, Name, Off)`, `local_store(W, V, Name, Off)`: allocate and access an invocation-local stack object `Name` of `Size` zeroed bytes (used by `local_storage.pl` for non-escaping stack objects). In the checked stage, `local_load` and `local_store` are lowered to `check_local` followed by `raw_load`/`raw_store`.
- `call(Res, Callee, [arg(K, V), ...])`: call `Callee`. `Res` is `void`, `result(tmp(D), K)`, or `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])`. In checked Fil-C modules, `Callee` must be `global(F)` (indirect calls use `check_function` + `raw_call`).
- `asm_fixed(Mnemonic, Ins, Outs)`: fixed-register inline assembly (`cpuid`, `xgetbv`, `rdtsc`, `rdtscp`, `lfence`, `sfence`, `pause`) reading `Reg-Value` pairs and defining `Reg-tmp(D)` outputs for registers `a`, `b`, `c`, `d`.
- `loc(File, Line)`: source location marker; has no runtime effect.

### Seeing the two stages on a corpus example

Consider [`tests/filc/pointer-effects.ir`](../tests/filc/pointer-effects.ir), a small unchecked Fil-C module from the test suite that allocates a destination buffer and a value pointer, triggers garbage collection, and stores the pointer:

```prolog
func(large_store, export, void, [], [
    block(start, [], [
        call(result(tmp(dst), p), global(c_large), []),
        call(result(tmp(src), p), global(c_value), [arg(l, const(80))]),
        call(void, global(c_collect), []),
        store(p, tmp(src), tmp(dst))
    ], ret)
]).
```

When `pizlonate:pizlonate_module/2` transforms `large_store`, the implicit `store(p, tmp(src), tmp(dst))` becomes two instructions:

```prolog
func(large_store, export, void, [], [
    block(start, [], [
        call(result(tmp(dst), p), global(c_large), []),
        call(result(tmp(src), p), global(c_value), [arg(l, const(80))]),
        call(void, global(c_collect), []),
        let(tmp(chk0), a, check(0, 8, write, 8), [tmp(dst)]),
        raw_store_pointer(0, tmp(src), tmp(chk0),
            [aux_ensure, lower_barrier, rooted_reload, lower_write, address_write])
    ], ret)
]).
```

Nothing is left implicit: `dst` is checked for an 8-byte aligned write on `[dst+0, dst+8)`, yielding the proven address `tmp(chk0)` of class `a`, and `raw_store_pointer` consumes `tmp(chk0)` along with the exact five-step Fil-C pointer-store protocol.

## Part II: How Checked IR Relates to Fil-C's Memory Safety

### GIMSO, flight pointers, and pointers at rest

Fil-C's design principle is **GIMSO** (*Garbage In, Memory Safety Out*): no matter how buggy or adversarial a C program is, it can never read or write memory outside the capability of the pointer it uses. Every operation either behaves according to its C/Fil-C specification or halts the process with a deterministic **Fil-C panic**.

To preserve C layout compatibility (`sizeof(void *) == 8`) while tracking bounds and object lifetime, Fil-C represents pointers differently in registers versus in memory (see [`filc.md`](filc.md)):

- **In flight (class `p`)**: A pointer in a register or frame slot is a pair of 64-bit words `(intval, lower)`:
  - `intval` is the raw 64-bit address visible to the C program. Arbitrary arithmetic (`flight`), casting (`ptoi`), or bit-masking only changes `intval`.
  - `lower` is the capability: an unforgeable pointer to the start of the heap/global/stack allocation the pointer is allowed to access. Immediately below `lower` in memory sits a 16-byte object header containing `upper` (the upper bound address) and the `aux` word (flags for `free` and `readonly`, plus a pointer to the object's shadow capability table).
- **At rest (in memory)**: When a pointer is stored into memory, its 8-byte `intval` is written into the object's ordinary payload bytes, while its `lower` is written at the matching offset inside the object's shadow **aux allocation**.

That split explains why `raw_load_pointer` and `raw_store_pointer` carry an explicit list of memory effects (`ir:pointer_memory_effects/2`):

- A heap pointer load (`[aux_read, lower_resolve, address_read]`) reads the object's aux word, resolves the stored capability (`lower`) from the aux allocation (or an atomic box), and reads the 64-bit `intval` from the primary payload.
- A heap pointer store (`[aux_ensure, lower_barrier, rooted_reload, lower_write, address_write]`) first ensures the destination object has an aux allocation (`aux_ensure`, calling into the runtime to allocate one if this is the first pointer stored into the object), runs the FUGC collector's write barrier (`lower_barrier`), reloads the rooted destination pointer (`rooted_reload`, because `aux_ensure` can exit to the runtime and zero a large aux table), writes the capability (`lower_write`), and writes the 64-bit address (`address_write`).

### `trap(Reason)` vs. `unchecked(Reason)`

Why turn checks into explicit IR instructions instead of simply emitting check assembly inside every `load` and `store`? Because nanofil optimizes checks (`check_reuse.pl`) and proves those optimizations sound in Rocq.

To state what it means for a check optimization to be sound, both [`interp.pl`](../src/interp.pl) and [`Semantics.v`](../rocq/theories/Semantics.v) evaluate capabilities on *both* checks and raw accesses, but give failures different outcomes:

| Instruction kind | Capability permits access | Capability forbids access |
| --- | --- | --- |
| `check`, `half_check`, `check_local`, `check_function` | Returns proven address `a` or function `f` | Halts with **`trap(Reason)`** (a legitimate Fil-C runtime panic: `null_capability`, `out_of_bounds`, `readonly`, `misaligned`, `not_a_function`). |
| `raw_load`, `raw_store`, `raw_call`, `renew`, `renew_hull`, `renew_if`, `check_limit` | Performs the load/store/call or returns the renewed proof | Halts with **`unchecked(Reason)`** (a safety violation: the compiler let an invalid access reach a raw operation without trapping first). |

An `unchecked(Reason)` outcome can never happen in valid unchecked IR. In checked IR, it represents a **soundness bug in the compiler**.

The validator (`ir:valid_module/1` in Prolog, [Validate.valid] in Rocq) statically checks that every raw access and every reuse form in a checked module is backed by valid evidence. Campaign 3's main theorem, [valid_no_unchecked] in [`Soundness.v`](../rocq/theories/Soundness.v), proves:

> For any runtime satisfying the Fil-C runtime axioms ([`Runtime.v`](../rocq/theories/Runtime.v)), if [Validate.valid] accepts a checked module, no execution starting from a ready state ever reaches `Unchecked r`.

### Safepoints, `free`, and check-reuse evidence

In Fil-C, `c: free(p)` does not immediately reuse virtual memory (the concurrent collector FUGC reclaims the memory only after no references remain), but `c: free(p)` immediately sets `upper = lower` and raises the `FREE` flag in the object header so any subsequent dereference traps (`use-after-free`).

Crucially, an object's bounds only ever shrink (to empty, when freed) and never move. Therefore, once `check(Lo, Hi, Rights, Align)` succeeds on a heap pointer `P`, the fact that `[P+Lo, P+Hi)` lies within `P`'s object remains true **until something can call `free`**.

On the current thread, `free` can happen only at a **safepoint**:

- Any `call` or `raw_call` (which may call `free` directly or indirectly).
- Any `poll(L)` edge (where deferred signal handlers may run and call `free`).
- `alloc` (large allocations may exit/re-enter the runtime and run signal handlers), `setjmp`, `va_arg`, or a symbol getter (`copy` of `global(S)`, unless it is a repeated getter whose first call already initialized the symbol).
- A pointer store's `aux_ensure` (`raw_store_pointer` or `atomic_store`), which may exit to the runtime when allocating an aux table.

Every instruction that cannot reach a safepoint or modify object bounds/rights is marked `evidence_preserving` (`ir.pl`, `Syntax.v`). This invariant governs how `check_reuse.pl` optimizes checks and how the validator checks the result:

1. **Direct proof reuse (`--checks=reuse`, `forward`)**: While only `evidence_preserving` instructions and unpolled CFG edges intervene on every path from a dominating heap check `tmp(Q)`, later scalar `raw_load` and `raw_store` instructions whose byte range `[Off, Off+Size)`, rights, and alignment are covered by `tmp(Q)` can reuse `tmp(Q)` directly—eliminating the second check completely.
2. **Temporal renewal (`renew`, `renew_hull`)**: If a safepoint (like a function call or loop poll edge) intervenes after a dominating heap check `tmp(Q1)` of `P1`, the spatial bounds `[Lo, Hi)` and alignment are still guaranteed to fit the object's original allocation, provided the object has not been freed since. `renew(Lo, Hi, Rights, Align)` takes `[tmp(Q1), P]` (where `P` is at a known constant offset from `P1` with the same `lower`) and emits a lightweight native check that tests only the header's `FREE` (and `READONLY`) flags.
3. **One-sided, guarded, and hoisted checks (`half_check`, `span_test` + `renew_if`, `limit` + `check_limit`)**: When an earlier check proved one bound (`half_check`), or a loop preheader ran a non-trapping `span_test` (`renew_if`) or took a `limit` snapshot (`check_limit`), the instruction names the earlier proof or guard temporary as an explicit operand. The validator verifies the dominance and offset-interval side conditions directly from the instruction stream without performing its own search.

## Part III: NFB (nanofil Bytecode)

### What NFB is and why it exists

**NFB** ([`nfb.md`](nfb.md), [`nfb.pl`](../src/nfb.pl)) is a binary encoding of `module(Items)` as a sequence of little-endian 32-bit unsigned integers (**words**). It is not a lower-level VM or a new IR: it encodes the exact grammar of `ir.pl`, in either stage (`unchecked` or `checked`) and either mode (`plain` or `filc`).

Four forces motivated adding NFB alongside Prolog term text:

1. **A wire format for `libnanofil` (JIT and runtime clients)**: The Gallina backend campaign ([`gallina-backend.md`](gallina-backend.md)) compiles nanofil's backend to C++ (via Rocq extraction and Crane) and builds it with Fil-C into a library (`libnanofil`). Runtime clients such as the PCRE2 regular-expression JIT hand IR to the compiler in memory; serializing and parsing Prolog text across that boundary is unnecessary overhead.
2. **Dense integer IDs instead of string-hashed maps**: In the term form, every temporary (`tmp('pr.1')`), block label (`'L3'`), local, and symbol is a ground term looked up in hash maps (`Maps.v`). In NFB, temporaries, blocks, locals, strings, symbols, and wide constants are numbered densely from `0` to `N - 1`, allowing consumers to index flat arrays directly.
3. **Content-addressed module identity**: Printing a module as text allows superficial variations (whitespace, quoting, temporary naming). NFB defines a strict **canonical form**: every valid module has **exactly one** core NFB encoding. The SHA-256 hash of the header and core sections is therefore a sound, rename-invariant cache key for compiled code.
4. **A small, total, verified reader**: Parsing nested text requires a lexer, recursive parser, and error recovery. NFB has no internal file offsets (only forward lengths and dense table indices) and no recursive nesting in code, so its Gallina decoder (`NfbTerm.v`, `Nfb.v`) is a short, total function proved never to exhaust its fuel (`NfbTotal.v`).

### Container and sections

An NFB file is a sequence of 32-bit little-endian words (`uint32_t`). Every length in the format—except string byte lengths—is measured in **words** (4 bytes per word).

#### The 4-word file header

| Word | Field | Value |
| --- | --- | --- |
| `0` | `magic` | `0x0042464E` (the four bytes `'N'`, `'F'`, `'B'`, `0x00` in little-endian order). |
| `1` | `version` | `0x00000001` (`major` in high 16 bits = `0`, `minor` in low 16 bits = `1`). |
| `2` | `flags` | Bitmask: bit 0 (`0x1`) = `checked` stage (`0` = `unchecked`); bit 1 (`0x2`) = `filc` mode (`0` = `plain`); bit 2 (`0x4`) = `ordered`. Bits `3..31` must be `0`. |
| `3` | `nsecs` | Number of sections that follow in the file. |

The `stage` and `mode` bits record what `ir:module_stage/2` and `ir:module_mode/2` derive from the module's instructions and items. The `ordered` bit (`0x4`) is computed by the encoder and set to `1` if and only if in every function:
- Every non-phi temporary operand refers to a temporary ID already defined earlier in the instruction stream (Well-formedness rule 11), and
- Every jump target to a block index ≤ the current block index has its `poll` bit set (Well-formedness rule 12, a one-pass syntactic sufficient condition for `polls_every_cycle/1`).

#### Section framing and section IDs

Immediately after the 4-word file header come `nsecs` sections. Each section begins with a 2-word header followed by its payload words:

```diagram
┌───────────────────────────┐
│ section id                │   word 0
├───────────────────────────┤
│ length in words N         │   word 1
├───────────────────────────┤
│ payload                   │   words 2 .. N+1
└───────────────────────────┘
```

Sections must appear in **strictly increasing `id` order**, at most once per ID. Any **empty core section is omitted** altogether.

Section IDs are split into two ranges:

- **Core sections (`id < 0x100`)**: Define the module's semantics and canonical identity. An unknown core section ID is rejected.
- **Side sections (`id >= 0x100`)**: Carry optional metadata (`0x100` for `NAMES`, `0x101` for `CONTEXT`, and `>= 0x200` for third-party tool sections). Side sections never change the meaning of a module.

| Section ID | Name | Contents |
| --- | --- | --- |
| `1` | `STRINGS` | `Count`, then each UTF-8 byte string as `[ByteLen, PackedWords...]` (4 bytes per word, little-endian, padded with `0x00` bytes to a word boundary). Sorted lexicographically by raw bytes, deduplicated, containing only strings used by `SYMBOLS` or `loc`. |
| `2` | `CONSTANTS` | `Count`, then 3 words (`[W0_low, W1_mid, W2_high]`) per wide constant: signed 96-bit two's complement integers in `[-2^95, 2^95 - 1]` that lie outside the 30-bit signed inline range `[-2^29, 2^29 - 1]`. Sorted ascending as signed integers, deduplicated, all used. |
| `3` | `SYMBOLS` | `Count`, then 3 words per symbol: `[NameStringId, Kind \/ (Linkage << 8), Extra]`. Defined symbols (`func` = kind `0`, `data` = kind `1`, `alias` = kind `2`) come first in module item order; referenced-only external symbols (kind `3`, linkage `0`, extra `0`) follow, sorted by name bytes. For `data` with `init(ctor/dtor, Priority)` where `Priority` is an integer, `Extra = Priority`; for `alias`, `Extra = TargetSymbolId`; otherwise `Extra = 0`. |
| `4` | `DATA` | One entry per kind-`1` (`data`) symbol, in symbol order: `[Align, ItemCount, ...DataItems]`. Each data item starts with a kind tag: `0` for `item(W, const(N))` (`[0, WidthCode, ConstOperandWord]`), `1` for `item(b, str(Chars))` (`[1, ByteLen, PackedWords...]`), `2` for `item(W, sym(S, Off))` (`[2, WidthCode, SymId, Off_lo, Off_hi]`), `3` for `zero(N)` (`[3, N_lo, N_hi]`). |
| `5` | `FUNCTIONS` | One entry per kind-`0` (`func`) symbol, in symbol order: `[BodyWordLength, ...BodyWords]`. Prefixing each function with its word length lets a reader skip functions or decode them in parallel. |
| `6` | `CERTIFICATES` | Reserved for Campaign 5 (`discharged(Cert)` check-discharge certificates). |
| `0x100` | `NAMES` | Side section: a local string pool, then for each function (in symbol order) three counted lists of terms giving the original names of its temporaries, block labels, and named locals in ID order. |
| `0x101` | `CONTEXT` | Side section: a local string pool, `Count`, then `[PrecedingNonContextItems, ContextTerm]` for each `context` item so decoding restores it to its exact position in `module(Items)`. |

### Function bodies, implicit dense IDs, and `rebind`

Each function in `FUNCTIONS` starts with `[BodyWordLength]` followed by `BodyWordLength` words consisting of a compact header and a flat instruction stream:

| Body field | Words | Description |
| --- | --- | --- |
| `RetWord` | `1` | `0` for `void`, class code `1..8` (`w=1, l=2, s=3, d=4, x=5, p=6, a=7, f=8`), or `0x100 + 16*K1 + K2` for `tuple([K1, K2])`. |
| `ParamCount` (`NP`) | `1` | Number of parameters. |
| `ParamClasses` | `NP` | Class code (`w`, `l`, `p`, `s`, or `d`) for each parameter `0 .. NP - 1`. |
| `BlockCount` (`NB`) | `1` | Total basic blocks in the stream. |
| `TempCount` (`NT`) | `1` | Total distinct temporaries (`NP` parameters plus first definitions in the stream). |
| `LocalCount` (`NL`) | `1` | Total `local_alloc` instructions in the stream. |
| `Stream` | rest | Flat sequence of instructions for blocks `0 .. NB - 1`. |

Before allocating tables of size `NB`, `NT`, or `NL`, the reader verifies that `NB <= WordsLeft`, `NT - NP <= WordsLeft`, and `NL <= WordsLeft`, preventing malformed headers from triggering large allocations.

#### Implicit dense numbering

NFB never writes destination temporary IDs, block labels, or local IDs at definition sites:

- **Temporaries (`0 .. NT - 1`)**: Parameters take IDs `0` through `NP - 1`. Thereafter, each instruction that defines a temporary for the first time implicitly claims the next sequential ID:
  - `phi`, `let`, `flight`, `local_load`, and `call`/`raw_call` with `result(tmp(D), K)` define **1** temporary.
  - `call`/`raw_call` with `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])` defines **2** temporaries.
  - `asm_fixed(M, Ins, Outs)` defines **1** temporary per output in `Outs`.
- **Blocks (`0 .. NB - 1`)**: There is no "start of block" marker word. Because every block consists of zero or more `phi` instructions (opcode `0x08`), zero or more plain instructions (`0x10 .. 0x74`), and **exactly one jump** (`0x80 .. 0x85`), each jump implicitly ends the current block and the next instruction starts block `i + 1`.
- **Locals (`0 .. NL - 1`)**: Each `local_alloc(Name, Size)` instruction implicitly defines the next local ID (`0, 1, ...`), which `local_load`, `local_store`, and `check_local` reference by index.

#### Redefining a temporary: the `rebind` prefix (opcode `0x01`)

What if a function is not in strict SSA and defines an already-existing temporary `tmp(D)` a second time?

Each distinct temporary name in the function is assigned its ID at its **first** definition. If a later instruction defines `k >= 1` temporaries and at least one of them is a redefinition of an existing ID, the encoder precedes that instruction with a **`rebind` prefix instruction** (opcode `0x01`, total length `1 + k` words):

```text
Header word: ((1 + k) << 16) | 0x01
Payload:     w_1, w_2, ..., w_k
```

For each of the `k` outputs defined by the immediately following instruction:
- `w_j = 0` means output `j` is a **first definition** and claims the next fresh temporary ID as usual.
- `w_j = Id + 1` (with `Id` already defined earlier in the stream) means output `j` **rebinds** temporary `Id` without advancing the fresh-ID counter.

If every output of an instruction is a first definition (which is true everywhere in strict-SSA modules), no `rebind` word is allowed.

For example, in [`rocq/tests/interval.ir`](../rocq/tests/interval.ir), `self_use` defines `tmp(a)` twice in block `b0`:

```prolog
func(self_use, export, w, [param(w, tmp(k))], [
    block(b0, [], [
        let(tmp(m), p, alloc(8), [const(8)]),
        let(tmp(a), w, add, [tmp(k), const(1)]),
        let(tmp(a), w, add, [tmp(a), tmp(k)])
    ], ret(tmp(a)))
]).
```

Here `tmp(k)` is parameter `0`, `tmp(m)` is first-defined as temporary `1`, and the first `add` defines `tmp(a)` as temporary `2`. The second `add` redefines `tmp(a)` (ID `2`), so in `nanofil encode`'s output (words 26–35 of `interval.nfb`) it is preceded by a 2-word `rebind` instruction with payload `2 + 1 = 3`:

```text
; first add: let(tmp(a), w, add, [tmp(k), const(1)])  -> defines tmp(2)
00040010   header: opcode 0x0010 (add), length 4 words
00000001   class w (1)
00000000   operand: tmp(0) (k)
00000005   operand: inline const(1) ((1 << 2) | 1 = 5)

; second add: let(tmp(a), w, add, [tmp(a), tmp(k)])   -> rebinds tmp(2)
00020001   header: opcode 0x0001 (rebind), length 2 words
00000003   rebind slot 0 to temporary ID (3 - 1) = 2 (a)
00040010   header: opcode 0x0010 (add), length 4 words
00000001   class w (1)
00000008   operand: tmp(2) (a, (2 << 2) | 0 = 8)
00000000   operand: tmp(0) (k)
```

### Instruction headers, opcodes, operands, and targets

#### Instruction header word

Every instruction begins with a single 32-bit header word packing its opcode in the low 16 bits and its total word count (including the header word itself, `1 <= L <= 65535`) in the high 16 bits:

```text
Header = (LengthInWords << 16) | Opcode
```

Variable-length instructions (`phi` pairs, `call` / `raw_call` arguments, `raw_load_pointer` / `raw_store_pointer` effect lists, `flight` arguments, `asm_fixed` outputs, `rets` values) need no separate count word when the variable list is at the end of the instruction: the reader reads elements until all `LengthInWords` words of the instruction are consumed (`rest(Xs, X, Fs)` in `nfb_form/3`). Only `asm_fixed` has two lists (`Ins` then `Outs`), so it prefixes `Ins` with a count word (`count(Ins, ...)`).

#### Opcode map (`nfb_form/3`)

The opcodes are partitioned by role so a reader can tell block boundaries from the opcode alone:

| Opcode range | Group | Instructions |
| --- | --- | --- |
| `0x01` | prefix | `rebind` (1 word per temporary defined by the next instruction). |
| `0x08` | `phi` | `phi(tmp(D), K, Pairs)` → `[K, PredBlockIdx_0, Opnd_0, ...]`. |
| `0x10 .. 0x1C` | `plain` | Binary `let` ops (`add`, `sub`, `mul`, `div`, `udiv`, `rem`, `urem`, `and`, `or`, `xor`, `sar`, `shr`, `shl`) → `[K, OpndA, OpndB]`. |
| `0x20 .. 0x30` | `plain` | Unary `let` ops (`neg`, `copy`, `cast`, `truncd`, `truncx`, `ptoi`, `itop`, `stosi`, `stoui`, `dtosi`, `dtoui`, `xtosi`, `xtoui`, `swtof`, `uwtof`, `sltof`, `ultof`) → `[K, OpndA]`. |
| `0x38 .. 0x40` | `plain` | Parameterized `let` ops: `0x38` `cmp(Cond, K1)`, `0x39` `ext(T)`, `0x3A` `load(T)`, `0x3B` `alloc(Align)`, `0x3C` `va_args`, `0x3D` `va_arg`, `0x3E` `setjmp(Kind)`, `0x3F` `atomic_load(p)`, `0x40` `cas(T)`. |
| `0x50 .. 0x5D` | `plain` | Checked-stage `let` ops: `0x50` `check`, `0x51` `check_ahead`, `0x52` `renew`, `0x53` `renew_hull`, `0x54` `half_check`, `0x55` `span_test`, `0x56` `renew_if`, `0x57` `limit`, `0x58` `check_limit`, `0x59` `check_local`, `0x5A` `check_function`, `0x5B` `raw_load`, `0x5C` `raw_load_pointer`, `0x5D` `raw_cas`. |
| `0x60 .. 0x69` | `plain` | Standalone instructions: `0x60` `store`, `0x61` `atomic_store`, `0x62` `fence`, `0x63` `access`, `0x64` `local_alloc`, `0x65` `local_load`, `0x66` `local_store`, `0x67` `call`, `0x68` `asm_fixed`, `0x69` `loc`. |
| `0x70 .. 0x74` | `plain` | Checked standalone instructions: `0x70` `touch`, `0x71` `raw_call`, `0x72` `flight`, `0x73` `raw_store`, `0x74` `raw_store_pointer`. |
| `0x80 .. 0x85` | `jump` | Block terminators: `0x80` `goto`, `0x81` `branch`, `0x82` `ret(V)`, `0x83` `rets`, `0x84` `ret`, `0x85` `unreachable`. |

Signed 64-bit attributes (`Lo`, `Hi`, `AHi`, `Off`, `Bytes`, `Size`) are encoded as two words `[Lo32, Hi32]` in little-endian two's complement (`i64`). Thus a check `range` (`Lo, Hi, Rights, Align`) always occupies 6 words: `Lo` (2 words), `Hi` (2 words), `Rights` (1 word: `0` = `read`, `1` = `write`), and `Align` (1 word).

#### Operands and constants

Every IR value operand (`tmp(N)`, `const(N)`, `global(S)`) is encoded as **one word** with a 2-bit tag in bits `0..1` and a 30-bit payload in bits `2..31`:

| Low 2 bits (`W & 3`) | High 30 bits (`P = W >> 2`) | Term |
| --- | --- | --- |
| `0` (`0b00`) | Temporary ID `Id` (`0 .. NT - 1`) | `tmp(Name_Id)` |
| `1` (`0b01`) | Signed 30-bit integer in `[-2^29, 2^29 - 1]` (`P` if `P < 2^29`, else `P - 2^30`) | `const(N)` (inline constant) |
| `2` (`0b10`) | Index `Idx` into the `CONSTANTS` section (`0 .. NConsts - 1`) | `const(N)` (wide constant outside `[-2^29, 2^29 - 1]`) |
| `3` (`0b11`) | Index `Sid` into the `SYMBOLS` section (`0 .. NSyms - 1`) | `global(Sym_Sid)` |

Two details about constants are worth noting:

1. **Signed 30-bit inline constants**: Small negative constants such as `const(-1)` fit in a single operand word without a `CONSTANTS` section entry. For `const(-1)`, `-1 mod 2^30 = 0x3FFFFFFF`, so the operand word is `(0x3FFFFFFF << 2) | 1 = 0xFFFFFFFD`.
2. **Signed 96-bit wide constants**: Why are `CONSTANTS` entries 3 words (96 bits signed, `[-2^95, 2^95 - 1]`) instead of 64 bits? Because `ir.pl` represents 80-bit x87 extended floats (`x`) as unsigned 80-bit IEEE bit patterns up to `2^80 - 1`, while also using negative 64-bit integers such as `-9223372036854775808` (`-2^63`) in data items and offsets. A signed 96-bit two's complement integer covers both `[-2^63, -2^29)` and `[2^29, 2^80)` with a single uniform representation. Any constant in `[-2^29, 2^29 - 1]` **must** use tag `1` (inline), and any constant outside that range **must** use tag `2` (`CONSTANTS`).

#### Jump targets

A jump target word in `goto` (`0x80`) or `branch` (`0x81`) packs the target block index (`0 .. NB - 1`) shifted left by 1 bit, with bit 0 set if and only if the edge is a `poll(L)` safepoint edge:

```text
TargetWord = (BlockIndex << 1) | PollBit
```

### Word-by-word walkthrough of a corpus module

Let's run `nanofil encode` and `nanofil decode` on [`rocq/tests/strings.ir`](../rocq/tests/strings.ir), a small checked Fil-C module from the test corpus:

```prolog
data(punctuation, ro(local), 1, [item(b, str("a;!z"))]).
func(semicolon, export, w, [], [
    block(start, [], [
        let(tmp(p), p, copy, [global(punctuation)]),
        let(tmp(c), a, check(1, 2, read, 1), [tmp(p)]),
        let(tmp(v), w, raw_load(ub, 1), [tmp(c)])
    ], ret(tmp(v)))
]).
```

Running `nanofil encode` produces an 82-word (328-byte) file, and `nanofil decode` recovers the exact IR module:

```sh
$ (cd nanofil/src && ../bin/nanofil encode ../rocq/tests/strings.ir /tmp/strings.nfb </dev/null)
$ (cd nanofil/src && ../bin/nanofil decode /tmp/strings.nfb </dev/null)
```

```prolog
data(punctuation, ro(local), 1, [item(b, str("a;!z"))]).
func(semicolon, export, w, [], [
    block(start, [], [
        let(tmp(p), p, copy, [global(punctuation)]),
        let(tmp(c), a, check(1, 2, read, 1), [tmp(p)]),
        let(tmp(v), w, raw_load(ub, 1), [tmp(c)])
    ], ret(tmp(v)))
]).
```

Here is every one of the 82 words in `/tmp/strings.nfb`, grouped by section:

```text
Word(s)    Hex words (little-endian u32)          Meaning
─────────  ─────────────────────────────────────  ──────────────────────────────────────────────────────────
; ── File header (4 words) ──
0          0042464e                               magic: "NFB\0"
1          00000001                               version: major 0, minor 1
2          00000007                               flags: 0x1 (checked) | 0x2 (filc) | 0x4 (ordered) = 7
3          00000005                               5 sections follow (ids 1, 3, 4, 5, 0x100; 2 is empty)

; ── Section 1: STRINGS (2 header + 9 payload = 11 words) ──
4..5       00000001 00000009                      section id 1 (STRINGS), length 9 words
6          00000002                               2 strings in table (sorted by UTF-8 bytes)
7..10      0000000b 636e7570 74617574 006e6f69    string 0: 11 bytes "punctuation" + 1 zero pad byte
11..14     00000009 696d6573 6f6c6f63 0000006e    string 1: 9 bytes  "semicolon"   + 3 zero pad bytes

; ── Section 3: SYMBOLS (2 header + 7 payload = 9 words) ──
15..16     00000003 00000007                      section id 3 (SYMBOLS), length 7 words
17         00000002                               2 symbols (defined symbols in module item order)
18..20     00000000 00000401 00000000             symbol 0: string 0 ("punctuation"),
                                                    kind 1 (data) | (linkage 4 (ro(local)) << 8) = 0x0401,
                                                    extra 0
21..23     00000001 00000000 00000000             symbol 1: string 1 ("semicolon"),
                                                    kind 0 (func) | (linkage 0 (export) << 8) = 0x0000,
                                                    extra 0

; ── Section 4: DATA (2 header + 5 payload = 7 words) ──
24..25     00000004 00000005                      section id 4 (DATA), length 5 words
26..27     00000001 00000001                      data for symbol 0 ("punctuation"): align 1, 1 data item
28..30     00000001 00000004 7a213b61             kind 1 (item(b, str(...))), 4 bytes "a;!z" (0x61,0x3b,0x21,0x7a)

; ── Section 5: FUNCTIONS (2 header + 26 payload = 28 words) ──
31..32     00000005 0000001a                      section id 5 (FUNCTIONS), length 26 words
33         00000019                               body of symbol 1 ("semicolon"): 25 words
34..38     00000001 00000000 00000001             ret class w (1), 0 params, 1 block,
           00000003 00000000                      3 temporaries (ids 0..2), 0 locals
39..41     00030021 00000006 00000003             let(tmp(0), p, copy, [global(punctuation)]):
                                                    header: len 3, opcode 0x0021 (copy);
                                                    class p (6);
                                                    operand: (symbol 0 << 2) | tag 3 (global) = 0x00000003
42..50     00090050 00000007                      let(tmp(1), a, check(1, 2, read, 1), [tmp(0)]):
           00000001 00000000                        header: len 9, opcode 0x0050 (check); class a (7);
           00000002 00000000                        Lo = 1 (i64: 1, 0); Hi = 2 (i64: 2, 0);
           00000000 00000001                        rights = read (0); align = 1;
           00000000                                 operand: (tmp 0 << 2) | tag 0 = 0x00000000
51..56     0006005b 00000001 00000015             let(tmp(2), w, raw_load(ub, 1), [tmp(1)]):
           00000001 00000000                        header: len 6, opcode 0x005b (raw_load);
           00000004                                 class w (1); load type ub (21 = 0x15); Off = 1 (i64: 1, 0);
                                                    operand: (tmp 1 << 2) | tag 0 = 0x00000004
57..58     00020082 00000008                      ret(tmp(2)) (ends block 0):
                                                    header: len 2, opcode 0x0082 (ret(V));
                                                    operand: (tmp 2 << 2) | tag 0 = 0x00000008

; ── Section 0x100: NAMES (2 header + 21 payload = 23 words) ──
59..60     00000100 00000015                      section id 0x100 (NAMES), length 21 words
61..70     00000004                               local string pool: 4 atoms ("c", "p", "start", "v")
           00000001 00000063                        pool 0: "c"
           00000001 00000070                        pool 1: "p"
           00000005 72617473 00000074               pool 2: "start"
           00000001 00000076                        pool 3: "v"
71..77     00000003                               function 0's 3 temporary names:
           00000001 00000001                        tmp 0 -> tag 1 (atom), pool 1 ("p")
           00000001 00000000                        tmp 1 -> tag 1 (atom), pool 0 ("c")
           00000001 00000003                        tmp 2 -> tag 1 (atom), pool 3 ("v")
78..80     00000001 00000001 00000002             function 0's 1 block label: tag 1 (atom), pool 2 ("start")
81         00000000                               function 0's 0 local names
```

### Names, side sections, and canonical form

What happens if we strip the `NAMES` side section (`nfb:nfb_core/2`), leaving only the 59 core words (`0..58`, with `nsecs` in word 3 changed from `5` to `4`)?

Without `NAMES`, the decoder assigns each temporary, block label, and local its dense integer ID (`0, 1, 2, ...`):

```prolog
data(punctuation, ro(local), 1, [item(b, str("a;!z"))]).
func(semicolon, export, w, [], [
    block(0, [], [
        let(tmp(0), p, copy, [global(punctuation)]),
        let(tmp(1), a, check(1, 2, read, 1), [tmp(0)]),
        let(tmp(2), w, raw_load(ub, 1), [tmp(1)])
    ], ret(tmp(2)))
]).
```

This core-only `.nfb` file is a complete, valid module: `nanofil check` prints `ok`, and `nanofil run /tmp/strings-core.nfb semicolon` prints `ret 59` (the ASCII byte `0x3b` of `';'` at offset 1 of `"a;!z"`).

When `NAMES` (`0x100`) or `CONTEXT` (`0x101`) is present, notice that side sections do **not** store printed Prolog text (which would require a term parser). Instead, each side section starts with its own sorted string pool of atom and functor names, followed by binary term trees using a 4-tag encoding:

| Term tag word | Following words | Prolog / `Term.v` term |
| --- | --- | --- |
| `0` | 3 words (`wide(N)`, signed 96-bit integer) | Integer `N` (`TInt N`) |
| `1` | `[PoolId]` | Atom (`TAtom s`) |
| `2` | `[FunctorPoolId, Arity, ...ArgTerms]` | Compound term `F(A1, ..., An)` (`TApp f args`) |
| `3` | `[Length, ...ElemTerms]` | Proper list `[E1, ..., En]` (`TList elems`) |

Because temporary names in optimized IR are often compound terms like `promote('pr.1')` or atoms like `'pr.2'`, encoding `NAMES` as tagged terms preserves structured names directly without text parsing. Note one implementation reality mentioned in [`nfb.md`](nfb.md): block labels do reach emitted assembly as local label suffixes (`.L<function>.<label>` in `filc_amd64.pl`), so while the Gallina backend is held to byte-for-byte assembly identity with the Prolog compiler, it reads `NAMES` to preserve block label names.

#### How canonical form is enforced

NFB guarantees that every valid module has a single core encoding because every potential degree of freedom is fixed:

- Top-level defined symbols, blocks, instructions, phi pairs, call arguments, and effect lists keep the module's exact list order.
- Referenced-only external symbols follow the defined symbols, sorted by UTF-8 name bytes.
- `STRINGS` and `CONSTANTS` are sorted, contain no duplicates, and contain no unreferenced entries.
- Constants in `[-2^29, 2^29 - 1]` are always inline (tag `1`); constants outside that range are always in `CONSTANTS` (tag `2`).
- Empty core sections are omitted; unused padding bytes and flag bits are zero; `rebind` is emitted only when at least one defined temporary is a redefinition.
- The `stage`, `mode`, and `ordered` header flags are functions of the module.

Rather than writing dozens of separate well-formedness checks for sorting, deduplication, unused table entries, and header flags, **both the Prolog reader (`nfb:read_words/2`) and the Gallina reader ([Nfb.decode] / [NfbTerm.decode_term]) enforce canonicality by re-encoding**:

1. The reader decodes the input word list `Ws` into a module `M` (checking bounds and counts on the way).
2. It runs the encoder on `M` (with the same core + `NAMES`/`CONTEXT` section selection).
3. It requires the re-encoded words `Ws1` to be **word-for-word identical** to `Ws` (ignoring third-party tool sections with ID `>= 0x200`).

If an input file has an unsorted string table, an unused constant, an inline-range constant stored in `CONSTANTS`, a spurious `rebind` of `0`, or a wrong `ordered` flag, re-encoding produces different words and the decoder rejects the file.

## Part IV: How the Prolog and Gallina Sides Relate

### One table in two languages: `nfb.pl` and `NfbTerm.v`

In [`src/nfb.pl`](../src/nfb.pl), the entire instruction format is driven by a single declarative table, `nfb_form(Opcode, Term, Fields)`, paired with `nfb_code(Enum, Term, Code)`:

```prolog
nfb_form(0x08, phi(tmp(D), K, Ps),
         [def(D), class(K), rest(Ps, L-V, [label(L), opnd(V)])]).
nfb_form(0x50, let(tmp(D), K, check(Lo, Hi, R, Al), [P]),
         [def(D), class(K), i64(Lo), i64(Hi), enum(rights, R), u32(Al), opnd(P)]).
nfb_form(0x5C, let(tmp(D), K, raw_load_pointer(Off, Es), [A]),
         [def(D), class(K), i64(Off), opnd(A), rest(Es, E, [enum(effect, E)])]).
```

When encoding, `module_nfb/2` unifies the instruction `Term` with `nfb_form/3` to instantiate the variables inside `Fields` and emits their words. When decoding, `read_inst//7` looks up `Opcode` in the same `nfb_form/3` table, reads the words described by `Fields`, and binds `Term`. Because both directions read one table, the writer and reader in `nfb.pl` cannot disagree on an opcode or field layout.

In Gallina ([`rocq/backend/NfbTerm.v`](../rocq/backend/NfbTerm.v)), where Prolog unification is replaced by total functions over `Term.v`'s inductive `term` type (`TInt`, `TAtom`, `TApp`, `TList`), the exact same table is written as `forms : list form` using first-order patterns (`pat`) with numbered holes (`PH 0`, `PH 1`, ...):

```rocq
Inductive pat : Type :=
| PH (i : nat)                  (* hole i *)
| PA (s : string)               (* atom s *)
| PC (f : string) (ps : list pat) (* compound f(ps...) *)
| PL (ps : list pat).           (* list [ps...] *)

Record form : Type := mkForm { f_code : Z; f_pat : pat; f_fields : list lfield }.
```

[match_pat] matches a `term` against `f_pat` to produce an environment `env` mapping hole numbers to subterms, and [lfields_out] encodes each hole according to `f_fields`. Conversely, [read_lfields] decodes words into an `env`, and [fill_pat] plugs those subterms back into `f_pat` to build the `term`.

### Bridging `Term.v` and `Syntax.v`: `IrTerm.v`, `Transport.v`, and `Nfb.v`

Why does the Gallina backend have both `NfbTerm.v` (operating on `Term.term`) and `Nfb.v` (operating on `Syntax.module`)?

The Rocq model's [`Syntax.v`](../rocq/theories/Syntax.v) defines typed inductive ASTs (`class`, `op`, `inst`, `jump`, `block`, `func`, `item`) for the **core subset** of checked Fil-C IR—the subset covered by `Semantics.v`, `Validate.v`, and `Soundness.v`. Functions that use features outside that subset (such as unchecked `load`/`store`, `cas`, `setjmp`, `asm_fixed`, or vector `touch`) are represented in `Syntax.module` by the constructor:

```rocq
| IOutside (n : name) (t : term)
```

Keeping the raw `term` inside [IOutside] allows `Validate.v` to inspect the function's signature and global symbol references even when its body lies outside the core subset, and allows NFB to round-trip any module through `Syntax.module` without losing outside functions.

[`rocq/backend/Nfb.v`](../rocq/backend/Nfb.v) composes the typed AST conversion with `NfbTerm.v`:

```diagram
Encode: Syntax.module ─▶ Nfb.enc_module ─▶ Term.term ─▶ NfbTerm.encode_term ─▶ list Z (words)
Decode: list Z (words) ─▶ NfbTerm.read_term ─▶ Term.term ─▶ Transport.decode_module ─▶ Syntax.module
```

Specifically:

- **`Nfb.encode (m : module) : option (list Z)`** turns every `IFunc f`, `IData ...`, and `IAlias ...` into its canonical `Term.term` via [Nfb.enc_module], built from `IrTerm.v`'s encoders (while `IOutside _ t` is already its `term` `t`), and passes `module(Items)` to `NfbTerm.encode_term true`.
- **`Nfb.decode (ws : list Z) : option module`** runs `NfbTerm.read_term ws` to get `(t, has_names)`, runs `Transport.decode_module t` to build `m : Syntax.module`, re-encodes `m` with `encode_with has_names m`, and checks [words_eqb] against `module_words ws` (which strips `CONTEXT` and tool sections `>= 0x200`).

One minor difference between the two readers is noted in [`nfb.md`](nfb.md): `NfbTerm.v` treats strings in `STRINGS` as raw byte sequences (`0..255`), whereas `nfb.pl` decodes `STRINGS` into Prolog atoms via `utf8_decode//1` and therefore also requires symbol and file names to be valid UTF-8.

### What is proved in Rocq and what the gates check

The RFC ([`nfb.md`](nfb.md)) specifies three formal properties for the Gallina NFB implementation, corresponding to [`NfbProof.v`](../rocq/backend/NfbProof.v) and [`NfbTotal.v`](../rocq/backend/NfbTotal.v):

1. **Canonical form and sound identity (`NfbProof.v`, proved)**:
   Because [Nfb.decode] accepts a word list `ws` only when [encode_with] reproduces `module_words ws`, the canonicality theorem is short and unconditional:
   ```rocq
   Theorem decode_canonical : forall ws m,
     decode ws = Some m -> encode_with (names_of ws) m = module_words ws.

   Corollary decode_identity : forall ws1 ws2 m,
     decode ws1 = Some m -> decode ws2 = Some m -> names_of ws1 = names_of ws2 ->
     module_words ws1 = module_words ws2.
   ```
   Any two word streams that decode to the same `Syntax.module` (both with `NAMES` or both without) have identical core and `NAMES` words.

2. **Total and bounded decoding (`NfbTotal.v`, proved)**:
   Every function in `NfbTerm.v` and `Nfb.v` is a total Gallina function (`decode_total : forall ws, decode ws = None \/ exists m, decode ws = Some m`). Wherever a reader function is not structurally recursive on the input list ([read_sections], [read_group], [read_blocks], [read_rest], [read_side_term], [read_name_recs]), it takes a `nat` fuel argument initialized at the call site to `length ws`. `NfbTotal.v` proves that every step consumes at least one word ([takes_word], [forms_rest_take_words]), so `length ws` is always sufficient fuel: passing any larger fuel `f' >= length ws` yields the exact same result ([sections_fuel], [group_fuel], [blocks_fuel], [rest_fuel], [side_term_fuel], [name_recs_fuel]). No input is ever rejected because fuel ran out.

3. **Round-trip inversion (`decode (encode m) = Some m`, proved)**:
   Because `decode` re-encodes what `read_term` and [decode_module] read, proving the round-trip theorem means proving that the reader inverts the writer on every well-formed module. [`NfbRead.v`](../rocq/backend/NfbRead.v) proves the leaf round-trip lemmas—64-bit signed integers ([i64_round_trip]), 96-bit signed wide constants ([wide_round_trip]), 30-bit signed inline constants ([inline_round_trip]), and bijective enumeration code tables ([codes_ok], [codes_round_trip])—and the reader half, [read_encode_term]; with [decode_enc_module] in [`NfbTransport.v`](../rocq/backend/NfbTransport.v), they give [round_trip] in `NfbProof.v` for every module that [Transport.decode_module] gives.

Alongside the Rocq proofs, two executable test gates hold the implementations to the corpus on every check run:

- **`nanofil/tests/nfb.sh`** (`nanofil nfb-check FILE`): Encodes and decodes every C and IR module in the corpus—both `unchecked` and `checked`, with and without `-O`—verifying that `module_nfb/2` recovers the identical Prolog term when `NAMES` and `CONTEXT` are included, and recovers a module with identical core words when side sections are stripped.
- **`nanofil/rocq/backend/tests/nfb.sh`** (`nanofil nfb-terms` + extracted `nanofil-backend nfb`): Runs the extracted Gallina [Nfb.encode] and [Nfb.decode] against `nfb.pl` across the corpus, requiring the Gallina encoder to emit the **exact same bytes** (`NAMES` included) as `nfb.pl` and the Gallina decoder to return the exact same `Syntax.module`.

## Quick Reference: Using NFB from the Command Line

You can inspect, validate, interpret, and compile `.nfb` files directly with `bin/nanofil`:

```sh
# 1. Encode an IR or C file to NFB (add -O to run the middle end first)
(cd nanofil/src && ../bin/nanofil encode ../rocq/tests/strings.ir /tmp/strings.nfb </dev/null)

# 2. Decode an NFB file back to readable IR text
(cd nanofil/src && ../bin/nanofil decode /tmp/strings.nfb </dev/null)

# 3. Validate, interpret, or compile an NFB file directly (file_module/2 accepts .nfb)
(cd nanofil/src && ../bin/nanofil check /tmp/strings.nfb </dev/null)
(cd nanofil/src && ../bin/nanofil run /tmp/strings.nfb semicolon </dev/null)
(cd nanofil/src && ../bin/nanofil compile /tmp/strings.nfb </dev/null)

# 4. Run the round-trip check (unchecked + checked, with and without side sections)
(cd nanofil/src && ../bin/nanofil nfb-check ../rocq/tests/strings.ir </dev/null)
```
