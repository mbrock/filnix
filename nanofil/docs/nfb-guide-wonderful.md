# The nanofil IR and NFB: a newcomer's guide

nanofil is a C compiler written in Prolog. It emits x86-64 assembly
for [Fil-C](https://github.com/pizlonator/fil-c), a memory-safe
implementation of C, and it doubles as an executable account of what
Fil-C's safety consists of: every check Fil-C makes appears
explicitly in nanofil's intermediate representation (IR), an
interpreter gives that IR a meaning, and a Rocq model proves that a
validated module's checks are enough.

This guide explains two things, in order:

1. **The IR itself** — modules, functions, blocks, phis,
   temporaries, the instruction set, and the *unchecked* and
   *checked* stages, including how checked IR carries Fil-C's memory
   safety.
2. **NFB**, the bytecode format that writes an IR module as a stream
   of 32-bit words — what it is, why it exists, and exactly how a
   module becomes words.

It assumes you are a capable programmer. It does not assume Prolog,
Fil-C, or Rocq. Where another document is the authority, it says so:
[ir.pl](../src/ir.pl) defines the IR and its validator,
[nfb.pl](../src/nfb.pl) is the Prolog encoder and decoder, and
[nfb.md](nfb.md) is the NFB RFC with the appendix of assigned
numbers. The Rocq side lives in
[Syntax.v](../rocq/theories/Syntax.v) and
[the backend's Nfb files](../rocq/backend/Nfb.v). For a walk through
the whole compiler, read [the guide](guide.md); for Fil-C itself,
[How Fil-C works](filc.md).

## Trying it as you read

Every IR fragment in this guide is a Prolog term, and every word
listing was produced by the current tools. From a filnix checkout,
`nanofil/bin/nanofil` runs the compiler on SWI-Prolog:

```sh
# IR text in, NFB out; and back again
nanofil/bin/nanofil encode FILE.ir OUT.nfb
nanofil/bin/nanofil decode OUT.nfb
# round-trip a corpus file (unchecked, and checked for Fil-C files)
nanofil/bin/nanofil nfb-check nanofil/tests/fixtures/arith.ir
```

Observed outputs used below:

```text
$ nanofil/bin/nanofil nfb-check nanofil/tests/fixtures/arith.ir
nanofil/tests/fixtures/arith.ir: unchecked 582 words, 335 core
$ nanofil/bin/nanofil nfb-check nanofil/tests/filc/pointer-effects.ir
nanofil/tests/filc/pointer-effects.ir: unchecked 79 words, 60 core
nanofil/tests/filc/pointer-effects.ir: checked 98 words, 75 core
```

"Core" means the words without the optional side sections (names
and context); §NFB explains the distinction.

# Part 1: the IR

## 1. A module is a list of items

A module is the term `module(Items)`. Each item is one of:

| Item | Means |
| --- | --- |
| `func(Name, Linkage, Ret, Params, Blocks)` | a function |
| `data(Name, Linkage, Align, Items)` | a data object (a global's initial bytes) |
| `alias(Name, Linkage, Target)` | a second symbol `Name` for a function or data object the module defines (Fil-C mode only) |
| `context(Name, Records)` | explanatory provenance: which C declaration each temporary came from. No stage's meaning depends on it |

`Name` is an atom, the symbol. No two items define the same name
(with one `extern(weak)` exception under Data below). Item order
matters: a backend emits in that order, and NFB preserves it.

A function's fields:

- **Linkage** is `export`, `local`, or (Fil-C mode) `weak` — an
  export that a strong definition elsewhere replaces.
- **Ret** is a class (below), `void`, or `tuple([K1, K2])`: two
  words returned together, a struct of 9 to 16 bytes as the System V
  ABI classifies it (Fil-C mode only).
- **Params** is a list of `param(K, tmp(N))`: each parameter has a
  class `K` (one of `w`, `l`, `p`, `s`, `d`) and names the temporary
  it defines.
- **Blocks** is a list of blocks, the *entry block first*.

Everything is a ground Prolog term: temporaries, labels, and locals
are ground names, and no logic variable ever appears in IR. A module
is ordinary data you can print, read back, compare, and — this is
what NFB adds — serialize canonically.

### Data

In `data(Name, Linkage, Align, Items)`, `Align` is the payload's
alignment (a power of two) and `Items` spells out the initial bytes:

| Item | Means |
| --- | --- |
| `item(W, const(N))` | the integer `N` at width `W` |
| `item(b, str(Chars))` | the bytes themselves, one character per byte |
| `item(l, sym(S, Off))` | the address of `S` plus `Off` (plain mode) |
| `item(p, sym(S, Off))` | a pointer to `S` plus `Off`, with `S`'s capability (Fil-C mode) |
| `zero(N)` | `N` zero bytes |

Data linkages say where the object lives and how it links:
`export`, `local`, `ro(...)` for read-only data, `tls(...)` for
thread-local objects, `weak` / `ro(weak)`, `extern(weak)` (a weak
declaration of a symbol defined elsewhere, not an object itself),
and `init(ctor, Priority)` / `init(dtor, Priority)` — entries in the
constructor/destructor tables the runtime runs, whose single item is
the pointer to the function. Most of these distinctions matter only
at the ABI boundary; what matters for NFB is that each gets a code.

## 2. Values and classes

Instructions read *values*, of which there are exactly three:

| Value | Means |
| --- | --- |
| `tmp(Name)` | a temporary: the result of a parameter, a phi, or a defining instruction |
| `const(N)` | an integer; at a float class, its IEEE bit pattern |
| `global(S)` | the address of the function or data object named `S` |

Every value has a *class*, written as one letter. Classes are the
IR's small type system, and the validator checks that each
instruction reads and produces the classes its form requires
(`op_arg_classes/4`, `op_result_ok/3` in ir.pl):

| Class | Value |
| --- | --- |
| `w` | 32-bit integer |
| `l` | 64-bit integer |
| `s` | 32-bit float |
| `d` | 64-bit float |
| `x` | x87 80-bit extended float, C's `long double` (Fil-C mode; never a parameter, result, argument, or phi) |
| `p` | pointer: an address together with its Fil-C *capability* (Fil-C mode) |
| `a` | *proven address*: a pointer a check has cleared (checked stage only) |
| `f` | *proven function*: a `p` a function check has cleared (checked stage only) |

Two related vocabularies ride along. A store's *width* may be any of
`b` (8 bits), `h` (16), `w`, `l`, `p`, `s`, `d`. A load or extension
names a *narrow type* — `sb`, `ub`, `sh`, `uh`, `sw`, `uw`, a signed
or unsigned byte, halfword, or word — for loads narrower than the
class they produce.

Classes `a` and `f` deserve a pause, because they are where the
safety argument lives. They are not data that can travel: a value of
class `a` or `f` is never a parameter, a phi, a call argument or
result, and never stored to memory. It exists only as the result of
a check, consumed by the raw access (or raw call) that the check
authorizes. Think of `a` as "this address, *with its receipt*" — the
same bits as the pointer it came from, distinguished by the fact
that a check just cleared them. Part 2 cashes this out.

## 3. Functions are blocks; blocks end in one jump

A block is `block(Label, Phis, Insts, Jump)`:

```prolog
block(loop, Phis, Insts, Jump)
```

First the phis, then the ordinary instructions, then exactly one
jump. The first block is the entry block and has no phis. There is
no other structure — no nested control flow, no fallthrough. If you
know LLVM IR or QBE, you already know this shape.

A tiny complete example, in plain mode (ordinary integers, no Fil-C
pointers):

```prolog
func(add1, export, w, [param(w, tmp(x))], [
    block(start, [], [
        let(tmp(y), w, add, [tmp(x), const(1)])
    ], ret(tmp(y)))
]).
```

Read it as: `add1` takes a 32-bit integer `x` and returns `x + 1`.
The one instruction is a `let`: it defines temporary `y` of class
`w` as `add` applied to `x` and the constant 1. The jump `ret`
returns `y`. We will turn exactly this module into NFB words in §17.

### Temporaries and phis

A *temporary* is a name for a value computed once and then read.
Parameters define temporaries; so does each `let`, each `phi`, and a
few other instructions (a call's result, a local load, an
`asm_fixed` output). A jump names *labels*; a `local_alloc` names a
*named local*. These are separate namespaces — a temporary, a label,
and a local may share a spelling without confusion — and NFB numbers
each namespace separately.

The IR is *almost* SSA. The middle end works in strict SSA (one
definition per temporary), and everything the frontend produces is
strict SSA. But the validator's rule is weaker: each *use* of a
temporary in a reachable block must be dominated by *a* definition
(`definitions_dominate/3`). A handful of hand-written fixtures define
a temporary twice in a dominating position, and the rule allows it:

```prolog
% from tests/fixtures/memory.ir: t is defined, then redefined
let(tmp(t), w, add, [tmp(a), const(1)]),
let(tmp(t), w, mul, [tmp(t), const(2)])
```

This small leniency has a visible consequence in NFB: the `rebind`
word of §13 exists because of it.

A *phi* chooses a value according to where control came from:

```prolog
phi(tmp(D), K, [Pred1-Value1, Pred2-Value2, ...])
```

`D`, of class `K`, is `Value_i` when control arrived along the edge
from block `Pred_i`. Phis sit at the head of a block, before every
other instruction, and all of them take effect simultaneously on the
edge (the backend implements this with shadow slots doing a parallel
copy). A counting loop shows the standard pattern — the phi is the
loop variable:

```prolog
func(count, export, w, [param(w, tmp(n))], [
    block(start, [], [], goto(loop)),
    block(loop, [
        phi(tmp(i), w, [start-const(0), loop-tmp(i1)])
    ], [
        let(tmp(i1), w, add, [tmp(i), const(1)]),
        let(tmp(c), w, cmp(slt, w), [tmp(i1), tmp(n)])
    ], branch(tmp(c), loop, done)),
    block(done, [], [], ret(tmp(i1)))
]).
```

`i` is 0 on the first entry (from `start`) and the previous `i1` on
each later entry (from `loop` itself). Note that a phi's incoming
value may be defined *later* in the function body than the phi —
`i1` is. That is normal for loops, and it is one of the two things
that keep NFB from being a purely "define before use" stream; the
*ordered* flag in §16 handles it by exempting phis.

### Named locals

A named local is an invocation-local object with a name instead of
an address. `local_alloc(Name, Size)` creates a zeroed, exact-sized
object (declared once, in the entry block); `local_load` and
`local_store` access it at fixed byte offsets, trapping outside
`[0, Size)`. Its native address is never a `p` value, so it cannot
escape as a pointer. The optimizer turns non-escaping allocations
into named locals; in the checked stage they get their own proof
form, `check_local` (§8).

## 4. The instruction set

Almost every computation is a `let`:

```prolog
let(tmp(D), K, Op, Args)    % D : K  :=  Op(Args...)
```

The `Op` determines the argument classes and count. Grouped by kind:

**Arithmetic and logic.** `add`, `sub`, `mul`, `div`, `udiv`,
`rem`, `urem`, `and`, `or`, `xor`, `sar`, `shr`, `shl` take two
arguments; `neg`, `copy`, and `cast` (bitwise reinterpretation
between `w`/`s` and `l`/`d`) take one. At class `p`, `add` and `sub`
are pointer-plus-or-minus-offset in the unchecked stage. Shift
counts are read at class `w`.

**Comparison and conversion.** `cmp(Cond, K1)` compares two values
of class `K1` and yields 0 or 1; `Cond` is one of `eq`, `ne`, the
signed and unsigned integer orders (`slt`, `sle`, ...; `ult`, `ule`,
...), or the float orders (`lt`, `le`, ..., `o`, `uo` for ordered /
unordered). `ext(T)` extends the low bytes named by narrow type `T`
(or widens a float, `ext(s)`, `ext(d)`); `truncd` and `truncx`
narrow floats; ten conversions move between floats and signed or
unsigned integers (`stosi`, `dtoui`, `swtof`, `ultof`, ...: source
class, signedness, "to"). `ptoi` and `itop` convert between a
pointer and an integer in Fil-C mode — §7 explains why `itop` yields
a pointer that can access nothing.

**Memory (unchecked forms).** `load(T)` loads a `T` through an
address. `alloc(Align)` allocates a zeroed heap object of the `l`
size it reads. These are the *checking* forms: in Fil-C mode a
`load` means "check, then access". The checked stage replaces them
with explicit checks plus raw accesses (§7).

**Atomics and miscellany.** `atomic_load(p)` is a sequentially
consistent, single-copy atomic pointer load. `cas(T)` is the one
atomic read-modify-write: it reads `[Expected, New, Addr]`, writes
`New` at `Addr` if the old value equals `Expected` (bitwise; for `p`,
addresses only), and returns the old value. Every other atomic RMW
is lowered to a `cas` loop. `va_args` / `va_arg` read a variadic
function's argument snapshot. `setjmp(Kind)` returns twice. The
checked-stage `let` ops — `check`, `raw_load`, and their relatives —
have their own section (§8).

The remaining instructions define nothing, or define through a
result slot rather than a `let`:

| Instruction | Means |
| --- | --- |
| `store(W, Value, Addr)` | store `Value` at width `W` (checking form) |
| `atomic_store(p, Value, Addr)` | atomic pointer store |
| `fence` | sequentially consistent fence |
| `access(K, Addr, Size, Align)` | trap exactly as a `K` access of `Size` bytes would, accessing nothing: a vector's full-width pre-check |
| `touch(tmp(Q))` | checked stage: consume the proof `Q`, do nothing else (pizlonated `access`) |
| `local_alloc`, `local_load`, `local_store` | named-local declare / load / store |
| `call(Res, Callee, Args)` | call `global(F)` or, in Fil-C mode, a `p` temporary; `Args` are `arg(K, Value)` pairs |
| `raw_call(Res, Callee, Args)` | checked stage: call a proven function (class `f`) |
| `flight(tmp(D), Op, Args, Lower)` | checked stage: build a pointer from an address computation and a separately chosen capability (§7) |
| `raw_store`, `raw_store_pointer` | checked stage: stores that do not check, reading a proof (§7) |
| `asm_fixed(M, Ins, Outs)` | a fixed-register machine instruction (`cpuid`, `rdtsc`, fences, ...) with register-pinned inputs and outputs |
| `loc(File, Line)` | does nothing; the instructions after it come from that source line |

A call's `Res` is `void`, `result(tmp(D), K)` (defines one
temporary), or `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])`
(defines two). A direct call names its callee as `global(F)`; `F`
may be a function the module does not define — an external, such as a
libc function. A `global(S)` value elsewhere is read only by
`let(tmp(D), p, copy, [global(S)])`, which materializes the symbol's
pointer (natively, it calls the symbol's *getter*; §6).

Finally, the jumps — the one instruction that ends every block:

| Jump | Means |
| --- | --- |
| `goto(L)` | go to `L` |
| `branch(V, L1, L2)` | to `L1` if `V` is nonzero, else `L2` |
| `ret(V)` | return `V` |
| `rets([V1, V2])` | return a tuple |
| `ret` | return from a `void` function |
| `unreachable` | stop the program (a trap instruction) |

A jump target may be wrapped: `poll(L)` means "pollcheck on this
edge, then go to `L`" — after the phis' copies, the thread answers
the garbage collector and runs any deferred signal handler. Poll
edges belong to the checked stage and to Fil-C's collector protocol
(§6), but the syntax is available in any module.

That is the whole instruction set: about fifty `let` ops, fifteen
other instructions, six jumps, and phis. [ir.pl's header](../src/ir.pl)
is the normative table, with `valid_op/1`, `op_arg_classes/4`, and
`op_result_ok/3` stating the same grammar as code.

## 5. Mode and stage are read off the vocabulary

Two independent classifications apply to every module. Neither is a
flag in the term; both are *derived from what the module contains*,
by `module_mode/2` and `module_stage/2`, so no annotation can
disagree with the contents.

**Mode: plain or filc.** A module is in *plain* mode if it uses only
the classes `w`, `l`, `s`, `d`, with addresses as plain `l` values;
the plain backend compiles it to ordinary x86-64. Anything
Fil-C-specific makes it *filc* mode: a `p` value, a tuple return,
read-only data, a pointer-only op, or a call to a function the
module does not define. In filc mode addresses are `p` values —
address-plus-capability pairs — and `alloc` yields a `p`.

**Stage: unchecked or checked.** A module is *unchecked* if it
contains no check, raw access, `flight`, or poll edge; otherwise it
is *checked*. The compiler's pipeline crosses from one to the other:

```diagram
 C source
    │  frontend
    ▼
 unchecked IR
    │  middle end (-O)
    ▼
 unchecked IR
    │  pizlonate
    ▼
 checked IR
    │  Fil-C backend
    ▼
 assembly
```

The frontend and the middle end write unchecked IR. *Pizlonation*
([pizlonate.pl](../src/pizlonate.pl), named after Fil-C's LLVM pass
FilPizlonator) rewrites it into checked IR, where every check Fil-C
makes is written out as an instruction. The Fil-C backend compiles
only checked IR. (In plain mode there is nothing to pizlonate; the
plain backend compiles the unchecked module directly, and poll edges
are still allowed.)

Both stages are validated by the same `valid_module/1`: grammar and
classes, labels, dominance of uses, and — in the checked stage — the
evidence rules of §9. And both stages have the same semantics,
given by the interpreter ([interp.pl](../src/interp.pl)):
pizlonation must preserve outcomes, traps included, which the
differential tests check on every run line.

|  | unchecked | checked |
| --- | --- | --- |
| written by | frontend, middle end, by hand | pizlonation, check passes |
| a Fil-C load is | `load(T)` — "check, then access" | `check` + `raw_load` — check and access separate |
| pointer arithmetic | `p add/sub/copy`, `itop` | `flight` |
| indirect call | `call` with a `p` callee | `check_function` + `raw_call` |
| loops | plain back edges | every CFG cycle has a poll edge |
| compiled by | plain backend (plain mode) | Fil-C backend |

# Part 2: checked IR and Fil-C's memory safety

## 6. What Fil-C guarantees, in one page

Fil-C's rule is **GIMSO: garbage in, memory safety out**. Every
operation either does what C says or stops the program with a Fil-C
panic (a *trap*). There is no third outcome in which a bad pointer
quietly reads or writes someone else's bytes — however buggy or
hostile the source program is, and with no `unsafe` escape hatch.

The mechanism is capabilities. A pointer in flight (in a register or
a local) is a pair of words:

- the **intval**, the address the program sees. The program may do
  anything with it — add, mask, print, compare. Nothing trusts it.
- the **lower**, the address of the first byte of the one object
  this pointer may access. The program cannot see or forge it; only
  an allocation creates one, and every pointer derived from it
  carries it.

Just below the lower, out of the program's reach, sits the object
header: the **upper** bound (one past the last byte) and a word of
flags (freed, read-only, ...) plus the pointer to the object's
**aux** array. An access of `N` bytes is allowed exactly when
`lower ≤ intval` and `intval + N ≤ upper`, the flags permit the
rights asked (a write needs a non-read-only, non-freed object), and
— for pointer, atomic, and vector accesses — the address is aligned.
Anything else traps.

Three consequences shape the IR:

- **Pointers at rest need two homes.** A stored pointer's intval
  goes in the object's bytes (C knows `sizeof(void*)` is 8), and its
  lower goes in the corresponding slot of the aux array. So a pointer
  load or store is a small protocol of aux, lower, and address
  steps — which checked IR spells out as an *effect list* (§8).
- **Free is immediate; reclamation is not.** `free` sets
  `upper = lower` and raises the free flag, so every alias fails
  every later check. The concurrent collector (FUGC) reclaims the
  memory later, once nothing points to it. A check is therefore good
  only until something might free the object — a call, or a signal
  handler at a safepoint. This is why proofs *die at safepoints*
  (§9).
- **Loops must poll.** The collector needs to find every live lower,
  including ones in registers. At a *safepoint* (a pollcheck) the
  compiler guarantees every live lower is recorded in the frame's
  root record. Checked IR marks pollchecks as `poll(L)` edges, and
  the validator requires one in every cycle of the control-flow
  graph, so no loop can starve the collector.

Two more Fil-C facts appear in checked IR. A function pointer's
lower names a special *function object*, and an indirect call must
check that the target really is that object's exact callable
address. And taking a global's address goes through a *getter* (a
runtime function that returns the symbol's pointer, initializing it
on first use), which is itself a safepoint.

[How Fil-C works](filc.md) is the full account; this is the subset
the IR makes you hold in mind.

## 7. Pizlonation: making every check a term

Pizlonation is deliberately naive: one check immediately before each
access, a poll on every backward edge. Each unchecked access splits
into a *check*, whose result of class `a` is a proven address, and a
*raw access* that reads only that proof and checks nothing itself.
Pointer arithmetic becomes `flight`, which states where the address
and where the capability each come from.

Here is a linked-list sum after optimization, first unchecked, then
checked (from [the guide](guide.md), which generates both):

```prolog
% unchecked: load means "check, then access"
block('L4', [], [
    let(tmp(v11), w, load(sw), [tmp('pr.1')]),        % n->value
    let(tmp(v12), w, add, [tmp('pr.2'), tmp(v11)]),
    let(tmp(v14), p, add, [tmp('pr.1'), const(8)]),   % &n->next
    let(tmp(v15), p, load(p), [tmp(v14)])             % n->next
], goto('L3'))
```

```prolog
% checked: every check written out
block('L4', [], [
    let(tmp(chk0), a, check(0, 4, read, 1), [tmp('pr.1')]),
    let(tmp(v11), w, raw_load(sw, 0), [tmp(chk0)]),
    let(tmp(v12), w, add, [tmp('pr.2'), tmp(v11)]),
    flight(tmp(v14), add, [address(tmp('pr.1')), const(8)],
           lower(tmp('pr.1'))),
    let(tmp(chk1), a, check(0, 8, read, 8), [tmp(v14)]),
    let(tmp(v15), p,
        raw_load_pointer(0, [aux_read, lower_resolve, address_read]),
        [tmp(chk1)])
], goto(poll('L3')))
```

Read the pieces:

- `check(0, 4, read, 1)` traps unless `pr.1`'s capability permits
  reading the four bytes `[pr.1+0, pr.1+4)`, alignment 1. Its result
  `chk0`, a class-`a` temporary holding the same address, is the
  *only* thing the following `raw_load(sw, 0)` may read. The raw
  load itself performs no test.
- `flight(tmp(v14), add, [address(pr.1), const(8)], lower(pr.1))`
  builds `&n->next` explicitly: the address is `pr.1`'s intval plus
  8 (`copy`, `add`, or `sub` over 64-bit words; each argument is an
  `l` value or an `address(P)` projection), and the capability is
  exactly `pr.1`'s (`lower(P)`), or `none` for integer-to-pointer.
  The two donors may differ. Constructing the pair proves nothing —
  the later check still tests it. The backend infers neither half.
- The pointer load's effect list
  `[aux_read, lower_resolve, address_read]` is Fil-C's at-rest
  protocol, executed in order: read the slot's stored lower (or
  atomic box) from aux, resolve it, then read the address. A pointer
  *store* runs the longer
  `[aux_ensure, lower_barrier, rooted_reload, lower_write,
  address_write]` (§8). These lists are closed vocabularies
  (`pointer_memory_effects/2`); the validator requires the complete
  protocol for the proof's provenance.
- `goto(poll('L3'))` puts the loop's pollcheck on the back edge.

A smaller, complete checked example — one we will also read as NFB
words in §18 — is the corpus file
[pointer-effects.ir](../tests/filc/pointer-effects.ir). Unchecked,
`large_store` fetches two pointers from C helpers, forces a
collection, and stores one into the other:

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

Pizlonated, the single store becomes a write-check of eight bytes at
alignment 8 followed by the raw pointer store with its full effect
protocol:

```prolog
let(tmp(chk0), a, check(0, 8, write, 8), [tmp(dst)]),
raw_store_pointer(0, tmp(src), tmp(chk0),
    [aux_ensure, lower_barrier, rooted_reload, lower_write,
     address_write])
```

`aux_ensure` may exit to the runtime (allocating a large aux), which
is why `rooted_reload` reloads the destination pair from its rooted
frame slot rather than trusting the ephemeral proof across that
call. The detail is in [pizlonation.md](pizlonation.md); the point
for the IR reader is that *nothing about the access is left for the
backend to invent*.

## 8. The checked vocabulary

The checked stage adds these `let` ops (all trapping exactly as the
plain `check` they refine, unless noted):

| Op | Reads | Means |
| --- | --- | --- |
| `check(Lo, Hi, Rights, Align)` | `[p]` → `a` | trap unless `[P+Lo, P+Hi)` is accessible with `Rights` and `P+Lo` is `Align`-aligned |
| `check_ahead(Lo, Hi, Rights, Align, AHi)` | `[p]` → `a` | as `check`, but only `[Lo, AHi)` is this access's own need; the rest is checked early for a later access every path reaches |
| `renew(Lo, Hi, Rights, Align)` | `[a, p]` → `a` | reuse the earlier dominating proof's bounds; retest only the free and read-only flags |
| `renew_hull(Lo, Hi, Rights, Align)` | `[a, a, p]` → `a` | a renew whose bounds two earlier proofs cover together |
| `half_check(Bound, Lo, Hi, Rights, Align)` | `[a, p]` → `a` | test only the one bound (`upper` or `lower`) the earlier proof does not already establish |
| `span_test(Lo, Hi)` | `[p]` → `w` | 1 if the object contains `[P+Lo, P+Hi)`, else 0; never traps, no safepoint |
| `renew_if(Lo, Hi, Rights, Align)` | `[p, w]` → `a` | `check` whose bounds a passing `span_test` proves; flags and alignment still tested |
| `limit(Size)` | `[p]` → `l` | an opaque snapshot of the pointer's bounds; never traps |
| `check_limit(Lo, Hi, Rights, Align)` | `[p, l]` → `a` | `check` with bounds tested against a `limit` snapshot |
| `check_local(Name, Off, Bytes, Rights, Align)` | `[]` → `a` | prove an access inside the named local `Name` |
| `check_function` | `[p]` → `f` | trap unless the pointer is a function object's exact callable address |
| `raw_load(T, Off)` | `[a]` | non-pointer load at `A+Off`, no check |
| `raw_load_pointer(Off, Effects)` | `[a]` → `p` | pointer load at `A+Off`, running `Effects` |
| `raw_cas(T, Off)` | `[a, K, K]` | `cas` at `A+Off`, immediately after its own check |

plus the instructions `raw_store`, `raw_store_pointer`, `raw_call`,
`flight`, and `touch` from §4. Stage discipline is strict: a checked
Fil-C module may contain no `load(T)` or `store` at a `p` address,
no ordinary indirect `call` (direct `global` calls remain), and no
pure `p` copy/add/sub or `itop` outside `flight` (symbol copies
still call getters). If any checked vocabulary appears at all, all
of these rules apply to the whole module.

The *reuse* family (`renew`, `half_check`, ...) exists because naive
pizlonation checks more often than necessary, and Fil-C's own
compiler removes redundant checks aggressively. nanofil's check
passes (`--checks=reuse`, `renew`, `combined`, ...; the `-O` default
is `combined`) rewrite checks into cheaper forms that cite an
earlier proof. The crucial design choice is that **the citation is
in the term**: a `renew` reads the proof it renews, a `half_check`
the proof that covers the other bound, a `renew_if` the span test
that guards it. Whoever produces checked IR must state its evidence;
the validator checks the citation and never searches for one. NFB
therefore needs nothing extra to carry proofs — they are already
operands (§16).

## 9. How the validator makes this mean "safe"

In a checked function, the rule (`checked_insts/5` and friends in
ir.pl) is structural. Which check covers a raw access is determined
by its address operand: that operand must be a class-`a` temporary,
and its defining check must

- **cover** the access: `Lo ≤ Off` and `Off + Size ≤ Hi`, the
  access's required alignment dividing the check's `Align` and
  `Off - Lo`, and write rights for a store (`access_size_align/3`
  gives each access form's size and alignment); and
- **still be valid** at the access: the check is immediately
  followed by its first use, and any later reuse of a heap proof is
  allowed only along paths where every intervening instruction is
  *evidence-preserving* (`evidence_preserving/1`) — no call, poll,
  `alloc`, `setjmp`, `va_arg`, getter, or other safepoint, and
  neither the proof nor the checked pointer redefined. Evidence
  crosses a block edge only if every incoming edge carries it; a
  poll edge carries none. Local (`check_local`) and function
  (`check_function`) proofs have exactly one use, immediately after.

The reuse forms extend this without weakening it: each states its
earlier proof, its constant pointer distance, single-definition
requirements, and span arithmetic, and the validator re-derives each
condition (`pointer_distance/4`, `guard_covers/5`, `half_known/6`,
and kin). Weaken a check so it covers two bytes instead of four and
the module is refused; delete it and the raw load reads an undefined
temporary — or, if you rewire it to the raw pointer, a class error
(`p` used as `a`). `nanofil check FILE` reports any of these on
hand-edited IR.

Semantically, the interpreter distinguishes three ways a run can go
wrong, and the distinction *is* the safety claim:

- **trap** — a Fil-C panic: the program did something its capability
  forbids, and stopped cleanly. Legitimate; buggy C gets this.
- **ub** — C undefined behaviour the model names as such.
- **unchecked(Why)** — a raw access or raw call whose proof did not
  actually authorize it at run time. This outcome means the
  *compiler* is broken: a missing or too-weak check let an access
  through that should have trapped (or worse).

"Soundness of checking" is the statement that a module the validator
accepts never reaches `unchecked`. For the model's *core subset*
(§19) this is proved in Rocq as [valid_no_unchecked]
([Soundness.v](../rocq/theories/Soundness.v)), under explicit axioms
about the Fil-C runtime, each backed by a native test
([formal.md](formal.md), [runtime-axioms.md](runtime-axioms.md)).
The proof is of the Rocq validator's transcription of the rule; that
the transcription *is* the rule is established by agreement with
`valid_module/1` over the corpus and its mutants, not proved. That
the emitted assembly does what the checked IR says, and that the
runtime keeps its side, are separate claims held by differential and
native tests. [campaign.md](campaign.md) keeps the three apart;
this guide follows it: the validator checks each module against a
rule, the theorem says the rule is sound (for the core subset), and
tests tie rule to machine.

A program that *never panics* is a different, stronger property of
one particular program, and is later work in the same campaign.

With the two stages understood, NFB's job can be stated in one
sentence: write any module `valid_module/1` accepts — either stage,
either mode — as words, with exactly one encoding per module, and
read it back.

# Part 3: NFB

## 10. What NFB is, and why it exists

**NFB is a faithful binary encoding of the term IR — not a new IR.**
It encodes exactly the grammar of ir.pl: nothing is added, dropped,
or reinterpreted. Every module `valid_module/1` accepts has exactly
one NFB encoding (Stage and mode recorded in the header), and
decoding gives the module back — exactly, when the optional NAMES
section is written; up to the names of temporaries, labels, and
locals when it is not.

Until NFB, the IR's only concrete form was Prolog canonical terms —
the right choice while every producer and consumer was Prolog. Four
pressures motivate a binary form (the RFC's account):

1. **A wire format for a library.** The Gallina backend campaign
   ends in `libnanofil`, a Fil-C library a program hands IR at run
   time; the regex compiler is the first client. Today it prints
   terms for a Prolog process to read.
2. **Decode cost.** In the Rocq model a name is a ground term,
   compared structurally, and every table is a map keyed by names.
   A format with dense integer ids takes names off the hot path.
3. **Identity.** Caches currently key compiled code by a hash of
   printed term text. With one encoding per module, the bytes
   themselves are the identity.
4. **A small proved reader.** A reader of untrusted input should be
   short, total, and proved. A hand-written term parser is none of
   these; the plan already replaces it with a Gallina one.

The goals follow: faithful, one encoding per module, linear to read
in a single forward pass with no recursion on input depth, dense
integer ids so consumers can use arrays instead of maps, simple
enough for short Gallina encoder/decoder functions with an inverse
theorem, and easy to produce from C with a header-only helper.
Deliberate non-goals: compactness (compress outside the format if
needed), a stable public ABI (the IR still changes; the format
follows it), replacing the term form (terms remain what people read
and Prolog computes on), and carrying native code.

Status, honestly: NFB is **version 0.1, provisional**. The Prolog
encoder/decoder ([nfb.pl](../src/nfb.pl)), the `encode` / `decode`
commands, and the corpus gate [tests/nfb.sh](../tests/nfb.sh) are
implemented. The Gallina twin is in the backend project (§19).
Opcode numbers are still provisional at major version 0 — do not
build an external tool on them yet. This guide describes the format
as implemented, following the RFC's "Changed in the implementation"
notes where they depart from the draft; those departures are flagged
below because each teaches something about the IR.

Five design decisions shape everything else. Hold onto these and the
details are unsurprising:

- **Container: sections with lengths**, as in WebAssembly. A reader
  can skip a section it does not need.
- **Body: a flat word stream**, as in SPIR-V. Every instruction
  begins with a word holding its opcode and length. Nothing is
  nested, so nothing is parsed recursively.
- **Ids are implicit and dense.** A temporary's id is its position
  among the function's *first* definitions; blocks and locals are
  numbered in stream order. (The "first" is the rebind story, §13.)
- **Phis stay phis.** No conversion to block parameters: the model,
  semantics, and proofs are about `phi(...)`, so NFB encodes phis.
- **Lists keep their order.** Items, blocks, phi pairs, and call
  arguments are written in term order. Canonical form comes from the
  encoder being a function of the term, never from sorting anything
  semantic.

## 11. The container: header and sections

An NFB file is a whole number of little-endian unsigned 32-bit
**words**. Every length in the format counts words, not bytes. The
file is a four-word header followed by sections:

| Word | Field | Value |
| --- | --- | --- |
| 0 | magic | `0x0042464E` — the bytes `N F B \0` |
| 1 | version | major in the high 16 bits, minor in the low 16; currently `0.1` |
| 2 | flags | bit 0: stage (0 unchecked, 1 checked); bit 1: mode (0 plain, 1 filc); bit 2: *ordered* (§16); all other bits zero |
| 3 | section count | how many sections follow |

Each section is an id word, a payload-length word (in words), then
the payload. Sections appear in strictly increasing id order, each
id at most once, and the file ends where the last section ends.

Section ids divide the world in two:

- **Core sections** (ids below `0x100`) *define* the module. A reader
  rejects a core id it does not know. An empty core section is
  omitted entirely.
- **Side sections** (ids `0x100` and up) never change what the
  module means, never contribute to its identity, and may be skipped
  unread. Ids from `0x200` up are open for tools' own data.

| Id | Name | Holds |
| --- | --- | --- |
| 1 | STRINGS | symbol names and `loc` file names |
| 2 | CONSTANTS | wide integer constants (§14) |
| 3 | SYMBOLS | every name the module defines or refers to |
| 4 | DATA | the `data` items' bodies |
| 5 | FUNCTIONS | the `func` bodies |
| 6 | CERTIFICATES | reserved, not yet specified (§16) |
| `0x100` | NAMES | original names of temporaries, labels, locals (§15) |
| `0x101` | CONTEXT | the `context` records and where they stood (§15) |

The flags deserve a remark. Stage and mode are *derived* from a
module's vocabulary by `module_stage/2` and `module_mode/2` (§5);
the header merely restates them, and a reader verifies the agreement
— in the Prolog implementation, by re-encoding (§16). The *ordered*
flag is computed by the encoder itself, exactly when the two
one-pass conditions of §16 hold, so it is part of the canonical form
rather than a producer's promise.

Two scalar conventions recur everywhere:

- **`i64`**: a signed 64-bit integer as two words, low then high
  (two's complement). Used for check bounds (`Lo`, `Hi`), offsets,
  and sizes.
- **Enumerations** (class, width, condition, rights, linkage, ...)
  take one word each, with listed codes; a value outside the list is
  an error. Class codes run `0` for `void` (result positions only),
  then `1 w`, `2 l`, `3 s`, `4 d`, `5 x`, `6 p`, `7 a`, `8 f`.
  Widths and load types deliberately reuse the class code numbers,
  adding `9 b`, `10 h` for widths and `16`–`21` for the narrow types
  `sw uw sh uh sb ub`. The full code table is in
  [nfb.md's appendix](nfb.md#appendix-assigned-numbers), generated
  from `nfb_code/3` in nfb.pl.

## 12. The tables: STRINGS, CONSTANTS, SYMBOLS, DATA

Four sections set up everything the function bodies refer to by id.
All are canonicalized the same way: sorted where the term has no
order to preserve, deduplicated, with nothing unused admitted.

**STRINGS (1).** A count, then each string as a byte length followed
by its bytes packed four to a word (low byte first, last word
zero-padded). The strings are the UTF-8 bytes of each symbol atom
and each `loc` file name, **sorted by bytes**, distinct, each used.
A *string id* is an index into this table. (The Prolog reader
requires the bytes to be valid UTF-8; the Gallina reader keeps a
string's bytes as they are — §19.)

**CONSTANTS (2).** A count, then each constant as **three words**,
low first: a signed 96-bit integer in two's complement, sorted
ascending as signed integers, distinct, each outside the inline
range of §14 and each used. The draft proposed unsigned 64-bit; the
implementation widened it because the corpus has negative constants
(`const(-1)`), a `-2^63` data item, and x87 extended constants above
2^64. Any constant from `-2^95` to `2^95 - 1` is encodable; anything
wider is an encoder error.

**SYMBOLS (3).** A count, then three words per symbol: its name (a
string id), a packed kind-and-linkage word (kind in the low 8 bits,
linkage code above them), and an extra word. Kinds:

| Kind | Means | Extra word |
| --- | --- | --- |
| 0 | function defined here | 0 |
| 1 | data defined here | the priority of an `init` linkage, else 0 |
| 2 | alias | the target's symbol id |
| 3 | named but not defined (an external) | 0 |

Ordering matters and is fixed: defined symbols and aliases come
first, **in the module's item order** (a backend emits in that
order); symbols that are only named — every `global(S)` and alias
target the module does not define — follow, **sorted by name**. A
*symbol id* is an index into this table. Note what an external
carries: just a name, exactly as in the IR. NFB records no signature
for an import; agreeing on what each import is remains the client's
business (an RFC open question).

**DATA (4).** For each kind-1 symbol, in symbol order: the alignment
word, an item count, then the items. Each item starts with a kind
word — `0` for `item(W, const(N))` (width code, then `N` as a
*constant word*, the operand form of §14, because data has the same
negative and wide constants as code), `1` for `item(b, str(Cs))`
(byte length, then the raw bytes packed — bytes as they are, not
UTF-8), `2` for `item(W, sym(S, Off))` (width, symbol id, `Off` as
i64), `3` for `zero(N)` (`N` as i64). `zero(N)` *describes* N bytes
without containing them: a consumer must bound it by its own limits,
not the file's size (§16).

**FUNCTIONS (5).** For each kind-0 symbol, in symbol order: the
body's length in words, then the body. The length lets a reader skip
to any function, or hand functions to separate workers, without
reading their contents.

## 13. Function bodies: a flat stream of instructions

A body is a short header, then one flat stream:

| Field | Words | Notes |
| --- | --- | --- |
| return type | 1 | a class code, `0` for `void`; `tuple([K1, K2])` is `0x100 + 16*K1 + K2` |
| parameter count | 1 | |
| parameter classes | 1 each | `w`, `l`, `p`, `s`, or `d` |
| block count | 1 | must equal the blocks in the stream |
| temporary count | 1 | must equal parameters plus first definitions |
| local count | 1 | must equal the `local_alloc` count |

The three counts let a consumer size its tables before reading the
stream. They are verified, never trusted: the reader bounds each
count against the words remaining *before* allocating anything
(every block, definition, and local costs at least one word), then
compares against what the stream actually contains.

### Instruction headers and groups

Every instruction starts with a **header word**: the *opcode* in the
low 16 bits and the instruction's *total length in words, header
included*, in the high 16. `0x00040010` is therefore "opcode
`0x10` (`add`), four words". The 16-bit length caps an instruction
at 65535 words; nothing in the corpus comes near it, and the encoder
refuses anything longer.

There is **no block marker**. A block is its phis, then its plain
instructions, then exactly one jump; the jump ends the block and the
next instruction begins the next one. Opcodes therefore fall into
three *groups*, and their order within a block is fixed:

| Group | Opcodes | Role |
| --- | --- | --- |
| rebind (prefix) | `0x01` | annotates the next instruction's definitions |
| phi | `0x08` | block heads (never in the entry block) |
| plain | `0x10`–`0x7F` | everything else |
| jump | `0x80`–`0x85` | block ends: `goto`, `branch`, `ret`, `rets`, void `ret`, `unreachable` |

Within the plain group the numbering is by family, with gaps:
`0x10`–`0x1C` binary ops, `0x20`–`0x30` unary ops and conversions,
`0x38`–`0x40` compare/extend/load/alloc/variadic/setjmp/atomics,
`0x50`–`0x5D` the checked-stage ops (checks, renewals, raw
accesses), `0x60`–`0x74` stores, locals, calls, `flight`, and raw
stores. The authoritative table is `nfb_form/3` in
[nfb.pl](../src/nfb.pl), restated in
[nfb.md's appendix](nfb.md#appendix-assigned-numbers). Opcodes are
never renumbered or reused within a major version; a removed
instruction's number stays retired.

### Layout rule

The layout after the header is *mechanical*. Each IR instruction
form, and each `let` op, gets one opcode. Its words are:

```text
header · [result class, if it defines a temporary]
       · static attributes, in the order the term writes them
       · operands
```

So `let(tmp(D), K, cmp(Cond, K1), [A, B])` (opcode `0x38`) is
`header, K, cond, K1, A, B`, and a `check` (opcode `0x50`) is
`header, K, Lo, Hi, rights, align, P` where `Lo, Hi` are each an i64
— the six-word *range* `Lo, Hi, rights, align` recurs in every check
form. You rarely need the appendix open: given the term, you can
predict the words.

Variable-length instructions take their element count from the
header's length — there is no separate count word to disagree with
it. A phi is its class, then `(block index, operand)` per pair, to
the end of the instruction. A call is its result word, its callee
operand, then `(class, operand)` per argument. Effect lists
(`raw_load_pointer`, `raw_store_pointer`) are written out code by
code to the end of the instruction, because the IR says these steps
are *executed*, not implied. (`asm_fixed` is the one exception that
carries an explicit input count, since inputs and outputs share one
instruction and the boundary between them must be stated.) No
instruction contains another: the deepest nesting in the whole
format is section, function, instruction.

### Dense ids, and the rebind word

Definitions never name their result. A temporary's id is implied by
counting: parameters take ids `0..n-1` in order; each later
*first* definition takes the next id, in stream order. A phi, a
`let`, a `flight`, a `local_load`, and a single call result define
one temporary; a tuple call result defines two; `asm_fixed` defines
one per output. Blocks are numbered in stream order (entry is 0),
named locals by their `local_alloc` in stream order — three separate
dense numberings, mirroring the IR's separate namespaces.

The catch is §3's leniency: the IR is not strict SSA — a temporary
may be defined again. A format in which a redefinition "cannot be
written" would be unfaithful, so the implementation adds the
**rebind** prefix (opcode `0x01`). It precedes an instruction that
redefines a temporary and holds one word per temporary that
instruction defines: `0` for a first definition (take the next id),
`id + 1` for a redefinition of `id`. It is written *only* when at
least one of those words is nonzero, so the encoding stays a
function of the module — and a strict-SSA producer (which is to say,
essentially every producer) never writes one. For the `twice`
fixture of §3, the second `let` defining `t` (id 1, after parameter
`a` as id 0 and the first `t`) is preceded by a one-payload rebind
naming `1 + 1 = 2`.

Jump targets pack the poll bit into the block index: a target word
is `block_index << 1`, with the low bit set for `poll(L)`. A call's
*result word* is `0` for `void`, a class code for one result, or the
`0x100 + 16*K1 + K2` tuple form — the same packing as a function's
return type. `flight` writes its op code (`copy`, `add`, `sub`), a
lower tag (`0` for `none` with no following operand; `1` for
`lower(P)` followed by `P`'s operand), then per argument a tag (`1`
for `address(P)`, `0` for a plain value) and an operand. `loc`
writes a STRINGS id and a line number — it stays in the stream,
hence in the module's identity, as the RFC's draft decided.

## 14. Operands and constants: one word per value

An IR *value* (`tmp`, `const`, or `global`) is a single **operand
word**: the low two bits are a tag, the upper thirty a payload.

| Tag | Payload | Term |
| --- | --- | --- |
| 0 | temporary id | `tmp(N)` — word = `N << 2` |
| 1 | the constant itself, signed 30-bit | `const(N)`, `-2^29 ≤ N < 2^29` |
| 2 | index into CONSTANTS | `const(N)`, any other `N` |
| 3 | symbol id | `global(S)` — word = `S << 2 \| 3` |

So temporary 1 is the word `4`, the inline constant 1 is
`1 << 2 | 1 = 5`, the inline constant 80 is `321` (`0x141`), and
symbol 2 is `11`. You will see all of these in §17–18.

The signed inline range is another implementation correction to the
draft (which assumed non-negative constants): tag 1's payload is a
signed 30-bit integer in two's complement, `-2^29` to `2^29 - 1`.
Tag 2 indexes the 96-bit CONSTANTS table of §12. Canonicity pins the
choice: a constant inside the inline range *must* be written inline,
so every constant has exactly one spelling. The same operand forms
serve as *constant words* inside DATA items.

Everything that is not a value is equally plain: an enumeration is
one word holding its code; an alignment, size, or line number is one
unsigned word; a bounds end or offset is an i64 (two words); a block
index (in a phi pair) is one word; a jump target is the shifted,
poll-tagged form of §13; a string id, symbol id, and local id are
each one word indexing their table. There are no variable-length
integers anywhere — no LEB128, no tagged unions the opcode does not
already determine. Given the opcode, a reader knows exactly what
each following word is.

## 15. Names: ids in the core, spelling on the side

Core sections contain no temporary, label, or local names at all —
only ids. **NAMES (`0x100`)** restores the spelling for round trips
with the term form: per function, in symbol order, three lists — its
temporaries' names in id order, then its labels', then its locals'.

The implementation encodes these names as *terms*, not term text, so
that no reader needs a Prolog term parser. Each side section begins
with its own string pool (in the STRINGS layout) holding every atom
and functor it uses. A term is then a tag word plus its parts:

| Tag | Form | Followed by |
| --- | --- | --- |
| 0 | integer | three words, as in CONSTANTS |
| 1 | atom | its pool id |
| 2 | compound | functor pool id, arity, then each argument term |
| 3 | proper list | length, then each element term |

NAMES writes each name list as a count followed by that many side
terms (the pool and the term tags are visible in the worked example
of §17). **CONTEXT (`0x101`)** uses the same term encoding: the
pool, a count, then for each `context` item the number of
non-context items that stood before it, followed by the item itself
— so the decoder splices every context record back into its original
position in the item list.

Without NAMES, a decoder names each temporary, label, and local by
its id — the integer itself: `tmp(0)`, block `0`. The decoded module
is then the same module *up to renaming*, and (this is the
round-trip gate's second half) its core encoding is word-for-word
the original's. `nanofil encode` writes NAMES and CONTEXT by
default; `module_nfb/3` takes the subset of side sections to write.

Two cautions about side sections. First, a *compiler* must not read
NAMES or CONTEXT for anything that affects the code: they are inert
by design. Second, a known wart: block labels *do* reach the emitted
assembly text (`.L<function>.<label>`), so while the Prolog compiler
is the byte-identity oracle, a backend that must match its output
byte-for-byte has to read NAMES for labels. The RFC records this as
open question 2; the guide merely warns you that "names don't
matter" is true of meaning, not yet of assembly bytes.

## 16. Canonical form, identity, and what a reader must refuse

A module has one encoding because every choice an encoder could make
is fixed:

- Lists keep term order; nothing semantic is sorted.
- STRINGS and CONSTANTS are sorted, deduplicated, and hold nothing
  unused; named-only symbols are sorted by name after the defined
  ones in item order.
- A constant in the inline range is written inline.
- Padding bytes and unused bits are zero; an empty core section is
  absent; a rebind appears only when needed.
- Ids are implied by position, so there is no numbering to choose.
- Header flags are computed from the module, including *ordered*.

The **module id** is the SHA-256 of the header and the core sections
(with the section count taken as the number of core sections). Side
sections do not contribute. Two modules with the same id are the
same term up to renaming. A cache key for compiled code is the
module id *together with* the compiler's version and options — the
format's version and the compiler's are separate things, and a cache
needs both. Each function body is likewise a self-contained range
once its symbols are fixed, so a per-function id (for a JIT cache)
can be defined the same way; `nfb_core/2` in nfb.pl computes the
core words the identity is taken over.

**Ordered.** The header's bit 2 promises the two properties a
one-pass consumer needs (well-formedness rules 11 and 12): every
non-phi temporary operand is defined earlier in the stream, and
every jump to a block at or before the current one carries its poll
bit. Rule 12 is a syntactic sufficient condition for "every CFG
cycle has a poll edge": any cycle has an edge that goes backward in
stream order. The encoder *sets the flag itself* exactly when both
hold — it is computed, not promised. (A plain-mode loop without poll
edges, like §18's `count`, is therefore *not* ordered; pizlonation's
poll on every backward edge is what lets checked loops qualify.)
Reverse postorder is deliberately not
tested; rules 11 and 12 are what one-pass compilation needs.

**Well-formedness** is the structural contract a reader enforces
before anything else looks at the module — twelve rules, each
checkable in one pass with no knowledge of what instructions mean:
magic, version, zero unused bits, and exact total length; increasing
section ids with every core id known; every count and length fitting
in what remains; every enumeration word listed; every id below its
table's size; every instruction's length legal for its opcode and
ending inside its body; blocks shaped phis–plain–jump with an
empty-phi entry and a jump last; header counts matching the stream;
locals used only after their `local_alloc`; the canonical-form rules
above; and, if ordered, rules 11 and 12.

The Prolog reader enforces all of this by a pleasingly blunt method:
it decodes the words, *re-encodes the module it read, and requires
the very words it was given* (tool sections from `0x200` aside).
Canonicality is thus not a second checker that could drift from the
writer; it is the writer. Stage and mode agreement comes free the
same way: a checked-stage opcode in an "unchecked" file changes the
derived stage, hence the flags, hence the words — refused. The
Gallina decoder does the same thing (§19), which is what makes its
canonical-form theorem cheap.

Passing the reader makes the words *a term of the grammar*. It does
not make them *valid*: classes, dominance, evidence coverage, and
stage discipline remain `valid_module/1`'s work (and its Rocq
transcription's). In particular:

> **Passing the reader proves nothing about safety.** Only
> pizlonation or validation does. A consumer that accepts checked
> modules must run the validator on what it decoded, every time.

**Which stage a client sends decides what it is trusted with:**

| A client sends | The library does | A wrong module can cause |
| --- | --- | --- |
| unchecked | pizlonate, validate, compile | a wrong result or a Fil-C panic |
| checked | validate, compile | nothing more — *if* the validator accepts only safe modules |

The second row rests on [valid_no_unchecked] (§9); a client not
trusted to be correct should send unchecked IR until that theorem
covers every construct it uses. Evidence needs no extra carriage:
the reuse forms already take earlier proofs as operands, so the
checked stream *is* the evidence. Section id 6 (CERTIFICATES) is
reserved for a future campaign's `discharged(Cert)` — a check
replaced by a certificate that it cannot fail — with one opcode
reserved to name a table entry; their layout waits on that
campaign's certificate language.

**Versioning.** A reader rejects a major version it was not built
for; while the IR changes, any layout change bumps the major, with
no compatibility promise across majors. A minor version may add
opcodes, codes, and core sections; an older reader rejects a module
using anything newer (unknown opcode, code, or core section fails
the whole module — guessing is worse than falling back) and reads
everything of its minor or earlier.

**Security posture** (the reader's input is untrusted by design;
under Fil-C a reader bug is a panic rather than a corruption, but a
panic in a host process is still a denial of service): the format
has lengths and indices but *no offsets* — a reader only moves
forward; every length is checked against what remains before it
sizes an allocation or a loop; nothing recurses on input depth; work
is linear in the input, except that `zero(N)` describes bytes it
does not contain, which a consumer must bound by policy. Resource
limits (largest module, most functions, largest allocation) belong
to the consumer, not the format.

## 17. Worked example: `add1`, word by word

The §3 module again:

```prolog
func(add1, export, w, [param(w, tmp(x))], [
    block(start, [], [
        let(tmp(y), w, add, [tmp(x), const(1)])
    ], ret(tmp(y)))
]).
```

`nanofil encode` writes 49 words (196 bytes): words 0–29 are the
core (header plus core sections), words 30–48 the NAMES section.
Here they are, exactly as read back from the file, annotated:

```text
; header                                                    ; word
0042464E  magic "NFB\0"                                         0
00000001  version 0.1                                           1
00000004  flags: unchecked, plain, ordered                      2
00000004  4 sections                                            3

; STRINGS (id 1, 3 words)
00000001  section id
00000003  payload: 3 words
00000001  1 string
00000004  4 bytes
31646461  "add1" (bytes 61 64 64 31, low byte first)       4..8

; SYMBOLS (id 3, 4 words) — CONSTANTS and DATA are empty, hence absent
00000003  section id
00000004  payload: 4 words
00000001  1 symbol
00000000  name: string 0 ("add1")
00000000  kind 0 (function), linkage export (code 0 above bit 8)
00000000  extra                                               9..14

; FUNCTIONS (id 5, 13 words)
00000005  section id
0000000D  payload: 13 words
0000000C  body: 12 words
00000001  returns class 1 = w
00000001  1 parameter
00000001  of class w                    ; defines temporary 0 (x)
00000001  1 block
00000002  2 temporaries (x, y)
00000000  0 locals                                           15..23
00040010  add (0x10), 4 words           ; defines temporary 1 (y)
00000001  result class w
00000000  operand: temporary 0          (0 << 2, tag 0)
00000005  operand: constant 1, inline   (1 << 2 | 1)           24..27
00020082  ret(V) (0x82), 2 words        ; ends block 0
00000004  operand: temporary 1          (1 << 2)              28..29
```

The core ends at word 29. Flags say *ordered*: the only non-phi
operands are temporaries 0 (a parameter) and 1 (defined by the
`add`), both defined before use, and there are no backward jumps.
NAMES follows (words 30–48). Its pool holds the three atoms
`start`, `x`, `y` sorted by bytes; then, for the one function, the
temporary list `[x, y]`, the label list `[start]`, and the empty
local list, each name a tag-1 (atom) side term naming a pool entry:

```text
00000100  section id 0x100 (NAMES)
00000011  payload: 17 words
00000003  pool: 3 strings — "start", "x", "y"   (8 words)
00000002  2 temporaries:  (tag 1, pool 1)="x", (tag 1, pool 2)="y"
00000001  1 label:        (tag 1, pool 0)="start"
00000000  0 locals
```

And back:

```sh
$ nanofil/bin/nanofil decode add1.nfb
```

```prolog
func(add1, export, w, [param(w, tmp(x))], [
    block(start, [], [
        let(tmp(y), w, add, [tmp(x), const(1)])
    ], ret(tmp(y)))
]).
```

Strip NAMES and the same core words decode to `tmp(0)`, `tmp(1)`,
block `0` — the same module up to renaming, with the same module id.

## 18. Two more readings: a phi, and a checked store

**A phi.** Encoding §3's `count` loop gives flags `0` (plain,
unchecked, *not* ordered — the back edge to `loop` has no poll bit,
so rule 12 fails). Temporary ids in stream order: `n`=0 (parameter),
`i`=1 (the phi), `i1`=2, `c`=3. The body's stream (header fields
elided) is:

```text
00020080  goto (0x80), 2 words
00000002  target: block 1 << 1, no poll        ; block 0 (start) ends
00060008  phi (0x08), 6 words                  ; defines temporary 1 (i)
00000001  class w
00000000  from block 0
00000001  operand: constant 0, inline  (0 << 2 | 1)
00000001  from block 1
00000008  operand: temporary 2 (i1)    (2 << 2) ; defined below — legal in a phi
00040010  add, 4 words                         ; defines temporary 2 (i1)
00000001  class w | 00000004 tmp 1 | 00000005 const 1
00060038  cmp (0x38), 6 words                  ; defines temporary 3 (c)
00000001  class w | 00000003 cond: slt | 00000001 K1 = w
00000008  tmp 2 | 00000000 tmp 0
00040081  branch (0x81), 4 words               ; block 1 (loop) ends
0000000C  operand: tmp 3 | 00000002 → block 1 | 00000004 → block 2
00020082  ret(V), 2 words                      ; block 2 (done)
00000008  operand: tmp 2
```

Notice the reading experience the format aims for: you always know
where you are. The phi's length (6 words) tells you it has two
predecessors — `(6 - 2) / 2` — before you read either; the `branch`
ends block 1, so the next word must begin block 2; and the phi's
forward reference to temporary 2 is visible exactly where SSA says
it must be.

**A checked store.** `nanofil nfb-terms` on
[pointer-effects.ir](../tests/filc/pointer-effects.ir) writes both
stages (`nfb-check` reports 79 words unchecked, 98 checked). The
checked header flags are `7` — checked, filc, ordered. STRINGS,
sorted by bytes, are `c_collect`, `c_large`, `c_value`,
`large_store` (ids 0–3); SYMBOLS puts the one defined function
first, then the three externals sorted by name: `large_store`=0
(kind 0), `c_collect`=1, `c_large`=2, `c_value`=3 (kind 3). Temporary
ids: `dst`=0, `src`=1, `chk0`=2. The call that fetched `src`, and
then the checked store, read:

```text
00050067  call (0x67), 5 words                 ; defines temporary 1 (src)
00000006  result word: class 6 = p
0000000F  callee: symbol 3 (c_value)   (3 << 2 | 3)
00000002  argument class: l
00000141  operand: constant 80, inline (80 << 2 | 1 = 321)

00090050  check (0x50), 9 words                ; defines temporary 2 (chk0)
00000007  result class: a (proven address)
00000000 00000000  Lo = 0    (i64, low then high)
00000008 00000000  Hi = 8    (i64)
00000001  rights: write
00000008  align: 8
00000000  operand: temporary 0 (dst)

000A0074  raw_store_pointer (0x74), 10 words
00000000 00000000  Off = 0   (i64)
00000004  value: temporary 1 (src)
00000008  address: temporary 2 (chk0) — the proof, an ordinary operand
00000003 00000004 00000005 00000006 00000007
          effects: aux_ensure, lower_barrier, rooted_reload,
                   lower_write, address_write  (codes 3–7, to end of instruction)
00010084  ret (0x84), 1 word                   ; void return; block 0 ends
```

Everything Part 2 said is visible here as ordinary data: the check's
range `[0, 8)` with write rights at alignment 8, the proof consumed
as the raw store's address operand, the five-step pointer protocol
spelled out. There is no separate "evidence section"; the checked
stream carries it because the checked IR already does.

# Part 4: the Prolog side and the Gallina side

## 19. One table, written twice

NFB is implemented twice, in two languages, from the same idea: *one
table states every instruction* — its opcode, its term shape, and
the fields its words hold, in order. Each implementation reads its
table in both directions, so its writer and reader cannot disagree
about a layout. The two implementations are then held to each other
on the corpus.

```diagram
Prolog: Prolog terms (ir.pl) ─▶ nfb.pl's module_nfb/2 ─▶ NFB words
Gallina: Prolog terms (ir.pl) ─▶ Transport.decode_module ─▶ Syntax.v modules ─▶ Nfb.v encode, via IrTerm encoders and NfbTerm words ─▶ NFB words
Agreement: nfb.pl's NFB words ─▶ byte-identical on the corpus ─▶ Nfb.v's NFB words
```

**Prolog: [nfb.pl](../src/nfb.pl).** The table is `nfb_form/3`
(opcode, instruction term with its parts as variables, field list)
with `nfb_code/3` for the enumerations. A field is a small descriptor
— `def(D)` (defines the next temporary, writes nothing), `class(K)`,
`enum(E, X)`, `u32(N)`, `i64(N)`, `opnd(V)`, `label(L)`, `target(T)`,
`local(X)`, `str(A)`, `result(R)`, `alt(...)` for tagged alternatives
(flight's lower and arguments), `count(...)` for a length-prefixed
list, `rest(...)` for elements to the end of the instruction. The
relation `module_nfb/2` runs either way: with the module ground it
writes; with words given it reads — and then re-writes the module it
read, succeeding only if the words come back identical (§16).
`module_nfb/3` chooses which side sections to write; `nfb_core/2`
strips to the identity words; `write_nfb_file/2` /
`read_nfb_file/2` convert words to little-endian bytes. The driver
([main.pl](../src/main.pl)) exposes `encode FILE OUT`, `decode FILE`
(both validating), plus the test commands `nfb-check` and
`nfb-terms`. Commands that load a module through `file_module/2`
accept a `.nfb` file wherever they accept IR text — the loader
dispatches on the suffix, and validates either way.

**Gallina (Rocq): three layers.** Rocq development calls its
language Gallina; "the Gallina side" is the Rocq model and the
backend extracted from it.

- [NfbTerm.v](../rocq/backend/NfbTerm.v) is the direct twin of
  nfb.pl, at the level of Prolog *terms*: its `forms` table gives
  each opcode a pattern with numbered holes and the fields naming
  those holes; the writer matches an instruction term against the
  patterns, the reader fills holes from fields. Words are integers
  below 2^32; ids, ordering, and canonicalization follow nfb.pl
  exactly, including naming by integer ids when NAMES is absent.
- [Nfb.v](../rocq/backend/Nfb.v) lifts that to
  [Syntax.v](../rocq/theories/Syntax.v) modules. `encode` first
  renders a Syntax module as the term ir.pl would print
  ([enc_module], built from IrTerm.v's per-instruction encoders),
  then writes that term as words with NfbTerm. `decode` goes the
  other way: NfbTerm's reader gives a module term, Transport.v's
  [decode_module] turns it into a Syntax module — and then, exactly
  as in Prolog, the words are accepted only if `encode` writes the
  same words back (NAMES if present; CONTEXT and tool sections
  aside).
- [Syntax.v](../rocq/theories/Syntax.v) itself is a transcription
  of ir.pl into inductive types — one constructor per IR functor
  (`Let`, `Flight`, `RawStore`, `Call`, ...; classes `W L P A F
  Single Double Extended`; `module` as a list of `item`s) — but only
  for the **core subset**: filc mode, the checked stage, the integer,
  pointer, and (for the Lua suite) float classes, checks and their
  reuse forms, raw accesses, `flight`, poll edges, calls, `free`,
  named locals, and variadics. Vectors, `cas` and atomics, `setjmp`,
  `asm_fixed`, `touch`, and plain mode are outside it.

That last point is the one asymmetry to understand. **NFB covers the
whole IR; Syntax.v covers a subset.** A function outside the core
subset still encodes and decodes perfectly well in NFB; on the
Gallina side it becomes `IOutside Name Term` — it keeps its address
and its term (the validator can still read its signature), but it
has no modelled body, and running it in the model is stuck.
Transport.v makes that decision. Names, in the model, remain ground
terms compared structurally (`name := term` in
[Term.v](../rocq/theories/Term.v)), so NFB's dense ids do not yet
speed up the model's maps; an id-indexed form proved to correspond
to the Syntax module is the RFC's suggested path, and is the model
owner's decision (open question 8).

**Agreement is tested, byte for byte.** [tests/nfb.sh](../tests/nfb.sh)
round-trips every module of the corpus through nfb.pl — unchecked
and checked, with and without `-O`: with NAMES and CONTEXT the
reading is the very term; without them its core words are identical.
[rocq/backend/tests/nfb.sh](../rocq/backend/tests/nfb.sh) holds the
extracted Gallina backend to the same bytes: for each corpus file,
`nanofil nfb-terms` writes the NFB and prints the module as a term;
the backend must write the *very same words*, NAMES included, and
read them back as the same module. One known difference between the
readers: the Prolog reader additionally requires STRINGS bytes to be
valid UTF-8, while the Gallina reader keeps a string's bytes as they
are.

**Proofs: what is claimed, stated carefully.** The RFC asks for
three theorems, in order of use: (1) *round trip* —
`decode (encode m) = Some m'`, with `m'` equal to `m` up to names;
(2) *canonical* — if `decode ws = Some m` then `encode m` is `ws` on
the core sections, which with (1) makes the module id sound;
(3) *total and bounded* — `decode` terminates on every word list
and rejects anything malformed, with any fuel it uses proved never
to run out at the input's length. As [nfb.md](nfb.md) records the
implementation's state: because the Gallina `decode` accepts words
only if `encode` reproduces them, the canonical theorem costs little
and is proved ([decode_canonical], with [decode_identity] giving the
sound identity), and totality is proved (`NfbTotal.v`: every fueled
reader is given the length of its words, and more fuel is shown to
give the same answer, because each round consumes a word). The cost
moves to the round trip — showing the reader inverts the writer,
field by field. **That proof is on `main` too:** [round_trip] in NfbProof.v proves
`decode (encode m) = Some m`, NAMES included, for every module
`Transport.decode_module` gives, from its two halves,
[read_encode_term] (the term reader gives back what the term writer
wrote) and [decode_enc_module] (`decode_module` reads
`enc_module m` as `m`). The very strong (but empirical) corpus
agreement above holds the same thing to every real module, in both
implementations.

## 20. A map for going further

| If you want... | Read |
| --- | --- |
| the IR's normative grammar and validator | [ir.pl](../src/ir.pl) (header first) |
| one C function through every compiler stage | [guide.md](guide.md) |
| Fil-C's capabilities, collector, and ABI | [filc.md](filc.md), [abi-findings.md](abi-findings.md) |
| the checked stage's contract and effects | [pizlonation.md](pizlonation.md), [m7.md](m7.md) |
| the safety theorem and the Rocq campaign | [formal.md](formal.md), [rocq.md](rocq.md) |
| NFB as a specification, with every assigned number | [nfb.md](nfb.md) (appendix), `nfb_form/3` in [nfb.pl](../src/nfb.pl) |
| NFB in Gallina | [NfbTerm.v](../rocq/backend/NfbTerm.v), [Nfb.v](../rocq/backend/Nfb.v) |
| the model NFB decodes into | [Syntax.v](../rocq/theories/Syntax.v), [Transport.v](../rocq/theories/Transport.v) |
| the backend `libnanofil` plan NFB serves | [gallina-backend.md](gallina-backend.md) |

To summarize the whole guide in four sentences. The IR is a small,
SSA-flavoured, explicitly classed term language with two stages:
unchecked, where a load means "check then access", and checked,
where every Fil-C check, pointer construction, memory effect, and
pollcheck is written out and every raw access cites its proof. The
validator's coverage-and-freshness rule over those citations is
nanofil's memory-safety argument, proved sound for the core subset
in Rocq. NFB writes either stage as little-endian words in a
sectioned container — dense implicit ids, one header word per
instruction, one operand word per value, names and context on the
side — with exactly one encoding per module, so the words are the
module's identity. And both the Prolog compiler and the Gallina
backend implement that encoding from a single shared table design,
held byte-identical on the corpus, with the canonical-form,
totality and round-trip theorems proved.





