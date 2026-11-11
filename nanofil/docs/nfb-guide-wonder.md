# The nanofil IR and its bytecode, NFB

nanofil is a C compiler written in Prolog. Most of it does not work on C
syntax for long: the frontend lowers C to a small intermediate
representation (IR), the middle end rewrites that IR, a pass called
pizlonation makes Fil-C's memory-safety checks explicit in it, and the
backend emits x86-64 assembly for Fil-C's ABI. The IR is the contract
between all of those stages, and the thing the interpreter runs and the
Rocq model reasons about.

This guide explains that IR first, on its own terms, and then NFB, the
binary form of the same IR. It assumes you can read a little Prolog
(`f(a, [x, y])` is a compound term `f` with two arguments, the second a
list) and some assembly-like notation, and nothing about Fil-C. Where a
claim matters, it names the file that states it: the IR's grammar and
validator are [ir.pl](../src/ir.pl), the bytecode relation is
[nfb.pl](../src/nfb.pl), the RFC and the table of assigned numbers are
[nfb.md](nfb.md), and the Gallina side is
[Syntax.v](../rocq/theories/core/Syntax.v),
[NfbTerm.v](../rocq/backend/NfbTerm.v) and
[Nfb.v](../rocq/backend/Nfb.v).

Two warnings before the details, because they prevent most misreadings:

- **NFB is not a second IR.** It encodes exactly the module the term
  form encodes — no construct added, dropped or reinterpreted — as
  little-endian 32-bit words. Terms stay the form people read, print
  and compute on; NFB is a wire, storage and identity form.
- **Reading NFB proves nothing about safety.** A well-formed NFB file
  gives you a grammatical module. Only nanofil's validator
  (`ir:valid_module/1` in Prolog, `valid` in the Rocq model) decides
  whether a checked module's accesses are all covered by checks, and
  only that decision connects the bytes to Fil-C's guarantee.

## 1. One module, two concrete forms

In memory, and in every Prolog stage, a module is one ground term:

```prolog
module(Items)
```

"Ground" means no logic variables anywhere: an IR module is ordinary
data that can be printed, read back and compared for equality. An
`.ir` text file is that module written one item per term (plus optional
`run(Fn, Args)` test lines, which are not module items and are never
encoded), and [ir_text.pl](../src/ir_text.pl) reads it.

NFB writes the same `module(Items)` as a stream of words:

```diagram
 C
    │  frontend
    ▼
 module(Items)
    │  middle end
    ▼
 module(Items)
    │  pizlonate
    ▼
 checked module(Items)
    │  nfb:module_nfb/2          from either stage; Gallina's Nfb.encode writes the same bytes
    ▼
 words ── write ──▶ .nfb file
```

The pipeline in one sentence: a module is **unchecked** when its
`load`s and `store`s still mean "check, then access", and **checked**
after pizlonation has written every check out as instructions of its
own. Independently, a module is in **plain** mode when it uses only
ordinary scalars and `l` addresses, and in **filc** mode when it uses
Fil-C pointers (`p`) or anything only the Fil-C ABI has. Neither axis
is a flag in the term: `ir:module_mode/2` and `ir:module_stage/2` read
both off the module's vocabulary, so no annotation can disagree with
the contents. NFB's header restates them, and its decoder re-derives
them (see §10).

## 2. Modules, functions and blocks

A module's items are four kinds of term:

| Item | Means |
|---|---|
| `func(Name, Linkage, Ret, Params, Blocks)` | a function definition |
| `data(Name, Linkage, Align, Items)` | a data object's initial contents |
| `alias(Name, Linkage, Target)` | a second symbol for a function or data object this module defines (filc mode; GNU's alias attribute) |
| `context(Name, Records)` | explanatory records about a function — which C declaration and typed-tree node each temporary and instruction came from. No stage reads it for code or safety; passes carry it so tools can show source lines. |

Functions, data and aliases share one symbol namespace: no two items
define the same name. Item order is part of the module (a backend
emits in that order), and NFB preserves it.

A function looks like this — the first function of the corpus file
[tests/fixtures/arith.ir](../tests/fixtures/arith.ir), which the worked
examples in §11 reuse:

```prolog
func(addw, export, w, [param(w, tmp(a)), param(w, tmp(b))], [
    block(start, [], [
        let(tmp(r), w, add, [tmp(a), tmp(b)])
    ], ret(tmp(r)))
]).
```

Its fields are a symbol `Name` (an atom), a `Linkage` (`export`,
`local`, or filc-only `weak`), a return type `Ret`, a list of
parameters `param(K, tmp(N))`, and a list of blocks. `Ret` is a class
(§3), `void`, or `tuple([K1, K2])`: a two-word return for a 9–16 byte
struct, each `Ki` one of `l p s d` (filc mode only).

A block is `block(Label, Phis, Insts, Jump)`:

- `Label` is the name jumps target. Labels are unique in a function,
  and no jump targets the entry block.
- `Phis` are the block's phi instructions (§4). The first block — the
  entry block — comes first in the list and has no phis.
- `Insts` are the ordinary instructions, in execution order.
- `Jump` is exactly one jump, and it ends the block. There is no
  fall-through in the term form: the next block in the list is reached
  only by naming its label.

A jump is one of:

| Jump | Means |
|---|---|
| `goto(L)` | go to block `L` |
| `branch(V, L1, L2)` | go to `L1` if `V` (read at class `w`) is nonzero, else `L2` |
| `ret(V)` | return the value `V` |
| `rets([V1, V2])` | return a two-word tuple |
| `ret` | return from a `void` function |
| `unreachable` | stop the program (a trap instruction) |

Any target may instead be `poll(L)`: go to `L`, but first run a
**pollcheck**, Fil-C's safepoint, on the edge — after the phis' copies.
At a pollcheck the thread may answer the garbage collector and run a
deferred signal handler. Polls look like a small annotation; they are
load-bearing in the checked stage, where every cycle of the
control-flow graph must contain one (§7), because a loop that never
polls would keep the collector waiting forever.

Data items describe bytes, not instructions:

| Item | Means |
|---|---|
| `item(W, const(N))` | the integer `N` stored at width `W` |
| `item(b, str(Chars))` | the bytes themselves, one character (code 0–255) per byte |
| `item(l, sym(Name, Off))` | the address of `Name` plus `Off` (plain mode) |
| `item(p, sym(Name, Off))` | a pointer to `Name` plus `Off`, with `Name`'s capability (filc mode) |
| `zero(N)` | `N` zero bytes |

`Align` is the object's alignment (a power of two, 1–4096), and the
linkage carries the object's storage story: `export`/`local`,
`ro(...)` for read-only data, `tls(...)` for a per-thread instance,
`weak`/`ro(weak)`, `init(ctor|dtor, Priority)` for a
constructor/destructor table entry (not an object: nothing may take
its address), and `extern(weak)` for a weak declaration with no items.

## 3. Temporaries, values and classes

An instruction reads **values** and defines **temporaries**. There are
only three value forms:

| Value | Means |
|---|---|
| `tmp(Name)` | a temporary: a function-local name holding one value of one class |
| `const(N)` | an integer constant; at a float class, `N` is the unsigned IEEE bit pattern (so float constants travel as integers everywhere) |
| `global(Name)` | the address of the function or data object `Name` |

A temporary's name is a ground term, usually an atom (`tmp(v14)`,
`tmp('pr.1')`), compared only for equality; outside the term form it
has no meaning. Parameters, phis and defining instructions define
temporaries. One deliberate wrinkle: **the IR is not strict SSA.** A
temporary may be defined more than once, provided one definition
dominates every use (`ir:definitions_dominate/3`); the corpus tests
the validator on exactly that (for example `redefined` in
[tests/fixtures/copy.ir](../tests/fixtures/copy.ir), which defines
`tmp(a)` twice). The middle end is stricter — promotion produces
strict SSA, one definition per temporary — and the check-reuse rules
only ever reason about temporaries with a single definition
(`ir:single_definitions/3`), because "the value of `tmp(N)`" is only
a stable fact then. Keep the two strengths apart: validity needs
dominance, reuse needs uniqueness.

Every value has a **class**, a one-letter tag that says how wide it is
and, for pointers, what rides along with it:

| Class | Value |
|---|---|
| `w` | 32-bit integer |
| `l` | 64-bit integer |
| `s` | 32-bit float (held as its bit pattern) |
| `d` | 64-bit float (held as its bit pattern) |
| `x` | x87 80-bit extended float, C's `long double` (filc only; never a parameter, result, call argument or phi) |
| `p` | a Fil-C pointer: an address **with its capability** (filc only) |
| `a` | a **proven address**: a pointer a check has cleared (checked stage only) |
| `f` | a **proven function**: a `p` a function check has cleared (checked stage only) |

The last two are not data. A proof class (`a` or `f`) is never a
parameter, phi, call argument, call result or stored value; only a
check defines one, and only raw accesses read one (§7). A store's
width may additionally be `b` (8 bits) or `h` (16 bits), and loads and
extensions name the narrow types `sb ub sh uh sw uw` (signed/unsigned
byte, halfword, word).

Classes police the boundary between integers and pointers. A `p`
temporary is read only at `p` and vice versa; `ptoi` and `itop` are
the explicit conversions, and an `itop` result has a null capability:
it can access nothing unless the integer was *laundered* (proved,
before checking, to come from exactly one pointer), and otherwise it
simply traps at its check, which is the safe outcome. Likewise `global(S)` is read at an address class
only as data's address in plain mode; in filc mode the one reader is
`let(tmp(D), p, copy, [global(S)])`, which yields `S`'s pointer
through its runtime getter.

**Named locals** are a second, separate namespace (filc mode).
`local_alloc(Name, Size)` — only in the entry block, before its uses,
and never in a function with `setjmp` — creates a zeroed, exact-sized
object that lives until the invocation exits and has no address value:
you cannot take a `p` to it. `local_load`/`local_store` access it at a
fixed signed byte offset, and any access outside `[0, Size)` traps.
They exist so non-escaping C locals can become stack objects with
checked fixed-offset accesses instead of heap allocations.

## 4. Phis

A phi sits at the head of a non-entry block:

```prolog
phi(tmp('pr.1'), p, ['L4'-tmp(v15), start-tmp(v0)])
```

(read from the optimized `sum` in
[docs/guide/list.c](guide/list.c)). It says: `pr.1` is `v15` when
control arrived from block `L4`, and `v0` when it arrived from
`start`. The pairs are `Pred-Value` terms, one per predecessor, and
the validator requires the predecessor set of the pairs to be exactly
the block's predecessor set computed from the jumps — no missing edge,
no invented one.

All of a block's phis execute together on entry, each reading its
operand **as it stood at the end of the predecessor** — the parallel
copy of SSA, not a sequence of assignments. (Natively each phi has a
shadow slot so the copy can be done without clobbering.) For the
validator, a phi's operand counts as used at the end of its
predecessor block, and a phi destination is a definition at the head
of its own block.

Phis are why blocks exist as a unit rather than as labelled
instructions: a value that differs per incoming edge needs a place
where "which edge did we come from?" is still known. NFB keeps phis
as phis for the same reason the model does (§9) — converting them to
block parameters would give the proofs a second form to cover.

## 5. The instruction set

Almost all computation is one term:

```prolog
let(tmp(D), K, Op, Args)     % D, of class K, is Op applied to Args
```

`Op` is an atom or a small compound carrying the op's own parameters.
The validator's one table for this is `ir:op_result_ok/3` (which
classes an op may produce) together with `ir:op_arg_classes/4` (the
class each argument is read at, given the result class). The sets:

**Binary ops** — `Args` is `[A, B]`:

| Ops | Result classes | Reading |
|---|---|---|
| `add`, `sub` | any | both at `K`; at `p`, a pointer and an `l` offset |
| `mul`, `div` | `w l s d` | both at `K` |
| `udiv`, `rem`, `urem`, `and`, `or`, `xor` | `w l` | both at `K` |
| `sar`, `shr`, `shl` | `w l` | value at `K`, shift count at `w` |

**Unary ops** — `Args` is `[A]` unless noted: `neg`; `copy`;
`cast` (bitwise between `w`/`s` and between `l`/`d`); `ptoi` (`p`→`l`)
and `itop` (`l`→`p`); the float↔integer conversions `stosi stoui dtosi
dtoui xtosi xtoui swtof uwtof sltof ultof`; `truncd` and `truncx`.

**Compound ops** — the op term carries parameters:

| Op | Means |
|---|---|
| `cmp(Cond, K1)` | compare two `K1` values; the result is an integer class (`w` when `K1` is a float class). `Cond` is `eq ne sle slt sge sgt ule ult uge ugt` for integers, `eq ne le lt ge gt o uo` for floats |
| `ext(T)` | extend the low bytes of a `w` per narrow type `T`; also float widening `ext(s)`, `ext(d)` |
| `load(T)` | load a `T` (`l p s d x` or a narrow type) at the address argument. **In unchecked filc IR this means "Fil-C's check, then the access"** |
| `alloc(Align)` | a new zeroed heap object of the `l` size argument; yields the address class (`l` plain, `p` filc). `Align` is a power of two, 4–4096 |
| `va_args`, `va_arg` | variadic support: a cursor into the entry argument snapshot, and a load through it that advances the cursor (filc only) |
| `setjmp(Kind)` | `setjmp`, `'_setjmp'` or `sigsetjmp` over `[Buf, SaveMask]`; returns `w`, and returns twice natively |
| `atomic_load(p)` | a sequentially consistent atomic pointer load (filc only) |
| `cas(T)` | atomic compare-exchange `[Expected, New, Addr]`: one atomic step returning the old value; for `p` the comparison is on addresses only, capabilities ignored |

The checked-stage ops of `let` get their own section (§7); they are
the other half of the vocabulary and are what make this IR unusual.

The remaining instructions are the ones with effects, several
results, or no `let` shape:

| Instruction | Means |
|---|---|
| `store(W, V, A)` | store `V` at `A` at width `W`. In unchecked filc IR, "check, then store" |
| `atomic_store(p, V, A)` | a sequentially consistent atomic pointer store (filc only) |
| `fence` | a sequentially consistent fence |
| `access(K, A, Size, Align)` | trap exactly as a `K` (`read`/`write`) access of `Size` bytes at `A` would, and access nothing: a vector's full-width check before its chunk accesses |
| `touch(tmp(Q))` | checked stage: consume the proof `Q` of the check just before it, and do nothing else (the pizlonated form of `access`) |
| `call(Res, Callee, [arg(K, V), ...])` | call `global(F)`, or in filc mode a `p` temporary. `Res` is `void`, `result(tmp(D), K)` or `tuple([result(tmp(D1), K1), result(tmp(D2), K2)])` |
| `raw_call(Res, Callee, Args)` | checked stage: call the proven function `Callee` (class `f`) |
| `flight(tmp(D), Op, Args, Lower)` | checked stage: build a `p` from an address computation and a separately chosen capability (§7) |
| `local_alloc(Name, Size)`, `local_load(tmp(D), K, T, Name, Off)`, `local_store(W, V, Name, Off)` | named locals (§3) |
| `asm_fixed(M, Ins, Outs)` | one fixed-register instruction (`cpuid`, `xgetbv`, `rdtsc`, `rdtscp`, `lfence`, `sfence`, `pause`): `w` inputs `Reg-Value`, one `w` temporary defined per output register |
| `loc(File, Line)` | does nothing; the instructions after it, up to the next `loc`, come from that source line. It is in the stream, so it is in the encoding and in the module's identity — a deliberate choice the RFC records as open question 3 |
| `raw_store(W, Off, V, A)`, `raw_store_pointer(Off, V, A, Effects)`, and the `raw_load` ops | checked stage: accesses that do no checking of their own, reading a proof (§7) |

Two reading rules cover most validation errors you will ever see.
First, argument classes are not "whatever fits": a `w` temporary read
as `l` is an error, as is a `p` read as an integer without `ptoi`.
Second, a call to a function the module defines must pass exactly the
callee's parameter classes (a variadic callee may be passed more);
in filc mode a call may also name a function the module does not
define at all — that is an external call, and it is one of the things
that makes the module filc mode.

## 6. What `valid_module/1` adds to the grammar

The tables above are the grammar: which terms exist. A module can be
grammatical and still invalid, and everything downstream — interpreter,
pizlonation, backends, NFB consumers that compile — is entitled to
assume `ir:valid_module/1` passed. It checks, in one pass per item:

- **Names and shapes.** Unique defined names; a function's linkage,
  return class and blocks well formed; no duplicate labels; no jump
  to the entry block; data items well shaped, pointer items 8-aligned
  within their object, an `init` entry naming a function of the
  module, an alias naming a defined target.
- **Classes.** Every temporary has one class across all its
  definitions; every operand is read at a class its definition and
  the op's tables allow; constants at float classes are in range;
  no constant, parameter, phi or call result is a proof.
- **Dominance.** In every reachable block, each use — including a
  phi operand, read at its predecessor's end, and the jump's operands,
  read at the block's end — is dominated by some definition.
  Unreachable blocks are exempt from the dominance check (their phis
  must still cover their predecessors, and in checked IR their cycles
  must still poll).
- **Locals.** Each named local declared once, in the entry block,
  before any use in stream order, in a function without `setjmp`.
- **Stage rules.** In a checked module, the evidence rules of §7; in
  any module, the mode's restrictions (for example `store(p, ...)`
  and weak linkages need filc mode).

When it refuses, it throws `nanofil_error(Message)` naming the
function and the first problem found, which is why `nanofil check
FILE` is the first debugging step for hand-written IR. Note what
validity is not: it says nothing about whether the program is
correct, terminates, or avoids traps. A valid module may divide by
zero (a trap), call `free` twice (a trap), or return the wrong
number. Validity is a statement about checks and structure only.

## 7. The two stages: unchecked and checked IR

### 7.1 What changes

In unchecked IR, memory access through a `p` is written as if Fil-C's
runtime check were part of the load or store — because semantically
it is: `load(T)` at a `p` address means "trap unless the capability
allows this access, then load". That is a good form for a frontend
and a middle end to write. It is a bad form for an audit, because the
check, its bounds and the question "which check covers this access?"
are all implicit.

Pizlonation ([pizlonate.pl](../src/pizlonate.pl), named after Fil-C's
FilPizlonator LLVM pass) rewrites each such access into two
instructions that say everything:

| Unchecked | Checked |
|---|---|
| `let(tmp(D), K, load(T), [A])` | `let(tmp(Q), a, check(0, S, read, Al), [A])`, then `let(tmp(D), K, raw_load(T, 0), [tmp(Q)])` |
| `store(W, V, A)` | a `check(0, S, write, Al)` proof, then `raw_store(W, 0, V, tmp(Q))` |
| pointer load / store | the same check, then `raw_load_pointer(0, Effects)` / `raw_store_pointer(0, V, tmp(Q), Effects)` |
| `atomic_load(p)`, `atomic_store(p, V, A)`, `cas(T)` | the same shape: a check (write, for `cas`), then `raw_load_pointer` / `raw_store_pointer` with the atomic effect list, or `raw_cas(T, 0)` |
| `access(K, A, S, Al)` | that check, then `touch(tmp(Q))` |
| `call(Res, tmp(P), Args)` | `let(tmp(Q), f, check_function, [tmp(P)])`, then `raw_call(Res, tmp(Q), Args)` |
| `let(D, p, add, [P, X])` (also `sub`) | `flight(D, add, [address(P), X], lower(P))` |
| `let(D, p, copy, [P])` | `flight(D, copy, [address(P)], lower(P))` |
| `let(D, p, itop, [X])` | `flight(D, copy, [X], none)` |
| `local_load` / `local_store` | a `check_local` proof (next paragraph), then the corresponding raw access at offset 0 |

`S` and `Al` are the access's size and required alignment
(`ir:access_size_align/3`: 8 for a pointer slot, 1 for plain scalars —
Fil-C, like the native ABI, does not demand natural alignment of an
integer in memory, and its checks say so). `Q` is a fresh `chkN` name.
A local access instead uses `check_local(Name, Off, Bytes, Rights,
Align)`, which has no pointer operand at all: it proves the fixed
range `[Off, Off+Bytes)` of the named object, whose identity is in the
instruction, not in a value.

It also finishes pointer arithmetic. In unchecked IR, `add` at class
`p` silently keeps `P`'s capability. In checked IR that combination
is forbidden (`ir:implicit_flight/1`), and `flight` states the two
halves separately: the address is computed by `copy`/`add`/`sub` in
unsigned 64-bit arithmetic from `l` values and `address(P)`
projections (the address bits of a pointer), and the capability is
donated by `lower(P)` — exactly `P`'s capability identity — or by
`none`. Building the pair proves nothing about access; it only stops
the compiler from having to guess which pointer a computed address
"meant". The check that follows decides.

Finally, every edge to a block at or before its source in block order
gains a `poll`, so every cycle polls (§2). In a plain module, whose
addresses are not Fil-C pointers, pizlonation adds only the polls.

The checked stage's own `let` ops, beyond `check` itself:

| Op (result) | Operands | Means |
|---|---|---|
| `check(Lo, Hi, Rights, Align)` (`a`) | `[P]` | trap unless `P`'s capability permits `Rights` on `[P+Lo, P+Hi)` and `P+Lo` is `Align`-aligned; the result is `P` as a proven address |
| `check_ahead(Lo, Hi, Rights, Align, AHi)` (`a`) | `[P]` | exactly that check, where only `[Lo, AHi)` is the following access's own need and `[AHi, Hi)` is checked early because every path ahead needs it before any effect intervenes |
| `renew(Lo, Hi, Rights, Align)` (`a`) | `[Q1, P]` | re-prove `P` from an earlier dominating check's proof `Q1`: the bounds are borrowed, only what a `free` can change (the freed and read-only flags) is retested |
| `renew_hull(...)` (`a`) | `[QL, QH, P]` | a renew whose bounds two earlier proofs of the same object cover together, from below and from above |
| `half_check(Bound, Lo, Hi, Rights, Align)` (`a`) | `[Q1, P]` | a check that tests only the `upper` or `lower` bound natively; the earlier proof `Q1` of the same object settles the other |
| `span_test(Lo, Hi)` (`w`, never traps) | `[P]` | 1 if `P`'s object contains `[P+Lo, P+Hi)`, else 0 |
| `renew_if(Lo, Hi, Rights, Align)` (`a`) | `[P, G]` | a check whose bounds a passing `span_test` result `G` proves; only flags and alignment are retested when `G` is 1 |
| `limit(Size)` (`l`, never traps) | `[P]` | an opaque snapshot of `P`'s bounds for `Size`-byte accesses; readable only by `check_limit` |
| `check_limit(Lo, Hi, Rights, Align)` (`a`) | `[P, U]` | a check whose bounds are tested against the `limit` snapshot `U` of `P`'s lower |
| `check_local(Name, Off, Bytes, Rights, Align)` (`a`) | `[]` | prove the fixed range of the named local |
| `check_function` (`f`) | `[P]` | trap unless `P` designates a function object at its exact callable address; the result is consumed by the `raw_call` immediately after |
| `raw_load(T, Off)` (as `load(T)`, except `p`) | `[A]` | a non-pointer load at proven address `A + Off` that does not check |
| `raw_load_pointer(Off, Effects)` (`p`) | `[A]` | a pointer load at `A + Off`, performing its effect list |
| `raw_cas(T, Off)` | `[A, Expected, New]` | a compare-exchange at `A + Off`, right after its own check |
| (instructions, not ops) `raw_store(W, Off, V, A)`, `raw_store_pointer(Off, V, A, Effects)` | — | the store forms, reading a proof `A` |

The reuse forms (`renew`, `renew_hull`, `half_check`, `renew_if`,
`check_limit`) are not optimism. Each reads the earlier evidence it
relies on as an operand — a proof temporary, a span test's `w`, a
limit's `l` — and the validator checks the arithmetic itself: that
the earlier check has a single definition and dominates, that `P` is
at a provable constant distance from the checked pointer through one
single-definition base, that the earlier range shifted by that
distance covers the new one at the required alignment, and that the
function has no `setjmp`. Ordinary pizlonation emits none of them:
one check immediately before each access. They are produced only by
the optional check passes after pizlonation, and every such pass's
output is validated again from scratch.

### 7.2 The evidence rule

The checked stage is defined by how a proof may be used. The rule, in
`ir:stage_func/6` and `ir:checked_insts/5`, is:

1. **A check is followed immediately by the first access it covers.**
   "Covers" is concrete: the access is a raw access at `tmp(Q)`, its
   offset and size lie in `[Lo, Hi)`, its alignment divides the
   check's, and its rights are allowed (`write` allows reading).
   A `check_function` is followed immediately by its `raw_call`; a
   `check_local` by its fixed-offset access. Weaken `check(0, 4, ...)`
   to `check(0, 2, ...)` before a 4-byte load and the validator's
   answer is `check tmp(chk0) is not followed by an access it covers`.
2. **A heap check's proof may then serve later accesses**, while its
   evidence lasts: on every path in between only
   evidence-preserving instructions (`ir:evidence_preserving/1` —
   pure arithmetic and conversions, checks, scalar raw accesses,
   flights, `loc`, `touch`, and pointer loads with the heap load
   effects) and unpolled edges intervene, and neither the proof nor
   the checked pointer is redefined (a phi destination counts as a
   redefinition). Local and function proofs have exactly one use.
   The reuse the validator grants directly is narrow — scalar raw
   accesses, and pointer loads with the heap load effect list, at
   offsets the live range covers (or the hull of several live ranges
   of the same object). A pointer store or a `cas` always keeps its
   own check: their protocols may exit to the runtime.
3. **No proof crosses a safepoint.** A call, an allocation, a getter,
   `setjmp`, `va_arg`, a poll edge — anything that can reach the
   runtime or run other code — ends every live proof, because that
   other code may `free` the object. Across blocks, a block's entry
   evidence is the intersection over its incoming edges of what each
   edge carries, and a poll edge, or an edge from a block later in
   block order, carries none. This is a conservative one-pass rule in
   block order, and it is the rule, not an approximation of a better
   one kept elsewhere.
4. **Nothing unchecked remains.** In a checked filc module a leftover
   `load`, `store`, `atomic_store`, `cas`, `access`, `local_load`,
   `local_store` or indirect `call` is refused
   (`ir:unchecked_access/2` in the checked path), as is ordinary `p`
   arithmetic in place of `flight`.

That is the whole contract a producer of checked IR must meet,
whether it is pizlonation, an evidence pass, or — the case NFB adds —
a remote client (§9).

### 7.3 A checked function, whole

From [tests/filc/check-range.ir](../tests/filc/check-range.ir), the
`narrow` function (with its one data object), already in checked form
as a corpus file would write it:

```prolog
data(g, local, 8, [item(l, const(123))]).
func(narrow, export, l, [param(l, tmp(off))], [
    block(start, [], [
        let(tmp(base), p, copy, [global(g)]),
        flight(tmp(p), add, [address(tmp(base)), tmp(off)], lower(tmp(base))),
        let(tmp(q), a, check(0, 8, read, 1), [tmp(p)]),
        let(tmp(r), l, raw_load(l, 0), [tmp(q)])
    ], ret(tmp(r)))
]).
```

Read it as the safety argument in miniature. `base` is `g`'s pointer,
obtained by the only `global` read filc mode allows. `flight` builds
the pointer `p` = `base + off` with `base`'s capability — note `off`
is an unchecked caller-supplied `l`, and nothing so far has promised
anything. `check(0, 8, read, 1)` is the promise: trap unless that
capability allows reading the 8 bytes at `p`. `raw_load(l, 0)` then
loads through the proof `q`, and knows — because the validator checked
the pairing — that its 8 bytes at offset 0 are inside `[0, 8)` with
read rights at alignment 1. If the check were missing, the load
reading `tmp(p)` (a `p`) where an `a` is required is a class error;
if it covered 4 bytes instead of 8, rule 1 above refuses it.

## 8. How checked IR is Fil-C's memory safety, stated in IR

Fil-C's guarantee (GIMSO: garbage in, memory safety out) is that a
program's every access either does what C says or ends the program in
a Fil-C panic; it never quietly reads or writes someone else's bytes.
The mechanism is the **capability** that travels with every pointer:
in a register the pointer is a pair — the address the program sees,
and the *lower*, the start of the one object it may access — and the
object's header just below the lower holds its upper bound and its
flags (freed, read-only, and the pointer to its aux array). An access of `N` bytes at address `A` with lower `L` is
allowed when `lower ≤ A` and `A + N ≤ upper`, the flags allow the
rights, and pointer-sized accesses are aligned. Anything else traps.

Checked IR is that test, written as data:

- `check(Lo, Hi, Rights, Align)` *is* the capability test, with its
  interval made literal. Where upstream Fil-C leaves that test
  implicit in the access it instruments, nanofil's checked stage
  gives it a name, a result, and a position in the instruction stream.
- The proof classes `a` and `f` are the type system's memory of "this
  test passed, for this pointer, this range, these rights". A raw
  access cannot be written without naming its proof, so an uncovered
  access is not a subtle bug in an emitter: it is a module the
  validator refuses, and in the interpreter it is the outcome
  `unchecked(Why)`, kept distinct from a trap precisely so tests and
  proofs can tell "the program was stopped" from "safety failed".
- `flight` is where capabilities come from, and it is deliberately
  unhelpful: an address from arbitrary integer arithmetic plus a
  capability donated by `lower(P)`, or none. Forging an address is
  always possible and never sufficient; only a check turns the pair
  into permission. That is Fil-C's own rule — an integer turned into
  a pointer has a null capability — with the laundering analysis
  already done before this stage.
- `free` is why proofs expire. Freeing sets the object's upper to its
  lower and raises its flag immediately, so every capability for it
  fails every later check, while the collector reclaims the bytes
  only once nothing points to them. A proof is a statement about a
  past test, so anything that might free — a call, a poll (a signal
  handler may run), an allocation — invalidates it (§7.2 rule 3),
  and the reuse forms survive precisely by retesting the flags that
  `free` changes, under dominance conditions the validator rechecks.
- Pointer contents need a protocol, not a load. A pointer at rest is
  an address in the object's bytes with its lower in the object's aux
  array, slot for slot. So a pointer load's effect list
  `[aux_read, lower_resolve, address_read]` and a store's
  `[aux_ensure, lower_barrier, rooted_reload, lower_write,
  address_write]` are executed steps in the IR (the closed lists of
  `ir:pointer_memory_effects/2`), not annotations: read the aux word,
  resolve the lower from it, then read the address — and for a store,
  make the aux exist, barrier the stored lower for the collector,
  reload the destination from its root, and write lower before
  address. An atomic pointer access delegates the whole protocol to a
  Fil-C helper (`[atomic_read]`, `[atomic_write]`, `[atomic_cas]`).

The formal claim is deliberately narrower than "nanofil is proved".
For the **core subset** of checked filc IR — the subset
[Syntax.v](../rocq/theories/core/Syntax.v) transcribes — the Rocq
development proves [valid_no_unchecked]: a module the model's
validator accepts never reaches an `unchecked` outcome, under stated
axioms about the Fil-C runtime (allocation is fresh, objects do not
move, free changes only the header, the collector frees nothing
reachable at a safepoint, and so on). Three other links are tested,
not proved: that the model's validator is `valid_module/1` (checked
by agreement on the corpus and its mutants), that the emitted
assembly does what the checked IR says, and that the runtime keeps
its axioms. [formal.md](formal.md) and [campaign.md](campaign.md)
keep those obligations separate; this guide follows them.

One consequence worth stating plainly, because NFB depends on it:
**the stage a client sends decides what it is trusted with** (the
RFC's table). Send unchecked IR and the receiver must pizlonate and
validate it; a wrong module can then still cause a wrong result or a
Fil-C panic, but the checks are the receiver's own. Send checked IR
and the receiver validates and compiles it; if `valid` accepts only
safe modules, a wrong module can cause nothing more. A client that is
not itself inside the safety argument should send unchecked IR until
the theorem covers every construct it uses.

## 9. NFB: what it is and why it exists

NFB ("nanofil bytecode") is a faithful binary encoding of one
`module(Items)` term: the same grammar, written as little-endian
32-bit words inside a small sectioned container. It is specified in
[nfb.md](nfb.md) — Mikael Brockman's RFC, with quoted "Changed in the
implementation" notes where the code departed from the draft, and an
appendix restating every assigned number — and implemented in
[nfb.pl](../src/nfb.pl) as one relation, `module_nfb/2`, that runs in
both directions. The command line is:

```sh
nanofil encode FILE OUT    # read FILE (.c, .ir or .nfb), validate, write its NFB to OUT
nanofil decode FILE.nfb    # read NFB, validate, print the IR
nanofil nfb-check FILE     # encode, read back, and require the same module (and, for
                           # a filc module, the same for its checked module)
```

Why a binary form at all, when terms already work? The RFC's four
reasons, in the order a newcomer will meet them:

1. **A wire format for a library.** The Gallina backend campaign ends
   in `libnanofil`, a Fil-C library a program hands IR at run time
   (a regex compiler generating code is the first client). Such a
   client should not have to print Prolog terms and start a Prolog
   process to read them.
2. **Decode cost.** In the Rocq model a name is a ground term compared
   structurally, and tables are maps keyed by hashed names. Dense
   integer ids — a temporary *is* its number — remove names from the
   hot path altogether. (That gain arrives only when a consumer works
   on ids directly; §12 is honest about where the two implementations
   stand.)
3. **Identity.** The bytes are canonical (§10): one module, one
   encoding. The hash of the core bytes can therefore name the
   module, where today a cache key is a hash of printed term text
   that omits what it should not.
4. **A small proved reader.** A reader of untrusted input should be
   short, total and proved. A byte format with no internal offsets,
   read in one forward pass, is something Gallina can be proved
   about; a hand-written term parser in OCaml is none of those.

And the non-goals, which explain several choices below: compactness
(a regex function is a few kilobytes; compress outside the format),
a stable public ABI (the format follows the IR, and the IR still
changes; major version 0), replacing the term form, and carrying
native code.

Five design decisions shape everything in §10 and §11:

- **Container: sections with lengths**, as in WebAssembly — a header,
  then `(id, length, payload)` sections a reader can skip.
- **Body: a flat word stream**, as in SPIR-V — every instruction
  begins with a word holding its opcode and its length, nothing is
  nested, so nothing is parsed recursively.
- **Ids are implicit and dense.** A temporary's id is its position
  among the function's definitions, a block's its position in the
  function, a local's its position among the `local_alloc`s. A
  definition never writes its result's id, so there is no numbering
  to choose — with one exception, the `rebind` word of §11, forced by
  the IR not being strict SSA.
- **Phis stay phis** (§4), and **lists keep their order** — items,
  blocks, phi pairs, call arguments. Canonical form comes from the
  encoder being a function of the term, not from sorting anything
  semantic.

## 10. The container, the sections, and canonical form

### 10.1 Header

A file is a whole number of words — four header words, then the
sections. Bytes are each word little-endian, so the file starts with
the bytes `4E 46 42 00`, "NFB\0":

| Word | Field | Value |
|---|---|---|
| 0 | magic | `0x0042464E` |
| 1 | version | `0x00000001` — format 0.1. While the IR changes, a change to any existing layout bumps the major version and readers reject a major they were not built for; both implementations today accept exactly this word |
| 2 | flags | bit 0: stage (0 unchecked, 1 checked); bit 1: mode (0 plain, 1 filc); bit 2: ordered (§11.4). Other bits zero |
| 3 | section count | the number of sections that follow |

Sections follow in increasing id order, each id at most once, each
as an id word, a payload length in words, and the payload; the file
ends where the last section ends. Ids below `0x100` are **core**: they
define the module, and a reader rejects a core id it does not know.
Ids from `0x100` are **side** sections: they never change what the
module means. An empty core section is omitted, so a module with no
wide constants has no CONSTANTS section and no apology.

### 10.2 The sections

| Id | Name | Holds |
|---|---|---|
| 1 | STRINGS | the symbol names and `loc` file names the core sections refer to |
| 2 | CONSTANTS | the constants an operand word cannot hold (§11.3) |
| 3 | SYMBOLS | every name the module defines or refers to |
| 4 | DATA | the `data` items |
| 5 | FUNCTIONS | the `func` items |
| 6 | CERTIFICATES | **reserved in the RFC** for a future certificate table (a proposed `discharged(Cert)` instruction that replaces a check by a proof it cannot fail). Nothing emits it today, and neither reader accepts section 6 yet |
| `0x100` | NAMES | the original names of temporaries, labels and locals (§11.5) |
| `0x101` | CONTEXT | the `context` items, each with the number of non-context items before it, so the decoder restores them where they stood |
| `0x200`– | (tools) | extension space: a tool's own data, inert for meaning and identity |

The three core tables come first because everything else refers to
them by index:

- **STRINGS** is a count, then each string as a byte length and its
  bytes zero-padded to a word boundary. Strings are the UTF-8 bytes of
  an atom — so the Prolog reader requires valid UTF-8 on decode; the
  Gallina reader keeps a string's bytes as they are. The table is
  sorted by bytes, distinct, and contains only strings a core section
  uses: every defined and referred symbol name, plus every `loc` file.
- **CONSTANTS** is a count, then each constant as three words, low
  first: a signed 96-bit integer in two's complement, from −2⁹⁵ to
  2⁹⁵−1. Signed, and 96-bit, because the corpus contains negative
  constants and x87 constants wider than 64 bits — one of the RFC's
  recorded departures from its own draft. The table is sorted
  ascending as signed integers, distinct, each entry outside the
  inline range (§11.3) and each used.
- **SYMBOLS** is a count, then three words per symbol: its name as a
  string id, one word packing the kind in the low 8 bits and the
  linkage code above them (the code tables are in nfb.md's appendix;
  a data `init(_, P)` linkage with an integer priority keeps `P` in
  the third word), and an extra word (an alias's target symbol id,
  an init priority, else 0). Kinds are 0 function defined here,
  1 data defined here, 2 alias, 3 named but not defined. Defined
  symbols and aliases come first, in module item order, because a
  backend emits in that order; symbols the module only names
  (`global(S)` references with no definition) follow, sorted by name.

DATA and FUNCTIONS then give each defined symbol its body, in symbol
order. DATA writes, per data symbol: the alignment (one word), an
item count, and per item a kind word — 0 for `item(W, const(N))`
(width code, then `N` as a constant word, §11.3), 1 for a `str` item
(byte length, then packed bytes), 2 for `item(W, sym(S, Off))` (width
code, symbol id, `Off` as a signed 64-bit pair), 3 for `zero(N)`
(`N` as a signed 64-bit pair). FUNCTIONS writes, per function symbol:
the body's length in words, then the body (§11) — the length lets a
reader skip to any function, or hand functions to separate workers.

NAMES and CONTEXT do not hold term *text*: a reader should not need a
term parser, which was half the point. A side section starts with its
own string pool (STRINGS' layout) of every atom and functor it uses,
then terms as tagged words: tag 0 an integer (three words, as
CONSTANTS), 1 an atom (a pool id), 2 a compound (functor pool id,
arity, arguments), 3 a proper list (length, elements). NAMES holds,
per function in symbol order, three such lists: its temporaries'
names in id order, its labels', its locals'. CONTEXT holds the pool,
a count, and per `context` item its recorded position and the item
as a term.

### 10.3 Canonical form, and what identity means

A module has exactly one encoding because every choice an encoder
could otherwise make is fixed:

- lists keep the term's order; nothing semantic is sorted;
- STRINGS and CONSTANTS are sorted, distinct and free of unused
  entries; a constant in the inline range is written inline;
- defined symbols are in item order, named-only symbols sorted after
  them; ids are implied by position, so there is no numbering to
  choose; a `rebind` is written only when a redefinition needs one;
- padding bytes and unused bits are zero; an empty core section is
  absent; the `ordered` flag is computed by the encoder from the
  body it wrote (§11.4), never merely promised by a producer.

The **module id** is the SHA-256 of the header and the core sections
exactly as `nfb:nfb_core/2` selects them, with the header's section
count taken as the core count. Side sections do not contribute, so
two modules with the same id are the same term up to the names of
temporaries, labels and locals — which is exactly the part of the
term those names are. (A usable cache key is the module id together
with the compiler's version and options; the format's version is not
the compiler's.) Each function body is likewise a self-contained byte
range once its symbols are fixed, so a per-function id can be defined
the same way for a JIT cache; that is a definition the RFC offers,
not a service either encoder performs today.

The readers do not trust any of this — they enforce it. The Prolog
reader makes one forward pass — in particular, it refuses a body
whose block, temporary or local count exceeds the words left in it
before any table is sized from those counts — and then checks the whole
file the blunt way: it re-encodes the module it read, with the same
side sections present, and requires the very words it was given
(tool sections from `0x200` aside). Unknown opcodes, unknown
enumeration codes, unknown core sections, an instruction running past
its body, a header whose stage or mode bits disagree with the
module's vocabulary — each fails the whole module, because each means
the words cannot be the encoder's image of anything. The RFC's
well-formedness list (§"Well-formedness" of [nfb.md](nfb.md)) states
the twelve structural rules this implements; the security section
after it is the checklist for writing another reader: lengths and
indices, never offsets; every length checked against what remains
before it is used; no recursion on input depth; declared counts
verified against the stream, not trusted. Note again the boundary
from the head of this guide: a module that passes the reader is a
term of the grammar. Classes, dominance, single-use of proofs and
the stage rules remain `valid_module/1`'s work — `nanofil decode`
runs it after reading, and so must any consumer that compiles,
every time.

## 11. How a module becomes words

### 11.1 The encoder in five steps

`module_nfb/2` in [nfb.pl](../src/nfb.pl) is one relation used in both
directions, driven by one table — which is the implementation's main
defence against the two directions drifting apart:

1. **Collect the tables** (`module_tables/2`). Walk every item and
   gather every referred symbol (`global(S)` in code, `sym(S, ...)`
   in data, an alias's target), every `loc` file, and every constant
   that does not fit inline. Sort and number them as §10.2 says.
2. **Lay out the symbols** in item order, named-only symbols after,
   and record each name's symbol id, string id and constant index in
   assoc tables the writers consult.
3. **Write each data object and each function body** in symbol order.
   For a function (`func_ids`, `body_words`), numbering comes
   first: parameters take temporary ids 0…n−1, then each defining
   instruction in stream order — blocks in list order, phis before
   instructions — takes the next ids; blocks are numbered in the same
   order; named locals by their `local_alloc` in stream order. The
   body header (next paragraph) is written from those counts, then
   the blocks back to back with no separator.
4. **Derive the header.** Stage and mode are `module_stage/2` and
   `module_mode/2` of the module being written; the ordered flag is
   the conjunction over bodies of §11.4's test. The encoder refuses,
   with a `nanofil_error`, what has no encoding: a non-atom symbol, a
   constant beyond 96 bits, an `i64` field beyond 64 bits, an
   instruction longer than 65535 words.
5. **Attach the side sections** the caller asked for. The default
   `module_nfb/2` (and so `nanofil encode`) writes NAMES and CONTEXT;
   `module_nfb(Module, [], Words)` writes core alone.

In nfb.pl all of this is generated from two tables: `nfb_code/3`,
which gives every enumeration's codes (classes, widths, load and
extension types, conditions, rights, bounds, setjmp kinds, the
pointer-effect steps, flight ops, asm mnemonics and registers, and
the three linkage families), and `nfb_form/3`, which gives every
instruction's opcode and, as a list of field descriptors, exactly
which words follow its header and in which order. The writer runs
the table with the term given and unifies the fields with the term's
parts; the reader runs it with the opcode given and fills the parts
from the words. One table, so writer and reader cannot disagree
about a layout — if a form is missing from the table, the encoder
says `no encoding for ...` instead of inventing bytes.

### 11.2 Function bodies and instruction words

A function body is a short header, then one flat stream:

| Field | Words | Notes |
|---|---|---|
| return type | 1 | 0 for `void`, a class code, or `0x100 + 16*K1 + K2` for `tuple([K1, K2])` |
| parameter count | 1 | then one class word per parameter (`w l p s d` only — never `x`, never a proof) |
| block count | 1 | must equal the blocks found in the stream |
| temporary count | 1 | must equal parameters plus definitions found |
| local count | 1 | must equal the `local_alloc`s found |

The three counts let a consumer size its tables before reading the
stream; the reader checks each against what the stream actually
contains, and refuses a body whose counts exceed its remaining words
before allocating anything from them.

Every instruction starts with a **header word**: the opcode in the
low 16 bits and the instruction's total length in words, header
included, in the high 16. After the header come the fields in the
order `nfb_form/3` lists them — for a `let`, the result class first
(the definition itself writes no word: the id is positional, §11.4),
then the op's static attributes (a comparison's condition, a check's
range, an alignment) in the order the term writes them, then the
operands. Variable-length forms — a phi's pairs, a call's arguments,
an `asm_fixed`, an effect list — take their element count from the
header's length: their per-element fields repeat to the instruction's
end. No instruction contains another instruction,
and the deepest structure in the file is section, function,
instruction.

There is no block marker. A block is its phis (opcode group *phi*),
then its plain instructions, then exactly one jump (group *jump*),
and the jump ends the block: the next header begins the next block.
The groups, with the assigned numbers (provisional, major version 0;
the full table is nfb.md's appendix, restated from `nfb_form/3`):

| Opcodes | Forms |
|---|---|
| `0x01` | `rebind`, the prefix word of §11.4 |
| `0x08` | `phi`: class, then (block index, operand) per predecessor pair, in the term's order |
| `0x10`–`0x1C` | the thirteen binary `let` ops (`add` … `shl`): class, operand, operand |
| `0x20`–`0x30` | the seventeen unary `let` ops (`neg` … `ultof`): class, operand |
| `0x38`–`0x40` | `cmp`, `ext`, `load`, `alloc`, `va_args`, `va_arg`, `setjmp`, `atomic_load`, `cas`, each with its attribute words then its operands |
| `0x50`–`0x5D` | the checked stage: `check`, `check_ahead`, `renew`, `renew_hull`, `half_check`, `span_test`, `renew_if`, `limit`, `check_limit`, `check_local`, `check_function`, `raw_load`, `raw_load_pointer`, `raw_cas`. A *range* — `Lo`, `Hi` as two-word signed pairs, rights, alignment — is six words wherever it appears |
| `0x60`–`0x74` | the other instructions: `store`, `atomic_store`, `fence`, `access`, `local_alloc`, `local_load`, `local_store`, `call`, `asm_fixed`, `loc`, `touch`, `raw_call`, `flight`, `raw_store`, `raw_store_pointer` |
| `0x80`–`0x85` | the jumps: `goto`, `branch`, `ret(V)`, `rets`, `ret`, `unreachable` |

Three layouts repay a closer look. A **call** (and `raw_call`) writes
a result word (0 for `void`, a class code, or the tuple packing —
defining zero, one or two temporaries), the callee operand, then for
each argument a class word and an operand word; the argument count
is what the header's length leaves. A **flight** writes its op code
(`copy`/`add`/`sub`), then its lower as a tag word (0 for `none`, 1
for `lower(P)` followed by `P`'s operand), then per argument a tag
(1 for `address(P)`, 0 for a plain `l` value) and its operand. A
**pointer raw access** writes its offset as a signed 64-bit pair and
its proof operand, then one effect code per remaining word of the
instruction — the effect lists are written out in full because the IR
says they are executed, not implied.

### 11.3 Operands, constants and the small fields

An IR value is one **operand word**: a tag in the low two bits and a
payload in the upper thirty.

| Tag | Payload | Term |
|---|---|---|
| 0 | temporary id | `tmp(N)` becomes operand `id << 2` |
| 1 | the constant itself, as a signed 30-bit payload in two's complement | `const(N)` for −2²⁹ ≤ `N` ≤ 2²⁹−1 |
| 2 | an index into CONSTANTS | any other `const(N)`, up to signed 96 bits |
| 3 | symbol id | `global(S)` |

A constant inside the inline range *must* be inline, and one outside
*must* use the table; that forced choice is part of canonical form.
Everything else numeric is fixed by the form: offsets, bounds and
sizes (`Lo`, `Hi`, `Off`, `Size`, a `zero(N)`, a data item's symbol
offset) are a signed 64-bit integer as two words, low then high;
alignments, a `limit`'s size, a `loc` line and an `asm_fixed` input
count are one unsigned word. Enumerations take one word each from
`nfb_code/3`: classes `w`1 `l`2 `s`3 `d`4 `x`5 `p`6 `a`7 `f`8 (with 0
for `void` in result positions), widths sharing the class codes with
`b`9 `h`10, load and extension types adding the narrow codes 16–21,
conditions 0–15 in the order `eq ne sle slt sge sgt ule ult uge ugt
le lt ge gt o uo`, rights (`read`0, `write`1), and so on. A jump
target is one word: the block index shifted left by one, with the low
bit set for `poll(L)` — where a phi pair, by contrast, writes its
predecessor's plain block index. A value outside its enumeration's
list is an error, never a guess.

From the corpus's copy tests
([tests/fixtures/copy.ir](../tests/fixtures/copy.ir)), the constants
at work: in

```prolog
let(tmp(a), l, copy, [const(4294967297)]),
let(tmp(b), l, copy, [const(-2)])
```

the first constant is outside the inline range, so the module's
CONSTANTS payload is the count `1` and the 96-bit words
`0x00000001 0x00000001 0x00000000` (4294967297 = 2³²+1), and `a`'s
copy instruction is the header `0x00030021` (opcode `0x21` = `copy`,
3 words), the class `0x00000002` (`l`), and the operand `0x00000002`
— tag 2, table index 0. The second constant is inline: its operand
word is `0xFFFFFFF9`, tag 1 under the two's-complement payload of
−2 in 30 bits. Both spellings are the only ones the reader accepts.

### 11.4 Ids, definitions and the `rebind` word

Temporary ids are assigned by **first definition**, in stream order:
parameters 0…n−1, then phis and instructions as they come. This is
where the IR's non-strict-SSA wrinkle (§3) reaches the format. When
an instruction defines a temporary that already has an id — the
`redefined` function of §3 defines `tmp(a)` a second time — the
definition does not take the next id; it redefines the old one, and
the stream must say so, because the positional rule alone would give
it a fresh id and silently change the module. So an instruction that
defines any already-defined temporary is preceded by a `rebind`
instruction (opcode `0x01`): its payload is one word per temporary
the following instruction defines, 0 for a first definition (take
the next id) and id+1 for a redefinition (rebind that id; the +1
keeps 0 meaningful). The prefix is written only when at least one of
those words is nonzero, so the encoding stays a function of the
module. A strict-SSA producer never writes one, and most modules
contain none. Call results and `asm_fixed` outputs follow the same
rule, one word per defined temporary.

Two related positional rules: a temporary id may be *read* before
its first definition in the stream (a phi operand of a loop, a use
the validator will in fact reject if no definition dominates it) —
ids are names, not a schedule. And the **ordered** header flag (bit
2) records the opposite situation when the encoder finds it: in
every body, each non-phi temporary operand is already defined
earlier in the stream (well-formedness rules 11), and every backward
jump target carries its poll bit (rule 12, a syntactic sufficient
condition for "every cycle polls", since any cycle has an edge that
goes backward in stream order). The encoder sets the flag exactly
when both hold; a one-pass consumer may rely on it, and everyone else
ignores it.

### 11.5 Names: what is lost, what is not

Notice what the core encoding never writes: the *names* of
temporaries, block labels and named locals. They are pure
identifiers — the module means the same with them renamed — so the
core form replaces them with ids, and a decoder working from core
alone invents names from the ids: temporary `tmp(0)`, block `0`. What
is **not** renamed away is symbol names. A function's or object's name
is its identity to the linker and to other modules, so symbols live
in STRINGS/SYMBOLS, and `global(S)`, a `sym(S, Off)` data item, a call
target and a symbol's own definition all refer to it by symbol id.

The NAMES side section is the bridge back to the term form people
read: with it, `decode` restores `tmp(x)`, block `start`, the local
names — the printed module is the very term that was encoded. Without
it, the decoded module differs only in those invented names, and its
core encoding is word-for-word the same. That is the precise sense of
the RFC's "decoding gives back the module, up to the names of
temporaries, labels and locals", and it is what the corpus gate
checks in both directions (§12).

### 11.6 Worked example: `addw` as 54 words

Save the function of §2 on its own (one `func` term ending in a
full stop, as an `.ir` file holds it) as `/tmp/addw.ir`. It encodes
(with NAMES, as `nanofil encode` writes it) to 54 words — 216 bytes:

```sh
export SWIPL=/tmp/swipl/bin/swipl          # see AGENTS.md for the one-time builds
nanofil/bin/nanofil encode /tmp/addw.ir /tmp/addw.nfb
nanofil/bin/nanofil decode /tmp/addw.nfb   # prints the addw term above, unchanged
nanofil/bin/nanofil nfb-check nanofil/tests/fixtures/arith.ir
#   nanofil/tests/fixtures/arith.ir: unchecked 582 words, 335 core
```

The words, grouped as the reader meets them (hex; each is stored
little-endian):

```text
header    0042464E 00000001 00000004 00000004
          magic    version  flags=ordered   4 sections
STRINGS   00000001 00000003 | 00000001 00000004 77646461
          id 1     3 words     1 string  4 bytes  "addw"
SYMBOLS   00000003 00000004 | 00000001 00000000 00000000 00000000
          id 3     4 words     1 symbol  name=str 0
                                         kind 0 (function), linkage 0 (export); extra 0
FUNCTIONS 00000005 0000000E | 0000000D 00000001 00000002 00000001
          id 5     14 words    body: 13w  ret w    2 params
                               00000001 00000001 00000001 00000003 00000000
                               param w   param w   1 block   3 temps   0 locals
                               00040010 00000001 00000000 00000004
                               add: len 4, opcode 0x10; class w; tmp 0; tmp 1 (1<<2)
                               00020082 00000008
                               ret: len 2, opcode 0x82; tmp 2 (2<<2)
NAMES     00000100 00000015 | 00000004 00000001 00000061 00000001 00000062
          id 0x100 21 words    pool: 4 atoms — "a" (1 byte, 0x61), "b"
                               00000001 00000072 00000005 72617473 00000074
                               "r"               "start" (5 bytes, packed)
                               00000003 00000001 00000000 00000001 00000001
                               temps: 3 names — (tag 1, pool 0), (1, 1),
                               00000001 00000002 00000001 00000001 00000003
                               (1, 2); labels: 1 name — (1, 3 = "start")
                               00000000
                               locals: 0 names
```

So the NAMES tail is, per function: a count and one two-word tagged
term per name — tag 1 and a pool id for each atom. Drop that whole
section, fix the header's count to 3, and the remaining 31 words are
the module's core and the whole of its identity; decoding them prints

```prolog
func(addw, export, w, [param(w, tmp(0)), param(w, tmp(1))], [
    block(0, [], [
        let(tmp(2), w, add, [tmp(0), tmp(1)])
    ], ret(tmp(2)))
]).
```

Everything else in the example is doing work you can now check by
hand: the function's name survives (STRINGS + SYMBOLS) while `a`,
`b`, `r`, `start` do not (NAMES only); the flags word is 4 because
the module is unchecked (0), plain (0) and ordered (4); the `add`
header packs length 4 over opcode `0x10`; and `const(1)` in the
RFC's own `add1` example would have been the operand `0x00000005`
(tag 1, payload 1), which is why this example, using two parameters,
has no CONSTANTS section at all.

### 11.7 Worked example: a checked body

The `narrow` function of §7.3 encodes with flags `0x00000007`
(checked + filc + ordered) in 96 words. Its body stream — the part
after the six-word body header `ret l; 1 param of class l; 1 block;
5 temporaries; 0 locals` — is (hex, with the file's word index):

```text
37  00030021  copy (len 3, 0x21)   class 00000006 (p)      opnd 00000003 (global, symbol 0 = g)
40  00080072  flight (len 8, 0x72) op 00000001 (add)       lower tag 00000001, opnd 00000004 (tmp 1)
                                   arg tag 00000001 (address), opnd 00000004 (tmp 1)
                                   arg tag 00000000 (value),   opnd 00000000 (tmp 0 = off)
48  00090050  check (len 9, 0x50)  class 00000007 (a)
                                   Lo 00000000 00000000   Hi 00000008 00000000
                                   rights 00000000 (read)  align 00000001
                                   opnd 00000008 (tmp 2 = p)
57  0006005B  raw_load (len 6, 0x5B) class 00000002 (l)   load type 00000002 (l)
                                   Off 00000000 00000000   opnd 0000000C (tmp 3 = q)
63  00020082  ret (len 2, 0x82)    opnd 00000010 (tmp 4 = r)
```

Read against §7.3, every safety fact survives the trip: the check's
interval `[0, 8)`, its rights and alignment, and the identity of the
proof are all in the bytes — the proof is temporary 3, defined by the
`check` at word 48 and read by the `raw_load` immediately after, and
the range is the six words §11.2 promised. Note too what the encoder
numbered without being told: `off`, `base`, `p`, `q`, `r` are
temporaries 0–4 by first definition, and `g` is symbol 0 because the
`data` item precedes the function in the module. The same file's DATA
section writes `g`'s contents as alignment `8`, one item, kind `0`,
width `2` (`l`), and the constant operand `0x000001ED` — tag 1,
payload 123.

## 12. The Prolog and Gallina sides

NFB is defined by two functions between terms and words, and
implemented twice, against the same table.

**Prolog** is the reference implementation. `nfb.pl`'s
`module_nfb/2` is a relation, so "encode"
and "decode" are the same clauses run with different arguments
ground; `ir.pl` is the grammar it encodes, `ir_text.pl` the text form
beside it. It carries `context` items (in CONTEXT) and accepts a
module in either stage and either mode.

**Gallina** mirrors it in two layers, because the Rocq development
has two representations of a module and NFB sits between them:

- [NfbTerm.v](../rocq/backend/NfbTerm.v) works at the level of ground
  Prolog **terms** (`Term.v`'s `TInt` / `TAtom` / `TApp` / `TList`) —
  the exact twin of nfb.pl, with the same one-table design (a list of
  `form` records: opcode, a pattern with numbered holes, and the
  fields that name the holes; the writer matches a term against the
  patterns, the reader fills them back). Its functions are
  `encode_term : bool -> term -> option (list Z)` and
  `read_term : list Z -> option (term * bool)` (the boolean: whether
  NAMES was present).
- [Nfb.v](../rocq/backend/Nfb.v) works at the level of
  [Syntax.v](../rocq/theories/core/Syntax.v)'s inductives. `encode` is
  [encode_term] of [enc_module], where the `IrTerm.v` encoders write
  a Syntax module as the very term Prolog would print; `decode` is
  the converse — `read_term`, then `Transport.v`'s [decode_module]
  into Syntax, then the demand that re-encoding that module
  reproduces the input words on the core sections and NAMES.

Syntax.v is deliberately **not** the whole IR: it is the core subset
of checked filc IR that the model gives a semantics to — the integer
and pointer classes, the float classes with their conversions, checks
and their reuse forms, the raw accesses, `flight`, poll edges, calls,
named locals, variadics. Vectors, `cas` and atomics, `setjmp`,
`asm_fixed` and plain mode are outside it. A function outside the
subset does not fail to cross: it becomes `IOutside name term`,
keeping its address and its whole term but no body, and since
[enc_item] writes an [IOutside] back as that stored term, such a
function still encodes into NFB and decodes back into the same
[IOutside]. The boundary of the *model* and the boundary of the
*format* are different boundaries, and NFB's is the wider one.

Three practical differences between the two encoders, all recorded in
the RFC's implementation notes:

- **Context.** A Syntax module has no `context` item, so the
  Gallina encoder writes no CONTEXT (and its word comparison sets
  CONTEXT aside). The byte-agreement gate therefore uses
  `nanofil nfb-terms`, which has Prolog write each module without its
  context items and with NAMES only.
- **Strings.** Prolog's STRINGS are UTF-8 and its reader rejects
  bytes that are not; Gallina keeps a string's bytes as they are.
- **Names on decode.** Both sides invent integer names from ids when
  NAMES is absent, and both restore the original names when it is
  present — NAMES is included in the Gallina comparison too.

**Agreement is tested, not assumed.** `tests/nfb.sh` round-trips
every module of the corpus (unchecked and checked, with and without
`-O`): with NAMES the reading is the very term; without, the same
core words. `rocq/backend/tests/nfb.sh` holds the Gallina side to the
same bytes on the same corpus, NAMES included, and its reader to the
same module — the same byte-identity standard the backend campaign
already uses for emitted assembly. Neither gate is a proof; they are
wide, cheap nets over every construct the corpus exercises.

**Where the proofs stand.** The RFC asks for three theorems, in this
order of use: round trip (`decode (encode m)` is `m` up to names),
canonical form (anything `decode` accepts is exactly `encode` of
what it returns, on the core sections), and totality with a bound
(`decode` terminates on every word list, rejecting the malformed).
As the RFC's implementation note records, the Gallina `decode`
accepts words only when re-encoding its result reproduces them,
which makes canonical form the cheap direction: it is stated and
proved as [decode_canonical] (with [decode_identity], the soundness
of the module id) in `NfbProof.v`, and totality as the fuel lemmas of
`NfbTotal.v` — every fuel-taking reader is given its input's length,
and each lemma shows more fuel gives the same answer because every
round consumes a word. **The full round-trip theorem is proved as well**:
[round_trip] in `NfbProof.v` gives
`decode (encode m) = Some m`, NAMES included, for every module
[decode_module] gives, from the term reader's half,
[read_encode_term], and Transport's, [decode_enc_module], which rest
on the field-level lemmas (a signed 64-bit or 96-bit integer, an
inline constant and an enumeration code each read back as written).
Beside it stands the empirical statement "the two implementations
produce identical bytes on the whole corpus, and the Gallina reader
accepts only canonical bytes". On trust, the same applies as in §8: passing either
reader establishes well-formedness, and a consumer that compiles,
above all one that accepts checked modules from elsewhere, runs the
validator on what it decoded, every time.

And the honest limitation from the RFC, so no one over-reads the
motivation of §9: today's Gallina `decode` still builds Syntax names
and the backend still looks them up in maps. The speed that dense ids
promise arrives only when a consumer works on the ids directly — as
an id-indexed form proved to correspond to the Syntax module — and
whether that is a second inductive or a change to Syntax.v is a
decision the format leaves open. NFB makes that consumer possible;
it does not yet contain it.

## 13. A reading map and a cheat sheet

If you read one thing per layer, read: the header comment of
[ir.pl](../src/ir.pl) for the grammar as the code states it,
[guide.md](guide.md) §8–§9 for pizlonation and the validator on a
real function, [pizlonation.md](pizlonation.md) for the checked
stage's contract, [nfb.md](nfb.md) for the format's decisions and its
appendix of assigned numbers, and the `nfb_form/3` table in
[nfb.pl](../src/nfb.pl) when a layout in this guide looks wrong —
the table is right and the prose is a summary.

| Question | Answer lives in |
|---|---|
| What terms exist, and what may each op return/read? | `ir:op_result_ok/3`, `ir:op_arg_classes/4`, ir.pl's header |
| Is this module valid, and if not, why not? | `ir:valid_module/1`; `nanofil check FILE` |
| Which stage and mode is this module? | `ir:module_stage/2`, `ir:module_mode/2` — read off the vocabulary, never stored |
| Why is this raw access allowed? | its proof's `check`, §7.2's rules, `ir:checked_insts/5` |
| What bytes is this module? | `nfb:module_nfb/2`; `nanofil encode FILE OUT` |
| Are these bytes *that* module, canonically? | the reader re-encodes and compares (§10.3); `nanofil nfb-check FILE` |
| What do the Gallina types mean? | Syntax.v's header table, one constructor per IR functor |
| What is proved about the bytes? | canonical form, totality and the round trip (§12) |
| Is a validated checked module memory-safe? | [valid_no_unchecked], for the core subset, under the runtime axioms (§8) |

The short version of the whole guide: the IR makes every fact a
consumer needs — classes, checks, proofs, capabilities' sources,
pointer protocols, safepoints — explicit as terms, and lets one
validator decide whether the facts suffice; NFB then writes those
same terms as words, positionally numbered and canonically ordered,
so that other implementations, including a proved one, can read
exactly the module the terms describe and no other.
