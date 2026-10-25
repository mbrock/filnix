# Toward a shorter, truer nanofil

nanofil exists to say what Fil-C does in a form a person can read in an
afternoon and a machine can run backwards. Every line of it should earn
its place by stating something true about C, about the IR or about the
Fil-C ABI, and it should state that thing once. When a fact appears
twice, the copies drift apart, and a reader has to check that they still
agree. When it appears once, as a relation, it can be read, tested and
queried, and sometimes run in a direction nobody planned.

The model is Markus Triska's [The Power of Prolog](https://www.metalevel.at/prolog).
Its lessons that matter most here:

- **Clean representations.** Every case of a datum is told apart by its
  principal functor, so case analysis lives in clause heads and gets
  first-argument indexing for free.
- **One description, many directions.** A DCG that prints can also parse;
  a relation that checks can also generate.
- **Describe what holds.** Write the conditions under which a relation is
  true, not a procedure that happens to compute it.
- **Reify, then interpret.** Turn a language into terms, then give it one
  interpreter.

nanofil already does most of this: the IR is clean, the interpreter is a
relation, state goes through DCG semicontext. What is left is mostly
knowledge that is written down more than once. This page measures where
the code is and names five factorings that make it shorter by making it
more semantic. It was written in October 2026; line counts will move.

## Where the lines are

`src/` holds about 13,600 lines of Prolog, about 20% of them comments.

| Layer | Files | Lines | Share |
|---|---|---|---|
| C frontend | c_lower 2413, c_pp 1170, c_parse 1031, c_types 846, c_lex 567 | 6027 | 44% |
| Fil-C and amd64 backend | filc_amd64 1929, amd64 504, asm 162 | 2595 | 19% |
| IR, semantics and QBE text | interp 1059, qbe_parse 644, ir 599, qbe_print 185 | 2487 | 18% |
| Middle end | cfg 524, promote 491, cfg_tabled 293, copy 254, escape 228, alias 149, opt 53 | 1992 | 15% |
| Driver | main 531 | 531 | 4% |

The largest predicates by code lines are `stmt_` (102), `statement_body`
(90), `rvalue` (84), `command` (71), `thunk` (64) and `obj` (63).

## Five factorings

### 1. One table of IR operators, read in both directions

The set of operators and their spellings is listed in five places:

- `op_arity/2` and `op_kind/2` in `ir.pl`;
- the `memberchk/2` lists of conditions, extension types and load types
  in `op_name/2` in `qbe_parse.pl`;
- `kind_opname//2` in `qbe_print.pl`;
- the comment grammar at the top of `ir.pl`;
- `cmp_op/3` and `arith_op/3` in `c_lower.pl`.

A single relation such as `op_text(Op, Chars)`, written as a DCG, can
describe both that `cmp(slt, w)` is spelled `"csltw"` and that `"csltw"`
is `cmp(slt, w)`, so the parser and the printer share it. Arity and kind
become columns of the same facts. This touches `ir.pl`, the shared
contract, so it needs the orchestrating thread's agreement first
(AGENTS.md).

### 2. One evaluator for C integer constants

The `#if` evaluator in `c_pp.pl` (`tree_value/2`, `expr_unsigned/2`,
`usual_unsigned/3`, `wrapped/3`, about 110 lines) re-implements part of
`const_eval/4` and `kind_binary/8` in `c_types.pl`. It uses its own tree
(`arith('+', A, B)` rather than `bin(add, A, B)`) and its own
approximation of the conversion rules.

`#if` arithmetic is C constant evaluation in which every value is `long`
or `ulong`. If the `#if` expression parsed into c_parse's expression
terms, `const_eval/4` could evaluate it with one more rule: an identifier
left after macro expansion is 0. C integer arithmetic would then have one
specification.

There is a possible bug here too, not yet confirmed by a run. `c_pp`
deliberately skips the arm of `&&`, `||` and `?:` that is not taken
("inactive arms must not divide by zero"). `const_eval/4` evaluates both
operands before applying the operator, so `int a[1 || 1/0];` is probably
rejected as not constant. A merged evaluator with the lazy rule fixes
both.

### 3. Initializers as a relation from type and initializer to leaves

`init_agg`, `init_slots` and `init_one` in `c_lower.pl` are repeated as
`static_agg`, `static_slots` and `static_one`, as their comment says:
they "follow init_agg, init_slots and init_one". Designators, brace
elision, string expansion, a union's first member and the
excess-initializer errors are each written twice.

The meaning of an initializer is one relation:

```prolog
% type_init_leaves(+Type, +Init, -Leaves): Leaves are the scalar
% assignments at(Offset, ScalarType, Expr) that Init makes to an
% object of Type, later ones overriding earlier ones.
```

A local initializer zeroes the object and stores each leaf; a static one
const-evaluates each leaf into a chunk. That removes about 100 lines and
makes initializer semantics testable on its own, without generating code.
It stays inside `c_lower.pl`, so it is the easiest place to start.

### 4. The Fil-C ABI as named facts

`filc_amd64.pl` writes the ABI inline:

- 27 `format(atom(_), 'pizlonated…', _)` calls build symbol names;
- object flags appear as numbers: `FO+16+36873221949095936` is
  `131 << 48`, next to `(17 + ReadOnly) << 48`;
- thread offsets appear as literals, `mem(128, rbx)` and `mem(384, rbx)`;
- the thunk's register moves are unrolled by hand for each return form.

A few facts make the backend read like
[abi-findings.md](abi-findings.md):

```prolog
abi_symbol(fo(F), Sym).          % pizlonatedFO_F, and so on
object_flag(global, 1).
object_flag(readonly, 2).
thread_field(cc_inline_buffer, 128).
```

A pin change then touches one place. This one is more about clarity than
length.

### 5. Not done: cfg_tabled.pl stays in src

This page first proposed moving it out as a finished experiment. It is
not one: [m5.md](m5.md) keeps it as the declarative specification that
the Nix check holds cfg.pl's functional analyses to, which is the kind
of executable reference this page argues for.

## What happened

All of this landed in October 2026, in this order. Each step left the
output of every test and corpus input byte-identical (cc-ir for 1 to 3,
the assembly for 4) apart from the fixes named below, and passed the
Nix check on both hosts.

- **3, initializers** ([`d7d228e`](https://github.com/mbrock/filnix/commit/d7d228e)).
  `init_leaves/4` relates a type and initializer to `zero`, `val` and
  `expr` leaves; locals store them, statics fold them into chunks, and
  `complete_array/6` takes an unknown length from the same walk. It
  fixed a designator naming a union member other than the first, and
  `int y = {}` in a local.
- **2, constants** ([`b17ca37`](https://github.com/mbrock/filnix/commit/b17ca37)).
  `#if` goes through c_lex, c_parse's `conditional` and `const_eval/4`
  with `Env = pp`; values are integers or `ub`, and `&&`, `||` and `?:`
  do not propagate `ub` from the operand they do not evaluate. It fixed
  `int a[1 || 1/0]` and `#if L'\xff'`. Forty `#if` edge cases agree with
  `clang -E`.
- **1, operators** ([`6eccbae`](https://github.com/mbrock/filnix/commit/6eccbae)).
  `op_text//1` in ir.pl spells every op for the parser and the printer;
  run backwards it enumerates the 56 ops. It turned up a Trealla bug
  (AGENTS.md): parsing an `atom_chars/2` list by backtracking picked the
  wrong op after the interpreter had run, so the parser generates names
  and compares them.
- **4, ABI facts** ([`2d16335`](https://github.com/mbrock/filnix/commit/2d16335)).
  `abi_symbol/3`, `struct_field/3`, `object_flag/2` and
  `aux_pointer_mask/1`, with the function and variadic objects sharing
  their getter and object data.

The four changed `src/` by about −80 lines, not the 400 to 600 estimated
above: the merged code describes its terms in comments, and naming the
ABI adds lines. What they removed is repetition: five lists of
operators, two constant evaluators with different laziness, two
initializer walks, and about 25 inline spellings of the ABI. Two
findings are open: c_lex reads `0b101` as a float, and `#if` errors at
the end of the line have no location.

## C's typing rules, each stated once

The next round moved the C frontend's typing into c_types, one relation
per rule of the standard, which both the type judgment and the lowering
read. Before, `c_lower` found types by lowering expressions into a
discarded state, and checked and converted operands in rules of its own
that `c_types` repeated more loosely.

- **The judgment** ([`3d6bd18`](https://github.com/mbrock/filnix/commit/3d6bd18)).
  `expression_type/3` types every expression form, so `sizeof`,
  `_Generic`, `?:` arms and whole-struct initializer entries read it
  instead of probing the lowering.
- **`?:`** ([`dbc72a4`](https://github.com/mbrock/filnix/commit/dbc72a4),
  [`82f9b8c`](https://github.com/mbrock/filnix/commit/82f9b8c),
  [`f0a3f49`](https://github.com/mbrock/filnix/commit/f0a3f49)).
  `conditional_type/3` with `composite_type/3`, audited against clang
  for all of C11 6.5.15. `compatible_type/2` became "has a composite
  type".
- **Operators** ([`da4188e`](https://github.com/mbrock/filnix/commit/da4188e),
  [`49ec532`](https://github.com/mbrock/filnix/commit/49ec532)).
  `binary_operands/6` and `unary_operand/3` give each operand's
  conversion and the result type; lowering picks the instruction from
  them in one clause.
- **Conversions** ([`674e033`](https://github.com/mbrock/filnix/commit/674e033),
  [`2f3c5e5`](https://github.com/mbrock/filnix/commit/2f3c5e5)).
  `assignable/3` for assignment, arguments, returns and initializers,
  with null pointer constants decided from the source expression, and
  `castable/2` for casts.
- **Value categories** ([`b9f6e30`](https://github.com/mbrock/filnix/commit/b9f6e30),
  [`513a743`](https://github.com/mbrock/filnix/commit/513a743)).
  Struct definitions keep their members' qualified types, and
  `expression_category/3` and `modifiable_lvalue/2` state C11 6.3.2.1.
  Assignment, `++`, `--` and `&` ask them, so lowering's `lv/2` only
  means "lowered to an address".

The IR stayed byte-identical on every snapshot input throughout. What
changed is which programs are accepted: stating each rule once removed
the gaps between the two copies. nanofil now rejects, as clang does,
`int *p = 1`, a pointer passed for an integer, incompatible function
pointers, `sizeof(1.0 % 2)`, `sizeof(!s)`, `sizeof((int)s)`, writes to
`const` objects and members, and `f().a = 1` or `&f().a`. It now
accepts what clang accepts and it refused: a `void` arm of `?:`
(c-testsuite 00213) and a struct cast to its own type. It also types
`?:` pointer arms by composite type and qualifiers. Each of these has
a test that failed before.

## Fil-C's checks, stated once

The access check was emitted by `filc_amd64.pl` inside every load and
store at a p address and given meaning, separately, by `interp.pl`.
Now `pizlonate.pl` states each check as an IR term that yields a proven
address (class `a`), which raw accesses read; `ir.pl` says when a check
covers an access and that every loop polls; the interpreter runs the
checks and reports an access no check covers as `unchecked(Why)`; and
the backend emits the check's sequence from the term. The assembly
stayed byte-identical. Along the way `valid_module` learned that
definitions dominate uses. Design, runtime evidence and review:
[pizlonation.md](pizlonation.md).

## The IR's words

The term names were QBE's mnemonics, shortened further: `ins(t(D), K,
Op, Args)`, `glo(S)`, `blk`, `jnz`, `hlt`. They are now words a reader
of C can guess: `let(tmp(D), K, Op, Args)`, `tmp`, `const`, `global`,
`param`, `block`, `result` (where a call puts its value), `goto`,
`branch`, `unreachable`, and the checked stage's `raw_load` and
`raw_store`. Only the names changed, by name and arity at the reader's
term positions, so `ins/3` (assembly), `t/4` (preprocessing tokens) and
`c/3` (initializers) kept theirs. The classes (`w l p s d a`) and the
op names stay short, and the playground's IR tab explains them. Every
output of the snapshot inputs is the old compiler's, renamed.

## Constants are folds over the typed tree

Integer constant expressions had their own walk over the source
(`const_eval/4`, with `kind_binary` choosing conversions again), and
static address constants another (`addr_const/5`, `lvalue_const/5`),
each with its own idea of types. Now both read the elaborator's tree:
`folded/3` in c_types does the arithmetic with the conversions the tree
already names, and c_lower's `address_constant/5` and
`place_constant/5` fold places to `sym(Symbol, Offset)`, a clause per
node. A `#if` expression is elaborated too: the one fact that
distinguishes it, that every integer type acts as intmax_t (C11
6.10.1p4), is `env_int_type/3` at the elaborator's constants and its
int-yielding operators. The old address walk had no case for an array
lvalue used as a value, so `&x[1][2]` was refused, and it took `0 + 0`
for pointer arithmetic on a null; both now agree with clang, with a
test that failed before.

## Function-target checks join the checked IR

An indirect call's target check now has its own term,
`check_function`, and an ephemeral proof class `f` consumed by
`raw_call`. The validator separates function proofs from memory proofs
and ordinary values; the interpreter shares one target-identity rule
between both stages; AMD64 emission selects the check from the term.
The existing fast/generic dispatch remains separate from target
validity. Fusion retains the original call's liveness interval, roots,
labels and setjmp payloads, so emitted assembly stays byte-identical.

This adds a contract rather than shrinking the backend: pointer pairs,
aux/barrier operations and frame/ABI lowering still need to move before
target emission. PLAN now distinguishes M3's completed runtime tests
from that unfinished architecture. Review, tests and native evidence
are in [pizlonation.md](pizlonation.md); the next responsibilities are
in [campaign.md](campaign.md).

## Address arithmetic and lower propagation are independent operands

Pure pointer construction now has the term `flight(D, Op, Args, Lower)`.
Pizlonation chooses the address calculation and the capability source;
the interpreter reads those choices independently, and AMD64 only emits
them. The backend no longer has a pointer-add rule that inherits a lower
or an integer-to-pointer rule that drops one. This is one instruction,
not separately scheduled components, so the existing rooting and frame
layout stay intact. Getters, pointer memory operations and the ABI are
still opaque and remain the next work.

The increment adds a contract rather than reducing line count. Review
also exposed an existing boundary problem: the unchecked-only middle
end must not process directly supplied checked IR. It now leaves that
input unchanged, including with `-O`. Design and evidence are in
[pizlonation.md](pizlonation.md).

## Where this goes

The direction past these five is the same. Look for anything that is
true in two places and give it one home, written as a relation that can
be read as a sentence about C or Fil-C. Each such change makes nanofil
shorter, and also more of what it is meant to be: a specification that
happens to compile programs, small enough to hold in your head, exact
enough to trust, and pleasant enough that people read it to learn how
memory-safe C works.

The current assessment and the roadmap from here are in
[campaign.md](campaign.md).
