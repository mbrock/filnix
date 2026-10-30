# A guide to nanofil

nanofil is a C compiler written in Prolog. It emits x86-64 assembly for
[Fil-C](https://github.com/pizlonator/fil-c)'s memory-safe ABI, so its
objects link with code clang builds for Fil-C. It is also an executable
account of what that safety consists of: every check Fil-C makes is a
term in nanofil's IR, an interpreter gives the IR a meaning, and one
validator decides whether a module's checks cover its accesses.

This guide follows one small C function from source text to assembly
through every stage, showing what each stage actually produces and which
module and predicate produce it. After the walkthrough come the ideas
you need to keep in mind, a map of the 31 modules, a glossary, recipes
for common changes, and a reading order through the rest of the
documentation. It assumes you know C and some Prolog, and nothing about
Fil-C.

Every output block below is generated. `nanofil/tests/guide.sh`
recomputes each block from nanofil's own commands and from
[tests/guide.pl](../tests/guide.pl), which calls the stage predicates
that have no command of their own. The Nix check fails if any block
differs from what the compiler now produces, so the outputs here are
the current compiler's.

## The pipeline at a glance

```diagram
 C source
    │  c_pp:pp_file/3 ── c_lex           preprocess, lex
    ▼
 tokens   tok(T, File:Line)
    │  c_parse:c_parse/2                 parse
    ▼
 syntax   fundef/4, decl/3, at(Loc, S), bin/3 …
    │  c_lower:c_module/2                lower, asking c_types:elaborate/4
    ▼        for each full expression's typed tree
 unchecked IR   func/5, data/4, context/2 (ir.pl)
    │  ir:valid_module/1                 validate
    │  opt:optimize/3                    -O only: inline, promote, copy,
    ▼                                    simplify, local_storage
 unchecked IR, optimized
    │  pizlonate:pizlonate_module/2      make every check explicit
    ▼
 checked IR   check, raw_load, flight, poll(L) …
    │  check_reuse (--checks)            reuse, renew, guard evidence
    │  ir:valid_module/1                 validate the evidence
    │  filc_abi:lower_function/5         frames, roots, calls, entries
    │  filc_amd64                        emit; frame_slots places slots
    │  amd64_regs + amd64_regs_check     -O: register homes, validated
    ▼
 asm.pl line terms ── asm:print_asm/1 ──▶ GNU as text
```

`nanofil cc` always takes this Fil-C path. IR text read by `nanofil
compile` may instead be in plain mode (no `p`, no external call;
`ir:module_mode/2`, below), and then goes to `amd64:module_asm/2`, the
plain SysV backend. The diagram is the order of the stages, not of the
calls: filc_amd64 drives the last three, fusing each check with its
access before it asks filc_abi for the plan, and amd64_regs runs its
own checker. The interpreter, `interp:run/5`, can run any IR module at any
point on this path. The tests use it as the oracle the native code is
compared with.

## The walkthrough

### Setting up

The commands below run from `nanofil/docs/guide`, with the tools from
[AGENTS.md](../AGENTS.md):

```sh
export SWIPL=/tmp/swipl/bin/swipl FILCC=/tmp/filcc/bin/clang
cd nanofil/docs/guide
../../bin/nanofil cc-ir list.c </dev/null
```

`bin/nanofil` runs [src/main.pl](../src/main.pl) on SWI-Prolog. `FILCC`
names Fil-C's clang. nanofil uses it to learn the target's predefined
macros and include paths and, in the build harnesses, to assemble and
link, but never to compile the program.

### The program

[docs/guide/list.c](guide/list.c) sums a linked list. `sum` has one
load of an `int` and one load of a pointer in a loop, which is enough to
show both kinds of access check, a pointer load's extra work and the
safepoint every loop must have. `three` is there so the interpreter has
something to run at the end.

<!-- guide: source -->
```c
struct node {
    int value;
    struct node *next;
};

int sum(struct node *n) {
    int s = 0;
    while (n) {
        s += n->value;
        n = n->next;
    }
    return s;
}

int three(void) {
    struct node c = {3, 0}, b = {2, &c}, a = {1, &b};
    return sum(&a);
}
```
<!-- /guide -->

### 1. The driver: main.pl

`main/0` reads the options. `-O` selects the middle end, and each of
`--registers`, `--branches`, `--checks`, `--memcpy`, `--inline` and
`--simplify` can be chosen on its own, with defaults that depend on
`-O`. GNU vector types are on by default; `--no-vectors` (or
`--vectors=off`, `NANOFIL_VECTORS=0`) refuses them. It then calls
`command/4`. For `cc FILE` that is:

```prolog
command(Opt, Registers, Checks, [cc, File]) :- !,
    c_file_module(File, Module0, AsmLines),   % frontend, then valid_module/1
    release_stacks,
    once(optimize(Opt, Module0, Module)),     % opt.pl; o0 does nothing
    release_stacks,
    mode_print_asm(filc, Registers, Checks, Module),
    forall(member(Line, AsmLines), format("~w~n", [Line])).
```

`mode_print_asm/4` calls `checked_module/3`, which pizlonates the
module, validates it, and runs the check passes `--checks` selects.
`filc_module_emit/3` then prints the assembly one item at a time. The
other commands (`cc-ir`, `tokens`, `check`, `print`, `compile`,
`run`, `difftest`) stop at an earlier stage or start from IR text. They are
listed at the top of [main.pl](../src/main.pl), the impure driver.
`check FILE` validates hand-edited IR, checked or not, and prints `ok`
or the validator's complaint. It
is a plain file, not a module, so it has no exports.

### 2. Preprocessing and lexing: c_pp.pl, c_lex.pl

`c_pp:pp_profile/2` asks `$FILCC` once for its predefined macros
(`-dM -E`) and its `#include <...>` search path. `c_pp:pp_file/3` then
does all of the preprocessing itself: includes, macros with hide sets,
conditionals (whose `#if` expressions it hands to c_types'
constant-expression evaluator), `#pragma once` and `push_macro`. It
lexes each resulting preprocessing token with c_lex and keeps the
location of the token it came from. The result is a list of
`tok(T, File:Line)`. Line 9, `s += n->value;`, comes out as:

<!-- guide: pp -->
```prolog
tok(id(s),'list.c':9)
tok(p(+=),'list.c':9)
tok(id(n),'list.c':9)
tok(p(->),'list.c':9)
tok(id(value),'list.c':9)
tok(p(;),'list.c':9)
```
<!-- /guide -->

`nanofil tokens FILE` prints the same tokens without their locations.
The token forms are tabled in [c_lex.pl](../src/c_lex.pl)'s header, and
preprocessing tokens and the preprocessor's environment in
[c_pp.pl](../src/c_pp.pl)'s.

### 3. Parsing: c_parse.pl

`c_parse:c_parse/2` is a DCG over the token list that produces a list of
items. Its only semantic state is the set of typedef names in scope,
which C's grammar needs in order to tell declarations from expressions.
Everything else (types, constants, tags) is resolved later. `sum`
parses to:

<!-- guide: parse -->
```prolog
fundef('list.c':6,
       [tspec(int)],
       dcl(some(sum),
           func(base,
                params([ param([su(struct,some(node),none,[])],
                               dcl(some(n),ptr(base,[]),none))
                       ],
                       fixed)),
           none),
       at('list.c':6,
          block([ decl('list.c':7,
                       [tspec(int)],
                       [init(dcl(some(s),base,none),num(0,none-other))]),
                  at('list.c':8,
                     while(id(n),
                           at('list.c':8,
                              block([ at('list.c':9,
                                         expr(assign(+=,
                                                     id(s),
                                                     arrow(id(n),value)))),
                                      at('list.c':10,
                                         expr(assign(=,
                                                     id(n),
                                                     arrow(id(n),next))))
                                    ])))),
                  at('list.c':12,return(id(s)))
                ]))).
```
<!-- /guide -->

Declarators are built around the atom `base`, which stands for the type
the specifiers give: `n`'s `ptr(base, [])` means "pointer to whatever
`struct node` is". Statements are `at(Loc, S)` so that every later stage
knows its line. The full grammar of items, declarators, specifiers,
statements and expressions is in [c_parse.pl](../src/c_parse.pl)'s
header.

### 4. Types and elaboration: c_types.pl

[c_types.pl](../src/c_types.pl) is C's type system as relations:
specifiers and declarators become type terms (`ptr(T)`, `struct(Id)`,
`func(Ret, Params, Arity)`, ...), and from those come sizes, layouts,
the integer conversions and the values of constant expressions. Its
central relation is `elaborate/3`, which reads a C expression in an
environment and gives its *typed tree*. Lowering asks `elaborate/4`
(the same with a location, raising C's diagnostic when the expression
cannot be typed) for each full expression it meets. For the two
assignments in the loop it gives:

<!-- guide: elaborate -->
```prolog
% assign(+=,id(s),arrow(id(n),value))
val(int,
    assign(+=,
           obj(int,id(s)),
           val(int,
               load(obj(int,
                        member(obj(struct(0),
                                   deref(val(ptr(struct(0)),
                                             load(obj(ptr(struct(0)),
                                                      id(n)))))),
                               value)))))).
% assign(=,id(n),arrow(id(n),next))
val(ptr(struct(0)),
    assign(=,
           obj(ptr(struct(0)),id(n)),
           val(ptr(struct(0)),
               load(obj(ptr(struct(0)),
                        member(obj(struct(0),
                                   deref(val(ptr(struct(0)),
                                             load(obj(ptr(struct(0)),
                                                      id(n)))))),
                               next)))))).
```
<!-- /guide -->

The tree states what C leaves implicit. The category is the principal
functor: `val(Type, Node)` for a value, `obj(Type, Place)` for an
lvalue, and `fun` for a function designator. Reading an lvalue is an
explicit `load` node, C11's lvalue conversion (6.3.2.1). `n->value` is
`member(obj(struct(0), deref(...)), value)`, as 6.5.2.3p4 defines `->`.
`struct(0)` is the first struct of the environment's `Defs` table,
whose layout puts `value` at offset 0 and `next` at offset 8.

c_types is the one module documented with `doc/3` facts instead of
comments. Each typing rule cites the paragraph of C11 it implements, and
its examples run as tests ([docs/dterm.md](dterm.md)). The same tree is
folded three ways: lowered to IR by c_lower, evaluated as an integer
constant by `const_eval/4` (also for `#if`), and evaluated as an address
constant for static initializers.

### 5. Lowering: c_lower.pl

`c_lower:c_module/2` turns the items into an IR module. `function/8`
lowers one definition: every named parameter and local variable gets
an `alloc`, hoisted into the entry block, except a variable length
array's, which is allocated where its declaration is reached (C11
6.2.4p7); statements and
expressions become instructions in blocks. The lowering nonterminals
(`stmt//2`, `lower//3` for values, `place//3` for objects) thread one
state term, `st/8`, through a DCG as semicontext; the fields are tabled
in [c_lower.pl](../src/c_lower.pl)'s header. `nanofil cc-ir list.c`
prints the result:

<!-- guide: lower -->
```prolog
func(sum, export, w, [param(p, tmp(v0))], [
    block(start, [], [
        let(tmp(v1), p, alloc(8), [const(8)]),
        let(tmp(v2), p, alloc(4), [const(4)]),
        store(p, tmp(v0), tmp(v1)),
        store(w, const(0), tmp(v2))
    ], goto('L3')),
    block('L3', [], [
        let(tmp(v6), p, load(p), [tmp(v1)]),
        let(tmp(v7), l, ptoi, [tmp(v6)]),
        let(tmp(v8), w, cmp(ne, l), [tmp(v7), const(0)])
    ], branch(tmp(v8), 'L4', 'L5')),
    block('L4', [], [
        let(tmp(v9), w, load(sw), [tmp(v2)]),
        let(tmp(v10), p, load(p), [tmp(v1)]),
        let(tmp(v11), w, load(sw), [tmp(v10)]),
        let(tmp(v12), w, add, [tmp(v9), tmp(v11)]),
        store(w, tmp(v12), tmp(v2)),
        let(tmp(v13), p, load(p), [tmp(v1)]),
        let(tmp(v14), p, add, [tmp(v13), const(8)]),
        let(tmp(v15), p, load(p), [tmp(v14)]),
        store(p, tmp(v15), tmp(v1))
    ], goto('L3')),
    block('L5', [], [
        let(tmp(v16), w, load(sw), [tmp(v2)])
    ], ret(tmp(v16)))
]).
```
<!-- /guide -->

This is nanofil's IR, which [ir.pl](../src/ir.pl) defines. A function is
`func(Name, Linkage, Ret, Params, Blocks)`, and a block is
`block(Label, Phis, Insts, Jump)`. Every value has a class: `w` and
`l` are 32- and 64-bit integers, `s` and `d` floats, and `p` a pointer,
which in Fil-C carries a capability. `v1` is the 8-byte slot of the
parameter `n` and `v2` the 4-byte slot of `s`. `while (n)` became the
loop `L3`/`L4` with exit `L5`. `n->value` is a `load(p)` of `n`'s slot
followed by a `load(sw)` (a signed word) at the pointer read, and
`n->next` is an `add` of 8 and a `load(p)`. In this *unchecked* IR a
`load` at a `p` address means "Fil-C's check, then the access"; no
check is written yet.

`cc-ir` also prints a `context(sum, Records)` item after the function,
left out above. It is explanatory metadata
([provenance.pl](../src/provenance.pl)): which C declaration and which
typed tree node each temporary and instruction came from. Its first
records:

<!-- guide: context -->
```prolog
origin(0,at('list.c',6),statement(function),[])
binding(v1,n,ptr(struct(0)),at('list.c',6))
origin(1,at('list.c',6),statement(block),[0])
origin(2,at('list.c',7),statement(decl),[1])
binding(v2,s,int,at('list.c',7))
origin(3,at('list.c',7),typed(val,int,int(0)),[2])
origin(4,at('list.c',8),statement(while),[1])
origin(5,at('list.c',8),statement(loop),[4])
```
<!-- /guide -->

Passes carry the context along as they rewrite, so the playground can
show source lines beside optimized IR. Context never takes part in
control flow or in the safety argument.

### 6. Validation: ir.pl

`ir:valid_module/1` checks every module the frontend produces against
the IR's grammar: operand and result classes (`op_arg_classes/4`,
`op_result_ok/3`), labels, that each use of a temporary is dominated by
a definition (`definitions_dominate/3`), and, in the checked stage,
the evidence rules of step 9. It throws `nanofil_error(Message)` naming
the first problem. A lowering bug therefore usually stops the compile
with a validator message rather than producing wrong assembly.

### 7. The middle end (-O): opt.pl and its passes

Without `-O`, the IR goes to pizlonation exactly as lowering made it.
That path is the *reference*: the simplest translation, which every
optimization is compared with. With `-O`, `opt:optimize/3` runs a fixed
sequence of passes, each an ordinary relation from module to module:

| Pass | Module | Does |
|---|---|---|
| inline | [inline.pl](../src/inline.pl) | inlines small `local` leaf functions (`sum` is exported, so it stays a call in `three`), in two rounds, the second with simplified callees (`inline_simplified`) |
| promote | [promote.pl](../src/promote.pl) | turns allocs whose address never escapes ([escape.pl](../src/escape.pl)) into SSA temporaries with phis |
| copy | [copy.pl](../src/copy.pl) | removes copies and trivial phis |
| simplify | [simplify.pl](../src/simplify.pl) | folds constants and branches, removes dead code, merges blocks, strength-reduces multiplies, divides and remainders by 2^k, and reuses pure values computed in dominating blocks |
| local_storage | [local_storage.pl](../src/local_storage.pl) | turns remaining non-escaping allocs into named locals with fixed-offset accesses |

After promotion alone, `n` and `s` are phis named `pr.1` and `pr.2`, and
every load and store of their slots is a copy:

<!-- guide: promote -->
```prolog
func(sum, export, w, [param(p, tmp(v0))], [
    block(start, [], [], goto('L3')),
    block('L3', [
        phi(tmp('pr.2'), w, ['L4'-tmp(v12), start-const(0)]),
        phi(tmp('pr.1'), p, ['L4'-tmp(v15), start-tmp(v0)])
    ], [
        let(tmp(v6), p, copy, [tmp('pr.1')]),
        let(tmp(v7), l, ptoi, [tmp(v6)]),
        let(tmp(v8), w, cmp(ne, l), [tmp(v7), const(0)])
    ], branch(tmp(v8), 'L4', 'L5')),
    block('L4', [], [
        let(tmp(v9), w, copy, [tmp('pr.2')]),
        let(tmp(v10), p, copy, [tmp('pr.1')]),
        let(tmp(v11), w, load(sw), [tmp(v10)]),
        let(tmp(v12), w, add, [tmp(v9), tmp(v11)]),
        let(tmp(v13), p, copy, [tmp('pr.1')]),
        let(tmp(v14), p, add, [tmp(v13), const(8)]),
        let(tmp(v15), p, load(p), [tmp(v14)])
    ], goto('L3')),
    block('L5', [], [
        let(tmp(v16), w, copy, [tmp('pr.2')])
    ], ret(tmp(v16)))
]).
```
<!-- /guide -->

After all the passes (`nanofil -O cc-ir list.c`), the copies are gone:

<!-- guide: optimized -->
```prolog
func(sum, export, w, [param(p, tmp(v0))], [
    block(start, [], [], goto('L3')),
    block('L3', [
        phi(tmp('pr.2'), w, ['L4'-tmp(v12), start-const(0)]),
        phi(tmp('pr.1'), p, ['L4'-tmp(v15), start-tmp(v0)])
    ], [
        let(tmp(v7), l, ptoi, [tmp('pr.1')]),
        let(tmp(v8), w, cmp(ne, l), [tmp(v7), const(0)])
    ], branch(tmp(v8), 'L4', 'L5')),
    block('L4', [], [
        let(tmp(v11), w, load(sw), [tmp('pr.1')]),
        let(tmp(v12), w, add, [tmp('pr.2'), tmp(v11)]),
        let(tmp(v14), p, add, [tmp('pr.1'), const(8)]),
        let(tmp(v15), p, load(p), [tmp(v14)])
    ], goto('L3')),
    block('L5', [], [], ret(tmp('pr.2')))
]).
```
<!-- /guide -->

The middle end is not re-proved on each compile. Its passes keep to
rules their headers state (promote only takes allocs whose every access
is in bounds, and simplify only rewrites pure operations, never a load,
store, call or trap), and the tests validate them by translation:
`nanofil -O difftest` runs every test input on the original and the
optimized module in the interpreter and requires each optimized outcome
to refine the original one (`opt:refines/2`). The playground shows each
pass's real output. [docs/m5.md](m5.md) describes the passes and their
validation.

### 8. Pizlonation: pizlonate.pl

`pizlonate:pizlonate_module/2`, named after Fil-C's LLVM pass
FilPizlonator, writes out the checks that unchecked IR leaves implicit.
Each access becomes a check, whose result of class `a` is a *proven
address*, followed by a raw access that reads it. Pointer arithmetic
becomes `flight`, which states where the address and the capability
each come from. Every edge back to an earlier block gets a pollcheck.
`sum` after `-O`:

<!-- guide: checked -->
```prolog
func(sum, export, w, [param(p, tmp(v0))], [
    block(start, [], [], goto('L3')),
    block('L3', [
        phi(tmp('pr.2'), w, ['L4'-tmp(v12), start-const(0)]),
        phi(tmp('pr.1'), p, ['L4'-tmp(v15), start-tmp(v0)])
    ], [
        let(tmp(v7), l, ptoi, [tmp('pr.1')]),
        let(tmp(v8), w, cmp(ne, l), [tmp(v7), const(0)])
    ], branch(tmp(v8), 'L4', 'L5')),
    block('L4', [], [
        let(tmp(chk0), a, check(0, 4, read, 1), [tmp('pr.1')]),
        let(tmp(v11), w, raw_load(sw, 0), [tmp(chk0)]),
        let(tmp(v12), w, add, [tmp('pr.2'), tmp(v11)]),
        flight(tmp(v14), add, [address(tmp('pr.1')), const(8)], lower(tmp('pr.1'))),
        let(tmp(chk1), a, check(0, 8, read, 8), [tmp(v14)]),
        let(tmp(v15), p, raw_load_pointer(0, [aux_read, lower_resolve, address_read]), [tmp(chk1)])
    ], goto(poll('L3'))),
    block('L5', [], [], ret(tmp('pr.2')))
]).
```
<!-- /guide -->

- `check(0, 4, read, 1)` traps unless `pr.1`'s capability allows
  reading bytes [0, 4) at it. Its proof `chk0` is the only thing the
  `raw_load(sw, 0)` after it may read. Like filcc
  (`needToCheckAlignment`), nanofil checks alignment for pointer slots,
  atomics and vectors (`access/4` at the least of the ABI alignment,
  the access size and 8), and checks plain integer and float scalars at
  alignment 1, as here (`ir:access_size_align/3`).
- `flight(tmp(v14), add, [address(tmp('pr.1')), const(8)], lower(tmp('pr.1')))`
  is `&n->next`: its address is `pr.1`'s plus 8, and its capability
  ("lower") is `pr.1`'s. Pizlonation states both; the backend emits
  them and infers neither.
- The pointer load reads an 8-aligned slot (`check(0, 8, read, 8)`), and
  its effect list `[aux_read, lower_resolve, address_read]` spells out
  how Fil-C finds a pointer's capability in memory: in the object's aux
  array, not beside the address (`ir:pointer_memory_effects/2`).
- `goto(poll('L3'))` is a pollcheck on the back edge: a safepoint where
  the thread answers the collector. Every cycle of a checked function
  must contain one.

Pizlonation is deliberately naive: one check right before each access
(a vector's `access/4` becomes one full-width check and a `touch` before
its chunks), and a poll on every backward edge.
[docs/pizlonation.md](pizlonation.md) is the contract.

### 9. Check evidence and the validator: check_reuse.pl, ir.pl

After pizlonation, `--checks` selects how much of that naivety to undo
(`checks_module/3` in main.pl; [docs/m7.md](m7.md)):

| `--checks=` | Does | Default |
|---|---|---|
| `reference` | every check stays | without `-O` |
| `reuse` | deletes a check whose access an earlier, still-valid heap check already covers | |
| `renew` | reuse, then replaces a check dominated by an earlier check of the same pointer with a `renew` that tests only the free and read-only flags | with `-O` |
| `guard` | renew, then puts a `span_test` before a loop and turns its checks into `renew_if` | |

Each pass's result must pass its `*_refines/2` check, which confirms
that only checks changed. Then `valid_module/1` checks the evidence
again with its own rule, without trusting the pass. In `sum`, renewal
finds nothing to do: each iteration checks a different `n`, and the two
checks in a block cover disjoint bytes.

<!-- guide: renew -->
```prolog
% unchanged
```
<!-- /guide -->

The validator's rule is the centre of nanofil's safety argument. In a
checked function (`ir:stage_func/5`, `ir:checked_insts/5`), every raw
access must read a proof that covers its bytes, alignment and rights,
and that proof must still be valid: no instruction between them may
free memory or reach a safepoint (`evidence_preserving/1`). Evidence
crosses a block edge only if every incoming edge carries it; a poll
edge carries none, and neither does an edge from a block not yet
processed in block order (`checked_block/6`). Only heap checks make
live evidence; `check_local` proves its access and nothing after it.
Weaken one check of `sum` so it covers 2 bytes instead of 4, and the
validator refuses the module:

<!-- guide: mutant -->
```prolog
% let(tmp(chk0),a,check(0,2,read,1),[tmp('pr.1')])
in sum: check tmp(chk0) is not followed by an access it covers
```
<!-- /guide -->

Deleting the check instead fails earlier: the load then reads an
undefined temporary, and reading the pointer `pr.1` itself is a class
error (`p` used as `a`). `nanofil check FILE` reports either on
hand-edited IR.

Whatever produced the checked IR (pizlonation, the check passes, or a
future proof search), it is accepted only if this rule accepts it. What
that does and does not establish is in
[Ideas to hold](#checks-proofs-and-one-validator).

### 10. ABI lowering: filc_abi.pl

`filc_abi:lower_function/5` turns a checked function into a plan for
the Fil-C calling convention before any instruction is chosen: the
frame's slots and GC roots, the entry and exit actions, each call's
word layout, and the function object and origins the runtime reads.
The plan below is the `-O` module's: `pr.1` and `pr.2` exist only
after promotion, so §11's no-`-O` listing has none.
For `sum`, the frame and entry actions are:

<!-- guide: abi -->
```prolog
frame([ storage(scalar,0),
        storage(scalar,1),
        storage(scalar,2),
        storage(pointer,0),
        storage(pointer,1),
        shadow('pr.1'),
        shadow('pr.2'),
        thread,
        aux
      ],
      [ lower(storage(pointer,0)),
        lower(storage(pointer,1)),
        lower(shadow('pr.1'))
      ],
      [ tmp('pr.1')-storage(pointer,0),
        lower(tmp('pr.1'))-lower(storage(pointer,0)),
        tmp('pr.2')-storage(scalar,0),
        tmp(v0)-storage(pointer,0),
        lower(tmp(v0))-lower(storage(pointer,0)),
        tmp(v11)-storage(scalar,1),
        tmp(v12)-storage(scalar,2),
        tmp(v14)-storage(pointer,1),
        lower(tmp(v14))-lower(storage(pointer,1)),
        tmp(v15)-storage(pointer,0),
        lower(tmp(v15))-lower(storage(pointer,0)),
        tmp(v7)-storage(scalar,1),
        tmp(v8)-storage(scalar,2)
      ]).
[ native_frame(registers),
  stack_check,
  save_thread,
  save_return(registers),
  zero_roots(3),
  push_frame(c),
  receive(registers,[wf(l,tmp(v0)),wf(l,lower(tmp(v0)))]),
  snapshots(
      [],
      [ shadow('pr.1'),
        shadow('pr.2'),
        tmp('pr.1'),
        tmp('pr.2'),
        tmp(v0),
        tmp(v11),
        tmp(v12),
        tmp(v14),
        tmp(v15),
        tmp(v7),
        tmp(v8)
      ])
].
```
<!-- /guide -->

`frame(Plain, Roots, Aliases)`: `Plain` lists the frame's slots, `Roots`
the `lowers[]` entries the collector scans, and `Aliases` which slot
each temporary uses. A `p` temporary takes two words, its address in a
pointer slot and its capability in that slot's `lower(...)` root, so
every live capability is somewhere the GC can see. `zero_roots(3)`
clears the three roots before `push_frame(c)` links the frame into the
thread's frame list. `receive(registers, ...)` takes the parameter `n`
as two words, `wf(l, tmp(v0))` its address and `wf(l, lower(tmp(v0)))`
its lower. A pointer argument to a call is laid out the same way,
`invoke(entry(g, Sig), registers, [wf(l, addr(tmp(P))), wf(l,
lower(tmp(P)))])`; a direct call to a global needs no `check_function`,
only a call through a pointer does. `shadow('pr.1')` is the slot of the
phi `pr.1`'s shadow: each incoming edge first writes every incoming
value to its phi's shadow and then copies the shadows into the phis, a
parallel copy. Temporaries whose live ranges do not overlap share slots
([frame_slots.pl](../src/frame_slots.pl)): `pr.1`, `v0` and `v15` all
use `storage(pointer, 0)`.

### 11. Emission: filc_amd64.pl, asm.pl

[filc_amd64.pl](../src/filc_amd64.pl) places the plan's words in the
frame and selects instructions, producing a list of
[asm.pl](../src/asm.pl) line terms (`ins(mov, q, [...])`, `label(S)`,
directives), which `asm:print_asm/1` prints as AT&T text. Before it
asks filc_abi for the plan, it fuses each check with the access after
it (`fused(Check, Access)`), so the two are emitted together. In the
reference emission (`nanofil cc list.c`, no `-O`), every temporary
lives in a frame slot. Here is the start of block `L4`, reading `s`
from its alloc:

<!-- guide: asm-check -->
```asm
.Lsum.L4:
	movq -48(%rbp), %rax
	movq -88(%rbp), %rcx
	testq %rcx, %rcx
	jz .Lsum..fail.4.0.1
	cmpq %rcx, %rax
	jb .Lsum..fail.4.0.1
	movq -16(%rcx), %rdx
	subq $4, %rdx
	jb .Lsum..fail.4.0.1
	cmpq %rdx, %rax
	ja .Lsum..fail.4.0.1
	movl (%rax), %eax
	movq %rax, -8(%rbp)
```
<!-- /guide -->

The pointer is in `%rax` and its capability (the object's *lower*) in
`%rcx`. A null capability fails, an address below the object fails,
and the upper bound, stored 16 bytes below the lower, must leave room
for 4 bytes. Each failure jumps to a block that calls the runtime's
`filc_optimized_access_check_fail` with a static description of the
check. For a pointer access, the emitted check also tests alignment
(`testb $7, %al`).

### 12. Register homes and their checker: amd64_regs.pl, amd64_regs_check.pl

With `-O`, `--registers=pointers` is the default. The emitter first
produces a stack-homed stream, in which every temporary has a frame
*home*: it has `-O`'s instruction and branch selection and a save slot
per callee-saved register, so it is not the no-`-O` emission of §11
(note the missing borrow test below), though amd64_regs_check calls it
the reference stream. `amd64_regs:regs_asm/6` then proposes a map from homes to
registers: callee-saved `rbx` and `r12`–`r15` for homes live across a
call, and `r10` and `r11` as well for the others. Pointer address words
may get registers, but a lower never does.
`amd64_regs:regs_asm/6` itself calls
`amd64_regs_check:check_regs/5`, which rebuilds the stream the map implies and
checks that every mapped register holds its home's value wherever the
reference could read it. A failed check stops the compile; nanofil never
falls back to unchecked output. A second untrusted step follows the
map: `amd64_regs:operands_rewrite/4` ([docs/perf.md](perf.md) step 3b)
forwards values and lets instructions read and write registers
directly, and `amd64_regs_check:check_operands/4` validates it. The
loop below shows both steps' work: `movq %rbx, %rax` and
`movl (%rax), %r10d` are the rewrite's. Two kinds of function keep the
stack-homed stream: those that call setjmp (`excluded(setjmp)`) and
those whose stream the preflight refuses (`excluded(unsupported)`). A
function with more than 16 scalar homes is lowered twice, and the first
map decides how slots are pooled (`filc_amd64:temps_first/5`). The map
for `sum`, where `allocated(8,2)` means 8 homes mapped and 2
callee-saved registers saved (rbx and r12, as the prologue shows):

<!-- guide: homes -->
```prolog
% allocated(8,2)
home(-8,[w]) -> r12
home(-16,[l]) -> r10
home(-24,[w]) stays in the frame
home(-32,[w]) -> r10
home(-40,[w]) -> r10
home(-72,[a]) -> r11
home(-64,[w]) -> r10
home(-48,[a]) -> rbx
home(-56,[a]) -> r11
root(-168,40): the frame record, never a home
```
<!-- /guide -->

`home(D, Classes)` is the 8-byte frame word at `D(%rbp)` and the classes
of the temporaries that share it (`a` is a pointer's address word). The
frame record at `-168(%rbp)`, which holds `lowers[]`, is a root range,
and the checker refuses any map that would put a home there. The
resulting `-O` assembly begins with the prologue:

<!-- guide: asm-prologue -->
```asm
pizlonatedFIP1066_sum:
	pushq %rbp
	movq %rsp, %rbp
	subq $176, %rsp
	cmpq %rsp, (%rdi)
	jae filc_stack_overflow_failure@PLT
	movq %rbx, -96(%rbp)
	movq %r12, -104(%rbp)
	movq %rdi, -80(%rbp)
	xorl %eax, %eax
	movq %rax, -152(%rbp)
	movq %rax, -144(%rbp)
	movq %rax, -136(%rbp)
	movq 16(%rdi), %rax
	movq %rax, -168(%rbp)
	leaq .Lsum..origin_c(%rip), %rax
	movq %rax, -160(%rbp)
	leaq -168(%rbp), %rax
	movq %rax, 16(%rdi)
	movq %rdx, %rbx
	movq %rcx, -152(%rbp)
.Lsum.start:
```
<!-- /guide -->

The prologue checks for stack overflow against the limit the thread
holds (`cmpq %rsp, (%rdi)`), saves the callee-saved registers the map
uses, zeroes the roots, and pushes the frame record (parent, origin,
`lowers[]`) onto the thread's frame list at `16(%rdi)`. The loop
follows:

<!-- guide: asm-loop -->
```asm
.Lsum.L3:
	movq %rbx, %r10
	movq %rbx, %rax
	cmpq $0, %rbx
	je .Lsum.L5
.Lsum.L4:
	movq %rbx, %rax
	movq -152(%rbp), %rcx
	testq %rcx, %rcx
	jz .Lsum..fail.4.0.1
	cmpq %rcx, %rax
	jb .Lsum..fail.4.0.1
	movq -16(%rcx), %rdx
	subq $4, %rdx
	cmpq %rdx, %rax
	ja .Lsum..fail.4.0.1
	movl (%rax), %r10d
	movl %r12d, %eax
	addl %r10d, %eax
	movq %rax, %r10
	movq %rbx, %rax
	movq -152(%rbp), %rcx
	addq $8, %rax
	movq %rax, %r11
	movq %rcx, -144(%rbp)
	movq %r11, %rax
	testq %rcx, %rcx
	jz .Lsum..fail.8.0.8
	cmpq %rcx, %rax
	jb .Lsum..fail.8.0.8
	movq -16(%rcx), %rdx
	subq $8, %rdx
	cmpq %rdx, %rax
	ja .Lsum..fail.8.0.8
	testb $7, %al
	jnz .Lsum..fail.8.0.8
	movq -8(%rcx), %rdx
	movabsq $281474976710655, %rsi
	andq %rsi, %rdx
	jz .Lsum.L4..3.nolower
	movq %rax, %rsi
	subq %rcx, %rsi
	movq (%rdx,%rsi), %rsi
	testb $1, %sil
	jz .Lsum.L4..3.have
	andq $-2, %rsi
	movq 8(%rsi), %rsi
	jmp .Lsum.L4..3.have
.Lsum.L4..3.nolower:
	xorl %esi, %esi
.Lsum.L4..3.have:
	movq (%rax), %rax
	movq %rsi, %rcx
	movq %rax, %rbx
	movq %rsi, -152(%rbp)
	movl %r10d, %r10d
	movq %rbx, %r11
	movq %rsi, -136(%rbp)
	movq %r10, %r12
	movq -136(%rbp), %rax
	movq %rax, -152(%rbp)
	movq -80(%rbp), %rdi
	testb $14, 8(%rdi)
	jz .Lsum.L4..j.poll
	leaq .Lsum..origin_n(%rip), %rsi
	call filc_pollcheck_slow@PLT
.Lsum.L4..j.poll:
	jmp .Lsum.L3
.Lsum.L5:
```
<!-- /guide -->

`s` stays in `%r12` and `n`'s address in `%rbx`, while `n`'s lower is
reloaded from its frame slot at `-152(%rbp)`, which is a root. The int
load's check is the same as before, without the borrow test, which
checks of at most 16 bytes do not need ([docs/perf.md](perf.md) item
6a). The pointer load reads the aux word at `-8(%rcx)`. If the object
has an aux array, it takes the loaded pointer's lower from the matching
aux slot, unboxing it when the low bit says it is boxed. An object
without aux gives a null lower (the `.nolower` path,
`xorl %esi, %esi`). Then it loads the address. Before the back edge, `testb $14, 8(%rdi)` asks whether
the thread has a pending safepoint request and calls
`filc_pollcheck_slow` if it has.

The rest of the output (not shown) is the function's public face: the
`pizlonated_sum` getter, a generic entry for callers that do not know
its signature, and the function object whose address C code takes.
`1066` in `pizlonatedFIP1066_sum` encodes the signature `int(ptr)`
(`filc_abi:signature/3`).

### 13. Running it: interp.pl

[interp.pl](../src/interp.pl) is the IR's meaning: a relation from a
module, a function, arguments and fuel to an outcome (`ret(V)`,
`trap(Reason)`, `ub(Reason)`, `unchecked(Why)`, ...). Integer arithmetic
is CLP(Z), so arguments may be unknown and the relation can search for
inputs. Memory, capabilities, `free` and Fil-C's traps are modelled
concretely.

<!-- guide: run -->
```text
$ nanofil run list.c three
ret 6
$ nanofil -O run list.c three
ret 6
```
<!-- /guide -->

The tests compare three things on the same inputs: the interpreter, the
native code nanofil emits, and for C files the native code clang emits
(`nanofil difftest`, `tests/difftest.sh`, `tests/progtest.sh`). A raw
access whose proof does not cover it runs to `unchecked(Why)`, an
outcome distinct from both a trap and undefined behaviour, so a missing
check shows up as a mismatch. An `asm_fixed` instruction the
interpreter cannot model stops at `unknown(asm(M, Xs))`, which difftest
reports as not comparable ([docs/asm-fixed.md](asm-fixed.md)).

The interpreter's trap reasons are coarse: past the end, below the
start, freed, and a function object all trap as `out_of_bounds`. So
difftest compares trap kinds, and the exact reason text is compared
natively: progtest against filcc, and
[tests/renew-trap.sh](../tests/renew-trap.sh).

## Ideas to hold

### The IR is the contract

[ir.pl](../src/ir.pl)'s term grammar is what the frontend writes, what
the interpreter runs, what the passes transform and what the backends
compile. Its header is the reference for every term. Three properties
are worth memorising:

- **Ground terms in SSA.** Temporaries are `tmp(Name)` with ground
  names, defined once, each use dominated by a definition. No logic
  variable appears in IR. A module is ordinary data you can print
  (`ir_text.pl`), read back, and compare.
- **Classes.** `w l s d x` are scalars, `p` is a pointer with its
  capability, and the checked stage adds `a` (a proven address) and
  `f` (a proven function). They are never parameters, phis, call
  arguments or stored values. A raw access reads a proof only while its
  evidence is live; a `renew` may also name an earlier dominating
  check's proof, for its bounds only.
- **Mode and stage are read off the vocabulary.** A module is in
  *filc* mode if it uses anything Fil-C-specific (a `p`, a call to an
  external function, ...), otherwise in *plain* mode
  (`ir:module_mode/2`). It is in the *checked* stage if it contains any
  check, raw access, flight or poll edge, otherwise *unchecked*
  (`ir:module_stage/2`). No flag can disagree with the contents.

### Address is not authority

A Fil-C pointer is two words: the address, and a *lower*, the address
of the first byte of the object it may access. The object's header sits
in the 16 bytes below the lower: its upper bound, and a word holding its
flags (freed, read-only, ...) and its aux array. Computing an address
never conjures a capability. `flight` makes the
two sources explicit, and integer-to-pointer conversion gives a null
capability unless the integer is laundered (glossary). In registers,
the pair travels together. In memory, the address is stored in the
object and the lower in the object's aux array, which is why a pointer
load or store has an effect list (`ir:pointer_memory_effects/2`). On
the stack, lowers live in the frame record's `lowers[]`, which the
collector scans. [docs/abi-findings.md](abi-findings.md) records how
each of these was established against the pinned Fil-C.

### Checks, proofs and one validator

Fil-C's safety obligation is that every access is allowed by its
pointer's capability. nanofil separates the *requirement* (this access
needs read rights on these bytes), the *evidence* that discharges it (a
check just before it, or an earlier check that still holds), and the
*implementation* (the instructions the emitter writes for the check).
In checked IR, evidence is structural: a raw access names its proof
temporary, and `valid_module/1` decides whether that proof covers it
and is still valid. Every producer of checked IR, now and in future,
must get its output past that one rule.

Be precise about what this gives. The validator checks each module
against a rule. That the rule is sound (that validated checked IR never
reaches `unchecked` in the interpreter) is an argument made in
[docs/pizlonation.md](pizlonation.md) and [docs/m7.md](m7.md) and
tested by mutation, not a mechanised proof. That the emitted assembly
does what the checked IR says, and that the runtime keeps its side of
the bargain, are separate claims, supported by differential and native
tests. [docs/campaign.md](campaign.md) states these three obligations
and keeps them apart, and the README is careful in the same way.

### Safepoints and GC roots

Fil-C's collector runs concurrently and asks each thread to stop at
*safepoints*: pollchecks, calls, allocations, and a few helpers that
may exit to the runtime. Two rules follow, and nanofil enforces both
structurally:

- **A proof dies at a safepoint.** A call can run code that frees the
  object, and so can a pollcheck, through a deferred signal handler
  (the collector itself never frees a reachable object). So no raw
  access may use a proof across one: the validator ends all live
  evidence at any instruction that is not `evidence_preserving/1`.
  Two forms are exceptions, because they test again what a free
  changes. An object's bounds change only by free, which sets its
  upper to its lower, and the flag test catches that.
  - `renew` names an earlier check's proof for its bounds. The check
    and its pointer have one definition each and dominate the renew,
    the renewed pointer has the same base and offset
    (`same_pointer/3`), and the function has no setjmp. It tests the
    freed and read-only flags again.
  - `renew_if` reads a guard's `span_test` result G instead of live
    evidence. The validator accepts it through `guard_covers/5`
    (single-definition G and P0, and the access inside the span), so
    it holds across the calls and polls in the loop. It tests the
    flags and the alignment, and when G failed it runs the full check
    out of line.
- **Every live capability is a root at every safepoint.** The ABI plan
  gives each live `p` a `lowers[]` entry in the frame record. The
  register checker refuses any home that overlaps the record, so
  registers never hold the only copy of a lower. A function that calls
  `setjmp` keeps the reference emission ([docs/setjmp.md](setjmp.md)).

Every cycle of a checked function must contain a poll edge
(`polls_every_cycle/1`), so a loop cannot keep the collector waiting.

### Plain and -O

Every `-O` choice is independently selectable, and its absence is the
reference path, which is the simplest correct translation:

| Choice | Reference (no `-O`) | `-O` default | How the `-O` choice is checked |
|---|---|---|---|
| middle end | none | inline, promote, copy, simplify, local_storage | interpreter refinement per test input (`difftest -O`); the passes' own preconditions |
| `--checks` | `reference` | `renew` | `*_refines/2` and the validator, on every compile |
| `--registers` | `stack` | `pointers` | `amd64_regs_check`, on every compile |
| `--branches` | `reference` | `selected` | differential and native tests |
| `--memcpy` | `call` | `inline` | differential tests; the inline copy is taken only when the runtime's checks would pass |

`tests/snapshot.sh` compares every output of a change with the previous
revision's, byte for byte, in the reference and in fixed `-O` modes.
A refactoring must leave the snapshot unchanged.

### Trusted and checked

| On every compile | By the tests | Trusted |
|---|---|---|
| IR well-formedness, SSA dominance and class rules (`valid_module/1`) | the frontend against clang on every test and corpus program | the soundness of the validator's evidence rule (argued and reviewed, not mechanised) |
| checked-IR evidence: every raw access covered by a live proof, every cycle polled | the middle end, by interpreter refinement | the emitter's check, pointer-access and call sequences (reviewed against Fil-C's, tested natively and under `FUGC_SCRIBBLE`/`FUGC_VERIFY`) |
| check passes change only checks (`*_refines/2`) | pizlonation, by agreement of unchecked and checked runs in the interpreter | the ABI facts in [docs/abi-findings.md](abi-findings.md) |
| register homes hold their values, and no home overlaps a GC root (`check_regs`, `check_operands`) | the emitted code against the interpreter and clang (difftest, progtest, whole programs) | the root ranges the emitter reports to the register checker |
| | | the emitter's home classes, and that only `%rbp`-relative operands reach a home, so homes and save slots never escape |
| | | amd64_contract's audited instruction effects (a form it does not know fails) |
| | | the Prolog host, the assembler, the linker and the Fil-C runtime |

## The module map

The 31 modules of `nanofil/src`, in pipeline order. Each module's
header is the full statement of what it owns. These paragraphs say
where it sits and what to read next. On the
[Pages site](https://mbrock.github.io/filnix/nanofil/) each module is
drawn as terms, with its predicates' documentation.

### Driver

**[main.pl](../src/main.pl)**: the command line. It parses options,
runs the stages for a command, and prints. It owns the option defaults
(`registers_default/2` and the others), `checked_module/3`, and
difftest's three-way validation (`mode_pizlonation_agrees/5`,
`report_validation/4`). It is the impure driver, a plain file with no
exports. Next: [opt.pl](../src/opt.pl) for the middle end's selection.

### Frontend

**[c_lex.pl](../src/c_lex.pl)**: C tokens. Input is preprocessed text
or single preprocessing tokens; output is `tok(T, File:Line)`. It also
owns the character classes and punctuators c_pp shares, `#pragma pack`,
and C23 keywords. Next: c_pp.

**[c_pp.pl](../src/c_pp.pl)**: the preprocessor. Input is a file and
a target profile; output is c_lex tokens with source locations. It is
self-contained: clang is asked only for the profile (`pp_profile/2`),
never to preprocess. The environment `env/5` holds macros, include
dirs, feature answers and `#pragma once` files. Next: c_parse.

**[c_parse.pl](../src/c_parse.pl)**: the grammar. Input is tokens;
output is items (`decl/3`, `fundef/4`, ...). It tracks typedef names
only. Its header is the reference for the syntax tree. Next: c_types'
`specs_type/4` and `apply_declarator/5`.

**[c_types.pl](../src/c_types.pl)**: C's types and typing rules as
relations, documented by `doc/3` with C11 citations and runnable
examples. It owns type terms, layouts (`type_size_align/4`, `su_layout`),
the environment `e(Ords, Tags, Defs, Next)`, the conversions, the
elaborator (`elaborate/3,4`) and constant evaluation (`const_eval/4`,
`pp_value/2`). Invariant: each C rule has one home here, and consumers
read it. Next: c_lower's `lower//3`.

**[c_lower.pl](../src/c_lower.pl)**: lowering to IR, in the style of
cproc. Input is items; output is a filc-mode module with `context/2`
items. Every local lives in an `alloc`. Expressions are lowered from
typed trees (`lower//3`, `place//3`), statements by `stmt//2`, static
initializers by folding trees to data chunks (`address_constant/5`).
It also owns the SysV eightbyte classification of struct arguments and
returns, builtins (`builtin//4`), atomics as cas loops, vectors as
8-byte chunks, laundering, VLAs and cleanup attributes. It is the
largest module; its `%%` sections are the way in. Next: ir.pl for what
it must produce.

### The IR and its meaning

**[ir.pl](../src/ir.pl)**: the IR's grammar and validator. Its header
tables every term; `valid_module/1` checks a module, including the
checked stage's evidence rules (`stage_func/5`, `checked_insts/5`). It
also owns the shared facts other modules read (`op_kind/2`,
`access_size_align/3`, `pointer_memory_effects/2`, `module_mode/2`).
Changing the grammar needs the orchestrating thread's agreement
([AGENTS.md](../AGENTS.md)). Next: interp.pl.

**[interp.pl](../src/interp.pl)**: the IR's semantics, as a relation
that can run with unknown integer inputs (CLP(Z)). It owns the memory
model (regions, explicit free, aux capabilities), Fil-C's trap reasons
and the `unchecked` outcome. Every differential test uses it as the
oracle. Next: [docs/lifetime.md](lifetime.md) for free.

**[ieee.pl](../src/ieee.pl)**: IEEE binary32, binary64 and x87
extended arithmetic on integer bit patterns, for the interpreter and
for constant folding. No host floats. Next: [docs/float.md](float.md).

**[ir_text.pl](../src/ir_text.pl)**: IR as Prolog clauses, read and
printed with a host-independent printer; also `run(Fn, Args)` facts in
test files. Next: tests/fixtures.

**[provenance.pl](../src/provenance.pl)**: the `context/2` records
that explain where IR came from (bindings, typed origins, sites,
aliases), and the helpers passes use to carry them along. Invariant:
context never participates in control flow or safety. Next:
promote's `promote_context/5` for how a pass maintains it.

### Analyses

**[cfg.pl](../src/cfg.pl)**: control-flow graph, dominators,
dominance frontiers, natural loops and liveness, as functions from IR
to assocs. Every pass that needs them uses this module.

**[cfg_tabled.pl](../src/cfg_tabled.pl)**: the same analyses as tabled
relations, kept to answer PLAN's question about tabling by measurement
([docs/m5.md](m5.md)). No pass uses it.

**[escape.pl](../src/escape.pl)**: which allocs are reached only through
their own address at known offsets (local), for promote and
local_storage.

**[alias.pl](../src/alias.pl)**: each address of a strict SSA function as
base plus constant offset. Its header says explicitly what the facts do
not justify.

### Middle end (-O)

**[opt.pl](../src/opt.pl)**: the pass sequence (`optimization_passes/2`),
one pass at a time for the playground (`optimize_pass/3`), and
`refines/2`, the outcome relation that validates them. Checked modules
pass through untouched.

**[inline.pl](../src/inline.pl)**: inlining of small static leaf
functions, with its eligibility rules tabled in the header.

**[promote.pl](../src/promote.pl)**: memory slots to SSA temporaries
(pruned SSA, phis named `pr.N`), with the exact conditions under which
an alloc is promotable. Also owns `strict_ssa/3`, which the other passes
use as a precondition.

**[copy.pl](../src/copy.pl)**: copy propagation and trivial phi removal.

**[simplify.pl](../src/simplify.pl)**: constant folding, identities,
value numbering, branch folding, dead code and block merging, all on
pure values only. Its rule table is in the header.

**[local_storage.pl](../src/local_storage.pl)**: non-escaping entry
allocs that promotion left become named local objects (`local_alloc`,
`local_load`, `local_store`), whose address is never a value.
Next: [docs/m5.md](m5.md), *Nonescaping local storage*.

### Checked IR

**[pizlonate.pl](../src/pizlonate.pl)**: unchecked to checked IR: one
check per access (a vector's `access/4` becomes a full-width check and
a `touch` before its chunks' own checks), `flight` for pure pointer operations, a poll on every
backward edge. Next: [docs/pizlonation.md](pizlonation.md).

**[check_reuse.pl](../src/check_reuse.pl)**: the evidence passes reuse,
renew and guard, and their `*_refines/2` checks. Next:
[docs/m7.md](m7.md).

### Fil-C backend

**[filc_abi.pl](../src/filc_abi.pl)**: the ABI plan of a checked
function: frame slots and roots, entry and exit actions, call layouts,
fast and generic entries, setjmp snapshots, origins and signatures. It
never inserts instructions. Next: filc_amd64's *Functions* section.

**[frame_slots.pl](../src/frame_slots.pl)**: slot sharing by disjoint
closed live intervals, in pools (pointer, scalar, float, wide).

**[filc_amd64.pl](../src/filc_amd64.pl)**: places the plan and emits
instructions. Its `%%` sections are the map: ABI facts, frame layout,
functions, blocks and jumps, instructions, the fast convention as data,
access checks, function objects, data objects (getters and
relocations), thread-locals, static data. Next:
[docs/m3.md](m3.md), then [docs/abi-findings.md](abi-findings.md).

**[amd64_regs.pl](../src/amd64_regs.pl)**: proposes the register map
for frame homes (greedy colouring weighted by loop depth) and the
operand rewrite. Nothing it decides is trusted.

**[amd64_regs_check.pl](../src/amd64_regs_check.pl)**: translation
validation of the map and of the register operands, per half-register
liveness on the reference stream's CFG. Its header tables the
obligations. Next: [docs/perf.md](perf.md) items 3 and 5.

**[amd64_contract.pl](../src/amd64_contract.pl)**: the audited effects of
each machine instruction form (registers read and written, memory,
flags, control). An unknown form fails, so the checker never guesses.

### Plain backend and assembly

**[amd64.pl](../src/amd64.pl)**: the naive SysV backend for plain-mode
modules (milestone 2), and the scalar instruction selection
(`compute_op//5`, loads, stores, conversions) that filc_amd64 reuses.

**[asm.pl](../src/asm.pl)**: assembly lines as terms and the only AT&T
printer.

### Host support

`src/swi/` maps the Trealla dialect nanofil is written in onto
SWI-Prolog (`compat.pl`) and supplies the small libraries
(`dcgs`, `format`, `pio`, `clpz`) under Trealla's names. See
[docs/hosts.md](hosts.md).

## Glossary

**access**: `access(K, Addr, Size, Align)`, a vector's full-width check
with no data movement, before its 8-byte chunks
([docs/vector-access.md](vector-access.md)). Pizlonated, it becomes a
check and a `touch`.

**alloc**: `let(D, p, alloc(Align), [Size])`, a fresh zeroed heap
object. The frontend gives every local one; promote and local_storage
remove most of them under `-O`.

**asm_fixed**: `asm_fixed(M, Ins, Outs)`, an inline asm of one
fixed-register instruction (`cpuid`, `xgetbv`, `rdtsc`, `rdtscp`, or
the operand-free `lfence`, `sfence` and `pause`;
`ir:asm_fixed_regs/3`, [docs/asm-fixed.md](asm-fixed.md)). Other
inline asm is a blank-template barrier (its operands are evaluated,
nothing else), a call to `zsafety_error` where filcc would refuse it
at run time, or refused.

**aux**: an object's auxiliary array, which holds the lowers of the
pointers stored in the object, slot for slot. A pointer store must
*ensure* it exists (may call the runtime); a pointer load reads it. An
entry with its low bit set is boxed, for a pointer accessed atomically,
and the real lower is at box+8.

**cas**: compare-and-exchange, the one atomic read-modify-write IR term;
every other atomic operation is a loop of it.

**check**: `check(Lo, Hi, Rights, Align)`, the checked stage's access
check, producing a proof of class `a`. `check_local` does the same for
a named local, and `check_function` produces a function proof of
class `f`.

**checked / unchecked**: the two IR stages. Unchecked IR implies Fil-C's
checks in every `load` and `store` at a `p` address; checked IR states
them.

**class**: a value's machine type: `w l s d x p`, plus `a` and `f` in
the checked stage.

**context**: a `context(Fn, Records)` item, explanatory provenance
(provenance.pl).

**elaborate**: to read a C expression into its typed tree
(`c_types:elaborate/3`).

**evidence**: whatever discharges an access's requirement. Today, a
check immediately before it, an earlier live heap check under reuse,
or, for `renew`, a dominating check of the same pointer, and for
`renew_if` a guard's span test. `live(Q, P, Lo, Hi, Rights, Align)` is the validator's
fact for it.

**fast / generic convention**: Fil-C's two ways in to a function. The
fast entry takes the arguments in registers when caller and callee
agree on the signature; the generic entry takes them as a buffer in the
thread for any caller. A call through a pointer compares the signature
word at lower+16 with its own and takes the fast entry if they match;
otherwise it marshals the arguments into thread+128 (data) and
thread+384 (lowers) and calls the generic entry, which checks the size.
Functions with over 16 words of arguments and variadic functions are
generic-only.

**flight**: `flight(D, Op, Args, Lower)`, a pointer built from an
address computation and an independently named capability source.

**fuel**: the interpreter's bound on executed blocks; running out gives
`out_of_fuel`, which proves nothing.

**getter**: the function that returns a global's or function's address
with its capability, initializing it on first use. Calling one is a
safepoint.

**guard**: `--checks=guard`, range guards: a `span_test` before a loop
proves its accesses' bounds once, and the loop's checks become
`renew_if`, which tests the flags and alignment when the guard passed
and runs the full check out of line otherwise ([docs/m7.md](m7.md),
round 5).

**home**: an 8-byte frame word that holds a temporary, a phi's shadow
or a pointer's address word in the stack-homed stream amd64_regs
starts from (§12). Scalar homes are `w` or `l` only; float temporaries
are kept out of them. Under `--registers=temps|pointers` a home may be
mapped to a register.

**launder**: give an integer converted back to a pointer the capability
of the pointer it came from, as Fil-C does when its analysis can follow
the integer. nanofil does it where the source is visible in the
expression or in a local variable defined once
(`c_lower:launder_fixpoint/5`, [docs/m4.md](m4.md), *Pointer-as-int
laundering*). Otherwise the pointer gets no capability and
dereferencing it traps.

**lower**: a capability, kept beside the address: the object's lower
bound. The header below it holds the upper bound at lower−16 and the
aux pointer at lower−8, with the object's flags in its top 16 bits.

**mode**: plain or filc (`ir:module_mode/2`).

**origin**: a static record the runtime reads to name a function and
location in a trap or backtrace, and in context records, a typed source
node.

**pizlonate**: to make Fil-C's checks explicit, turning unchecked IR
into checked IR (after FilPizlonator, Fil-C's LLVM pass).

**poll / pollcheck / safepoint**: `poll(L)` is a jump target that runs a
pollcheck before going to L. A pollcheck is a safepoint, a point where
the thread may run signal handlers and answer the collector. Calls,
allocations and some helpers are safepoints too.

**proof**: a temporary of class `a` or `f`, the result of a check.

**raw access**: `raw_load`, `raw_store`, `raw_load_pointer`,
`raw_store_pointer`, `raw_cas` and `raw_call`, which do no checking of
their own and read a proof.

**reference path**: the selection without `-O`, against which every
optimization is compared.

**refines**: `opt:refines/2`, the outcome relation that translation
validation of the middle end uses: undefined behaviour allows anything,
an unknown value allows any consistent one, otherwise the outcomes must
be equal.

**renew**: `renew(Lo, Hi, Rights, Align)`, which reuses an earlier
dominating check's bounds and tests only that the object is not freed
(and, for a write, not read-only) ([docs/m7.md](m7.md), round 4). The
`-O` default.

**renew_if**: `renew_if(Lo, Hi, Rights, Align)`, reading the pointer P
and a guard's `span_test` result G: a `renew` whose bounds come from
the guard (see guard).

**reuse**: `--checks=reuse`, deleting a check whose access an earlier
live proof already covers, so the access reads that proof. It works
across plain edges and for related pointers at a constant offset
([docs/m7.md](m7.md), round 3).

**root**: a frame word the collector scans: an entry of the frame
record's `lowers[]`, a local's stack aux, or a jmpbuf root.

**shadow**: two meanings. In the backends, a phi's shadow slot, which
holds the incoming value during a parallel copy. In c_lower, a
laundering variable's capability shadow, a pointer slot that holds the
capability of the value last stored in the variable.

**snapshot**: `tests/snapshot.sh`, the byte-identity gate across
revisions. Also the copies of every temporary a setjmp function keeps
([docs/setjmp.md](setjmp.md)).

**touch**: `touch(tmp(Q))`, the use of a vector check's proof that
accesses nothing.

**translation validation**: checking a transformation's result rather
than proving the transformation: the register checker, `*_refines/2`,
and the interpreter refinement of `difftest -O`.

**unchecked(Why)**: the interpreter outcome of a raw access its
capability does not allow. Only a broken pass produces it.

## Where to start

**Add a builtin.** Give its result type in `c_types:builtin_type/2`,
with a `doc/3` example if it adds a case, and lower it in a
`c_lower:builtin//4` clause, which receives the source arguments. If it
is a library function under a `__builtin_` name, a `library_proto/3`
fact is enough. Put the `builtin//4` clause before the catch-all that
reports "wrong arguments"; that catch-all is also how a wrong argument
count is refused. If the builtin must work in constant expressions
(array sizes, static initializers), add a `c_types:folded/3` clause.
A new c_types helper that c_lower calls must be exported. Pizlonation
and the validator need nothing as long as the lowering emits existing
IR ops; a builtin that needs a new op is *Add an IR term or op* below.
`__has_builtin` is answered by `$FILCC`'s clang, not nanofil. Add a
function with `// run:` lines to a file in `tests/c` (difftest compares
the interpreter, nanofil and clang, so clang must know the builtin;
otherwise test it in IR or with the interpreter), and a
`tests/c/reject` case if some use must be refused.

**Accept a C construct nanofil refuses.** Find the message in the
source (`sema_error` calls and `fault/4` in c_types). Typing goes in
c_types (the elaborator and its `doc/3` examples), lowering in
c_lower's `lower_node//3` or `stmt_//2`. Check with
`tests/difftest.sh` on a `tests/c` file and with `tests/reject.sh`,
then run the snapshot to see what else changed.

**Fix a miscompile.** Reduce it to a C file with a `// run:` line, and
compare `nanofil run` (the interpreter) on `cc-ir` output with native
output from `tests/difftest.sh`. If the interpreter is already wrong,
the bug is in the frontend; otherwise compare reference and `-O`, then
`--checks=reference`, `--registers=stack` and the other choices one at a
time to find the stage.

**Add an IR term or op.** Agree it with the orchestrating thread first.
Then state it in ir.pl's header and validator, give it a meaning in
interp.pl, and teach the backends, cfg.pl's `inst_uses/2` and
`inst_def/2`, and ir_text if it prints specially. Recent examples with
their reviewed contracts: [docs/asm-fixed.md](asm-fixed.md) and
[docs/vector-access.md](vector-access.md).

**Add a middle-end pass.** Write it as a module-to-module relation on
unchecked IR, add it to `opt:optimization_passes/2` and main.pl's
options, carry contexts along (provenance.pl), and validate it with
`difftest -O` and the unit tests. [docs/m5.md](m5.md) shows how the
existing ones were validated.

**Accept new evidence for an access.** This is a semantic change.
State the obligation, the evidence, the validator rule, the
interpreter's behaviour and the emitter's sequence, and have the
contract reviewed before implementing it ([docs/campaign.md](campaign.md),
AGENTS.md). [docs/m7.md](m7.md) is the worked example, round by round.

**Change instruction selection or the frame.** Start in
filc_amd64's *Instructions* or *Frame layout* section. Anything the
register checker reads must stay in amd64_contract's audited forms.
Prove the change with the snapshot and a native test, and measure with
the benchmark gate in [docs/perf.md](perf.md).

**Learn a fact about Fil-C's ABI.** Look in
[docs/abi-findings.md](abi-findings.md) first, then the pinned source
(`filc-staging-ref-src`, AGENTS.md); record what you verify there.

## Reading on

The other documents were written as the work happened. Some are
reference; others are history whose conclusions have since moved into
code or into the reference documents.

| Document | Kind | Read it for |
|---|---|---|
| [README.md](../README.md) | reference | what nanofil compiles, what it refuses, and its claims, stated carefully |
| [AGENTS.md](../AGENTS.md) | reference | tools, tests, dialect rules and conventions |
| [campaign.md](campaign.md) | reference | the semantic foundation: requirement, evidence and implementation; the three obligations; current priorities |
| [pizlonation.md](pizlonation.md) | reference | the checked stage's contract: proofs, safepoints, flight, pointer effects |
| [m7.md](m7.md) | reference | evidence reuse, renew and guards, round by round, with their reviews |
| [lifetime.md](lifetime.md) | reference | the interpreter's model of free |
| [abi-findings.md](abi-findings.md) | reference | the Fil-C ABI as verified at the pin |
| [setjmp.md](setjmp.md), [float.md](float.md), [asm-fixed.md](asm-fixed.md), [vector-access.md](vector-access.md) | reference | contracts for setjmp, floating point, fixed-register asm and vector checks |
| [ub.md](ub.md) | reference | what Fil-C and nanofil do with C's undefined behaviour |
| [dterm.md](dterm.md) | reference | the Pages renderer and `doc/3` |
| [PLAN.md](../PLAN.md) | both | decisions and rules (reference), milestones (history) |
| [m1.md](m1.md) | history | the IR's origin as a QBE subset; the semantics decisions still hold |
| [m2.md](m2.md), [m3.md](m3.md) | history, partly reference | the plain backend and the first Fil-C lowering; m3 still states the backend's rules |
| [m4.md](m4.md) | history, partly reference | the frontend, construct by construct; search it for a feature |
| [m5.md](m5.md) | history, partly reference | the middle end's passes and their validation |
| [m6.md](m6.md) | history | the retired scalar stack cache |
| [perf.md](perf.md) | history, partly reference | code quality work item by item; the benchmark gate and register modes are current |
| [factorings.md](factorings.md) | history | completed refactorings and what each bought |
| [handoff.md](handoff.md) | history | the original design notes |
| [corpus.md](corpus.md), [survey.md](survey.md), [lua.md](lua.md) | measurement | what compiles, and why the rest does not |
| [arith.md](arith.md) | measurement | constant folding against the IR and clang |
| [hosts.md](hosts.md) | measurement | other Prolog hosts |

A good order for a newcomer: this guide, [campaign.md](campaign.md),
[ir.pl](../src/ir.pl)'s header, [pizlonation.md](pizlonation.md), then
the module headers along the walkthrough, then [m7.md](m7.md) when you
reach evidence.

## Documentation conventions

These keep the modules readable and are checked.

- **A header per module.** Each file in `src/` begins with a
  `/* ... */` comment that says what the module owns, the terms it
  consumes and produces (as tables of term forms), its invariants and
  where it fits. It is written in the little Markdown that dterm renders
  ([docs/dterm.md](dterm.md), *Module headers as prose*): `##`
  headings, pipe tables, `prolog` and `diagram` fences.
- **PlDoc for every export.** Each exported predicate has a signature
  comment with modes and determinism, then its meaning:

  ```prolog
  %! valid_module(+M) is semidet.
  %
  %  M is a well-formed module. ...
  ```

  A module listed in `tests/unit.pl`'s `documented_module/1` (c_types)
  uses `doc/3` facts instead, whose examples are tests. Important
  internal predicates of the large modules have `%!` comments too;
  smaller internal ones have a `%` comment that begins with their head.
- **Sections.** A `%% Title` line starts a section, which dterm draws as
  a heading and lists in the page's navigation.
- **Checks.** [tests/docs.pl](../tests/docs.pl) fails when a module lacks
  a header or an export lacks `%!` or `doc/3`.
  [tests/guide.sh](../tests/guide.sh) `--check` fails when an output in
  this guide differs from what the compiler produces; run it without
  `--check` to update them. Both run in
  `nix build .#checks.x86_64-linux.nanofil`.
