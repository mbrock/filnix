# The campaign: nanofil as a specification that compiles programs

This is the compass for the refactoring campaign. Read it before
changing how nanofil is factored, and update its roadmap when a step
lands or the plan changes. [factorings.md](factorings.md) is the log of
what has been done and why; this file is where we are going.

## The ambition

nanofil should read like the standards it implements. A clause of
`c_types.pl` should be recognizable as a paragraph of C11, a clause of
`ir.pl` as a sentence about the IR, a clause of `filc_amd64.pl` as a
fact about the Fil-C ABI. Each fact is stated once, as a relation, and
everything that needs it reads it. When that holds, the compiler is
short because nothing is said twice, trustworthy because there is no
second copy to drift, and delightful because you can learn memory-safe
C by reading it. Some relations can even run backwards, generating the
programs they describe.

The model is Markus Triska's [The Power of Prolog](https://www.metalevel.at/prolog):
clean representations with cases told apart by their principal functor,
case analysis in clause heads, one description read in several
directions, and relations that describe what holds rather than
procedures that compute it. AGENTS.md's "Purity where it pays" records
where we deliberately stop short (`#=` and `if_/3` on ground compiler
data).

## How we work

- **Behaviour-preserving by default.** A refactoring keeps the IR
  byte-identical on the snapshot: `tests/snapshot.sh` compares the
  working tree with a revision over every test and corpus input.
- **Every behaviour change has a fail-first test.** When merging two
  copies of a rule changes what nanofil accepts or computes, compare
  with clang, add a test that fails before the change and passes after,
  and say so in the commit.
- **Both hosts.** Code runs on SWI-Prolog and Trealla; watch Trealla's
  memory on c-testsuite 00040 and 00200 for changes to the frontend.
- **Measure the claim.** Report line counts honestly. "One home per
  rule" is a gain; "shorter" must be shown with `git diff --stat`.
- **Coordinate.** Shared files (`c_lower.pl`, `filc_amd64.pl`, `ir.pl`,
  `interp.pl`) may have other owners; see AGENTS.md.

## Where we stand (October 2026)

Rounds 1 and 2 are logged in factorings.md. An outside review in
October 2026 found:

- **Succeeding:** each C typing rule now has one home in `c_types.pl`
  as a short case analysis citing its paragraph (`castable/2`,
  `assignable/3`, `arms_type/5`, `composite_type/3`,
  `binary_operands/6`, `unary_operand/3`, `expression_category/3`,
  `modifiable_lvalue/2`). Merging the copies closed about 15 gaps
  against clang, each with a test.
- **Not yet shorter:** round 1 was about −80 lines; round 2 was about
  +190 in `src/`.
- **Still two engines:** the judgment (`expression_type/3`) infers
  types but checks little; `c_lower.pl` raises 71 of the frontend's 78
  semantic errors, and asks the judgment about subtrees again (`&`,
  `?:`, null pointer constants, modifiable lvalues), which is quadratic
  on nested `?:`.

The largest redundancy left is that four walks traverse the same C
expression grammar, each with its own idea of types and categories:

| Walk | Where | Lines |
| --- | --- | --- |
| Lowering | `c_lower.pl`: `obj//3`, `rvalue//3`, `decay//3`, `convert//3` | ~380 |
| Judgment | `c_types.pl`: `expression_type/3`, `expression_category/3` | ~120 |
| Integer constants | `c_types.pl`: `const_eval/4`, `kind_binary`, `const_convert/4` | ~150 |
| Address constants | `c_lower.pl`: `addr_const/5`, `lvalue_const/5`, `expr_chunk/7` | ~130 |

Smaller ones: scalar-type facts spread over eight tables (`int_info/3`,
`rank/2`, `unsigned_of/2`, `type_class/2`, `load_op/3`, `store_width/2`,
`narrow_ext/2`, `conversion_int_type/2`); C operators tabled about six
times (`c_parse`, `c_types`, `c_lower`), with punctuators and
identifier characters defined in both `c_lex.pl` and `c_pp.pl`; and the
Fil-C checks, which have no IR form and are stated separately by
`filc_amd64.pl` (emission) and `interp.pl` (semantics).

## The next big intervention: one typed tree

Elaborate each full expression once into a typed tree, and let every
consumer fold over it: IR emission, integer constants and address
constants. That ends the four walks, which is where the lines go.

```prolog
% X     ::= val(Type, Node) | obj(Type, Place) | fun(Type, Designator)
% Place ::= local(Name) | global(Sym) | deref(X) | at(Place, Off)
%         | literal(Lit) | complit(Type, Init)
% Node  ::= int(N) | float(Bits) | conv(Conversion, X) | bin(Op, X, X) | ...
% Conversion ::= load | decay_array | decay_function | int(From, To)
%              | int_float | float_int | ptr_int | int_ptr | bool | void
%              | null_ptr
```

- The category is the principal functor, so consumers dispatch in
  clause heads. Conversions are explicit `conv/2` nodes named after
  C11 6.3; `binary_operands/6`'s converted operand types are exactly
  the conversions to insert.
- `elaborate/4` (E, Env, Loc, X) raises the C diagnostics, keeping the
  current message texts (`tests/reject.sh` matches on them) or changing
  reject tests deliberately.
- `expression_type/3` and `expression_category/3` become projections of
  the tree. `c_lower` loses `decay//3`, `convert//3`'s case analysis,
  `assign_convert//5`, `cond_type//4`, `modifiable//3`, `expr_type//3`
  and most `sema_error` calls; `obj//3` becomes `place//2` and
  `rvalue//3` becomes `value//2`. The estimate is −300 to −400 lines
  net.
- Incremental and byte-identical: introduce a `src(E)` bridge node for
  forms not yet elaborated, which lowering handles the old way; convert
  one form at a time; elaborate once per full expression, never per
  subexpression. Keep literal symbol numbering and the order of fresh
  temporaries as they are today. `#if` elaborates with `Env = pp`.
- Rejected alternative: computing constants by lowering and running
  `interp`. Signed overflow in a constant expression is an error in C
  but wraps in the IR. `interp` is a good test oracle, not the
  implementation.

## Roadmap

Update the status column when a step lands, with its commit.

| # | Step | Verify | Status |
| --- | --- | --- | --- |
| 1 | Commit the snapshot gate, `tests/snapshot.sh`. | Plant a one-token change in `arith_op/3`; the gate fails. | Done: 1006 outputs; the planted change made 6 differ. |
| 2 | One scalar table (`scalar/5` or similar) replacing the eight scalar-fact tables; one C operator table replacing `binop/3`, `assign_op/1`, `binary_kind/2`, `cmp_op/3`, `arith_op/3`, `compound_op/2`; one punctuator and identifier-character definition shared by `c_lex.pl` and `c_pp.pl`. | Snapshot identical; `pptest.sh`; unit tests and Nix checks on both hosts. Expect about −100 lines. | Done, −53 lines: `integer_type/4` and ir's `narrow_type/3`; `c_operator/4` with `compound_assignment/2`; c_lex's `punctuator/1`, `digraph/1` and character classes, shared by c_pp. Not done: `const_arith/4`, `cmp_op/3` and `arith_op/3`, which map C ops to IR ops and belong to step 3. |
| 3 | `elaborate/4` as the judgment: `expression_type/3` and `expression_category/3` become projections, and the elaborator raises diagnostics. | Assert old and new agree on every subexpression the snapshot reaches; snapshot identical; reject tests reject. | |
| 4 | Lower from the tree, form by form, through `src(E)`: literals and conversions (deleting `decay//3`, `assign_convert//5`), then places, then `?:` and assignment, then calls. Delete `obj//3` and `rvalue//3`. | Snapshot identical after every form; Trealla memory on c-testsuite 00040 and 00200. | |
| 5 | Integer and address constants as folds over the tree: `const_eval/4` loses its own typing, `addr_const`/`lvalue_const` fold places to `sym(S, Off)`. | The `#if` cases against `clang -E`, `pptest.sh`, snapshot, `nanofil-zlib`, `nanofil-lua`. Count lines: the −300 should show here. | |

## Visions

Where the campaign leads if it succeeds, to keep the ambition honest:

- **c_types reads as C11 6.3 and 6.5; c_lower is an IR compiler.**
  `elaborate/4` is about 600 lines with each clause group citing its
  paragraph; `c_lower` is about 1,700 lines with no type logic and only
  "unsupported" diagnostics. The C11 tags give an index from clause to
  predicate, and a report of which clauses the corpora exercise.
- **One arithmetic, three readings, cross-checked backwards.** With the
  typing relations table-driven, the elaborator can generate
  well-typed constant expressions over a finite type universe; then
  `const_eval` must equal `interp(lower(E))` must equal clang. That is
  the C-level counterpart of what `gen.py` does for the IR.
- **Fil-C safety as an IR relation.** A pass from IR to IR makes every
  access check explicit, `interp` runs it, and "every access is
  checked" becomes testable; `filc_amd64.pl` shrinks to emission. This
  changes the IR contract, so it needs the orchestrating thread's
  agreement and an Oracle review first.
