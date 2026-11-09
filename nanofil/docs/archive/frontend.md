# The frontend's one typed tree: the record

Archived from [campaign.md](../campaign.md) in November 2026. In October
2026 four walks of the C expression grammar each had their own idea of
types; steps 3 to 5 below made them one elaborated tree that lowering,
integer constants and address constants all read. The work is done and
the code is the reference ([c_types.pl](../../src/c_types.pl),
[c_lower.pl](../../src/c_lower.pl)); this page keeps the review that
started it, the design, and the record of each step.

## Where we stand (October 2026)

Rounds 1 and 2 are logged in [factorings.md](factorings.md). An outside review in
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

When this review was written, four walks traversed the same C
expression grammar, each with its own idea of types and categories
(steps 3 to 5 below made them one tree, read three ways):

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
identifier characters defined in both `c_lex.pl` and `c_pp.pl`. (The
Fil-C checks, stated separately by `filc_amd64.pl` and `interp.pl`, now
have an IR form: [pizlonation.md](../pizlonation.md).)

## Completed frontend design: one typed tree

Steps 3–5 below implemented this design. Its rationale is retained here:
elaborate each full expression once into a typed tree, and let every
consumer fold over it: IR emission, integer constants and address
constants. One description of what each C expression is, read three ways.

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
  `interp`. A constant context must refuse an oversized shift count or
  a zero divisor, where the IR masks the count and traps. (Signed
  overflow is a constraint violation by C11 6.6p4, but `const_eval`
  wraps it as clang's default folding does; see [ub.md](../ub.md).)
  `interp` is a good test oracle, not the implementation.

## Frontend roadmap and implementation record

Update the status column when a step lands, with its commit.

| # | Step | Verify | Status |
| --- | --- | --- | --- |
| 1 | Commit the snapshot gate, `tests/snapshot.sh`. | Plant a one-token change in `arith_op/3`; the gate fails. | Done: 1006 outputs; the planted change made 6 differ. |
| 2 | One scalar table (`scalar/5` or similar) replacing the eight scalar-fact tables; one C operator table replacing `binop/3`, `assign_op/1`, `binary_kind/2`, `cmp_op/3`, `arith_op/3`, `compound_op/2`; one punctuator and identifier-character definition shared by `c_lex.pl` and `c_pp.pl`. | Snapshot identical; `pptest.sh`; unit tests and Nix checks on both hosts. Expect about −100 lines. | Done, −53 lines: `integer_type/4` and ir's `narrow_type/3`; `c_operator/4` with `compound_assignment/2`; c_lex's `punctuator/1`, `digraph/1` and character classes, shared by c_pp. Not done: `const_arith/4`, `cmp_op/3` and `arith_op/3`, which map C ops to IR ops and belong to step 3. |
| 3 | `elaborate/4` as the judgment: `expression_type/3` and `expression_category/3` become projections, and the elaborator raises diagnostics. | Assert old and new agree on every subexpression the snapshot reaches; snapshot identical; reject tests reject. | First part done: `elaborate/3` builds the tree, the two old predicates are its projections, and 15,413 queries agreed with the old judgment. Second part done: every operand is elaborated (call arguments, assignment sources, comma left operands, `?:` conditions, `sizeof` operands, `va_arg`'s list), and `src(E)` is gone. No child failed to elaborate on the snapshot or on zlib and Lua. Builtin arguments, statement-expression blocks and compound-literal initializers stay as source. Third part begun: c_lower judges each full expression with `elaborate/4` first, and `fault/4` diagnoses one that cannot be typed with lowering's messages, in its evaluation order. The elaborator now checks the constraints lowering did (modifiable targets, assignment and argument conversions, call arity, scalar conditions and logical operands, `&` of a value), and on the corpora raises 20 diagnoses itself with lowering's texts. It declines only where lowering refuses first something C allows (unsupported types, structs by value, `va_arg`, statement expressions). Remaining for step 4: delete lowering's duplicate checks as each form lowers from the tree. |
| 4 | Lower from the tree, form by form, through `src(E)`: literals and conversions (deleting `decay//3`, `assign_convert//5`), then places, then `?:` and assignment, then calls. Delete `obj//3` and `rvalue//3`. | Snapshot identical after every form. | Done. `rval//3` elaborates, then `lower//3` and `place//3` translate the tree; nothing lowers from source any more, and the source argument is gone. Deleted: `obj//3`, `rvalue//3`, `decay//3`, `expr_type//3`, `lower_call` and the duplicate checks for `?:`, assignment, `++`/`--`, casts and calls. Each node has one clause, with its C11 section: places (identifiers, `__func__`, string literals, compound literals, `*`, `.`) and values (constants, conversions, operators, `&&`/`||`, `?:`, assignment, calls, builtins, casts, `va_arg`, `sizeof`/`alignof`/`offsetof`, statement expressions, members of struct values). A cast, compound literal or `va_arg` keeps its type name in the tree, so lowering reads it again with the VM check. c_types now owns the remaining judgments: `assigned/4` for returns, initializers and builtin arguments, and `unsupported_type/3` for what nanofil refuses, which `fault/4` reports instead of declining (the long double literal's error now has its line). `assign_convert//5` remains as that judgment then `converted//3`, until returns and initializers become tree nodes. |
| 5 | Integer and address constants as folds over the tree: `const_eval/4` loses its own typing, `addr_const`/`lvalue_const` fold places to `sym(S, Off)`. | The `#if` cases against `clang -E`, `pptest.sh`, snapshot, `nanofil-zlib`, `nanofil-lua`. The four walks should be one. | Done. `const_eval/4` elaborates, then `folded/3` does arithmetic on the tree with the elaborator's conversions (`binary_operands/6` gives a comparison's common type); `kind_binary` lost its typing. `#if` elaborates with `Env = pp`: `env_int_type/3` at constants and int-yielding operators states 6.10.1p4 once, and refuses floating constants there. Null pointer constants are judged on the elaborated tree, not by elaborating the source again. c_lower's `address_constant/5` and `place_constant/5` replace `addr_const/5` and `lvalue_const/5`, one clause per tree node, which closed two gaps against clang, both now in `tests/c/static-array-address.c`: `&x[1][2]` (an array lvalue that decays) and `0 + 0` as a null pointer. Snapshot identical apart from cproc's `initializer-nested-array-address.c`, which now compiles. −16 lines in `src/`. |
