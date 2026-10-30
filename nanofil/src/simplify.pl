/*  A cheap middle end (docs/perf.md item 8), run after copy
    propagation on unchecked IR in strict SSA form: simplify_module/2
    folds constants, simplifies booleans and identities, numbers pure
    values, folds constant branches, removes unreachable blocks and dead
    pure definitions, and merges straight-line blocks. Selected with
    `--simplify=full`.

    ## What it may change

    Only values and control flow that no memory access, call or trap
    observes. Every load, store, call, alloc, division, `va_arg`, cas and
    fence stays, in its order, with its arguments' values: a removed
    or rewritten definition is pure (`pure_op/2`: no memory, no effect,
    no native trap), so no check is added,
    removed or moved, and no trap changes its time or reason. Constant
    operations are evaluated by the interpreter's own `alu/4`, so a
    folded value is the one the IR's semantics gives; one that would be
    undefined (a division by zero) is left alone. Pollchecks are not in
    unchecked IR: pizlonation adds one on every edge to a block at or
    before its source, so every cycle of the result still polls.

    ## Rules

    | Rewrite | When |
    |---|---|
    | `Op(c1, c2)` to its value | integer Op of `w` or `l` constants, its value defined |
    | `x + 0`, `x - 0`, `x | 0`, `x ^ 0`, `x << 0`, `x * 1`, `x & ~0` to `x`; `x * 0`, `x & 0`, `x - x`, `x ^ x` to 0 | integer classes; a shift count is read modulo the width |
    | `x * 2^k` to `x << k`, `x udiv 2^k` to `x >> k`, `x urem 2^k` to `x & (2^k - 1)` | integer classes |
    | a constant first operand of `add`, `mul`, `and`, `or`, `xor` or an integer `cmp` second | the backends encode an immediate second operand |
    | `b != 0`, `b == 1`, `ext(T)` of a boolean `b` (0 or 1) to `b` | the result's class has an equal boolean |
    | `ext(T2)` of a `load(T)` or `ext(T)` value `x` to `x` | every T is a T2, and the result's class is x's |
    | `(a C b) == 0` to `a C' b` | C an integer condition, C' its negation |
    | `branch(b == 0, L1, L2)` to `branch(b, L2, L1)` | b a boolean |
    | a pure operation already computed in a dominating block to that value | same class, operation and operands (commutative operands in either order) |
    | `branch(c, L1, L2)` to `goto` | c constant, or L1 = L2 |

    Then blocks no longer reachable go, with their phi edges; copies and
    trivial phis go (copy.pl), up to three rounds while branches fold;
    pure definitions nobody uses go; a block whose only predecessor
    jumps to it is appended to that predecessor; and an empty block that
    only jumps on, whose predecessors do not already reach its
    successor, is bypassed, its phis moved into the successor's.

    Functions that are not in strict SSA form, and functions that call
    setjmp, are left alone. Source contexts follow: instruction sites
    are re-indexed, sites of removed blocks, instructions and phis go,
    and the values keep their records as history.
*/
:- module(simplify, [simplify_module/2, simplify_context/5]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(ir, [modulus/2, class_bits/2, op_kind/2, op_arg_classes/4,
                   module_mode/2, setjmp_func/1]).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2, dom_children/3, jump_succs/2,
                    edge_label/2, inst_uses/2, jump_uses/2]).
:- use_module(promote, [strict_ssa/3]).
:- use_module(copy, [temp_classes/3, reps_block/4, copied_records/4, copy_reps/4]).
:- use_module(interp, [alu/4]).
:- use_module(provenance, [legacy_context/2, code_items/2, context_index/2,
                           context_records/3, with_context/3, remap_sites/3,
                           emission_sites/7]).

%! simplify_module(+M0, -M) is det.
%
%  M is M0 with each strict SSA function simplified.
simplify_module(M0, module(Items)) :-
    legacy_context(M0, module(Items0)),
    module_mode(module(Items0), Mode),
    code_items(Items0, Code), context_index(Items0, Contexts),
    maplist(simplify_item(Mode, Contexts), Code, Groups), append(Groups, Items).

% The cut leaves no choicepoint per function (promote_item/4).
simplify_item(Mode, All, F0, Items) :-
    F0 = func(Name, _, _, _, _), !, context_records(All, Name, Rs0),
    once(simplify_context(Mode, F0, Rs0, F, Rs)), with_context(F, Rs, Items).
simplify_item(_, _, Item, [Item]).

%! simplify_context(+Mode, +F0, +Records0, -F, -Records) is det.
%
%  F is the function F0 simplified as the header says, and Records its
%  context: sites re-indexed, those of removed blocks, instructions and
%  phis dropped, and removed values kept as history. F0 not in strict
%  SSA form, or calling setjmp, is left alone.
simplify_context(_, F, Rs, F, Rs) :- setjmp_func(F), !.
simplify_context(Mode, F0, Rs0, F, Rs) :-
    (   ssa_cfg(F0, Cfg, Idom)
    ->  F0 = func(_, _, _, Params, Blocks0),
        temp_classes(Params, Blocks0, Classes),
        Cx = cx(Classes, Mode),
        fold_rounds(3, Cx, F0, Cfg, Idom, Rs0, F1, Rs1),
        dead_code(F1, Rs1, F2, Rs2),
        merge_blocks(F2, Rs2, F3, Rs3, Merged),
        (   Merged == true -> trivial_phis(Cx, F3, Rs3, F, Rs)
        ;   F = F3, Rs = Rs3
        )
    ;   F = F0, Rs = Rs0
    ).

ssa_cfg(F, Cfg, Idom) :-
    F = func(_, _, _, _, Blocks),
    func_cfg(Blocks, Cfg), cfg_idoms(Cfg, Idom),
    strict_ssa(F, Cfg, Idom).

% fold_rounds(+N, +Cx, +F0, +Cfg, +Idom, +Rs0, -F, -Rs): fold, remove the
% replaced definitions (copy.pl's substitution) and the unreachable
% blocks; again, up to N rounds, while a branch folded (its successor's
% phis may have become constant). Each rewrite keeps strict SSA, so
% later rounds need not check it again.
fold_rounds(N, Cx, F0, Cfg, Idom, Rs0, F, Rs) :-
    F0 = func(Name, L, R, Ps, Blocks0),
    fold_func(Cx, F0, Cfg, Idom, func(_, _, _, _, Blocks1), Reps, Folded),
    (   empty_assoc(Reps) -> Blocks2 = Blocks1, Rs2 = Rs0
    ;   maplist(reps_block(Reps), Blocks1, Blocks2, Maps), append(Maps, Map),
        copied_records(Reps, Map, Rs0, Rs2)
    ),
    Cfg = cfg(_, Rpo, _, _),
    (   Folded == false, length(Rpo, NR), length(Blocks0, NR)
    ->  F3 = func(Name, L, R, Ps, Blocks2), Rs3 = Rs2
    ;   prune(func(Name, L, R, Ps, Blocks2), Rs2, F2, Rs4),
        trivial_phis(Cx, F2, Rs4, F3, Rs3)
    ),
    (   Folded == true, N > 1
    ->  N1 is N - 1,
        F3 = func(_, _, _, _, Blocks3),
        func_cfg(Blocks3, Cfg3), cfg_idoms(Cfg3, Idom3),
        fold_rounds(N1, Cx, F3, Cfg3, Idom3, Rs3, F, Rs)
    ;   F = F3, Rs = Rs3
    ).

% trivial_phis(+Cx, +F0, +Rs0, -F, -Rs): F is F0 without the phis whose
% operands, other than the phi itself, are one value, which replaces it.
% A pruned edge or a bypassed block leaves these; one pass, following
% replacements by other such phis (copy.pl's copy_reps/4: after pruning
% every phi is reachable, so strict SSA rules out cycles among them).
trivial_phis(Cx, func(N, L, R, Ps, Blocks0), Rs0, func(N, L, R, Ps, Blocks), Rs) :-
    findall(D-V,
            ( member(block(_, Phis, _, _), Blocks0), member(phi(tmp(D), K, Pairs), Phis),
              pairs_values(Pairs, Vs), exclude(==(tmp(D)), Vs, Others),
              sort(Others, [V0]), replacement(Cx, K, V0, V) ),
            Pairs0),
    (   Pairs0 == [] -> Blocks = Blocks0, Rs = Rs0
    ;   list_to_assoc(Pairs0, Direct), empty_assoc(E),
        foldl(copy_reps(Direct), Pairs0, E, Reps),
        maplist(reps_block(Reps), Blocks0, Blocks, Maps), append(Maps, Map),
        copied_records(Reps, Map, Rs0, Rs)
    ).

%% Folding: a walk of the dominator tree
%
% The state st(Reps, Bools, Defs, Out, Folded) is threaded through the
% walk; Avail, the pure values computed in the dominating blocks, is
% passed down only, so it is scoped to the subtree.
%
% | Part | Is |
% |---|---|
% | Reps | assoc Temp -> the value that replaces it (a same-class temp or a w/l constant) |
% | Bools | assoc Temp -> K-Temp pairs equal to it, each 0 or 1 |
% | Defs | assoc Temp -> cmp(Cond, K, A, B) for an integer comparison, not(B) for `B == 0` of a boolean B, or narrow(T) for a load or extension of narrow type T |
% | Out | assoc Label -> the rewritten block |
% | Folded | true once a branch became a goto |

fold_func(Cx, func(N, L, R, Ps, Blocks0), Cfg, Idom, func(N, L, R, Ps, Blocks), Reps, Folded) :-
    Cfg = cfg(Entry, _, _, _),
    dom_children(Cfg, Idom, Kids),
    findall(Lb-B, ( member(B, Blocks0), B = block(Lb, _, _, _) ), Pairs),
    list_to_assoc(Pairs, BlockIndex),
    empty_assoc(E),
    walk(Entry, Kids, BlockIndex, Cx, E, st(E, E, E, E, false), st(Reps, _, _, Out, Folded)),
    maplist(out_block(Out), Blocks0, Blocks).

out_block(Out, B0, B) :-
    B0 = block(L, _, _, _),
    ( get_assoc(L, Out, B1) -> B = B1 ; B = B0 ).

walk(L, Kids, Index, Cx, Avail0, St0, St) :-
    get_assoc(L, Index, block(L, Phis0, Insts0, Jump0)),
    St0 = st(Reps0, Bools0, Defs, Out0, F0),
    foldl(fold_phi(Cx), Phis0, Phis, Reps0-Bools0, Reps1-Bools1),
    fold_insts(Insts0, Insts, L, Cx, Avail0, Avail, st(Reps1, Bools1, Defs, Out0, F0), St1),
    St1 = st(Reps2, Bools2, Defs2, Out1, F1),
    fold_jump(Jump0, Jump, Reps2, Bools2, Defs2, F1, F2),
    put_assoc(L, Out1, block(L, Phis, Insts, Jump), Out2),
    get_assoc(L, Kids, Cs),
    foldl(walk_kid(Kids, Index, Cx, Avail), Cs, st(Reps2, Bools2, Defs2, Out2, F2), St).

walk_kid(Kids, Index, Cx, Avail, L, St0, St) :-
    walk(L, Kids, Index, Cx, Avail, St0, St).

% A phi whose operands, other than itself, are one value is that value;
% its operands from blocks not yet visited are not substituted yet, so
% this is conservative, and copy.pl finds the rest.
fold_phi(Cx, phi(tmp(D), K, Pairs0), phi(tmp(D), K, Pairs), Reps0-Bools0, Reps-Bools) :-
    maplist(subst_pair(Reps0), Pairs0, Pairs),
    pairs_values(Pairs, Vs),
    exclude(==(tmp(D)), Vs, Others), sort(Others, Distinct),
    (   Distinct = [V], replacement(Cx, K, V, R)
    ->  put_assoc(D, Reps0, R, Reps)
    ;   Reps = Reps0
    ),
    (   Others \== [], maplist(boolean(Bools0, K), Others)
    ->  put_assoc(D, Bools0, [K-D], Bools)
    ;   Bools = Bools0
    ).

subst_pair(Reps, P-V0, P-V) :- subst(Reps, V0, V).

subst(Reps, tmp(T), V) :- !, ( get_assoc(T, Reps, V0) -> V = V0 ; V = tmp(T) ).
subst(_, V, V).

% replacement(+Cx, +K, +V, -R): every use of a temp of class K that is
% always V may read R instead: a temp of class K, or a w/l constant.
replacement(cx(Classes, _), K, tmp(S), tmp(S)) :- get_assoc(S, Classes, K).
replacement(_, K, const(N), const(V)) :-
    memberchk(K, [w, l]), modulus(K, M), V is N mod M.

boolean(_, _, const(N)) :- integer(N), memberchk(N, [0, 1]).
boolean(Bools, _, tmp(T)) :- get_assoc(T, Bools, _).

fold_insts([], [], _, _, Avail, Avail, St, St).
fold_insts([I0|Is0], [I|Is], L, Cx, Avail0, Avail, St0, St) :-
    fold_inst(I0, I, L, Cx, Avail0, Avail1, St0, St1),
    fold_insts(Is0, Is, L, Cx, Avail1, Avail, St1, St).

fold_inst(let(tmp(D), K, Op0, Args0), I, L, Cx, Avail0, Avail, St0, St) :- !,
    St0 = st(Reps0, Bools0, Defs0, Out, F),
    maplist(subst(Reps0), Args0, Args1),
    once(simplified(K, Op0, Args1, Cx, Bools0, Defs0, R)),
    (   R = value(V)
    ->  I = let(tmp(D), K, copy, [V]),
        ( replacement(Cx, K, V, Rep) -> put_assoc(D, Reps0, Rep, Reps) ; Reps = Reps0 ),
        ( boolean(Bools0, K, V) -> put_assoc(D, Bools0, [K-D], Bools) ; Bools = Bools0 ),
        Avail = Avail0, Defs = Defs0
    ;   R = op(Op, Args),
        (   numbered(K, Op, Args, L, Key), get_assoc(Key, Avail0, E)
        ->  I = let(tmp(D), K, copy, [tmp(E)]),
            put_assoc(D, Reps0, tmp(E), Reps),
            ( get_assoc(E, Bools0, Eq) -> put_assoc(D, Bools0, [K-D|Eq], Bools) ; Bools = Bools0 ),
            Avail = Avail0, Defs = Defs0
        ;   I = let(tmp(D), K, Op, Args), Reps = Reps0,
            ( numbered(K, Op, Args, L, Key) -> put_assoc(Key, Avail0, D, Avail) ; Avail = Avail0 ),
            facts(D, K, Op, Args, Bools0, Defs0, Bools, Defs)
        )
    ),
    St = st(Reps, Bools, Defs, Out, F).
fold_inst(I0, I, _, _, Avail, Avail, St, St) :-
    St = st(Reps, _, _, _, _),
    inst_subst(I0, Reps, I).

inst_subst(loc(F, L), _, loc(F, L)).
inst_subst(store(W, V0, A0), Reps, store(W, V, A)) :-
    subst(Reps, V0, V), subst(Reps, A0, A).
inst_subst(atomic_store(W, V0, A0), Reps, atomic_store(W, V, A)) :-
    subst(Reps, V0, V), subst(Reps, A0, A).
inst_subst(fence, _, fence).
inst_subst(access(K, A0, S, Al), Reps, access(K, A, S, Al)) :- subst(Reps, A0, A).
inst_subst(asm_fixed(M, Ins0, Outs), Reps, asm_fixed(M, Ins, Outs)) :-
    maplist(subst_pair(Reps), Ins0, Ins).
inst_subst(call(R, F0, Args0), Reps, call(R, F, Args)) :-
    subst(Reps, F0, F), maplist(arg_subst(Reps), Args0, Args).

arg_subst(Reps, arg(K, V0), arg(K, V)) :- subst(Reps, V0, V).

% facts(+D, +K, +Op, +Args, +Bools0, +Defs0, -Bools, -Defs): what the
% kept definition D = Op(Args) tells later rewrites.
facts(D, K, Op, Args, Bools0, Defs0, Bools, Defs) :-
    (   bool_result(K, Op, Args, Bools0, Eq)
    ->  put_assoc(D, Bools0, [K-D|Eq], Bools)
    ;   Bools = Bools0
    ),
    (   Op = cmp(eq, CK), int_class(CK), Args = [tmp(B), const(Z)], zero(CK, Z),
        get_assoc(B, Bools0, _)
    ->  put_assoc(D, Defs0, not(B), Defs)
    ;   Op = cmp(C, CK), int_class(CK), Args = [A, B]
    ->  put_assoc(D, Defs0, cmp(C, CK, A, B), Defs)
    ;   ( Op = load(T) ; Op = ext(T) ), fits(T, T)
    ->  put_assoc(D, Defs0, narrow(T), Defs)
    ;   Defs = Defs0
    ).

% fits(?T, ?T2): every value of the narrow type T is one of T2, so
% extending a T value as T2 gives it back.
fits(ub, ub). fits(ub, uh). fits(ub, uw). fits(ub, sh). fits(ub, sw).
fits(uh, uh). fits(uh, uw). fits(uh, sw).
fits(sb, sb). fits(sb, sh). fits(sb, sw).
fits(sh, sh). fits(sh, sw).
fits(uw, uw). fits(sw, sw).

% bool_result(+K, +Op, +Args, +Bools, -Eq): Op(Args) is 0 or 1; Eq are
% temps equal to it.
bool_result(_, cmp(_, _), _, _, []).
bool_result(_, ext(_), [tmp(B)], Bools, Eq) :- get_assoc(B, Bools, Eq).
bool_result(_, and, [_, const(1)], _, []).
bool_result(_, Op, [X, Y], Bools, []) :-
    memberchk(Op, [and, or, xor]),
    boolean(Bools, _, X), boolean(Bools, _, Y).

int_class(w).
int_class(l).

zero(K, N) :- integer(N), modulus(K, M), N mod M =:= 0.
one(K, N) :- integer(N), modulus(K, M), N mod M =:= 1.

%% Simplification of one operation
%
% simplified(+K, +Op, +Args, +Cx, +Bools, +Defs, -R): R is value(V),
% the operation is V read at class K (a copy), or op(Op1, Args1), an
% equivalent operation. Args have the replacements applied.

simplified(_, copy, [global(G)], _, _, _, op(copy, [global(G)])).
simplified(_, copy, [V], _, _, _, value(V)).
simplified(p, Op, [X, const(N)], _, _, _, value(X)) :-
    memberchk(Op, [add, sub]), zero(l, N).
simplified(K, Op, Args, Cx, _, _, value(const(V))) :-
    int_class(K), foldable(Op), maplist(is_const, Args),
    Cx = cx(_, Mode), op_arg_classes(Op, K, Mode, Classes),
    maplist(arg_number, Classes, Args, Xs),
    alu(Op, K, Xs, val(V)).
simplified(K, Op, [X, Y], Cx, Bools, Defs, R) :-
    int_class(K), commutative(Op), X = const(_), Y \= const(_), !,
    simplified(K, Op, [Y, X], Cx, Bools, Defs, R).
simplified(K, cmp(C, CK), [X, Y], Cx, Bools, Defs, R) :-
    int_class(CK), X = const(_), Y \= const(_), !,
    mirrored(C, C1),
    simplified(K, cmp(C1, CK), [Y, X], Cx, Bools, Defs, R).
simplified(K, Op, Args, Cx, Bools, Defs, R) :-
    int_class(K), identity(Op, K, Args, Cx, Bools, Defs, R), !.
simplified(K, cmp(C, CK), Args, Cx, Bools, Defs, R) :-
    int_class(CK), boolean_cmp(C, CK, K, Args, Cx, Bools, Defs, R), !.
simplified(K, ext(_), [tmp(B)], Cx, Bools, _, value(tmp(E))) :-
    get_assoc(B, Bools, Eq), same_class(Cx, K, Eq, E).
simplified(K, ext(T), [tmp(D)], cx(Classes, _), _, Defs, value(tmp(D))) :-
    get_assoc(D, Defs, narrow(T0)), fits(T0, T), get_assoc(D, Classes, K).
simplified(_, Op, Args, _, _, _, op(Op, Args)).

is_const(const(N)) :- integer(N).

arg_number(K, const(N), X) :- modulus(K, M), X is N mod M.

% Integer operations alu/4 evaluates on integers. Division is among
% them: alu/4 gives ub for a zero divisor or an overflowing quotient,
% and then the operation stays.
foldable(Op) :-
    op_kind(Op, Kind),
    memberchk(Kind, [additive, alu, shift, neg, copy, cmp, ext]),
    ( Op = cmp(_, CK) -> int_class(CK) ; true ).

commutative(add). commutative(mul). commutative(and). commutative(or). commutative(xor).

% mirrored(?C, ?C1): x C y is y C1 x.
mirrored(eq, eq). mirrored(ne, ne).
mirrored(slt, sgt). mirrored(sgt, slt). mirrored(sle, sge). mirrored(sge, sle).
mirrored(ult, ugt). mirrored(ugt, ult). mirrored(ule, uge). mirrored(uge, ule).

% negated(?C, ?C1): not (x C y) is x C1 y, for integers.
negated(eq, ne). negated(ne, eq).
negated(slt, sge). negated(sge, slt). negated(sle, sgt). negated(sgt, sle).
negated(ult, uge). negated(uge, ult). negated(ule, ugt). negated(ugt, ule).

% identity(+Op, +K, +Args, +Cx, +Bools, +Defs, -R): algebraic identities
% of integer operations at class K; a constant operand is second.
identity(Op, K, [X, const(N)], _, _, _, value(X)) :-
    memberchk(Op, [add, sub, or, xor]), zero(K, N).
identity(Op, K, [X, const(N)], _, _, _, value(X)) :-
    memberchk(Op, [shl, shr, sar]), class_bits(K, Bits), N mod Bits =:= 0.
identity(Op, K, [X, const(N)], _, _, _, value(X)) :-
    memberchk(Op, [mul, udiv, div]), one(K, N).
identity(and, K, [X, const(N)], _, _, _, value(X)) :-
    modulus(K, M), N mod M =:= M - 1.
identity(and, _, [X, const(1)], _, Bools, _, value(X)) :-
    boolean(Bools, _, X).
identity(Op, K, [_, const(N)], _, _, _, value(const(0))) :-
    memberchk(Op, [mul, and]), zero(K, N).
identity(Op, _, [tmp(X), tmp(X)], _, _, _, value(const(0))) :-
    memberchk(Op, [sub, xor]).
identity(Op, _, [tmp(X), tmp(X)], _, _, _, value(tmp(X))) :-
    memberchk(Op, [and, or]).
identity(mul, K, [X, const(N)], _, _, _, op(shl, [X, const(S)])) :-
    power_of_two(K, N, S), S > 0.
identity(udiv, K, [X, const(N)], _, _, _, op(shr, [X, const(S)])) :-
    power_of_two(K, N, S), S > 0.
identity(urem, K, [X, const(N)], _, _, _, op(and, [X, const(Mask)])) :-
    power_of_two(K, N, S), S > 0, Mask is (1 << S) - 1.

% power_of_two(+K, +N, -S): N at class K is 2^S.
power_of_two(K, N, S) :-
    modulus(K, M), V is N mod M, V > 0, V /\ (V - 1) =:= 0,
    log2(V, 0, S).

log2(1, S, S) :- !.
log2(V, S0, S) :- V1 is V >> 1, S1 is S0 + 1, log2(V1, S1, S).

% boolean_cmp(+C, +CK, +K, +Args, +Cx, +Bools, +Defs, -R): a comparison
% of a boolean with 0 or 1, or of a value with itself.
boolean_cmp(C, _, _, [tmp(X), tmp(X)], _, _, _, value(const(V))) :-
    ( memberchk(C, [eq, ule, uge, sle, sge]) -> V = 1 ; V = 0 ).
boolean_cmp(ult, CK, _, [_, const(N)], _, _, _, value(const(0))) :- zero(CK, N).
boolean_cmp(uge, CK, _, [_, const(N)], _, _, _, value(const(1))) :- zero(CK, N).
boolean_cmp(C, CK, K, [tmp(B), const(N)], Cx, Bools, Defs, R) :-
    get_assoc(B, Bools, Eq),
    (   C == ne, zero(CK, N) -> Truth = same
    ;   C == eq, one(CK, N) -> Truth = same
    ;   C == eq, zero(CK, N) -> Truth = negated
    ;   C == ne, one(CK, N) -> Truth = negated
    ),
    (   Truth == same
    ->  same_class(Cx, K, [K-B|Eq], E), R = value(tmp(E))
    ;   member(_-E, [K-B|Eq]), get_assoc(E, Defs, cmp(C0, CK0, A0, B0))
    ->  negated(C0, C1), R = op(cmp(C1, CK0), [A0, B0])
    ).

% same_class(+Cx, +K, +Eq, -E): E is a temp of class K among Eq.
same_class(cx(Classes, _), K, Eq, E) :-
    member(_-E, Eq), get_assoc(E, Classes, K), !.

% numbered(+K, +Op, +Args, +L, -Key): Op is pure, and Key identifies its
% value: commutative integer operands in a fixed order. A pointer plus or
% minus a constant (a field's address) is numbered only within its block
% L: recomputing it is one add the backend folds into the access, while
% sharing it down the dominator tree keeps a pointer and its capability
% live across the function. In bzip2's BZ2_decompress that cost 20% more
% cycles for 4% fewer instructions (docs/perf.md, item 8).
numbered(K, Op, Args, L, K-Op-Key) :-
    pure_op(Op, K), Op \== copy,
    (   commutative(Op), int_class(K) -> msort(Args, Key0) ; Key0 = Args ),
    (   K == p, memberchk(const(_), Args) -> Key = Key0-L ; Key = Key0 ).

% removable(+Inst): Inst defines a temp by a pure operation. A copy of a
% symbol in a Fil-C module calls its getter, which stays.
removable(let(tmp(_), K, Op, Args)) :-
    pure_op(Op, K), \+ ( Op == copy, Args = [global(_)] ).

% pure_op(+Op, +K): Op reads no memory, has no effect and does not trap
% natively, so its definition can be removed or shared. (A float_to_int
% whose value is undefined is ub in the interpreter, which refinement
% allows to disappear; Fil-C does not trap there.)
pure_op(Op, _) :-
    op_kind(Op, Kind),
    memberchk(Kind, [additive, shift, neg, copy, ptoi, itop, cmp, ext,
                     float_convert, int_to_float, float_to_int, cast]), !.
pure_op(Op, _) :-
    memberchk(Op, [mul, and, or, xor]).

fold_jump(branch(V0, T1, T2), J, Reps, Bools, Defs, F0, F) :- !,
    subst(Reps, V0, V),
    (   V = const(N)
    ->  ( N mod 4294967296 =\= 0 -> J = goto(T1) ; J = goto(T2) ), F = true
    ;   T1 == T2
    ->  J = goto(T1), F = true
    ;   V = tmp(X), get_assoc(X, Defs, not(B)), get_assoc(B, Bools, _)
    ->  J = branch(tmp(B), T2, T1), F = F0
    ;   J = branch(V, T1, T2), F = F0
    ).
fold_jump(ret(V0), ret(V), Reps, _, _, F, F) :- !, subst(Reps, V0, V).
fold_jump(rets(Vs0), rets(Vs), Reps, _, _, F, F) :- !, maplist(subst(Reps), Vs0, Vs).
fold_jump(J, J, _, _, _, F, F).

%% Unreachable blocks

% prune(+F0, +Rs0, -F, -Rs): F is F0 without its unreachable blocks, and
% each phi without the operands of edges that no longer exist.
prune(func(N, L, R, Ps, Blocks0), Rs0, func(N, L, R, Ps, Blocks), Rs) :-
    func_cfg(Blocks0, cfg(_, Rpo, Succs, _)),
    findall(Lb-true, member(Lb, Rpo), RPairs), list_to_assoc(RPairs, Reach),
    include(reachable(Reach), Blocks0, Kept),
    maplist(live_phi_edges(Reach, Succs), Kept, Blocks),
    (   Blocks0 == Blocks -> Rs = Rs0
    ;   exclude(reachable(Reach), Blocks0, Gone),
        findall(Lb, member(block(Lb, _, _, _), Gone), GoneLabels),
        findall(T, ( member(block(_, Phis, _, _), Gone), member(phi(tmp(T), _, _), Phis) ), GonePhis),
        drop_sites(GoneLabels, GonePhis, Rs0, Rs)
    ).

reachable(Reach, block(L, _, _, _)) :- get_assoc(L, Reach, _).

live_phi_edges(Reach, Succs, block(L, Phis0, Is, J), block(L, Phis, Is, J)) :-
    maplist(live_phi(Reach, Succs, L), Phis0, Phis).

live_phi(Reach, Succs, L, phi(D, K, Pairs0), phi(D, K, Pairs)) :-
    include(live_edge(Reach, Succs, L), Pairs0, Pairs).

live_edge(Reach, Succs, L, P-_) :-
    get_assoc(P, Reach, _), get_assoc(P, Succs, Ss), memberchk(L, Ss).

% drop_sites(+Labels, +Phis, +Rs0, -Rs): Rs is Rs0 without the sites of
% the blocks Labels and the phis Phis.
drop_sites(Labels, Phis, Rs0, Rs) :-
    findall(L-true, member(L, Labels), LP), list_to_assoc(LP, LA),
    findall(T-true, member(T, Phis), TP), list_to_assoc(TP, TA),
    exclude(dropped_site(LA, TA), Rs0, Rs).

dropped_site(LA, _, site(inst(L, _), _)) :- get_assoc(L, LA, _).
dropped_site(LA, _, site(jump(L), _)) :- get_assoc(L, LA, _).
dropped_site(_, TA, site(phi(T), _)) :- get_assoc(T, TA, _).

%% Dead pure definitions

% dead_code(+F0, +Rs0, -F, -Rs): F is F0 without the pure definitions and
% phis whose values nothing that stays uses, transitively.
dead_code(func(N, L, R, Ps, Blocks0), Rs0, func(N, L, R, Ps, Blocks), Rs) :-
    findall(D-Us,
            ( member(block(_, Phis, Insts, _), Blocks0),
              (   member(phi(tmp(D), _, Pairs), Phis), pairs_values(Pairs, Vs),
                  temps_of(Vs, Us)
              ;   member(I, Insts), removable(I), I = let(tmp(D), _, _, _),
                  inst_uses(I, Us)
              ) ),
            PureUses),
    list_to_assoc(PureUses, Pure),
    findall(U,
            ( member(block(_, _, Insts, J), Blocks0),
              (   member(I, Insts), \+ pure_def(Pure, I), inst_uses(I, Us)
              ;   jump_uses(J, Us)
              ),
              member(U, Us) ),
            Roots),
    empty_assoc(E),
    mark(Roots, Pure, E, Live),
    (   forall(gen_assoc(D, Pure, _), get_assoc(D, Live, _))
    ->  Blocks = Blocks0, Rs = Rs0
    ;   maplist(live_block(Pure, Live), Blocks0, Blocks, Maps), append(Maps, Map),
        remap_sites(Rs0, Map, Rs1),
        findall(T, ( member(block(_, Phis, _, _), Blocks0), member(phi(tmp(T), _, _), Phis),
                     \+ get_assoc(T, Live, _) ),
                DeadPhis),
        drop_sites([], DeadPhis, Rs1, Rs)
    ).

pure_def(Pure, let(tmp(D), _, _, _)) :- get_assoc(D, Pure, _).

temps_of(Vs, Ts) :- findall(T, member(tmp(T), Vs), Ts0), sort(Ts0, Ts).

mark([], _, Live, Live).
mark([T|Ts], Pure, Live0, Live) :-
    (   get_assoc(T, Live0, _)
    ->  mark(Ts, Pure, Live0, Live)
    ;   put_assoc(T, Live0, true, Live1),
        (   get_assoc(T, Pure, Us) -> append(Us, Ts, Ts1) ; Ts1 = Ts ),
        mark(Ts1, Pure, Live1, Live)
    ).

live_block(Pure, Live, block(L, Phis0, Insts0, J), block(L, Phis, Insts, J), Map) :-
    exclude(dead_phi(Live), Phis0, Phis),
    live_insts(Insts0, Pure, Live, Insts, L, 0, 0, Map).

dead_phi(Live, phi(tmp(D), _, _)) :- \+ get_assoc(D, Live, _).

live_insts([], _, _, [], _, _, _, []).
live_insts([I|Is0], Pure, Live, Is, L, Old, New, Map) :-
    (   I = let(tmp(D), _, _, _), get_assoc(D, Pure, _), \+ get_assoc(D, Live, _)
    ->  Is = Rest, Out = []
    ;   Is = [I|Rest], Out = [I]
    ),
    emission_sites(L, Old, New, Out, Map, Maps, Next), Old1 is Old + 1,
    live_insts(Is0, Pure, Live, Rest, L, Old1, Next, Maps).

%% Merging blocks
%
% Both rewrites below run over the blocks in order once, with Index
% (assoc Label -> block) and Preds (assoc Label -> the labels of its
% incoming edges, one per jump target) kept current.

% merge_blocks(+F0, +Rs0, -F, -Rs, -Merged): F is F0 with each empty
% block that only jumps on bypassed, then each block whose only
% predecessor ends in a goto to it appended to that predecessor. Merged
% is true if a block went.
merge_blocks(func(N, L, R, Ps, Blocks0), Rs0, func(N, L, R, Ps, Blocks), Rs, Merged) :-
    Blocks0 = [block(Entry, _, _, _)|_],
    findall(Lb-B, ( member(B, Blocks0), B = block(Lb, _, _, _) ), Pairs),
    list_to_assoc(Pairs, Index0),
    pairs_keys(Pairs, Order),
    edge_preds(Blocks0, Preds0),
    use_counts(Blocks0, Uses0),
    empty_assoc(E),
    foldl(bypass(Entry), Order, m(Index0, Preds0, Uses0, [], []), m(Index1, Preds1, _, Bypassed, DeadPhis)),
    foldl(absorb(Entry), Order, a(Index1, Preds1, E, E), a(Index, _, Moves, JumpOf)),
    (   Bypassed == [], empty_assoc(Moves)
    ->  Blocks = Blocks0, Rs = Rs0, Merged = false
    ;   findall(B, ( member(Lb, Order), get_assoc(Lb, Index, B) ), Blocks),
        merged_records(Moves, JumpOf, Bypassed, DeadPhis, Rs0, Rs),
        Merged = true
    ).

edge_preds(Blocks, Preds) :-
    findall(T-From,
            ( member(block(From, _, _, J), Blocks), jump_targets(J, Ts), member(T0, Ts),
              edge_label(T0, T) ),
            Pairs0),
    keysort(Pairs0, Pairs), group_pairs_by_key(Pairs, Groups),
    list_to_assoc(Groups, Preds).

jump_targets(goto(T), [T]).
jump_targets(branch(_, T1, T2), [T1, T2]).
jump_targets(ret(_), []).
jump_targets(ret, []).
jump_targets(rets(_), []).
jump_targets(unreachable, []).

preds_of(Preds, L, Ps) :- ( get_assoc(L, Preds, Ps0) -> Ps = Ps0 ; Ps = [] ).

atom_label(T) :- T \= poll(_).

% use_counts(+Blocks, -Uses): assoc Temp -> how many operands read it.
use_counts(Blocks, Uses) :-
    findall(T,
            ( member(block(_, Phis, Insts, J), Blocks),
              (   member(phi(_, _, Pairs), Phis), member(_-tmp(T), Pairs)
              ;   member(I, Insts), operand_temp(I, T)
              ;   jump_operand(J, T)
              ) ),
            Ts0),
    msort(Ts0, Ts), clumped_pairs(Ts, Counts), list_to_assoc(Counts, Uses).

clumped_pairs([], []).
clumped_pairs([T|Ts], [T-N|Ps]) :- same_run(T, Ts, 1, N, Rest), clumped_pairs(Rest, Ps).
same_run(T, [U|Us], N0, N, Rest) :- U == T, !, N1 is N0 + 1, same_run(T, Us, N1, N, Rest).
same_run(_, Rest, N, N, Rest).

operand_temp(let(_, _, _, Args), T) :- member(tmp(T), Args).
operand_temp(store(_, V, A), T) :- member(tmp(T), [V, A]).
operand_temp(atomic_store(_, V, A), T) :- member(tmp(T), [V, A]).
operand_temp(asm_fixed(_, Ins, _), T) :- member(_-tmp(T), Ins).
operand_temp(access(_, tmp(T), _, _), T).
operand_temp(call(_, F, Args), T) :- ( F = tmp(T) ; member(arg(_, tmp(T)), Args) ).

jump_operand(branch(tmp(T), _, _), T).
jump_operand(ret(tmp(T)), T).
jump_operand(rets(Vs), T) :- member(tmp(T), Vs).

count(Uses, T, N) :- ( get_assoc(T, Uses, N0) -> N = N0 ; N = 0 ).

add_use(D, tmp(T), Uses0, Uses) :- !, count(Uses0, T, N0), N is N0 + D, put_assoc(T, Uses0, N, Uses).
add_use(_, _, Uses, Uses).

% bypass(+Entry, +E, +M0, -M): M is m(Index, Preds, Uses, Bypassed,
% DeadPhis). E, empty, not the entry, ending in goto(T), goes when each
% predecessor P reaches it once, by a plain edge, and does not reach T
% already, and E's phis are read only by T's operands from E. Each P
% then jumps to T, and T's operand from E becomes, for each P, that
% operand with E's phis read as their operands from P: a value read
% there was defined in a block dominating E, so it dominates each P.
bypass(Entry, E, m(Index0, Preds0, Uses0, Gone0, Dead0), M) :-
    (   get_assoc(E, Index0, block(E, EPhis, [], goto(T))),
        E \== Entry, atom_label(T), T \== E,
        preds_of(Preds0, E, EPreds), EPreds \== [],
        sort(EPreds, Distinct), length(EPreds, N), length(Distinct, N),
        \+ memberchk(E, EPreds),
        preds_of(Preds0, T, TPreds),
        \+ ( member(P, EPreds), memberchk(P, TPreds) ),
        forall(member(P, EPreds), plain_edge(Index0, P, E)),
        get_assoc(T, Index0, block(T, TPhis0, TInsts, TJump)),
        small_join(Index0, Preds0, T),
        forall(member(phi(tmp(D), _, _), EPhis),
               ( count(Uses0, D, ND), forwarded_reads(TPhis0, E, D, ND) ))
    ->  findall(D-Pairs, member(phi(tmp(D), _, Pairs), EPhis), PhiPairs),
        list_to_assoc(PhiPairs, EPhiA),
        foldl(bypassed_phi(E, EPreds, EPhiA), TPhis0, TPhis, Uses0, Uses1),
        foldl(dropped_phi_uses, EPhis, Uses1, Uses),
        put_assoc(T, Index0, block(T, TPhis, TInsts, TJump), Index1),
        foldl(retarget(E, T), EPreds, Index1, Index2),
        del_assoc(E, Index2, _, Index),
        exclude(==(E), TPreds, TPreds1), append(TPreds1, EPreds, TPreds2),
        put_assoc(T, Preds0, TPreds2, Preds1), del_assoc(E, Preds1, _, Preds),
        findall(D, member(phi(tmp(D), _, _), EPhis), Ds), append(Ds, Dead0, Dead),
        M = m(Index, Preds, Uses, [E|Gone0], Dead)
    ;   M = m(Index0, Preds0, Uses0, Gone0, Dead0)
    ).

% small_join(+Index, +Preds, +S): S has no phis or at most 64 incoming
% edges. Rewriting a join's phis is linear in its edges, so each block
% merged into a dispatch loop's header would otherwise cost the whole
% header, quadratic over its cases.
small_join(Index, Preds, S) :-
    get_assoc(S, Index, block(S, Phis, _, _)),
    (   Phis == [] -> true
    ;   preds_of(Preds, S, Ps), length(Ps, N), N =< 64
    ).

plain_edge(Index, P, E) :-
    get_assoc(P, Index, block(P, _, _, J)),
    jump_targets(J, Ts), memberchk(E, Ts), \+ memberchk(poll(E), Ts).

% forwarded_reads(+TPhis, +E, +D, +N): T's phis read tmp(D) N times, all
% as operands from E.
forwarded_reads(TPhis, E, D, N) :-
    findall(x, ( member(phi(_, _, Pairs), TPhis), member(E-tmp(D), Pairs) ), Xs),
    length(Xs, N).

bypassed_phi(E, EPreds, EPhiA, phi(D, K, Pairs0), phi(D, K, Pairs), Uses0, Uses) :-
    (   select(E-V, Pairs0, Rest)
    ->  findall(P-VP, ( member(P, EPreds), forwarded(EPhiA, P, V, VP) ), New),
        append(Rest, New, Pairs),
        add_use(-1, V, Uses0, Uses1),
        pairs_values(New, NewVs),
        foldl(add_use(1), NewVs, Uses1, Uses)
    ;   Pairs = Pairs0, Uses = Uses0
    ).

forwarded(EPhiA, P, tmp(X), V) :- get_assoc(X, EPhiA, Pairs), !, memberchk(P-V, Pairs).
forwarded(_, _, V, V).

dropped_phi_uses(phi(_, _, Pairs), Uses0, Uses) :-
    pairs_values(Pairs, Vs), foldl(add_use(-1), Vs, Uses0, Uses).

retarget(E, T, P, Index0, Index) :-
    get_assoc(P, Index0, block(P, Phis, Insts, J0)),
    retargeted(J0, E, T, J),
    put_assoc(P, Index0, block(P, Phis, Insts, J), Index).

retargeted(goto(E), E, T, goto(T)) :- !.
retargeted(branch(V, T1, T2), E, T, branch(V, U1, U2)) :- !,
    ( T1 == E -> U1 = T ; U1 = T1 ),
    ( T2 == E -> U2 = T ; U2 = T2 ).
retargeted(J, _, _, J).

% absorb(+Entry, +B, +A0, -A): A is a(Index, Preds, Moves, JumpOf).
% While B ends in goto(T), T is not the entry, has no phis and B is its
% only predecessor, T's instructions and jump follow B's. Moves: T ->
% B-Offset, T's instructions now in B after Offset others; JumpOf: B ->
% the label whose jump B now ends with.
absorb(Entry, B, a(Index0, Preds0, Moves0, JumpOf0), A) :-
    (   get_assoc(B, Index0, block(B, Phis, Insts, goto(T))),
        atom_label(T), T \== B, T \== Entry,
        preds_of(Preds0, T, [B]),
        get_assoc(T, Index0, block(T, [], TInsts, TJump)),
        jump_targets(TJump, Ts0), findall(S, ( member(S0, Ts0), edge_label(S0, S) ), Ss0),
        sort(Ss0, Ss),
        forall(member(S, Ss), small_join(Index0, Preds0, S))
    ->  length(Insts, Off), append(Insts, TInsts, Insts1),
        del_assoc(T, Index0, _, Index1),
        put_assoc(B, Index1, block(B, Phis, Insts1, TJump), Index2),
        foldl(renamed_pred(T, B), Ss, Index2-Preds0, Index-Preds1),
        del_assoc(T, Preds1, _, Preds),
        put_assoc(T, Moves0, B-Off, Moves),
        (   get_assoc(T, JumpOf0, J) -> del_assoc(T, JumpOf0, J, JumpOf1)
        ;   J = T, JumpOf1 = JumpOf0
        ),
        put_assoc(B, JumpOf1, J, JumpOf),
        absorb(Entry, B, a(Index, Preds, Moves, JumpOf), A)
    ;   A = a(Index0, Preds0, Moves0, JumpOf0)
    ).

% renamed_pred(+T, +B, +S, +State0, -State): S's edges from T come from B.
renamed_pred(T, B, S, Index0-Preds0, Index-Preds) :-
    get_assoc(S, Index0, block(S, Phis0, Is, J)),
    maplist(renamed_phi(T, B), Phis0, Phis),
    put_assoc(S, Index0, block(S, Phis, Is, J), Index),
    preds_of(Preds0, S, Ps0),
    maplist(renamed_label(T, B), Ps0, Ps),
    put_assoc(S, Preds0, Ps, Preds).

renamed_phi(T, B, phi(D, K, Pairs0), phi(D, K, Pairs)) :-
    maplist(renamed_pair(T, B), Pairs0, Pairs).

renamed_pair(T, B, P0-V, P-V) :- renamed_label(T, B, P0, P).

renamed_label(T, B, L0, L) :- ( L0 == T -> L = B ; L = L0 ).

% merged_records(+Moves, +JumpOf, +Bypassed, +DeadPhis, +Rs0, -Rs): an
% appended block's instruction sites follow it, a holder's jump site is
% that of the block whose jump it now has, and the sites of bypassed
% blocks and their phis go.
merged_records(Moves, JumpOf, Bypassed, DeadPhis, Rs0, Rs) :-
    findall(S-Os, member(site(jump(S), Os), Rs0), JP0), sort(JP0, JP),
    list_to_assoc(JP, JumpSites),
    findall(site(jump(H), Os),
            ( gen_assoc(H, JumpOf, S), get_assoc(S, JumpSites, Os) ), NewJumps),
    findall(L-true, member(L, Bypassed), BP), list_to_assoc(BP, BA),
    findall(T-true, member(T, DeadPhis), DP), list_to_assoc(DP, DA),
    merged_records_(Rs0, Moves, JumpOf, BA, DA, Kept),
    append(Kept, NewJumps, Rs).

merged_records_([], _, _, _, _, []).
merged_records_([R0|Rs0], Moves, JumpOf, BA, DA, Rs) :-
    (   merged_record(Moves, JumpOf, BA, DA, R0, R) -> Rs = [R|Rs1] ; Rs = Rs1 ),
    merged_records_(Rs0, Moves, JumpOf, BA, DA, Rs1).

merged_record(Moves, _, _, _, site(inst(L, I), Os), site(inst(H, I1), Os)) :- !,
    holder(Moves, L, H, Off), I1 is I + Off.
merged_record(Moves, JumpOf, BA, _, site(jump(L), Os), site(jump(L), Os)) :- !,
    \+ get_assoc(L, Moves, _), \+ get_assoc(L, JumpOf, _), \+ get_assoc(L, BA, _).
merged_record(_, _, _, DA, site(phi(T), Os), site(phi(T), Os)) :- !,
    \+ get_assoc(T, DA, _).
merged_record(_, _, _, _, R, R).

% holder(+Moves, +L, -H, -Off): L's instructions are in block H from
% instruction Off on.
holder(Moves, L, H, Off) :-
    (   get_assoc(L, Moves, B-Off0)
    ->  holder(Moves, B, H, Off1), Off is Off0 + Off1
    ;   H = L, Off = 0
    ).
