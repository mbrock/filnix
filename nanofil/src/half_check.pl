/*  Half checks: a check whose object was checked before at another range
    tests only the bound that is not already known (docs/half.md).

    An access check tests that the capability is not null, that the
    address is at or above lower and that its end is at or below upper.
    When an earlier check of the same object, through a pointer at a
    constant distance from the same base, dominates this one, it proved
    the capability not null and an address range of the object. If this
    access starts at or above where that range started, the lower test
    is known; if it ends at or below where that range ended, the upper
    test is, since an object's upper changes only when it is freed, which
    sets its free flag. The check becomes

    | Term | Tests |
    |---|---|
    | `half_check(upper, Lo, Hi, Rights, Align)` | upper, then read-only for a write, and alignment |
    | `half_check(lower, Lo, Hi, Rights, Align)` | lower (signed), the free flag and read-only for a write, and alignment |

    reading `[tmp(Q1), P]`, Q1 the earlier proof. It traps exactly where
    the check would, at the same access and with the same report. Nothing
    moves, and no fact needs a kill list: the facts it uses last as long
    as the object does.

    The pass is selected with `--checks=half`, after renewal. ir.pl's
    validator accepts each half check by its own rule (half_known/6), and
    `half_refines/2` checks that the only change is checks replaced in
    place by half checks of the same pointer, range, rights and alignment.
*/
:- module(half_check, [half_checks/2, half_refines/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(ir, [single_definitions/3, guard_chain/3, pointer_distance/4]).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2, dom_intervals/3, dominates_by_interval/3]).

%! half_checks(+M0, -M) is det.
%
%  M is the checked module M0 with each heap check that an earlier heap
%  check of the same object dominates, at a constant distance through one
%  single-definition base, replaced by a half check of the bound that
%  earlier check does not establish. Functions with a setjmp are
%  unchanged. Every instruction keeps its index, so context sites are
%  unchanged.
half_checks(module(Items0), module(Items)) :-
    maplist(half_item, Items0, Items).

half_item(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    (   member(block(_, _, Is, _), Bs0), member(let(_, _, setjmp(_), _), Is)
    ->  Bs = Bs0
    ;   single_definitions(Ps, Bs0, Once),
        func_cfg(Bs0, Cfg), cfg_idoms(Cfg, Idom), dom_intervals(Cfg, Idom, Dom),
        half_sources(Bs0, Once, Dom, Sources),
        maplist(half_block(Once, Dom, Sources), Bs0, Bs)
    ).
half_item(Item, Item).

/* half_sources(+Blocks, +Once, +Dom, -Sources): Sources maps each
   single-definition base name B to s(Pre, L, I, Q1, P1, Lo1, Hi1, K1)
   for each heap proof Q1 of P1 in a reachable block L at index I that
   proves P1+[Lo1, Hi1), where Q1 and P1 have one definition and P1 is
   B + K1 exactly (guard_chain/3). Pre is L's preorder number in the
   dominator tree (dom_intervals/3), so a block's dominators come before
   it, and dominance is an interval test, not a walk up the tree. */
half_sources(Blocks, Once, Dom, Sources) :-
    findall(B-s(Pre, L, I, Q1, P1, Lo1, Hi1, K1),
            ( member(block(L, _, Is, _), Blocks),
              get_assoc(L, Dom, Pre-_),
              nth0(I, Is, let(tmp(Q1), a, Op, Args)),
              proves(Op, Args, P1, Lo1, Hi1),
              get_assoc(Q1, Once, _), P1 = tmp(N1), get_assoc(N1, Once, _),
              guard_chain(Once, P1, Chain),
              member(tmp(B)-i(K1, K1), Chain), get_assoc(B, Once, _) ),
            Pairs0),
    keysort(Pairs0, Pairs),
    group_pairs_by_key(Pairs, Groups0),
    findall(B-Ss, ( member(B-Ss0, Groups0), msort(Ss0, Ss) ), Groups),
    list_to_assoc(Groups, Sources).

% proves(+Op, +Args, -P, -Lo, -Hi): a heap proof Op of Args has proven
% P's [Lo, Hi): a check or check_ahead of its whole range, a guarded
% renewal or a hoisted check, which are their checks.
proves(check(Lo, Hi, _, _), [P], P, Lo, Hi).
proves(check_ahead(Lo, Hi, _, _, _), [P], P, Lo, Hi).
proves(renew_if(Lo, Hi, _, _), [P, _], P, Lo, Hi).
proves(check_limit(Lo, Hi, _, _), [P, _], P, Lo, Hi).

half_block(Once, Dom, Sources, block(L, Phis, Is0, J), block(L, Phis, Is, J)) :-
    (   get_assoc(L, Dom, _)
    ->  half_insts(Is0, 0, L, Once, Dom, Sources, Is)
    ;   Is = Is0
    ).

half_insts([], _, _, _, _, _, []).
half_insts([Inst0|Is0], I, L, Once, Dom, Sources, [Inst|Is]) :-
    (   Inst0 = let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]),
        Is0 = [_|_],
        guard_chain(Once, P, Chain),
        member(tmp(B)-i(K, K), Chain),
        get_assoc(B, Sources, Ss),
        member(s(_, L1, I1, Q1, P1, Lo1, Hi1, K1), Ss),
        (   L1 == L -> I1 < I ; dominates_by_interval(Dom, L1, L) ),
        known_bound(K - K1, Lo, Hi, Lo1, Hi1, Bound),
        % The validator's identity rule, whose walk is bounded: the pass
        % makes only half checks it accepts.
        pointer_distance(Once, P, P1, D), (D - (K - K1)) mod (1 << 64) =:= 0
    ->  Inst = let(tmp(Q), a, half_check(Bound, Lo, Hi, Rights, Align), [tmp(Q1), P])
    ;   Inst = Inst0
    ),
    I2 is I + 1,
    half_insts(Is0, I2, L, Once, Dom, Sources, Is).

/* known_bound(+Distance, +Lo, +Hi, +Lo1, +Hi1, -Bound): a check of
   [Lo, Hi) at P = P1 + Distance (modulo 2^64), after a passed check of
   [Lo1, Hi1) at P1, needs to test only Bound: lower when its end is at
   or below the earlier end (one test fewer for a write, whose flag test
   then covers free too), else upper when its start is at or above the
   earlier start. The distance is taken signed, and both differences
   must be far from 2^63, where an address could wrap. */
known_bound(Distance, Lo, Hi, Lo1, Hi1, Bound) :-
    D is ((Distance + 9223372036854775808) mod 18446744073709551616) - 9223372036854775808,
    Start is D + Lo - Lo1, End is D + Hi - Hi1,
    Near = 4611686018427387904,
    abs(Start) =< Near, abs(End) =< Near, Hi - Lo =< Near,
    (   End =< 0 -> Bound = lower
    ;   Start >= 0 -> Bound = upper
    ).

%! half_refines(+M0, +M) is semidet.
%
%  M is M0 except for heap checks replaced in place by half checks of the
%  same pointer, range, rights and alignment. A half check is its check
%  by definition (ir.pl); whether its source establishes the bound it
%  leaves untested is the validator's question (valid_module/1).
half_refines(module(Items0), module(Items)) :-
    maplist(item_refines, Items0, Items).

item_refines(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    maplist(block_refines, Bs0, Bs).
item_refines(Item, Item).

block_refines(block(L, Ph, Is0, J), block(L, Ph, Is, J)) :-
    maplist(inst_refines, Is0, Is).

inst_refines(Inst, Inst) :- !.
inst_refines(let(Q, a, check(Lo, Hi, Rs, Al), [P]),
             let(Q, a, half_check(Bound, Lo, Hi, Rs, Al), [tmp(_), P])) :-
    memberchk(Bound, [upper, lower]).
