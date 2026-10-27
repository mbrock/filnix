/*  Check reuse: a heap access check's proof covers later scalar accesses
    through the same pointer in the same block (docs/m7.md).

    Pizlonation states one check per access, right before it. This pass
    deletes a check when an earlier proof in its block already
    establishes what it would: the same pointer operand, at least its
    range and rights, and nothing in between that could free the object
    or redefine either temporary. The covered access then reads the
    earlier proof. Nothing is moved, widened or added, so every
    remaining check fails exactly where it failed before.

    ## Facts

    | Fact | Means |
    |---|---|
    | `avail(P, Q, Lo, Hi, Rights, Align)` | `tmp(Q)` is a proof of P that P+[Lo, Hi) allows Rights at alignment Align |

    The facts at a block's entry are none: evidence never crosses an
    edge, so there is no merge. A kept heap check adds its fact once its
    first access has run. An instruction that is `transparent/1` keeps
    the facts that do not mention the temporary it defines; any other
    instruction (a call, allocation, getter, pointer access, setjmp,
    va_arg, ...) removes them all.

    The pass is selected with `--checks=reuse`; the reference path keeps
    every check. ir.pl's validator accepts the result by its own rule,
    and `reuse_refines/2` checks that the only change is deleted checks
    whose access now reads a proof of the same operand.
*/
:- module(check_reuse, [reuse_checks/2, reuse_refines/2]).

:- use_module(library(lists)).
:- use_module(ir, [op_kind/2, pointer_memory_effects/2]).
:- use_module(cfg, [inst_def/2, inst_uses/2]).
:- use_module(provenance, [code_items/2, context_records/3, with_context/3,
                           remap_sites/3]).

%! reuse_checks(+M0, -M) is det.
%
%  M is the checked module M0 with each heap check that an available
%  proof covers deleted, and its access reading that proof. Context
%  sites follow the instructions; `alias(Q, tmp(Q1), none, Os)` records
%  that the access of the deleted proof Q reads Q1.

reuse_checks(module(Items0), module(Items)) :-
    code_items(Items0, Code),
    maplist(reused_item(Items0), Code, Groups), append(Groups, Items).

reused_item(All, func(N, L, R, Ps, Bs0), Items) :- !,
    reused_blocks(Bs0, Bs, Map, Reused),
    context_records(All, N, Rs0),
    (   Rs0 == [] -> Rs = []
    ;   remap_sites(Rs0, Map, Rs1),
        findall(alias(Q, tmp(Q1), none, Os),
                ( member(Q-Q1, Reused),
                  ( memberchk(value(Q, _, Os), Rs0) -> true ; Os = [] ) ),
                Aliases),
        append(Rs1, Aliases, Rs)
    ),
    with_context(func(N, L, R, Ps, Bs), Rs, Items).
reused_item(_, Item, [Item]).

reused_blocks([], [], [], []).
reused_blocks([block(L, Phis, Insts0, J)|Bs0], [block(L, Phis, Insts, J)|Bs],
              Map, Reused) :-
    reused_insts(Insts0, [], L-0-0, Insts, Map0, Reused0),
    reused_blocks(Bs0, Bs, Map1, Reused1),
    append(Map0, Map1, Map), append(Reused0, Reused1, Reused).

% reused_insts(+Insts0, +Facts, +L-Old-New, -Insts, -Map, -Reused): Old
% and New index the next instruction of block L before and after; Map
% pairs their sites, and Reused pairs each deleted proof with its
% replacement.
reused_insts([], _, _, [], [], []).
reused_insts([let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts0],
             Facts, L-Old-New, Insts, Map, Reused) :-
    scalar_access(Access0, Q), !,
    Old1 is Old + 1, Old2 is Old + 2,
    (   member(avail(P, Q1, Lo1, Hi1, Rights1, Align1), Facts),
        subsumes(Lo1, Hi1, Rights1, Align1, Lo, Hi, Rights, Align),
        unread_after(Insts0, Q)
    ->  renamed_access(Access0, Q1, Access), Insts = [Access|Insts1],
        Map = [inst(L, Old1)-inst(L, New)|Map1], New2 is New + 1,
        Reused = [Q-Q1|Reused1], Facts1 = Facts
    ;   Insts = [let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts1],
        New1 is New + 1, New2 is New + 2,
        Map = [inst(L, Old)-inst(L, New), inst(L, Old1)-inst(L, New1)|Map1],
        exclude(mentions(Q), Facts, Facts0),
        Reused = Reused1, Facts1 = [avail(P, Q, Lo, Hi, Rights, Align)|Facts0]
    ),
    after_def(Access0, Facts1, Facts2),
    reused_insts(Insts0, Facts2, L-Old2-New2, Insts1, Map1, Reused1).
reused_insts([Inst|Insts0], Facts0, L-Old-New, [Inst|Insts],
             [inst(L, Old)-inst(L, New)|Map], Reused) :-
    (   transparent(Inst) -> after_def(Inst, Facts0, Facts) ; Facts = [] ),
    Old1 is Old + 1, New1 is New + 1,
    reused_insts(Insts0, Facts, L-Old1-New1, Insts, Map, Reused).

%! reuse_refines(+M0, +M) is semidet.
%
%  M is M0 except for deleted heap checks, each of whose single access
%  now reads an earlier proof in its block of the same operand. This is
%  identity, not safety: that the earlier proof still covers the access
%  is ir.pl's rule, which valid_module/1 checks separately.

reuse_refines(module(Items0), module(Items)) :-
    code_items(Items0, Code0), code_items(Items, Code),
    maplist(item_refines, Code0, Code).

item_refines(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    maplist(block_refines, Bs0, Bs).
item_refines(Item, Item).

block_refines(block(L, Phis, Insts0, J), block(L, Phis, Insts, J)) :-
    insts_refine(Insts0, Insts, []).

% insts_refine(+Insts0, +Insts, +Proofs): Proofs are Q-Check for the
% heap checks defining tmp(Q) seen so far in the block, newest first. A
% deleted check must be subsumed by the check whose proof replaces it.
insts_refine([], [], _).
insts_refine([Inst|Insts0], [Inst|Insts], Proofs) :- !,
    (   Inst = let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P])
    ->  Proofs1 = [Q-checked(P, check(Lo, Hi, Rights, Align))|Proofs]
    ;   Proofs1 = Proofs
    ),
    insts_refine(Insts0, Insts, Proofs1).
insts_refine([let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts0],
             [Access|Insts], Proofs) :-
    scalar_access(Access0, Q),
    renamed_access(Access0, Q1, Access),
    memberchk(Q1-checked(P1, check(Lo1, Hi1, Rights1, Align1)), Proofs), P1 == P,
    subsumes(Lo1, Hi1, Rights1, Align1, Lo, Hi, Rights, Align),
    unread_after(Insts0, Q),
    insts_refine(Insts0, Insts, Proofs).

% unread_after(+Insts, +Q): no instruction of Insts reads tmp(Q) before
% one redefines it, so the deleted check's access was its single use.
unread_after([], _).
unread_after([Inst|Insts], Q) :-
    inst_uses(Inst, Us), \+ memberchk(Q, Us),
    (   inst_def(Inst, Q) -> true ; unread_after(Insts, Q) ).

% scalar_access(+Access, +Q): Access is a scalar raw access at tmp(Q).
scalar_access(let(_, _, raw_load(T, _), [tmp(Q)]), Q) :- T \== p.
scalar_access(raw_store(W, _, _, tmp(Q)), Q) :- W \== p.

renamed_access(let(D, K, raw_load(T, Off), [_]), Q, let(D, K, raw_load(T, Off), [tmp(Q)])).
renamed_access(raw_store(W, Off, V, _), Q, raw_store(W, Off, V, tmp(Q))).

% subsumes(+Lo1, +Hi1, +Rights1, +Align1, +Lo, +Hi, +Rights, +Align): a
% check of [Lo1, Hi1) with Rights1 at Align1 that succeeded implies that
% the check of [Lo, Hi) with Rights at Align, of the same pointer and
% object state, would succeed. Comparing with the deleted check, not just
% its access, keeps a wider or stronger check's trap.
subsumes(Lo1, Hi1, Rights1, Align1, Lo, Hi, Rights, Align) :-
    Lo1 =< Lo, Hi =< Hi1,
    rights_include(Rights1, Rights),
    Align1 mod Align =:= 0, (Lo - Lo1) mod Align =:= 0.

rights_include(write, _).
rights_include(read, read).

% after_def(+Inst, +Facts0, -Facts): Facts are those of Facts0 that do
% not mention the temporary Inst defines.
after_def(Inst, Facts0, Facts) :-
    (   inst_def(Inst, D)
    ->  exclude(mentions(D), Facts0, Facts)
    ;   Facts = Facts0
    ).

mentions(D, avail(P, Q, _, _, _, _)) :- ( Q == D ; P == tmp(D) ).

% transparent(+Inst): Inst cannot free, reallocate or relabel an object,
% and reaches no safepoint: arithmetic, comparisons, conversions, pure
% pointer construction, checks, scalar raw accesses and raw pointer loads
% (which read aux and box words, calling no helper).
transparent(loc(_, _)).
transparent(flight(_, _, _, _)).
transparent(raw_store(W, _, _, _)) :- W \== p.
transparent(let(_, p, raw_load_pointer(_, Es), _)) :-
    ( pointer_memory_effects(load, Es) ; pointer_memory_effects(local_load, Es) ), !.
transparent(let(_, _, Op, Args)) :-
    op_kind(Op, Kind),
    transparent_kind(Kind, Args).

transparent_kind(additive, _).
transparent_kind(alu, _).
transparent_kind(shift, _).
transparent_kind(neg, _).
transparent_kind(cmp, _).
transparent_kind(ext, _).
transparent_kind(float_convert, _).
transparent_kind(float_to_int, _).
transparent_kind(int_to_float, _).
transparent_kind(cast, _).
transparent_kind(ptoi, _).
transparent_kind(check, _).
transparent_kind(ld, _).
transparent_kind(check_local, _).
transparent_kind(copy, Args) :- \+ memberchk(global(_), Args).
