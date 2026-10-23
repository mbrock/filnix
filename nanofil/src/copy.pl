/*  Copy propagation after promote, by copy_module/2.

    Only strict SSA functions are changed. Same-class temporary copies
    and integer constant copies disappear, then trivial phis: ignoring
    self inputs, all operands must name one value. In particular, an
    l -> w copy narrows, and a p symbol/literal must still materialize a
    pointer (and keep the module's ABI/mode).

    Index the eligible copies, then resolve each chain once, memoizing
    every link on the way back. Source order need not be dependency
    order. The copy work is O((definitions + uses) log definitions), not
    repeated whole-function scans or one chain walk per use.

    strict_ssa checks dominance only in reachable blocks. Never remove
    dead definitions: they may contain cycles or use-before-definition.
    Do rewrite dead uses of removed live copies, including phi edges,
    so all temporaries remain defined. Phi simplification considers even
    dead incoming edges, and leaves all-self and nontrivial cycles alone.
*/
:- module(copy, [copy_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir).
:- use_module(cfg).
:- use_module(promote, [strict_ssa/3]).

%! copy_module(+M0, -M) is det.
%
%  M is the module M0 with copies and trivial phis propagated away in
%  each strict SSA function.

copy_module(module(Items0), module(Items)) :-
    maplist(copy_item, Items0, Items).

% copy_item(+Item0, -Item): Item is the module item Item0, with copies
% propagated if it is a function.
% Reps (here and below): assoc Temp -> the value that replaces it.
copy_item(func(Name, Linkage, Ret, Params, Blocks0), F) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    func_cfg(Blocks0, Cfg),
    cfg_idoms(Cfg, Idom),
    (   strict_ssa(F0, Cfg, Idom)
    ->  temp_classes(Params, Blocks0, Classes),
        Cfg = cfg(_, Rpo, _, _),
        findall(L-true, member(L, Rpo), ReachPairs),
        list_to_assoc(ReachPairs, Reach),
        findall(D-V,
                ( member(blk(L, _, Insts, _), Blocks0),
                  get_assoc(L, Reach, _),
                  member(ins(t(D), K, copy, [Src]), Insts),
                  copy_value(Src, K, Classes, V) ),
                CopyPairs),
        list_to_assoc(CopyPairs, Copies),
        empty_assoc(Empty),
        foldl(copy_reps(Copies), CopyPairs, Empty, Reps),
        maplist(reps_block(Reps), Blocks0, Copied),
        trivial_phis(Copied, Classes, Reach, Blocks),
        F = func(Name, Linkage, Ret, Params, Blocks)
    ;   F = F0
    ).
copy_item(data(Name, Linkage, Align, Items),
          data(Name, Linkage, Align, Items)).

% temp_classes(+Params, +Blocks, -Classes): assoc Temp -> class of its
% definition.
temp_classes(Params, Blocks, Classes) :-
    findall(T-K, member(par(K, t(T)), Params), ParamPairs),
    findall(T-K,
            ( member(blk(_, Phis, Insts, _), Blocks),
              (   member(phi(t(T), K, _), Phis)
              ;   member(ins(t(T), K, _, _), Insts)
              ;   member(call(to(t(T), K), _, _), Insts)
              ;   member(call(tuple(Tos), _, _), Insts),
                  member(to(t(T), K), Tos)
              ) ),
            BlockPairs),
    append(ParamPairs, BlockPairs, Pairs),
    list_to_assoc(Pairs, Classes).

% copy_value(+Src, +K, +Classes, -V): a copy at class K of Src can be
% replaced by V (a same-class temp, or a w/l constant reduced mod 2^bits).
copy_value(t(S), K, Classes, t(S)) :- get_assoc(S, Classes, K).
copy_value(c(N), K, _, c(V)) :-
    memberchk(K, [w, l]),
    modulus(K, M),
    V is N mod M.

% copy_reps(+Copies, +D-_, +Reps0, -Reps): Reps is Reps0 with the
% value that replaces D, and every link on the way to it, added.
% Strict dominance rules out cycles among the live copy definitions.
% copy_chain/6 is tail recursive even when a chain has thousands of
% links.
copy_reps(Copies, D-_, Reps0, Reps) :-
    copy_chain(t(D), Copies, Reps0, [], Path, V),
    foldl(value_temp_reps(V), Path, Reps0, Reps).

% copy_chain(+V0, +Copies, +Reps, +Path0, -Path, -V): following copies
% (and the values already in Reps) from V0 ends at V, a value that is
% not one; Path is the temps on the way that are not in Reps, in front
% of Path0. Copies and Reps hold temps and constants only.
copy_chain(t(T), Copies, Reps, Path0, Path, V) :-
    (   get_assoc(T, Reps, V)
    ->  Path = Path0
    ;   get_assoc(T, Copies, Src)
    ->  copy_chain(Src, Copies, Reps, [T|Path0], Path, V)
    ;   V = t(T),
        Path = Path0
    ).
copy_chain(c(N), _, _, Path, Path, c(N)).

value_temp_reps(V, T, Reps0, Reps) :-
    put_assoc(T, Reps0, V, Reps).

% Copy propagation exposes invariant phis. Index their users so that a
% simplification revisits only dependent phis, not the whole function.
% Redirect those dependencies too: if A becomes B and B later becomes C,
% every remaining phi that used A must see C.
trivial_phis(Blocks0, Classes, Reach, Blocks) :-
    findall(D-Vs,
            ( member(blk(L, PhiList, _, _), Blocks0),
              get_assoc(L, Reach, _),
              member(phi(t(D), K, Args), PhiList),
              maplist(phi_value(K, Classes), Args, Vs) ),
            PhiPairs),
    list_to_assoc(PhiPairs, Phis),
    findall(S-D, ( member(D-Vs, PhiPairs), member(t(S), Vs) ), Edges0),
    sort(Edges0, Edges),
    group_pairs_by_key(Edges, UserPairs),
    list_to_assoc(UserPairs, Users),
    assoc_to_keys(Phis, Pending),
    empty_assoc(Empty),
    phi_worklist_reps(Pending, Phis, Users, Empty, Aliases),
    assoc_to_list(Aliases, AliasPairs),
    foldl(copy_reps(Aliases), AliasPairs, Empty, Reps),
    maplist(reps_block(Reps), Blocks0, Blocks).

phi_value(K, Classes, _-Src, V) :-
    copy_value(Src, K, Classes, V).

% phi_worklist_reps(+Pending, +Phis0, +Users0, +Reps0, -Reps): Reps is
% Reps0 with the value of each trivial phi, as found by a worklist over
% the phi temps Pending. Phis0: assoc D -> operand values, for the phis
% not yet simplified; Users0: assoc S -> ordset of the phis that read
% t(S). Invariant: no phi left in Phis0 reads the temp of a phi already
% simplified, and each one that may have become trivial is in Pending.
phi_worklist_reps([], _, _, Reps, Reps).
phi_worklist_reps([D|Pending0], Phis0, Users0, Reps0, Reps) :-
    (   get_assoc(D, Phis0, Vs),
        exclude(=(t(D)), Vs, Other),
        sort(Other, [V])
    ->  del_assoc(D, Phis0, _, Phis1),
        put_assoc(D, Reps0, V, Reps1),
        (   get_assoc(D, Users0, DUsers) -> true ; DUsers = [] ),
        include(is_phi(Phis1), DUsers, Live),
        foldl(phi_redirected(D, V), Live, Phis1, Phis),
        (   V = t(S), get_assoc(S, Phis, _)
        ->  (   get_assoc(S, Users0, Old) -> true ; Old = [] ),
            ord_union(Old, Live, New),
            put_assoc(S, Users0, New, Users)
        ;   Users = Users0
        ),
        ord_union(Pending0, Live, Pending),
        phi_worklist_reps(Pending, Phis, Users, Reps1, Reps)
    ;   phi_worklist_reps(Pending0, Phis0, Users0, Reps0, Reps)
    ).

is_phi(Phis, D) :-
    get_assoc(D, Phis, _).

% phi_redirected(+D, +V, +U, +Phis0, -Phis): in Phis, phi U reads V
% wherever it reads t(D) in Phis0.
phi_redirected(D, V, U, Phis0, Phis) :-
    get_assoc(U, Phis0, Vs0),
    maplist(value_redirected(D, V), Vs0, Vs),
    put_assoc(U, Phis0, Vs, Phis).

value_redirected(D, V, V0, R) :-
    (   V0 == t(D)
    ->  R = V
    ;   R = V0
    ).

%% Substitution

% reps_block(+Reps, +Block0, -Block): Block is Block0 without
% the phis and copies whose temp is in Reps, and with every use of such
% a temp replaced by its value.
reps_block(Reps, blk(L, Phis0, Insts0, Jump0),
                  blk(L, Phis, Insts, Jump)) :-
    phis_reps(Phis0, Reps, Phis),
    insts_reps(Insts0, Reps, Insts),
    jump_reps(Jump0, Reps, Jump).

phis_reps([], _, []).
phis_reps([P0|Ps0], Reps, Ps) :-
    (   P0 = phi(t(D), _, _), get_assoc(D, Reps, _)
    ->  Ps = Rest
    ;   Ps = [P|Rest],
        reps_phi(Reps, P0, P)
    ),
    phis_reps(Ps0, Reps, Rest).

reps_phi(Reps, phi(D, K, Args0), phi(D, K, Args)) :-
    maplist(reps_edge(Reps), Args0, Args).

reps_edge(Reps, L-V0, L-V) :-
    value_reps(V0, Reps, V).

insts_reps([], _, []).
insts_reps([I0|Is0], Reps, Is) :-
    (   I0 = ins(t(D), _, copy, _), get_assoc(D, Reps, _)
    ->  Is = Rest
    ;   Is = [I|Rest],
        inst_reps(I0, Reps, I)
    ),
    insts_reps(Is0, Reps, Rest).

inst_reps(ins(D, K, Op, Vs0), Reps, ins(D, K, Op, Vs)) :-
    maplist(reps_value(Reps), Vs0, Vs).
inst_reps(store(W, V0, A0), Reps, store(W, V, A)) :-
    value_reps(V0, Reps, V),
    value_reps(A0, Reps, A).
inst_reps(call(R, F0, Args0), Reps, call(R, F, Args)) :-
    value_reps(F0, Reps, F),
    maplist(reps_arg(Reps), Args0, Args).

reps_arg(Reps, arg(K, V0), arg(K, V)) :-
    value_reps(V0, Reps, V).

jump_reps(jmp(L), _, jmp(L)).
jump_reps(jnz(V0, T, F), Reps, jnz(V, T, F)) :-
    value_reps(V0, Reps, V).
jump_reps(ret(V0), Reps, ret(V)) :-
    value_reps(V0, Reps, V).
jump_reps(ret, _, ret).
jump_reps(rets(Vs0), Reps, rets(Vs)) :-
    maplist(reps_value(Reps), Vs0, Vs).
jump_reps(hlt, _, hlt).

reps_value(Reps, V0, V) :-
    value_reps(V0, Reps, V).

% value_reps(+V0, +Reps, -V): V is the replacement of V0 in Reps,
% or V0 itself.
value_reps(t(T), Reps, V) :-
    (   get_assoc(T, Reps, V1)
    ->  V = V1
    ;   V = t(T)
    ).
value_reps(c(N), _, c(N)).
value_reps(glo(G), _, glo(G)).
