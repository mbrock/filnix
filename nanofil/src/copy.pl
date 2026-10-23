/*  Copy propagation after promote.

    copy_module(+M0, -M)

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

copy_module(module(Items0), module(Items)) :-
    maplist(copy_item, Items0, Items).

copy_item(F0, F) :-
    F0 = func(Name, Lk, Ret, Params, Blocks0), !,
    fn_cfg(Blocks0, Cfg),
    dominators(Cfg, Idom),
    (   strict_ssa(F0, Cfg, Idom)
    ->  temp_classes(Params, Blocks0, Classes),
        Cfg = cfg(_, Rpo, _, _),
        findall(L-true, member(L, Rpo), ReachPairs),
        list_to_assoc(ReachPairs, Reach),
        findall(D-V,
                ( member(blk(L, _, Is, _), Blocks0), get_assoc(L, Reach, _),
                  member(ins(t(D), K, copy, [Src]), Is),
                  copy_value(Src, K, Classes, V) ),
                Pairs),
        list_to_assoc(Pairs, Copies),
        empty_assoc(Empty),
        foldl(resolve_copy(Copies), Pairs, Empty, Reps),
        maplist(copy_block(Reps), Blocks0, Copied),
        trivial_phis(Copied, Classes, Reach, Blocks),
        F = func(Name, Lk, Ret, Params, Blocks)
    ;   F = F0
    ).
copy_item(D, D).

temp_classes(Params, Blocks, Classes) :-
    findall(T-K, member(par(K, t(T)), Params), Pairs0),
    findall(T-K,
            ( member(blk(_, Phis, Is, _), Blocks),
              (   member(phi(t(T), K, _), Phis)
              ;   member(ins(t(T), K, _, _), Is)
              ;   member(call(to(t(T), K), _, _), Is)
              ;   member(call(tuple(Tos), _, _), Is), member(to(t(T), K), Tos)
              ) ), Pairs1),
    append(Pairs0, Pairs1, Pairs),
    list_to_assoc(Pairs, Classes).

copy_value(t(S), K, Classes, t(S)) :- get_assoc(S, Classes, K).
copy_value(c(N), K, _, c(V)) :-
    memberchk(K, [w, l]), modulus(K, M), V is N mod M.

% Strict dominance rules out cycles among the live copy definitions.
% walk_copy is tail recursive even when a chain has thousands of links.
resolve_copy(Copies, D-_, Reps0, Reps) :-
    walk_copy(t(D), Copies, Reps0, [], Path, V),
    foldl(cache_copy(V), Path, Reps0, Reps).

walk_copy(t(T), Copies, Reps, Path0, Path, V) :- !,
    (   get_assoc(T, Reps, V)
    ->  Path = Path0
    ;   get_assoc(T, Copies, Src)
    ->  walk_copy(Src, Copies, Reps, [T|Path0], Path, V)
    ;   V = t(T), Path = Path0
    ).
walk_copy(V, _, _, Path, Path, V).

cache_copy(V, T, A0, A) :- put_assoc(T, A0, V, A).

% Copy propagation exposes invariant phis. Index their users so that a
% simplification revisits only dependent phis, not the whole function.
% Redirect those dependencies too: if A becomes B and B later becomes C,
% every remaining phi that used A must see C.
trivial_phis(Blocks0, Classes, Reach, Blocks) :-
    findall(D-Vs,
            ( member(blk(L, Ps, _, _), Blocks0), get_assoc(L, Reach, _),
              member(phi(t(D), K, Args), Ps),
              maplist(phi_value(K, Classes), Args, Vs) ),
            Pairs),
    list_to_assoc(Pairs, Phis),
    findall(S-D, ( member(D-Vs, Pairs), member(t(S), Vs) ), Edges0),
    sort(Edges0, Edges), group_pairs_by_key(Edges, UserPairs),
    list_to_assoc(UserPairs, Users),
    assoc_to_keys(Phis, Pending),
    empty_assoc(Empty),
    phi_work(Pending, Phis, Users, Empty, Aliases),
    assoc_to_list(Aliases, AliasPairs),
    foldl(resolve_copy(Aliases), AliasPairs, Empty, Reps),
    maplist(copy_block(Reps), Blocks0, Blocks).

phi_value(K, Classes, _-Src, V) :- copy_value(Src, K, Classes, V).

phi_work([], _, _, Reps, Reps).
phi_work([D|Pending0], Phis0, Users0, Reps0, Reps) :-
    (   get_assoc(D, Phis0, Vs),
        exclude(=(t(D)), Vs, Other), sort(Other, [V])
    ->  del_assoc(D, Phis0, _, Phis1),
        put_assoc(D, Reps0, V, Reps1),
        ( get_assoc(D, Users0, Us) -> true ; Us = [] ),
        include(phi_pending(Phis1), Us, Live),
        foldl(redirect_phi(D, V), Live, Phis1, Phis),
        (   V = t(S), get_assoc(S, Phis, _)
        ->  ( get_assoc(S, Users0, Old) -> true ; Old = [] ),
            ord_union(Old, Live, New), put_assoc(S, Users0, New, Users)
        ;   Users = Users0
        ),
        ord_union(Pending0, Live, Pending),
        phi_work(Pending, Phis, Users, Reps1, Reps)
    ;   phi_work(Pending0, Phis0, Users0, Reps0, Reps)
    ).

phi_pending(Phis, D) :- get_assoc(D, Phis, _).
redirect_phi(D, V, U, Phis0, Phis) :-
    get_assoc(U, Phis0, Vs0),
    maplist(redirect_value(D, V), Vs0, Vs),
    put_assoc(U, Phis0, Vs, Phis).
redirect_value(D, V, V0, R) :- ( V0 == t(D) -> R = V ; R = V0 ).

copy_block(Reps, blk(L, Ps0, Is0, J0), blk(L, Ps, Is, J)) :-
    copy_phis(Ps0, Reps, Ps),
    copy_insts(Is0, Reps, Is),
    copy_jump(J0, Reps, J).

copy_phis([], _, []).
copy_phis([P0|Ps0], Reps, Ps) :-
    (   P0 = phi(t(D), _, _), get_assoc(D, Reps, _)
    ->  Ps = Rest
    ;   Ps = [P|Rest], copy_phi(Reps, P0, P)
    ),
    copy_phis(Ps0, Reps, Rest).

copy_phi(Reps, phi(D, K, Ps0), phi(D, K, Ps)) :-
    maplist(copy_edge(Reps), Ps0, Ps).
copy_edge(Reps, L-V0, L-V) :- copy_use(Reps, V0, V).

copy_insts([], _, []).
copy_insts([I0|Is0], Reps, Is) :-
    (   I0 = ins(t(D), _, copy, _), get_assoc(D, Reps, _)
    ->  Is = Rest
    ;   Is = [I|Rest], copy_inst(I0, Reps, I)
    ),
    copy_insts(Is0, Reps, Rest).

copy_inst(ins(D, K, Op, Vs0), Reps, ins(D, K, Op, Vs)) :-
    maplist(copy_use(Reps), Vs0, Vs).
copy_inst(store(W, V0, A0), Reps, store(W, V, A)) :-
    copy_use(Reps, V0, V), copy_use(Reps, A0, A).
copy_inst(call(R, F0, As0), Reps, call(R, F, As)) :-
    copy_use(Reps, F0, F), maplist(copy_arg(Reps), As0, As).
copy_arg(Reps, arg(K, V0), arg(K, V)) :- copy_use(Reps, V0, V).

copy_jump(jnz(V0, T, F), Reps, jnz(V, T, F)) :- !, copy_use(Reps, V0, V).
copy_jump(ret(V0), Reps, ret(V)) :- !, copy_use(Reps, V0, V).
copy_jump(rets(Vs0), Reps, rets(Vs)) :- !, maplist(copy_use(Reps), Vs0, Vs).
copy_jump(J, _, J).

copy_use(Reps, t(T), V) :- get_assoc(T, Reps, V), !.
copy_use(_, V, V).
