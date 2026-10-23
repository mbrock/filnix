/*  Copy propagation after promote.

    copy_module(+M0, -M)

    Only strict SSA functions are changed. Same-class temporary copies
    and integer constant copies disappear; everything else stays. In
    particular, an l -> w copy narrows, and a p symbol/literal copy must
    still materialize a pointer (and keep the module's ABI/mode).

    Index the eligible copies, then resolve each chain once, memoizing
    every link on the way back. Source order need not be dependency
    order. The copy work is O((definitions + uses) log definitions), not
    repeated whole-function scans or one chain walk per use.

    strict_ssa checks dominance only in reachable blocks. Never remove
    dead definitions: they may contain cycles or use-before-definition.
    Do rewrite dead uses of removed live copies, including phi edges,
    so all temporaries remain defined. Phis themselves are not removed.
*/
:- module(copy, [copy_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
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
        maplist(copy_block(Reps), Blocks0, Blocks),
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

copy_block(Reps, blk(L, Ps0, Is0, J0), blk(L, Ps, Is, J)) :-
    maplist(copy_phi(Reps), Ps0, Ps),
    copy_insts(Is0, Reps, Is),
    copy_jump(J0, Reps, J).

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
