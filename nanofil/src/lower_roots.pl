/*  Shared lowers: a derived pointer's `lowers[]` entry is its lower
    root's (docs/lowers.md). Opt-in as `--lowers=shared`; the default,
    own, gives every pointer temporary an entry of its own.

    A capability's lower never changes, and a flight with `lower(P)`
    has P's lower, whatever its address. So a flight needs no entry of
    its own when the entry of the pointer it derives from still holds
    that lower wherever the flight is live; nor does a phi whose inputs
    all have one lower root. This module chooses those pointers (the
    producer); frame_slots.pl keeps each root's entry for as long as any
    of its derived pointers is live; filc_amd64.pl emits no lower load
    or store for a flight whose donor's entry is its own, nor for a phi
    whose inputs' entries are all its own; and lowers_check.pl validates
    the resulting frame, so none of these is trusted for the GC-root
    contract.

    ## The rule

    | Term | Means |
    |---|---|
    | `D-R` in Derived | the pointer `tmp(D)` shares the entry of its lower root `tmp(R)` |

    It is FilPizlonator's `computeLowerRoots` (staging 18b6663,
    FilPizlonator.cpp:2914-3004) for nanofil's two derivations. Every
    pointer starts as its own root; then, until nothing changes, in
    reachable blocks and for names with one definition:

    - a flight `flight(tmp(D), Op, Args, lower(tmp(P)))` has P's root;
    - a phi of class p has the root C of its inputs when all of them
      are temporaries with one definition, every input other than the
      phi itself has root C, and C is a parameter or is defined in
      another block that dominates the phi's. Without that, C could be
      defined in the phi's own loop, after it, and be written again
      while the phi still holds C's previous lower.

    Definitions are counted on the liveness view (fused accesses bare,
    `uses/2` unwrapped), so a fused pointer load cannot hide a second
    definition (docs/perf.md item 17's review). Functions with setjmp
    are left alone: longjmp restores `lowers[]` (docs/setjmp.md). If
    the roots have not settled after 32 rounds, nothing is shared.
*/
:- module(lower_roots, [lowers_mode/1, derived_lowers/3]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).
:- use_module(ir, [temp_defs/3]).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2, dom_intervals/3, dominates_by_interval/3, inst_def/2]).

%! lowers_mode(-Mode) is det.
%
%  Mode is NANOFIL_LOWERS (main.pl's --lowers=): own, the default, or
%  shared.
lowers_mode(Mode) :-
    (   getenv('NANOFIL_LOWERS', Mode0), memberchk(Mode0, [own, shared])
    ->  Mode = Mode0
    ;   Mode = own
    ).

%! derived_lowers(+Params, +LiveBlocks, -Derived) is det.
%
%  Derived maps each pointer D that shares its root's `lowers[]` entry
%  to that root R (the rule above). Empty for a function with setjmp.
derived_lowers(Params, Blocks, Derived) :-
    empty_assoc(None),
    (   member(block(_, _, Is, _), Blocks), member(I, Is),
        bare(I, let(_, w, setjmp(_), _))
    ->  Derived = None
    ;   maplist(bare_block, Blocks, Bare),
        temp_defs(Params, Bare, Defs),
        pairs_keys(Defs, Names), msort(Names, Sorted),
        once_names(Sorted, Once0), list_to_assoc(Once0, Once),
        func_cfg(Bare, Cfg), Cfg = cfg(_, Rpo, _, _),
        cfg_idoms(Cfg, Idom), dom_intervals(Cfg, Idom, Dom),
        findall(N-param, member(param(_, tmp(N)), Params), PBs),
        findall(N-L, ( member(block(L, Phis, Is, _), Bare),
                       ( member(phi(tmp(N), _, _), Phis) ; member(I, Is), inst_temp(I, N) ) ),
                Bs0),
        append(PBs, Bs0, Bs1),
        findall(N-B, ( member(N-B, Bs1), get_assoc(N, Once, _) ), Bs2),
        list_to_assoc(Bs2, DefBlock),
        findall(L-B, ( member(B, Bare), B = block(L, _, _, _) ), LBs),
        list_to_assoc(LBs, ByLabel),
        findall(C, ( member(L, Rpo), get_assoc(L, ByLabel, block(_, Phis, Is, _)),
                     candidate(Once, L, Phis, Is, C) ),
                Cands),
        (   settle(Cands, DefBlock, Dom, None, 0, Parents)
        ->  findall(D-R, ( member(C, Cands), cand_name(C, D),
                           root(Parents, D, R), R \== D, \+ get_assoc(R, Parents, _) ),
                    Pairs),
            list_to_assoc(Pairs, Derived)
        ;   Derived = None
        )
    ).

% candidate(+Once, +L, +Phis, +Insts, -Cand): a single-definition flight
% with a single-definition donor, or a single-definition pointer phi of
% block L whose inputs are all single-definition temporaries.
candidate(Once, _, _, Is, flight(D, P)) :-
    member(flight(tmp(D), _, _, lower(tmp(P))), Is),
    get_assoc(D, Once, _), get_assoc(P, Once, _).
candidate(Once, L, Phis, _, phi(D, L, Vs)) :-
    member(phi(tmp(D), p, Pairs), Phis),
    get_assoc(D, Once, _),
    findall(V, member(_-V, Pairs), Vs0),
    forall(member(V, Vs0), ( V = tmp(N), get_assoc(N, Once, _) )),
    findall(N, member(tmp(N), Vs0), Vs1), sort(Vs1, Vs).

cand_name(flight(D, _), D).
cand_name(phi(D, _, _), D).

% settle(+Cands, +DefBlock, +Dom, +Parents0, +Round, -Parents): the
% fixpoint of one pass over the candidates, each pointing at the root
% its rule gives; fails after 32 rounds.
settle(Cands, DefBlock, Dom, Parents0, Round, Parents) :-
    Round < 32,
    foldl(cand_root(DefBlock, Dom), Cands, Parents0, Parents1),
    (   Parents1 == Parents0
    ->  Parents = Parents1
    ;   Round1 is Round + 1,
        settle(Cands, DefBlock, Dom, Parents1, Round1, Parents)
    ).

cand_root(_, _, flight(D, P), Ps0, Ps) :-
    root(Ps0, P, R),
    set_parent(D, R, Ps0, Ps).
cand_root(DefBlock, Dom, phi(D, L, Vs), Ps0, Ps) :-
    findall(R, ( member(V, Vs), root(Ps0, V, R), R \== D ), Rs0), sort(Rs0, Rs),
    (   Rs = [C], get_assoc(C, DefBlock, CB),
        ( CB == param -> true ; CB \== L, dominates_by_interval(Dom, CB, L) )
    ->  set_parent(D, C, Ps0, Ps)
    ;   set_parent(D, D, Ps0, Ps)
    ).

set_parent(D, D, Ps0, Ps) :- !,
    ( get_assoc(D, Ps0, _) -> del_assoc(D, Ps0, _, Ps) ; Ps = Ps0 ).
set_parent(D, R, Ps0, Ps) :- put_assoc(D, Ps0, R, Ps).

% root(+Parents, +N, -R): N's root, following parents (at most 64).
root(Ps, N, R) :- root(Ps, N, R, 0).
root(Ps, N, R, Depth) :-
    (   Depth < 64, get_assoc(N, Ps, P)
    ->  Depth1 is Depth + 1, root(Ps, P, R, Depth1)
    ;   R = N
    ).

inst_temp(I, N) :- inst_def(I, N).

once_names([], []).
once_names([N, M|Ns], Once) :- N == M, !, drop(N, Ns, Rest), once_names(Rest, Once).
once_names([N|Ns], [N-x|Once]) :- once_names(Ns, Once).

drop(N, [M|Ns], Rest) :- N == M, !, drop(N, Ns, Rest).
drop(_, Ns, Ns).

bare_block(block(L, Phis, Is0, J), block(L, Phis, Is, J)) :- maplist(bare, Is0, Is).

bare(uses(I0, _), I) :- !, bare(I0, I).
bare(I, I).
