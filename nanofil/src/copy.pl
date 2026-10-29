/*  Copy propagation, run after promote: copy_module/2 removes copies
    and trivial phis from each function in strict SSA form, replacing
    every use by the value it copies.

    ## What disappears

    - A copy of a temporary of the same class.
    - A copy of an integer constant at class `w` or `l`, reduced modulo
      2^32 or 2^64.
    - Then each trivial phi: one whose operands, ignoring its own
      temporary, all name one value.

    Everything else stays. An `l` to `w` copy narrows, and a `p` copy of
    a symbol or literal must still materialize a pointer, keeping the
    module's ABI and mode. Functions that are not in strict SSA form,
    and functions that call setjmp, are left alone.

    ## How

    The eligible copies are indexed, then each chain is resolved once,
    memoizing every link on the way back, so source order need not be
    dependency order. The copy work is O((definitions + uses) log
    definitions), not repeated whole-function scans or one chain walk
    per use. Trivial phis are found by a worklist that revisits only the
    phis that read a simplified one.

    ## Dead code

    strict_ssa/3 checks dominance only in reachable blocks, so:

    - Dead definitions are never removed: they may contain cycles or
      uses before definitions. Only copies in reachable blocks are
      eligible, and only phis in reachable blocks are simplified.
    - Dead uses of removed live copies are rewritten, including phi
      edges, so every temporary stays defined.
    - Phi simplification counts dead incoming edges too, and leaves
      all-self phis and nontrivial cycles alone.
*/
:- module(copy, [copy_module/2, copy_context/4, temp_classes/3, reps_block/4, copied_records/4,
                 copy_reps/4]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir).
:- use_module(cfg).
:- use_module(promote, [strict_ssa/3]).
:- use_module(provenance).

%! copy_module(+M0, -M) is det.
%
%  M is the module M0 with copies and trivial phis propagated away in
%  each strict SSA function.

copy_module(M0, module(Items)) :-
    legacy_context(M0, module(Items0)), code_items(Items0, Code),
    context_index(Items0, Contexts),
    maplist(copy_item(Contexts), Code, Groups), append(Groups, Items).

% copy_item(+Item0, -Item): Item is the module item Item0, with copies
% propagated if it is a function.
% Reps (here and below): assoc Temp -> the value that replaces it.
% The cut leaves no choicepoint per function (promote_item/4).
copy_item(All, F0, Items) :-
    F0 = func(Name, _, _, _, _), !, context_records(All, Name, Rs0),
    copy_context(F0, Rs0, F, Rs), with_context(F, Rs, Items).
copy_item(_, data(N, L, A, Is), [data(N, L, A, Is)]).
copy_item(_, alias(N, L, T), [alias(N, L, T)]).

copy_context(F, Rs, F, Rs) :- setjmp_func(F), !.
copy_context(func(Name, Linkage, Ret, Params, Blocks0), Rs0, F, Rs) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    func_cfg(Blocks0, Cfg),
    cfg_idoms(Cfg, Idom),
    (   strict_ssa(F0, Cfg, Idom)
    ->  temp_classes(Params, Blocks0, Classes),
        Cfg = cfg(_, Rpo, _, _),
        findall(L-true, member(L, Rpo), ReachPairs),
        list_to_assoc(ReachPairs, Reach),
        findall(D-V,
                ( member(block(L, _, Insts, _), Blocks0),
                  get_assoc(L, Reach, _),
                  member(let(tmp(D), K, copy, [Src]), Insts),
                  copy_value(Src, K, Classes, V) ),
                CopyPairs),
        list_to_assoc(CopyPairs, Copies),
        empty_assoc(Empty),
        foldl(copy_reps(Copies), CopyPairs, Empty, Reps),
        maplist(reps_block(Reps), Blocks0, Copied, Maps), append(Maps, Map),
        copied_records(Reps, Map, Rs0, Rs1),
        trivial_phis(Copied, Classes, Reach, Blocks, PhiReps, PhiMap),
        copied_records(PhiReps, PhiMap, Rs1, Rs),
        F = func(Name, Linkage, Ret, Params, Blocks)
    ;   F = F0, Rs = Rs0
    ).

% A substitution is history, not a new primary name for its survivor.
copied_records(Reps, Map, Rs0, Rs) :-
    remap_sites(Rs0, Map, Rs1),
    exclude(removed_phi_site(Reps), Rs1, Rs2),
    maplist(alias_reps(Reps), Rs2, Rs3),
    findall(alias(T, V, Hint, Os),
            ( member(value(T, Hint, Os), Rs0), get_assoc(T, Reps, V) ), Aliases),
    append(Rs3, Aliases, Rs).

removed_phi_site(Reps, site(phi(T), _)) :- get_assoc(T, Reps, _).
alias_reps(_, alias(T, historical(Id), H, Os), alias(T, historical(Id), H, Os)) :- !.
alias_reps(Reps, alias(T, V0, H, Os), alias(T, V, H, Os)) :- !,
    value_reps(V0, Reps, V).
alias_reps(_, R, R).

% temp_classes(+Params, +Blocks, -Classes): assoc Temp -> class of its
% definition.
temp_classes(Params, Blocks, Classes) :-
    findall(T-K, member(param(K, tmp(T)), Params), ParamPairs),
    findall(T-K,
            ( member(block(_, Phis, Insts, _), Blocks),
              (   member(phi(tmp(T), K, _), Phis)
              ;   member(let(tmp(T), K, _, _), Insts)
              ;   member(call(result(tmp(T), K), _, _), Insts)
              ;   member(call(tuple(Tos), _, _), Insts),
                  member(result(tmp(T), K), Tos)
              ) ),
            BlockPairs),
    append(ParamPairs, BlockPairs, Pairs),
    list_to_assoc(Pairs, Classes).

% copy_value(+Src, +K, +Classes, -V): a copy at class K of Src can be
% replaced by V (a same-class temp, or a w/l constant reduced mod 2^bits).
copy_value(tmp(S), K, Classes, tmp(S)) :- get_assoc(S, Classes, K).
copy_value(const(N), K, _, const(V)) :-
    memberchk(K, [w, l]),
    modulus(K, M),
    V is N mod M.

% copy_reps(+Copies, +D-_, +Reps0, -Reps): Reps is Reps0 with the
% value that replaces D, and every link on the way to it, added.
% Strict dominance rules out cycles among the live copy definitions.
% copy_chain/6 is tail recursive even when a chain has thousands of
% links.
copy_reps(Copies, D-_, Reps0, Reps) :-
    copy_chain(tmp(D), Copies, Reps0, [], Path, V),
    foldl(value_temp_reps(V), Path, Reps0, Reps).

% copy_chain(+V0, +Copies, +Reps, +Path0, -Path, -V): following copies
% (and the values already in Reps) from V0 ends at V, a value that is
% not one; Path is the temps on the way that are not in Reps, in front
% of Path0. Copies and Reps hold temps and constants only.
copy_chain(tmp(T), Copies, Reps, Path0, Path, V) :-
    (   get_assoc(T, Reps, V)
    ->  Path = Path0
    ;   get_assoc(T, Copies, Src)
    ->  copy_chain(Src, Copies, Reps, [T|Path0], Path, V)
    ;   V = tmp(T),
        Path = Path0
    ).
copy_chain(const(N), _, _, Path, Path, const(N)).

value_temp_reps(V, T, Reps0, Reps) :-
    put_assoc(T, Reps0, V, Reps).

% Copy propagation exposes invariant phis. Index their users so that a
% simplification revisits only dependent phis, not the whole function.
% Redirect those dependencies too: if A becomes B and B later becomes C,
% every remaining phi that used A must see C.
trivial_phis(Blocks0, Classes, Reach, Blocks, Reps, Map) :-
    findall(D-Vs,
            ( member(block(L, PhiList, _, _), Blocks0),
              get_assoc(L, Reach, _),
              member(phi(tmp(D), K, Args), PhiList),
              maplist(phi_value(K, Classes), Args, Vs) ),
            PhiPairs),
    list_to_assoc(PhiPairs, Phis),
    findall(S-D, ( member(D-Vs, PhiPairs), member(tmp(S), Vs) ), Edges0),
    sort(Edges0, Edges),
    group_pairs_by_key(Edges, UserPairs),
    list_to_assoc(UserPairs, Users),
    assoc_to_keys(Phis, Pending),
    empty_assoc(Empty),
    phi_worklist_reps(Pending, Phis, Users, Empty, Aliases),
    assoc_to_list(Aliases, AliasPairs),
    foldl(copy_reps(Aliases), AliasPairs, Empty, Reps),
    maplist(reps_block(Reps), Blocks0, Blocks, Maps), append(Maps, Map).

phi_value(K, Classes, _-Src, V) :-
    copy_value(Src, K, Classes, V).

% phi_worklist_reps(+Pending, +Phis0, +Users0, +Reps0, -Reps): Reps is
% Reps0 with the value of each trivial phi, as found by a worklist over
% the phi temps Pending. Phis0: assoc D -> operand values, for the phis
% not yet simplified; Users0: assoc S -> ordset of the phis that read
% tmp(S). Invariant: no phi left in Phis0 reads the temp of a phi already
% simplified, and each one that may have become trivial is in Pending.
phi_worklist_reps([], _, _, Reps, Reps).
phi_worklist_reps([D|Pending0], Phis0, Users0, Reps0, Reps) :-
    (   get_assoc(D, Phis0, Vs),
        exclude(=(tmp(D)), Vs, Other),
        sort(Other, [V])
    ->  del_assoc(D, Phis0, _, Phis1),
        put_assoc(D, Reps0, V, Reps1),
        (   get_assoc(D, Users0, DUsers) -> true ; DUsers = [] ),
        include(is_phi(Phis1), DUsers, Live),
        foldl(phi_redirected(D, V), Live, Phis1, Phis),
        (   V = tmp(S), get_assoc(S, Phis, _)
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
% wherever it reads tmp(D) in Phis0.
phi_redirected(D, V, U, Phis0, Phis) :-
    get_assoc(U, Phis0, Vs0),
    maplist(value_redirected(D, V), Vs0, Vs),
    put_assoc(U, Phis0, Vs, Phis).

value_redirected(D, V, V0, R) :-
    (   V0 == tmp(D)
    ->  R = V
    ;   R = V0
    ).

%% Substitution

% reps_block(+Reps, +Block0, -Block): Block is Block0 without
% the phis and copies whose temp is in Reps, and with every use of such
% a temp replaced by its value.
reps_block(Reps, block(L, Phis0, Insts0, Jump0),
                  block(L, Phis, Insts, Jump), Map) :-
    phis_reps(Phis0, Reps, Phis),
    insts_reps(Insts0, Reps, Insts, L, 0, 0, Map),
    jump_reps(Jump0, Reps, Jump).

phis_reps([], _, []).
phis_reps([P0|Ps0], Reps, Ps) :-
    (   P0 = phi(tmp(D), _, _), get_assoc(D, Reps, _)
    ->  Ps = Rest
    ;   Ps = [P|Rest],
        reps_phi(Reps, P0, P)
    ),
    phis_reps(Ps0, Reps, Rest).

reps_phi(Reps, phi(D, K, Args0), phi(D, K, Args)) :-
    maplist(reps_edge(Reps), Args0, Args).

reps_edge(Reps, L-V0, L-V) :-
    value_reps(V0, Reps, V).

insts_reps([], _, [], _, _, _, []).
insts_reps([I0|Is0], Reps, Is, L, Old, New, Map) :-
    (   I0 = let(tmp(D), _, copy, _), get_assoc(D, Reps, _)
    ->  Is = Rest, Out = []
    ;   Is = [I|Rest],
        inst_reps(I0, Reps, I), Out = [I]
    ),
    emission_sites(L, Old, New, Out, Map, Maps, Next), Old1 is Old + 1,
    insts_reps(Is0, Reps, Rest, L, Old1, Next, Maps).

inst_reps(loc(F, L), _, loc(F, L)).
inst_reps(let(D, K, Op, Vs0), Reps, let(D, K, Op, Vs)) :-
    maplist(reps_value(Reps), Vs0, Vs).
inst_reps(store(W, V0, A0), Reps, store(W, V, A)) :-
    value_reps(V0, Reps, V),
    value_reps(A0, Reps, A).
inst_reps(atomic_store(W, V0, A0), Reps, atomic_store(W, V, A)) :-
    value_reps(V0, Reps, V),
    value_reps(A0, Reps, A).
inst_reps(fence, _, fence).
inst_reps(call(R, F0, Args0), Reps, call(R, F, Args)) :-
    value_reps(F0, Reps, F),
    maplist(reps_arg(Reps), Args0, Args).

reps_arg(Reps, arg(K, V0), arg(K, V)) :-
    value_reps(V0, Reps, V).

jump_reps(goto(L), _, goto(L)).
jump_reps(branch(V0, T, F), Reps, branch(V, T, F)) :-
    value_reps(V0, Reps, V).
jump_reps(ret(V0), Reps, ret(V)) :-
    value_reps(V0, Reps, V).
jump_reps(ret, _, ret).
jump_reps(rets(Vs0), Reps, rets(Vs)) :-
    maplist(reps_value(Reps), Vs0, Vs).
jump_reps(unreachable, _, unreachable).

reps_value(Reps, V0, V) :-
    value_reps(V0, Reps, V).

% value_reps(+V0, +Reps, -V): V is the replacement of V0 in Reps,
% or V0 itself.
value_reps(tmp(T), Reps, V) :-
    (   get_assoc(T, Reps, V1)
    ->  V = V1
    ;   V = tmp(T)
    ).
value_reps(const(N), _, const(N)).
value_reps(global(G), _, global(G)).
