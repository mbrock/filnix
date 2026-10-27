/*  Pizlonation: from the unchecked IR to the checked IR (ir.pl), the
    form the Fil-C backend compiles, named after Fil-C's LLVM pass.

    The checks Fil-C requires are implicit in the unchecked stage, where
    a load or store at a `p` address means "check, then access". This
    pass states them: each such access becomes a check, whose class `a`
    result is the proven address, and the raw access that reads it.

    | Unchecked | Checked |
    |---|---|
    | `let(tmp(D), K, load(T), [A])` | `let(tmp(Q), a, check(0, S, read, Al), [A])`, then `let(tmp(D), K, raw_load(T, 0), [tmp(Q)])` |
    | `store(W, V, A)` | `let(tmp(Q), a, check(0, S, write, Al), [A])`, then `raw_store(W, 0, V, tmp(Q))` |
    | pointer load/store | the same check, then `raw_load_pointer` or `raw_store_pointer` with its explicit `pointer_memory_effects/2` sequence |
    | `atomic_load(p)`, `atomic_store(p, V, A)` | the same check, then the raw pointer access with the atomic effect list (`[atomic_read]`, `[atomic_write]`) |
    | `call(Res, tmp(P), Args)` | `let(tmp(Q), f, check_function, [tmp(P)])`, then `raw_call(Res, tmp(Q), Args)` |
    | `let(D, p, add, [P, X])` (also `sub`) | `flight(D, add, [address(P), X], lower(P))` |
    | `let(D, p, copy, [P])` (not a symbol) | `flight(D, copy, [address(P)], lower(P))` |
    | `let(D, p, itop, [X])` | `flight(D, copy, [X], none)` |

    S and Al are the access's size and alignment
    (ir:access_size_align/3), and Q is a fresh name.

    Every edge that does not go forward in block order, to a block at
    or before its source, gets a pollcheck, `poll(L)`, so every cycle
    polls. In a plain module, whose addresses are not Fil-C pointers,
    only the polls are added.

    This is the naive pass: one check per access, right before it, and
    every backward edge polls. Merging checks needs a model of free in
    the interpreter first (docs/pizlonation.md).

    The jmp_buf store of `setjmp` and the cursor of `va_arg` stay
    opaque: the backend checks them inside the instruction, as the
    runtime helpers they call do.
*/
:- module(pizlonate, [pizlonate_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(format)).
:- use_module(ir).
:- use_module(cfg, [inst_def/2]).
:- use_module(provenance).

%! pizlonate_module(+M0, -M) is det.
%
%  M is the unchecked module M0 with every check explicit and a poll on
%  every edge to a block at or before its source in block order. In a
%  plain module, whose addresses are not Fil-C pointers, only the polls
%  are added.

pizlonate_module(M0, module(Items)) :-
    module_mode(M0, Mode),
    legacy_context(M0, module(Items0)), code_items(Items0, Code),
    maplist(pizlonated_item_once(Mode, Items0), Code, Groups), append(Groups, Items).

% Each item has one pizlonation; committing to it frees the choicepoints
% that would otherwise keep every function's intermediate terms alive.
pizlonated_item_once(Mode, All, Item, Items) :- once(pizlonated_item(Mode, All, Item, Items)).

pizlonated_item(Mode, All, func(Name, Linkage, Ret, Params, Blocks0), Items) :-
    func_temp_names(Params, Blocks0, Names),
    findall(L-I, nth0(I, Blocks0, block(L, _, _, _)), Pairs),
    list_to_assoc(Pairs, Index),
    context_records(All, Name, Rs0),
    pizlonated_blocks(Blocks0, p(Mode, Names, Index), 0, 0, Blocks, Map, Generated),
    remap_sites(Rs0, Map, Rs1),
    checked_origins(Rs0, Rs1, Generated, Rs),
    with_context(func(Name, Linkage, Ret, Params, Blocks), Rs, Items).
pizlonated_item(_, _, data(N, L, A, Is), [data(N, L, A, Is)]).

checked_origins([], Rs, _, Rs) :- !.
checked_origins(Before, Rs0, Generated, Rs) :-
    site_index(Before, Sites), origin_ids(Before, Ids0),
    findall(Q, member(proof(Q, _), Generated), Temps),
    retire_values(Rs0, Temps, Ids0, Ids1, Retired),
    findall(L-true, member(poll(L), Generated), Pairs), list_to_assoc(Pairs, Polls),
    exclude(polled_site(Polls), Retired, Kept),
    generated_records(Generated, Sites, Ids1, _, Extra), append(Kept, Extra, Rs).

generated_records([], _, Ids, Ids, []).
generated_records([proof(Q, Site)|Gs], Sites, Ids0, Ids,
                  [origin(Id, none, generated(pizlonate, check), Os),
                   value(Q, none, [Id])|Rs]) :-
    site_origins(Sites, Site, Os), fresh_origin(pizlonate(Q), Ids0, Ids1, Id),
    generated_records(Gs, Sites, Ids1, Ids, Rs).
generated_records([poll(L)|Gs], Sites, Ids0, Ids,
                  [origin(Id, none, generated(pizlonate, poll), Os),
                   site(jump(L), [Id])|Rs]) :-
    site_origins(Sites, jump(L), Os), fresh_origin(poll(L), Ids0, Ids1, Id),
    generated_records(Gs, Sites, Ids1, Ids, Rs).
polled_site(Polls, site(jump(L), _)) :- get_assoc(L, Polls, _).

% func_temp_names(+Params, +Blocks, -Names): the assoc of every temp
% name the function defines, so a fresh name avoids them. A valid
% function reads only temps it defines.
func_temp_names(Params, Blocks, Names) :-
    findall(N-t,
            (   member(param(_, tmp(N)), Params)
            ;   member(block(_, Phis, Insts, _), Blocks),
                (   member(phi(tmp(N), _, _), Phis)
                ;   member(Inst, Insts), inst_def(Inst, N)
                )
            ),
            Pairs0),
    sort(Pairs0, Pairs),
    list_to_assoc(Pairs, Names).

% pizlonated_blocks(+Blocks0, +P, +I, +N, -Blocks): Blocks are Blocks0,
% the first at index I, checked; P is p(Mode, Names, Index), and N
% counts fresh names. Plain recursion: Trealla copies a closure's
% arguments at every call.
pizlonated_blocks([], _, _, _, [], [], []).
pizlonated_blocks([block(L, Phis, Insts0, Jump0)|Bs0], P, I, N0,
                  [block(L, Phis, Insts, Jump)|Bs], Map, Generated) :-
    P = p(Mode, Names, Index),
    checked_insts(Insts0, Mode, Names, N0, N, Insts, L, 0, 0, Map0, G0),
    polled_jump(Jump0, I, Index, Jump),
    I1 is I + 1,
    pizlonated_blocks(Bs0, P, I1, N, Bs, Map1, G1),
    ( Jump0 == Jump -> G2 = G1 ; G2 = [poll(L)|G1] ),
    append(Map0, Map1, Map), append(G0, G2, Generated).

% checked_insts(+Insts0, +Mode, +Names, +N0, -N, -Insts).
checked_insts([], _, _, N, N, [], _, _, _, [], []).
checked_insts([Inst0|Insts0], Mode, Names, N0, N, Insts, L, Old, New, Map, Generated) :-
    (   Mode == filc, checked_access(Inst0, Q, Out, [])
    ->  fresh_name(Names, N0, N1, Q), Generated = [proof(Q, inst(L, Old))|Gs]
    ;   Mode == filc, flight_inst(Inst0, Inst)
    ->  Out = [Inst], N1 = N0, Generated = Gs
    ;   Out = [Inst0], N1 = N0, Generated = Gs
    ),
    append(Out, Insts1, Insts),
    emission_sites(L, Old, New, Out, Map, Maps, Next), Old1 is Old + 1,
    checked_insts(Insts0, Mode, Names, N1, N, Insts1, L, Old1, Next, Maps, Gs).

% Pure pointer operations choose the address calculation and lower
% independently. No new temporary or safepoint separates the components.
% A symbol copy still calls its getter; it is not a pure projection.
flight_inst(let(D, p, add, [P, X]), flight(D, add, [address(P), X], lower(P))).
flight_inst(let(D, p, sub, [P, X]), flight(D, sub, [address(P), X], lower(P))).
flight_inst(let(D, p, copy, [tmp(N)]), flight(D, copy, [address(tmp(N))], lower(tmp(N)))).
flight_inst(let(D, p, copy, [const(N)]), flight(D, copy, [address(const(N))], lower(const(N)))).
flight_inst(let(D, p, itop, [X]), flight(D, copy, [X], none)).

% checked_access(+Access, ?Q, -Insts, ?Insts1): Insts less Insts1 are
% Access's check, defining tmp(Q), and its raw access.
checked_access(let(D, p, load(p), [A]), Q,
               [let(tmp(Q), a, check(0, Size, read, Align), [A]),
                let(D, p, raw_load_pointer(0, Effects), [tmp(Q)])|Is], Is) :- !,
    access_size_align(p, Size, Align),
    pointer_memory_effects(load, Effects).
checked_access(store(p, V, A), Q,
               [let(tmp(Q), a, check(0, Size, write, Align), [A]),
                raw_store_pointer(0, V, tmp(Q), Effects)|Is], Is) :- !,
    access_size_align(p, Size, Align),
    pointer_memory_effects(store, Effects).
% An atomic pointer access has the same inline check; Fil-C's helper
% does the rest (ir.pl, pointer_memory_effects/2).
checked_access(let(D, p, atomic_load(p), [A]), Q,
               [let(tmp(Q), a, check(0, Size, read, Align), [A]),
                let(D, p, raw_load_pointer(0, Effects), [tmp(Q)])|Is], Is) :- !,
    access_size_align(p, Size, Align),
    pointer_memory_effects(atomic_load, Effects).
checked_access(atomic_store(p, V, A), Q,
               [let(tmp(Q), a, check(0, Size, write, Align), [A]),
                raw_store_pointer(0, V, tmp(Q), Effects)|Is], Is) :- !,
    access_size_align(p, Size, Align),
    pointer_memory_effects(atomic_store, Effects).
checked_access(let(D, K, load(T), [A]), Q,
               [let(tmp(Q), a, check(0, Size, read, Align), [A]),
                let(D, K, raw_load(T, 0), [tmp(Q)])|Is], Is) :-
    access_size_align(T, Size, Align), !.
checked_access(store(W, V, A), Q,
               [let(tmp(Q), a, check(0, Size, write, Align), [A]),
                raw_store(W, 0, V, tmp(Q))|Is], Is) :-
    access_size_align(W, Size, Align), !.
checked_access(call(Res, tmp(P), Args), Q,
               [let(tmp(Q), f, check_function, [tmp(P)]),
                raw_call(Res, tmp(Q), Args)|Is], Is).
checked_access(local_load(D, K, T, Name, Off), Q,
               [let(tmp(Q), a, check_local(Name, Off, Size, read, Align), []),
                Access|Is], Is) :-
    access_size_align(T, Size, Align),
    ( T == p -> pointer_memory_effects(local_load, Es),
                Access = let(D, p, raw_load_pointer(0, Es), [tmp(Q)])
    ; Access = let(D, K, raw_load(T, 0), [tmp(Q)]) ).
checked_access(local_store(W, V, Name, Off), Q,
               [let(tmp(Q), a, check_local(Name, Off, Size, write, Align), []),
                Access|Is], Is) :-
    access_size_align(W, Size, Align),
    ( W == p -> pointer_memory_effects(local_store, Es),
                Access = raw_store_pointer(0, V, tmp(Q), Es)
    ; Access = raw_store(W, 0, V, tmp(Q)) ).

% fresh_name(+Names, +N0, -N, -Q): Q is chkI for the least I >= N0 not
% among Names, and N is I + 1.
fresh_name(Names, N0, N, Q) :-
    format(atom(Q0), "chk~d", [N0]),
    N1 is N0 + 1,
    (   get_assoc(Q0, Names, _)
    ->  fresh_name(Names, N1, N, Q)
    ;   Q = Q0, N = N1
    ).

% polled_jump(+Jump0, +From, +Index, -Jump): Jump is Jump0, ending the
% block at index From, with poll(L) for each target L at or before it.
polled_jump(goto(L), From, Index, goto(T)) :-
    polled_target(L, From, Index, T).
polled_jump(branch(V, L1, L2), From, Index, branch(V, T1, T2)) :-
    polled_target(L1, From, Index, T1),
    polled_target(L2, From, Index, T2).
polled_jump(ret(V), _, _, ret(V)).
polled_jump(rets(Vs), _, _, rets(Vs)).
polled_jump(ret, _, _, ret).
polled_jump(unreachable, _, _, unreachable).

% Checked IR (a poll target, and no load or store) passes unchanged.
polled_target(poll(L), _, _, poll(L)) :- !.
polled_target(L, From, Index, T) :-
    get_assoc(L, Index, To),
    (   To =< From -> T = poll(L) ; T = L ).
