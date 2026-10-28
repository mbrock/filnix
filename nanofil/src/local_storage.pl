/*  Nonescaping memory that remains after scalar promotion.

    local_storage_module/2 replaces an entry allocation and its address
    chain with a named local object and fixed-offset accesses. A local
    object's address is not a value: it cannot become a heap lower, a
    call argument or a stored pointer. Pointer *contents* still have
    ordinary Fil-C capabilities.

    Selection is deliberately smaller than escape classification: strict
    SSA, no returns-twice operation, a constant entry size, and all
    accesses within the exact size. Heap allocations have rounded bounds;
    selecting an access in their padding would change the IR's meaning.
    Overlapping and misaligned accesses remain, with all their checks.
    Local payload/aux storage is limited to 4096 bytes per function;
    larger objects and the remainder keep the heap fallback.
    Plain-mode and checked modules are unchanged.
*/
:- module(local_storage, [local_storage_module/2, local_storage_func/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ir).
:- use_module(cfg).
:- use_module(escape).
:- use_module(promote, [strict_ssa/3]).
:- use_module(provenance).

%! local_storage_module(+M0, -M) is det.
%
%  M has named local objects for the eligible allocations of M0.
local_storage_module(M0, M) :-
    (   module_mode(M0, filc), module_stage(M0, unchecked)
    ->  legacy_context(M0, module(Items0)), code_items(Items0, Code),
        context_index(Items0, Contexts),
        maplist(local_item(Contexts), Code, Groups), append(Groups, Items),
        M = module(Items)
    ;   M = M0
    ).

local_item(All, F0, Items) :-
    F0 = func(N, _, _, _, _), context_records(All, N, Rs0),
    local_context(F0, Rs0, F, Rs), with_context(F, Rs, Items).
local_item(_, data(N, L, A, Is), [data(N, L, A, Is)]).

%! local_storage_func(+F0, -F) is det.
%
%  F0 is an unchecked Fil-C function. Unknown or unsupported allocation
%  uses keep their heap representation.
local_storage_func(F0, F) :- local_context(F0, [], F, _).

local_context(F0, Rs0, F, Rs) :-
    F0 = func(N, L, R, Ps, Bs0),
    (   \+ setjmp_func(F0),
        local_objects(F0, []),
        % Only a constant alloc in the entry block can become local
        % (local_objects/3): most functions have none, so look first.
        Bs0 = [block(_, _, Entry, _)|_],
        memberchk(let(_, p, alloc(_), [const(_)]), Entry),
        func_cfg(Bs0, Cfg), cfg_idoms(Cfg, Idom),
        strict_ssa(F0, Cfg, Idom),
        address_temps(F0, Addresses),
        local_objects(F0, Addresses, Objects), Objects \== []
    ->  maplist(local_block(Objects, Addresses), Bs0, Bs, Maps), append(Maps, Map),
        remap_sites(Rs0, Map, Rs), F = func(N, L, R, Ps, Bs)
    ;   F = F0, Rs = Rs0
    ).

% Only in-bounds accesses qualify, but not necessarily disjoint ones:
% those are the objects promote could not turn into SSA values.
local_objects(F, Addresses, Objects) :-
    F = func(_, _, _, _, Blocks),
    Blocks = [block(_, _, Entry, _)|_],
    alloc_classes(F, Classes),
    % escape's fixed-slot vocabulary currently excludes float loads.
    % Missing access events are not evidence that an object is unused.
    findall(A,
            ( member(block(_, _, Is, _), Blocks),
              member(let(_, _, load(T), [tmp(P)]), Is),
              \+ load_width(T, _), get_assoc(P, Addresses, A-_) ),
            Unsupported),
    findall(A-Size,
            ( member(A-local(const(Size), Accesses), Classes),
              integer(Size), Size >= 0,
              \+ memberchk(A, Unsupported),
              memberchk(let(tmp(A), p, alloc(_), [const(Size)]), Entry),
              maplist(access_inside(Size), Accesses) ),
            Candidates),
    within_budget(Candidates, 4096, Objects).

% Payload and aux round to 16; reserve a header, a root, and alignment
% slack too. This is selection policy, not a relaxation of local bounds.
within_budget([], _, []).
within_budget([A-Size|As], Budget, Objects) :-
    Cost is 2 * ((Size + 15) // 16 * 16) + 32,
    ( Cost =< Budget
    -> Objects = [A-Size|Rest], Remaining is Budget - Cost
    ; Objects = Rest, Remaining = Budget ),
    within_budget(As, Remaining, Rest).

access_inside(Size, acc(Off, Width)) :-
    width_bytes(Width, Bytes),
    Off >= 0, Off + Bytes =< Size.

local_block(Objects, Addresses, block(L, Phis, Is0, Jump),
            block(L, Phis, Is, Jump), Map) :-
    local_insts(Is0, Objects, Addresses, Is, L, 0, 0, Map).

local_insts([], _, _, [], _, _, _, []).
local_insts([I0|Is0], Objects, Addresses, Is, L, Old, New, Map) :-
    (   I0 = let(tmp(A), p, alloc(_), [const(Size)]),
        memberchk(A-Size, Objects)
    ->  Out = [local_alloc(A, Size)]
    ;   local_access(I0, Objects, Addresses, I)
    ->  Out = [I]
    ;   I0 = let(tmp(D), p, _, _),
        get_assoc(D, Addresses, A-_), memberchk(A-_, Objects)
    ->  Out = []
    ;   Out = [I0]
    ),
    append(Out, Rest, Is),
    emission_sites(L, Old, New, Out, Map, Maps, Next), Old1 is Old + 1,
    local_insts(Is0, Objects, Addresses, Rest, L, Old1, Next, Maps).

local_access(let(D, K, load(T), [tmp(P)]), Objects, Addresses,
             local_load(D, K, T, A, Off)) :-
    get_assoc(P, Addresses, A-Off), memberchk(A-_, Objects).
local_access(store(W, V, tmp(P)), Objects, Addresses,
             local_store(W, V, A, Off)) :-
    get_assoc(P, Addresses, A-Off), memberchk(A-_, Objects).
