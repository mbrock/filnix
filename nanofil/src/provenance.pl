/*  Explanatory context, separate from executable IR and safety evidence.

    A context(Function, Records) item accompanies a func/5. Bindings and
    origins have function-local identities. Origins are shallow typed
    nodes at the enclosing statement's location, not expression spans.
    Values retain their original identities and hints even when removed;
    alias/4 records substitution without renaming the surviving value.

    site(inst(Label, Index), Origins) uses a zero-based index in THIS
    stage's instruction list. Passes produce explicit old-to-new site
    maps while rewriting. Phis and jumps have stable sites phi(Temp)
    and jump(Label). Context never participates in CFG or safety proofs.

    ## Records

    | Record | Meaning |
    |---|---|
    | `binding(Id, Name, CType, Location)` | declaration identity and spelling; shadowed names have distinct IDs |
    | `origin(Id, Location, Description, Parents)` | a typed lowering node, enclosing statement, or generated operation, linked by origin IDs |
    | `value(Temp, Hint, Origins)` | original definition, retained as history if eliminated |
    | `site(Site, Origins)` | provenance of a live instruction, phi or terminator |
    | `alias(Temp, Replacement, Hint, Origins)` | copy/phi substitution, including replacement by a constant |
    | `history(Id, Temp, Hint, Origins, Replacement)` | retired definition when an executable name is reused; Replacement is none or replaced(Value) |

    Location is at(File, Line) or none. A typed description is
    typed(val|obj|fun, CType, ShallowForm), a statement is statement(Kind),
    and a synthesized operation is generated(Pass, Reason). Parents
    express containment or contributing origins, not executable uses.
    Hint is none or named(BindingId, value|address|piece). C types are
    explanations of source nodes, never substitutes for IR classes.

    If a pass reuses a deleted temporary's spelling, its old definition
    moves to history/5. Incoming alias/history replacements then use
    historical(Id), referencing that history record, not the new value.
    This metadata-only reference can never be an executable operand.

    Promotion conservatively cites the slot's declaration/initial value
    and stores, not an assertion that every store reaches every phi.
    Copies preserve the survivor's primary name. Raw accesses and their
    adjacent checks inherit the same access origin; checks and poll edges
    additionally have generated origins. Erasure cannot authorize an
    otherwise-invalid check/access pair.
*/
:- module(provenance, [code_items/2, context_records/3, context_index/2, with_context/3,
                       remap_sites/3, site_origins/3, valid_contexts/1,
                       legacy_context/2, emission_sites/7, site_index/2,
                       origin_ids/2, fresh_origin/4, fresh_origin/3, retire_values/5]).
:- use_module(library(lists)).
:- use_module(library(assoc)).

code_items(Items, Code) :- exclude(is_context, Items, Code).
is_context(context(_, _)).

% context_records(+Items, +Name, -Records): Records are the context of
% function Name in Items, or [] if it has none. Items may be the
% contexts(Index) of context_index/2: a pass over every function of a
% large module (SQLite's 3,000) would otherwise scan its items for each.
context_records(contexts(Index), Name, Records) :- !,
    ( get_assoc(Name, Index, Rs) -> Records = Rs ; Records = [] ).
context_records(Items, Name, Records) :-
    ( memberchk(context(Name, Rs), Items) -> Records = Rs ; Records = [] ).

% context_index(+Items, -Contexts): Contexts indexes the contexts of
% Items by function name, the first of a name as memberchk/2 finds it.
context_index(Items, contexts(Index)) :-
    empty_assoc(Index0), foldl(index_context, Items, Index0, Index).

index_context(Item, Index0, Index) :-
    (   Item = context(Name, Rs), \+ get_assoc(Name, Index0, _)
    ->  put_assoc(Name, Index0, Rs, Index)
    ;   Index = Index0
    ).

with_context(F, [], [F]) :- !.
with_context(F, Rs, [F, context(Name, Rs)]) :- F = func(Name, _, _, _, _).

site_index(Rs, Sites) :-
    findall(S-Os, member(site(S, Os), Rs), Pairs), list_to_assoc(Pairs, Sites).

site_origins(Sites, Site, Os) :-
    ( get_assoc(Site, Sites, Origins) -> Os = Origins ; Os = [] ).

origin_ids(Rs, Ids) :-
    findall(Id-true, member(origin(Id, _, _, _), Rs), Pairs), list_to_assoc(Pairs, Ids).

% Only metadata names consult metadata. Executable fresh names remain
% exactly what the metadata-free transformation would choose.
fresh_origin(Base, Ids0, Ids, Id) :-
    ( get_assoc(Base, Ids0, _) -> unused_origin(Base, 0, Ids0, Id) ; Id = Base ),
    put_assoc(Id, Ids0, true, Ids).
% fresh_origin(+Base, +Ids, -Id): Id is fresh_origin/4's for Base, but
% Ids is not extended: for a batch of bases that are distinct and so
% cannot choose the same Id (derived ids keep their base), inserting
% each one in a function's whole origin assoc only costs time.
fresh_origin(Base, Ids, Id) :-
    ( get_assoc(Base, Ids, _) -> unused_origin(Base, 0, Ids, Id) ; Id = Base ).
unused_origin(Base, N, Ids, Id) :-
    Candidate = derived(Base, N),
    ( get_assoc(Candidate, Ids, _) -> N1 is N + 1, unused_origin(Base, N1, Ids, Id)
    ; Id = Candidate ).

retire_values(Rs0, Temps, Ids0, Ids, Rs) :-
    findall(T-true, member(T, Temps), NewPairs), list_to_assoc(NewPairs, New),
    findall(T-V, member(alias(T, V, _, _), Rs0), APairs), list_to_assoc(APairs, Aliases),
    findall(T-true, member(value(T, _, _), Rs0), VPairs), list_to_assoc(VPairs, Values),
    findall(T, (member(R, Rs0), historical_temp(R, T), get_assoc(T, New, _)), Ts0),
    sort(Ts0, Ts), retirement_ids(Ts, Ids0, Ids, Pairs), list_to_assoc(Pairs, Retired),
    retire_records(Rs0, Retired, Aliases, Values, Records),
    findall(Rs1, (member(T-Id, Pairs), \+ get_assoc(T, Values, _), \+ get_assoc(T, Aliases, _),
                 retired(T, none, [], none, Id, Rs1, [])), Missing),
    append([Records|Missing], All), maplist(retired_reference(Retired), All, Rs).

historical_temp(value(T, _, _), T).
historical_temp(alias(T, _, _, _), T).
historical_temp(alias(_, tmp(T), _, _), T).
historical_temp(history(_, _, _, _, replaced(tmp(T))), T).

% The temps Ts are distinct, so their bases retired(T) are, and no other
% base is retired/1: the new ids cannot meet each other or a later
% fresh_origin's, and Ids0 need not grow (inserting each one in a large
% function's origin assoc was most of retirement's time).
retirement_ids(Ts, Ids, Ids, Pairs) :-
    findall(T-Id, ( member(T, Ts), fresh_origin(retired(T), Ids, Id) ), Pairs).

retire_records([], _, _, _, []).
retire_records([value(T, H, Os)|Rs0], New, As, Vs, Rs) :-
    get_assoc(T, New, Id), !,
    ( get_assoc(T, As, V) -> Replacement = replaced(V) ; Replacement = none ),
    retired(T, H, Os, Replacement, Id, Rs, Rest),
    retire_records(Rs0, New, As, Vs, Rest).
retire_records([alias(T, V, H, Os)|Rs0], New, As, Vs, Rs) :-
    get_assoc(T, New, Id), !,
    ( get_assoc(T, Vs, _) -> Rs = Rest
    ; retired(T, H, Os, replaced(V), Id, Rs, Rest) ),
    retire_records(Rs0, New, As, Vs, Rest).
retire_records([R|Rs0], New, As, Vs, [R|Rs]) :-
    retire_records(Rs0, New, As, Vs, Rs).

retired(T, H, Os, Replacement, Id,
        [origin(Id, none, generated(context, retired(T)), Os),
         history(Id, T, H, Os, Replacement)|Rest], Rest).

% Incoming references identify the old definition, not a new proof that
% happens to reuse its spelling. Historical references are not IR values.
retired_reference(Ids, alias(T, tmp(Old), H, Os), alias(T, historical(Id), H, Os)) :-
    get_assoc(Old, Ids, Id), !.
retired_reference(Ids, history(HId, T, H, Os, replaced(tmp(Old))),
                  history(HId, T, H, Os, replaced(historical(Id)))) :-
    get_assoc(Old, Ids, Id), !.
retired_reference(_, R, R).

% Map is OldSite-NewSite, with one pair per emitted instruction. An
% instruction that expands has several destinations; one erased has none.
remap_sites(Rs0, Map, Rs) :-
    site_index(Rs0, Sites),
    exclude(instruction_site, Rs0, Kept),
    findall(site(New, Os),
            ( member(Old-New, Map), get_assoc(Old, Sites, Os) ), NewSites),
    append(Kept, NewSites, Rs).

instruction_site(site(inst(_, _), _)).

% The rewriting loop calls this with the instructions it just emitted.
% The cut leaves no choicepoint per instruction (10,000 in SQLite's
% sqlite3VdbeExec), which would pin the rest of the function's trail.
emission_sites(_, _, J, [], Rest, Rest, J) :- !.
emission_sites(L, I, J, [_|Is], [inst(L, I)-inst(L, J)|Ms], Rest, End) :-
    J1 is J + 1, emission_sites(L, I, J1, Is, Ms, Rest, End).

% Legacy loc markers remain valid input. At unchecked transformation
% boundaries they become context, never before checked-IR validation.
legacy_context(M, M) :- ir:module_stage(M, checked), !.
% The frontend writes no loc markers: such a module is its own result,
% shared rather than copied (a copy of SQLite's contexts is 60 MB, and
% the caller still holds the original).
legacy_context(module(Is), module(Is)) :-
    \+ ( member(func(_, _, _, _, Bs), Is), member(block(_, _, Insts, _), Bs),
         memberchk(loc(_, _), Insts) ), !.
legacy_context(module(Is0), module(Is)) :-
    context_index(Is0, Contexts),
    maplist(legacy_item_once(Contexts), Is0, Groups), append(Groups, Is).

legacy_item_once(All, Item, Items) :- once(legacy_item(All, Item, Items)).

legacy_item(All, func(N, L, R, Ps, Bs0), Items) :- !,
    context_records(All, N, Rs0),
    origin_ids(Rs0, Ids), legacy_blocks(Bs0, Bs, Ids, _, Added, Map),
    remap_sites(Rs0, Map, Rs1), site_index(Rs1, Sites0),
    foldl(legacy_site, Added, Sites0, Sites), assoc_to_list(Sites, Pairs),
    findall(site(S, Os), member(S-Os, Pairs), SiteRecords),
    append(Rs1, Added, AllRecords), exclude(is_site, AllRecords, Kept),
    append(Kept, SiteRecords, Rs),
    with_context(func(N, L, R, Ps, Bs), Rs, Items).
legacy_item(_, context(_, _), []) :- !.
legacy_item(_, I, [I]).

is_site(site(_, _)).
legacy_site(site(S, Os), Sites0, Sites) :- !,
    site_origins(Sites0, S, Before), append(Before, Os, Both), sort(Both, Merged),
    put_assoc(S, Sites0, Merged, Sites).
legacy_site(_, Sites, Sites).

legacy_blocks([], [], Ids, Ids, [], []).
legacy_blocks([block(L, Ps, Is0, J)|Bs0], [block(L, Ps, Is, J)|Bs], Ids0, Ids, Rs, Map) :-
    legacy_insts(Is0, L, 0, 0, none, Is, IRs, Last, Ids0, Ids1, M0),
    ( Is0 = [loc(_, _)|_], IRs = [origin(First, _, _, _)|_]
    -> findall(site(phi(T), [First]), member(phi(tmp(T), _, _), Ps), PRs)
    ; PRs = [] ),
    ( Last == none -> JRs = [] ; JRs = [site(jump(L), [Last])] ),
    legacy_blocks(Bs0, Bs, Ids1, Ids, Rest, M1),
    append([PRs, IRs, JRs, Rest], Rs), append(M0, M1, Map).

legacy_insts([], _, _, _, Loc, [], [], Loc, Ids, Ids, []).
legacy_insts([loc(F, Line)|Is0], L, Old, New, _, Is,
             [origin(Id, at(F, Line), statement(legacy), [])|Rs], Last, Ids0, Ids, Map) :- !,
    fresh_origin(legacy(L, Old), Ids0, Ids1, Id), Next is Old + 1,
    legacy_insts(Is0, L, Next, New, Id, Is, Rs, Last, Ids1, Ids, Map).
legacy_insts([Inst|Is0], L, Old, New, Loc, [Inst|Is], Rs, Last, Ids0, Ids,
             [inst(L, Old)-inst(L, New)|Map]) :-
    ( Loc == none -> Rs = Rest ; Rs = [site(inst(L, New), [Loc])|Rest] ),
    Old1 is Old + 1, New1 is New + 1,
    legacy_insts(Is0, L, Old1, New1, Loc, Is, Rest, Last, Ids0, Ids, Map).

valid_contexts(Items) :-
    findall(N, member(context(N, _), Items), Names),
    sort(Names, Unique), length(Names, Count), length(Unique, Count),
    % Each context's function is found in an index of the module's, not
    % by a scan of its items per context (quadratic for SQLite). The
    % records are read in place: a findall/3 would copy them all.
    empty_assoc(Funcs0), foldl(index_func, Items, Funcs0, Funcs),
    forall(member(context(N, Rs), Items), valid_context(Funcs, N-Rs)).

index_func(Item, Fs0, Fs) :-
    (   Item = func(Name, _, _, _, Bs), \+ get_assoc(Name, Fs0, _)
    ->  put_assoc(Name, Fs0, Bs, Fs)
    ;   Fs = Fs0
    ).

valid_context(Funcs, Name-Rs) :-
    get_assoc(Name, Funcs, Bs),
    ground(Rs), is_list(Rs),
    record_keys(Rs, Ids, Bindings0, Values, Aliases, Hs, Sites),
    unique_assoc(Ids, Origins), unique_assoc(Bindings0, Bindings),
    unique_assoc(Values, _), unique_assoc(Aliases, _),
    unique_assoc(Hs, Histories), unique_assoc(Sites, _),
    findall(L-N, (member(block(L, _, Is, _), Bs), length(Is, N)), Sizes), list_to_assoc(Sizes, Blocks),
    findall(T-true, (member(block(_, Ps, _, _), Bs), member(phi(tmp(T), _, _), Ps)), Phis0),
    list_to_assoc(Phis0, Phis),
    % forall/2 leaves no choicepoint per record, which a large function's
    % hundreds of thousands of records would otherwise keep alive.
    forall(member(R, Rs),
           valid_record(index(Origins, Bindings, Histories), sites(Blocks, Phis), R)).

% record_keys(+Rs, -Origins, -Bindings, -Values, -Aliases, -Histories,
% -Sites): the K-true pairs of each kind of record's key, in order, in
% one pass over a context's records. Other records are left to
% valid_record/3, which rejects them.
record_keys([], [], [], [], [], [], []).
record_keys([R|Rs], Os, Bs, Vs, As, Hs, Ss) :-
    record_key(R, Os, Bs, Vs, As, Hs, Ss, Os1, Bs1, Vs1, As1, Hs1, Ss1),
    record_keys(Rs, Os1, Bs1, Vs1, As1, Hs1, Ss1).

record_key(origin(Id, _, _, _), [Id-true|Os], Bs, Vs, As, Hs, Ss, Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(binding(B, _, _, _), Os, [B-true|Bs], Vs, As, Hs, Ss, Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(value(T, _, _), Os, Bs, [T-true|Vs], As, Hs, Ss, Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(alias(T, _, _, _), Os, Bs, Vs, [T-true|As], Hs, Ss, Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(history(Id, _, _, _, _), Os, Bs, Vs, As, [Id-true|Hs], Ss, Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(site(S, _), Os, Bs, Vs, As, Hs, [S-true|Ss], Os, Bs, Vs, As, Hs, Ss) :- !.
record_key(_, Os, Bs, Vs, As, Hs, Ss, Os, Bs, Vs, As, Hs, Ss).

% The pairs are all K-true: the assoc is built from the sorted keys in
% linear time.
unique_assoc(Pairs, Assoc) :-
    sort(Pairs, Unique),
    length(Pairs, N), length(Unique, N), ord_list_to_assoc(Unique, Assoc).

valid_record(_, _, binding(_, Name, _, Loc)) :- atom(Name), location(Loc).
valid_record(Rs, _, origin(_, Loc, Description, Parents)) :-
    location(Loc), description(Description), origins(Rs, Parents).
valid_record(Rs, _, value(T, Hint, Os)) :- atom(T), hint(Rs, Hint), origins(Rs, Os).
valid_record(Rs, _, alias(T, V, Hint, Os)) :-
    atom(T), replacement(Rs, V), hint(Rs, Hint), origins(Rs, Os).
valid_record(Rs, _, history(Id, T, Hint, Os, Replacement)) :-
    origin_exists(Rs, Id), atom(T), hint(Rs, Hint), origins(Rs, Os),
    ( Replacement == none ; Replacement = replaced(V), replacement(Rs, V) ).
valid_record(Rs, Bs, site(S, Os)) :- valid_site(Bs, S), origins(Rs, Os).

location(none).
location(at(F, L)) :- atom(F), integer(L), L >= 0.
description(statement(K)) :- atom(K).
description(typed(C, _, _)) :- memberchk(C, [val, obj, fun]).
description(generated(P, _)) :- atom(P).
hint(_, none).
hint(index(_, Bs, _), named(B, Role)) :-
    memberchk(Role, [value, address, piece]), get_assoc(B, Bs, _).
origins(Rs, Os) :- is_list(Os), maplist(origin_exists(Rs), Os).
origin_exists(index(Origins, _, _), O) :- get_assoc(O, Origins, _).
replacement(_, tmp(T)) :- atom(T).
replacement(_, const(N)) :- integer(N).
replacement(_, global(N)) :- atom(N).
replacement(index(_, _, Hs), historical(Id)) :- get_assoc(Id, Hs, _).
valid_site(sites(Bs, _), inst(L, I)) :-
    get_assoc(L, Bs, N), integer(I), I >= 0, I < N.
valid_site(sites(_, Ps), phi(T)) :- get_assoc(T, Ps, _).
valid_site(sites(Bs, _), jump(L)) :- get_assoc(L, Bs, _).
