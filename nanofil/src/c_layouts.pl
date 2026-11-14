/* This module exposes the completed C record layouts without changing the IR.
   Each record retains its original definition and adds member sizes and alignments.
   Function uses include records reached through the types in source contexts.
   These tables support diagnostics and offset checks, not safety premises. */
:- module(c_layouts, [module_layouts/3]).
:- use_module(c_types, [member_layout/6, type_size_align/4]).
:- use_module(library(assoc)).
:- use_module(library(lists)).

module_layouts(Env, module(Items), layouts(Records, Uses)) :-
    Env = e(Ords, Tags, Defs, _),
    findall(record(Id, Names, Def, Fields),
            ( gen_assoc(Id, Defs, Def), integer(Id),
              Def = def(Kind, Members, _, _), SU =.. [Kind, Id],
              record_names(Ords, Tags, SU, Names),
              findall(field(N, T, Off, Size, Align, Bits),
                      ( member_name(Members, Defs, N),
                        member_layout(SU, N, Env, T, Off, Bits),
                        member_size_align(T, Env, Size, Align) ), Fields) ), Complete),
    findall(record(Id, Names, incomplete, []),
            ( gen_assoc(_, Tags, tag(Kind, Id)),
              \+ get_assoc(Id, Defs, def(_, _, _, _)), SU =.. [Kind, Id],
              record_names(Ords, Tags, SU, Names) ), Missing0),
    sort(Missing0, Missing), append(Complete, Missing, Records),
    findall(uses(F, Ids),
            ( member(context(F, Rs), Items),
              record_ids(Rs, Seeds), reachable(Seeds, Defs, [], Ids) ), Uses).

record_names(Ords, Tags, SU, Names) :-
    SU =.. [Kind, Id],
    findall(Name,
            ( gen_assoc(N, Tags, tag(Kind, Id)), Name = tag(Kind, N)
            ; gen_assoc(N, Ords, typedef(SU)), Name = typedef(N) ), Names).

member_name(Members, _, N) :- member(M, Members), arg(1, M, some(N)).
member_name(Members, Defs, N) :-
    member(m(none, SU, _), Members), SU =.. [_, Id],
    get_assoc(Id, Defs, def(_, Inner, _, _)), member_name(Inner, Defs, N).

% A flexible array occupies no bytes; its element still determines its alignment.
member_size_align(array(T, none), Env, 0, Align) :- !,
    type_size_align(T, Env, _, Align).
member_size_align(T, Env, Size, Align) :- type_size_align(T, Env, Size, Align).

record_ids(Term, Ids) :-
    findall(Id, (sub_term(S, Term), nonvar(S),
                 (S = struct(Id) ; S = union(Id)), integer(Id)), Is),
    sort(Is, Ids).

reachable([], _, Seen, Ids) :- sort(Seen, Ids).
reachable([Id|Rest], Defs, Seen, Ids) :-
    ( memberchk(Id, Seen) -> reachable(Rest, Defs, Seen, Ids)
    ; ( get_assoc(Id, Defs, def(_, Members, _, _)) -> record_ids(Members, More)
      ; More = [] ),
      append(More, Rest, Todo), reachable(Todo, Defs, [Id|Seen], Ids)
    ).
