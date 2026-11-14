/* This command selects completed layouts used by the fixture's functions.
   Translation-unit identities stay separate until their named layouts agree. */
:- use_module(library(http/json)).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, [Functions|Specs]),
    atomic_list_concat(Names, ',', Functions),
    findall(Row, (member(Spec, Specs), unit_row(Spec, Names, Row)), Rows0),
    sort(Rows0, Rows), json_write_dict(current_output, Rows, [width(0)]), nl.

unit_row(Spec, Names, Row) :-
    atomic_list_concat([Obj, File], '=', Spec),
    read_file_to_terms(File, [layouts(Records, Uses)], []),
    member(uses(F, Ids), Uses),
    (memberchk(F, Names) ; atomic_list_concat([Obj, '#', F], Linked), memberchk(Linked, Names)),
    member(Id, Ids), member(record(Id, Aliases, Def, Fields), Records),
    ( Def = def(Kind, _, Size, Align)
    -> layout_name(Aliases, Obj, Kind, Id, Tag),
       findall([Name, Off, Bytes, Alignment],
               member(field(Name, _, Off, Bytes, Alignment, _), Fields), Fs),
       Row = layout{tag:Tag, size:Size, align:Align, fields:Fs}
    ; member(tag(Kind, _), Aliases), layout_name(Aliases, Obj, Kind, Id, Tag),
      Row = missing{tag:Tag, missing:true} ).

layout_name([], Obj, Kind, Id, Tag) :-
    atomic_list_concat([Obj, ':anonymous ', Kind, '#', Id], Tag).
layout_name(Aliases, _, Kind, _, Tag) :-
    member(Alias, Aliases),
    (Alias = tag(Kind, N), atomic_list_concat([Kind, N], ' ', Tag)
    ; Alias = typedef(N), atom_concat('typedef ', N, Tag)).
