/* This command reads source hints from the selected checked function bodies.
   Locations and declaration names explain generated code; they do not supply
   safety evidence. Loop headers come from the compiler's control-flow analysis.
*/
:- use_module('../../../src/cfg').
:- use_module(library(assoc)).
:- use_module(library(http/json)).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, [File|Names]),
    read_file_to_terms(File, [module(Items)], [encoding(utf8)]),
    findall(Row,
            ( member(func(N, _, _, Ps, Bs), Items),
              ( Names == [] -> true ; memberchk(N, Names) ),
              ( memberchk(context(N, Rs), Items) -> true ; Rs = [] ),
              function_row(N, Ps, Bs, Rs, Row) ), Rows),
    json_write_dict(current_output, Rows, [width(0)]), nl.

function_row(N, Ps, Bs, Rs, Row) :-
    ( member(origin(_, at(F, Line), statement(function), _), Rs)
    -> Source = [F, Line] ; Source = null ),
    findall([L, F0, Line0],
            ( member(B, Bs), B = block(L, _, _, _),
              once((block_site(B, S), memberchk(site(S, Os), Rs),
                    located(Os, Rs, [], F0, Line0))) ), Locations),
    findall(T, ( (sub_term(tmp(T), Ps-Bs), atom(T)) ; member(value(T, _, _), Rs) ), Ts0),
    sort(Ts0, Ts),
    findall([T, Name],
            ( member(T, Ts), memberchk(value(T, named(Id, value), _), Rs),
              memberchk(binding(Id, Name, _, _), Rs) ), Names),
    func_cfg(Bs, Cfg), cfg_idoms(Cfg, Idom), natural_loops(Cfg, Idom, Loops),
    assoc_to_keys(Loops, Headers),
    length(Bs, Blocks), length(Ts, Temps),
    Row = _{function:N, source:Source, block_src:Locations, temp_names:Names,
            loop_heads:Headers, blocks:Blocks, temps:Temps}.

% Phis precede instructions, and the jump is the last site in a block.
block_site(block(_, Phis, _, _), phi(T)) :- member(phi(tmp(T), _, _), Phis).
block_site(block(L, _, Is, _), inst(L, I)) :- nth0(I, Is, _).
block_site(block(L, _, _, _), jump(L)).

% Generated origins may have no location but cite a located parent.
located(Ids, Rs, Seen, F, Line) :-
    member(Id, Ids), \+ memberchk(Id, Seen),
    memberchk(origin(Id, Loc, _, Parents), Rs),
    ( Loc = at(F, Line)
    ; Loc = none, located(Parents, Rs, [Id|Seen], F, Line) ).
