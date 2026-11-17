/* This command reads source hints from the selected checked function bodies.
   Locations and declaration names explain generated code; they do not supply
   safety evidence. Loop headers come from the compiler's control-flow analysis.
*/
:- use_module('../../../src/cfg').
:- use_module(library(assoc)).
:- use_module(library(aggregate)).
:- use_module(library(lists)).
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
    temp_keys(Ps, Bs, Rs, Keys, Kinds),
    findall(Shape, temp_shape(Ps, Bs, Rs, Shape), Shapes),
    Row = _{function:N, source:Source, block_src:Locations, temp_names:Names,
            temp_keys:Keys, key_kinds:Kinds, temp_shapes:Shapes,
            loop_heads:Headers, blocks:Blocks, temps:Temps}.

% A shape says how the value of a temporary of the body is made, so that names.py
% can write the C expression it holds. Each row is [Temp, Label, Index, Shape],
% in the order parameters, phis, instructions. Index is the instruction's
% position in its block, and -1 for a parameter or a phi. A hint of the
% temporary's own comes first. The shape [raw] has no C expression.
temp_shape(Ps, _, Rs, [T, start, -1, S]) :-
    member(param(_, tmp(T)), Ps), shape(T, none, Rs, S).
temp_shape(_, Bs, Rs, [T, L, -1, S]) :-
    member(block(L, Phis, _, _), Bs), member(phi(tmp(T), _, _), Phis), shape(T, none, Rs, S).
temp_shape(_, Bs, Rs, [T, L, I, S]) :-
    member(block(L, _, Is, _), Bs), nth0(I, Is, Inst), defines(Inst, T), shape(T, Inst, Rs, S).

defines(let(tmp(T), _, _, _), T).
defines(flight(tmp(T), _, _, _), T).
defines(call(result(tmp(T), _), _, _), T).
defines(raw_call(result(tmp(T), _), _, _), T).
defines(local_load(tmp(T), _, _, _, _), T).

% JSON reads the atoms null, true and false as constants, and vfprintf has a
% variable called null, so a C name is written as a string.
shape(T, _, Rs, [Kind, Name]) :- own_key(T, Rs, Kind, _), !,
    memberchk(value(T, named(Id, _), _), Rs), memberchk(binding(Id, Name0, _, _), Rs),
    atom_string(Name0, Name).
shape(_, Inst, _, [add, R, K]) :- source_of(Inst, R, K), Inst = flight(_, _, _, _), !.
shape(_, Inst, _, [check, R]) :- source_of(Inst, R, 0), !.
shape(_, let(_, _, copy, [global(G0)]), _, [global, G]) :- !, atom_string(G0, G).
shape(_, let(_, _, copy, [tmp(R)]), _, [same, R]) :- !.
shape(_, let(_, _, ptoi, [tmp(R)]), _, [addr, R]) :- !.
shape(_, let(_, _, cmp(Op, _), [A, B]), _, [cmp, Op, SA, SB]) :- operand(A, SA), operand(B, SB), !.
shape(_, let(_, _, Op, [tmp(R)]), _, [load, R, Off]) :- load_offset(Op, Off), !.
shape(_, call(_, global(G0), _), _, [call, G]) :- !, atom_string(G0, G).
shape(_, _, _, [raw]).

load_offset(raw_load(_, Off), Off).
load_offset(raw_load_pointer(Off, _), Off).
load_offset(load(_), 0).
operand(tmp(T), [tmp, T]).
operand(const(K), [const, K]) :- integer(K).

% A key says which C value a temporary of the body holds. A temporary with a
% value hint holds the variable; one with an address hint holds the variable's
% address, written &NAME. A check or a constant pointer addition holds the value
% of the temporary it was computed from, moved by an offset. Each row is
% [Temp, Root, Key, Offset]. A temporary without a row has no C key.
temp_keys(Ps, Bs, Rs, Keys, _{current:C, named:Nn, address:An, derived:Dn, raw:Rn}) :-
    findall(T, (sub_term(tmp(T), Ps-Bs), atom(T)), Cs0), sort(Cs0, Cs),
    findall(T-I, (member(block(_, _, Is, _), Bs), member(I, Is), compound(I), arg(1, I, tmp(T))), Defs0),
    reverse(Defs0, Defs1), list_to_assoc(Defs1, Defs),
    findall(T-key(Kind, Root, Key, Off), (member(T, Cs), temp_key(T, Defs, Rs, Kind, Root, Key, Off)), Rows),
    findall([T, Root, Key, Off], (member(T-key(Kind, Root, Key, Off), Rows), Kind \== plain), Keys),
    length(Cs, C),
    aggregate_all(count, member(_-key(named, _, _, _), Rows), Nn),
    aggregate_all(count, member(_-key(address, _, _, _), Rows), An),
    aggregate_all(count, member(_-key(derived, _, _, _), Rows), Dn),
    Rn is C - Nn - An - Dn.

temp_key(T, Defs, Rs, Kind, Root, Key, Off) :-
    (   own_key(T, Rs, Kind0, Key0)
    ->  Kind = Kind0, Root = T, Key = Key0, Off = 0
    ;   temp_root(T, Defs, Rs, 16, Root, Off),
        (   Root == T -> Kind = plain, Key = T
        ;   own_key(Root, Rs, _, Key0) -> Kind = derived, Key = Key0
        ;   Kind = raw, Key = Root ) ).

own_key(T, Rs, named, Name) :-
    memberchk(value(T, named(Id, value), _), Rs), memberchk(binding(Id, Name, _, _), Rs), !.
own_key(T, Rs, address, Key) :-
    memberchk(value(T, named(Id, address), _), Rs), memberchk(binding(Id, Name, _, _), Rs),
    atom_concat('&', Name, Key).

% The walk stops at a temporary that has its own key, or that is defined in any other way.
temp_root(T, Defs, Rs, Fuel, Root, Off) :-
    (   Fuel > 0, get_assoc(T, Defs, I), source_of(I, T1, K), \+ T1 == T
    ->  (   own_key(T1, Rs, _, _) -> Root = T1, Off = K
        ;   Fuel1 is Fuel - 1, temp_root(T1, Defs, Rs, Fuel1, Root, Off1), Off is Off1 + K )
    ;   Root = T, Off = 0 ).

source_of(let(_, a, Op, Args), T, 0) :-
    compound(Op), functor(Op, F, _),
    memberchk(F, [check, check_ahead, renew, renew_hull, half_check]),
    last(Args, tmp(T)).
source_of(flight(_, add, [address(tmp(T)), const(K)], lower(tmp(T))), T, K) :- integer(K).

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
