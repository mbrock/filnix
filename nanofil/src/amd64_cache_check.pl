/* Independent translation validation for the block-local scalar cache.
   There are no allocation intervals, slot assignments or eviction plans
   here. The two streams execute together on symbolic register and home
   contents; only the three eligible moves may differ, and a load may be
   absent when its complete result is already in its destination. All other
   lines match exactly, including flags, failure arguments and control flow.

   Ordinary registers have one shared symbolic map: a changed load must
   prove equality before writing it. Homes have separate reference and
   actual contents, and each cache register holds a full 64-bit value.
   Values have independent low/high halves, so a 32-bit read zero-extends
   its destination without truncating the cached home. Unchanged opaque
   instructions give their written families fresh, shared symbols.

   Before every boundary all homes must agree. Afterward we forget the
   cache and start with arbitrary common homes/registers. This proves
   each straight-line region for every possible entry state, including
   entries from other branches; it does not follow textual fallthrough
   through a label. Unmentioned/noneligible homes cannot differ because
   every instruction touching them is unchanged and a boundary. The home
   map is sparse: untouched homes have a common epoch-tagged default.
   Boundaries scan only homes written in that region, not the frame. */
:- module(amd64_cache_check, [check_cache/3]).

:- use_module(amd64_contract,
              [instruction_effects/2, register/3, explicit_registers/2]).
:- use_module(library(assoc)).
:- use_module(library(lists)).

%! check_cache(+Metadata, +Before, +After) is semidet.
%
%  Metadata is cache_metadata(Setjmp, [home(Offset, Classes), ...]).
%  Every alias's class must be present; unknown is an ineligible class.
%  Placement and complete alias classes are trusted emitter metadata.
%  Unsupported original code and any setjmp permit identity only. Once
%  preflight succeeds, a bad candidate fails, never falls back to identity.
%  Validate a whole function: caching starts only after movq rsp,rbp.
check_cache(Metadata, Before, After) :-
    ground(Metadata-Before-After),
    is_list(Before), is_list(After),
    Metadata = cache_metadata(Setjmp, Homes),
    memberchk(Setjmp, [true,false]),
    home_offsets(Homes, Offsets),
    (   Setjmp == true
    ->  Before == After
    ;   preflight(Before, Instructions)
    ->  maplist(known_line, After),
        empty_assoc(Values),
        once(paired(Instructions, After, Offsets,
                    state(Values, [], [], 0, 1, unframed)))
    ;   Before == After
    ).

% Check disjoint offsets, then derive eligibility from the trusted classes.
% Duplicate/overlapping homes are not a physical scalar-slot description.
home_offsets(Homes, Eligible) :-
    is_list(Homes),
    maplist(home_description, Homes, All),
    msort(All, Sorted),
    disjoint_homes(Sorted),
    findall(O-true,
            (member(home(O, Classes), Homes), scalar_classes(Classes)),
            Pairs),
    list_to_assoc(Pairs, Eligible).

home_description(home(O, Classes), O) :-
    integer(O), O < 0, is_list(Classes).

disjoint_homes([]).
disjoint_homes([_]).
disjoint_homes([A,B|Os]) :-
    B - A >= 8,
    disjoint_homes([B|Os]).

scalar_classes([C|Cs]) :-
    memberchk(C, [w,l]),
    maplist(scalar_class, Cs).
scalar_class(w).
scalar_class(l).

preflight([], []).
preflight([Line|Lines], [instruction(Line, Effect)|Instructions]) :-
    once(instruction_effects(Line, Effect)),
    explicit_registers(Line, Registers),
    \+ (member(R, Registers), cache_family(R)),
    preflight(Lines, Instructions).

known_line(Line) :- once(instruction_effects(Line, _)).

cache_family(r10).
cache_family(r11).
cache_name(r10, r10, 64).
cache_name(r11, r11, 64).
cache_name(r10d, r10, 32).
cache_name(r11d, r11, 32).

% The syntax partitions extra moves from matched instructions: preflight
% excludes the cache bank everywhere in the original, including addresses.
paired(Before, [Line|After], Offsets, S0) :-
    extra_move(Line, Offsets, Move),
    fill_anchor(Move, Before, After, Offsets), !,
    execute_extra(Move, S0, S),
    paired(Before, After, Offsets, S).
paired([instruction(Line, Effect)|Before], [Actual|After], Offsets, S0) :-
    matched(Line, Actual, Effect, Offsets, S0, S), !,
    paired(Before, After, Offsets, S).
paired([instruction(Line, Effect)|Before], After, Offsets, S0) :-
    \+ boundary(Line, Effect, Offsets),
    eligible_move(Line, Offsets, load(O,F,Bits)),
    S0 = state(Hs,Rs,_,E,_,open),
    home_value(O, Hs, E, Reference, _),
    read_width(Bits, Reference, Expected),
    ordinary_value(F, Rs, Value),
    Value == Expected,
    next_symbol(S0, S),
    paired(Before, After, Offsets, S).
paired([], [], _, state(Homes, _, _, _, _, _)) :-
    synchronized(Homes).

extra_move(ins(mov,q,[mem(O,rbp),reg(R)]), Os, fill(O,F)) :-
    get_assoc(O, Os, _), cache_name(R,F,64).
extra_move(ins(mov,q,[reg(R),mem(O,rbp)]), Os, spill(O,F)) :-
    get_assoc(O, Os, _), cache_name(R,F,64).

% A fill replaces the next original read, never speculates one. In
% particular, rbp may exist before stack growth and its overflow check.
fill_anchor(fill(O,F), [instruction(Line,Effect)|_], [Actual|_], Os) :-
    \+ boundary(Line, Effect, Os),
    eligible_move(Line, Os, Load), Load = load(O,_,_),
    replacement(Load, Line, Actual, F).
fill_anchor(spill(_,_), _, _, _).

execute_extra(fill(O,F), state(Hs,Rs,Cs,E,N,open),
              state(Hs,Rs,Next,E,N,open)) :-
    home_value(O, Hs, E, _, Value),
    put_value(F, Value, Cs, Next).
execute_extra(spill(O,F), state(Hs,Rs,Cs,E,N,open),
              state(Next,Rs,Cs,E,N,open)) :-
    memberchk(F-Value, Cs),
    home_value(O, Hs, E, Reference, _),
    Value == Reference,
    put_assoc(O, Hs, home(Reference,Value), Next).

matched(Line, Actual, Effect, Os, S0, S) :-
    (   boundary(Line, Effect, Os)
    ->  Line == Actual,
        S0 = state(Hs,_,_,_,N,Mode0),
        synchronized(Hs),
        empty_assoc(Fresh),
        frame_mode(Line, Effect, Mode0, Mode),
        N1 is N + 1,
        S = state(Fresh,[],[],N,N1,Mode)
    ;   eligible_move(Line, Os, Move)
    ->  matched_move(Move, Line, Actual, S0, S1),
        next_symbol(S1, S)
    ;   Line == Actual,
        Effect = effect(_,Writes,_,[],next),
        S0 = state(Hs,Rs,Cs,E,N,Mode),
        opaque_writes(Writes, N, Rs, Next),
        N1 is N + 1,
        S = state(Hs,Next,Cs,E,N1,Mode)
    ).

boundary(_, effect(_,_,_,_,Flow), _) :- Flow \== next, !.
boundary(_, effect(_,Writes,_,_,_), _) :-
    member(write(F,_), Writes), memberchk(F, [rbp,rsp]), !.
boundary(Line, effect(_,_,_,Memory,_), Os) :-
    Memory \== [],
    \+ eligible_move(Line, Os, _).

% The original prologue must establish the frame before any cache use.
% Later labels can enter another epilogue's live frame, but labels before
% that prologue cannot open it. No inserted access follows leave/terminal
% until a label; even an apparently harmless fill-and-spill is forbidden.
frame_mode(ins(mov,q,[reg(rsp),reg(rbp)]), _, _, open) :- !.
frame_mode(_, _, unframed, unframed) :- !.
frame_mode(ins(leave,none,[]), _, _, closed) :- !.
frame_mode(_, effect(_,_,_,_,terminal), _, closed) :- !.
frame_mode(_, effect(_,_,_,_,label), _, open) :- !.
frame_mode(_, _, Mode, Mode).

eligible_move(ins(mov,q,[reg(R),mem(O,rbp)]), Os, store(O,F)) :-
    get_assoc(O, Os, _), register(R,F,64).
eligible_move(ins(mov,q,[mem(O,rbp),reg(R)]), Os, load(O,F,64)) :-
    get_assoc(O, Os, _), register(R,F,64).
eligible_move(ins(mov,l,[mem(O,rbp),reg(R)]), Os, load(O,F,32)) :-
    get_assoc(O, Os, _), register(R,F,32).

matched_move(Move, Line, Actual, S0, S) :-
    (   Line == Actual
    ->  unchanged_move(Move, S0, S)
    ;   replacement(Move, Line, Actual, Cache),
        changed_move(Move, Cache, S0, S)
    ).

replacement(store(_, _), ins(mov,q,[Source,_]),
            ins(mov,q,[Source,reg(R)]), F) :- cache_name(R,F,64).
replacement(load(_, _, Bits), ins(mov,Width,[_,Dest]),
            ins(mov,Width,[reg(R),Dest]), F) :- cache_name(R,F,Bits).

unchanged_move(store(O,F), state(Hs,Rs,Cs,E,N,Mode),
               state(Next,Rs,Cs,E,N,Mode)) :-
    ordinary_value(F, Rs, Value),
    put_assoc(O, Hs, home(Value,Value), Next).
unchanged_move(load(O,F,Bits), state(Hs,Rs,Cs,E,N,Mode),
               state(Hs,Next,Cs,E,N,Mode)) :-
    home_value(O, Hs, E, Reference, Actual),
    read_width(Bits, Reference, Expected),
    read_width(Bits, Actual, Value),
    Value == Expected,
    put_value(F, Value, Rs, Next).

changed_move(store(O,F), Cache, state(Hs,Rs,Cs,E,N,open),
             state(Next,Rs,NextCache,E,N,open)) :-
    ordinary_value(F, Rs, Value),
    home_value(O, Hs, E, _, Actual),
    put_assoc(O, Hs, home(Value,Actual), Next),
    put_value(Cache, Value, Cs, NextCache).
changed_move(load(O,F,Bits), Cache, state(Hs,Rs,Cs,E,N,open),
             state(Hs,Next,Cs,E,N,open)) :-
    home_value(O, Hs, E, Reference, _),
    memberchk(Cache-Cached, Cs),
    read_width(Bits, Reference, Expected),
    read_width(Bits, Cached, Value),
    Value == Expected,
    put_value(F, Value, Rs, Next).

read_width(64, Value, Value).
read_width(32, value(Low,_), value(Low,zero)).

ordinary_value(F, Values, Value) :-
    (   memberchk(F-V, Values)
    ->  Value = V
    ;   symbol_value(entry(F), 64, Value)
    ).

opaque_writes([], _, Rs, Rs).
opaque_writes([write(F,Bits)|Writes], N, Rs0, Rs) :-
    symbol_value(write(N,F), Bits, Value),
    put_value(F, Value, Rs0, Rs1),
    opaque_writes(Writes, N, Rs1, Rs).

% Partial and vector writes may conservatively forget the whole family:
% the original and candidate execute the same instruction on equal inputs.
symbol_value(Symbol, 32, value(low(Symbol),zero)) :- !.
symbol_value(Symbol, _, value(low(Symbol),high(Symbol))).

home_value(O, Homes, Epoch, Reference, Actual) :-
    (   get_assoc(O, Homes, home(R,A))
    ->  Reference = R, Actual = A
    ;   symbol_value(home(Epoch,O), 64, Value),
        Reference = Value, Actual = Value
    ).

synchronized(Homes) :-
    assoc_to_list(Homes, Pairs),
    maplist(synchronized_home, Pairs).
synchronized_home(_-home(Reference,Actual)) :- Reference == Actual.

next_symbol(state(Hs,Rs,Cs,E,N,Mode), state(Hs,Rs,Cs,E,N1,Mode)) :-
    N1 is N + 1.

put_value(F, Value, [], [F-Value]).
put_value(F, Value, [F-_|Rest], [F-Value|Rest]) :- !.
put_value(F, Value, [V|Rest], [V|Next]) :-
    put_value(F, Value, Rest, Next).
