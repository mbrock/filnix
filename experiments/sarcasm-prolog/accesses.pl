:- module(sp_accesses, [plan/4, validate/2]).
:- use_module(library(lists)).

% The trace is the record of the actual search, not an explanation recreated
% afterward. Only explicit rejection permits trying a smaller read.
plan(Mode,IR,Plan,Decisions) :-
    demand(ground(Mode-IR),non_ground_input),
    demand(memberchk(Mode,[on,off]),unknown_mode(Mode)),
    planning(Mode,IR,Plan,Decisions).
planning(_,[],[],[]).
planning(Mode,[load(V,P,I,K,O,W,L)|Xs],[read(P,I,K,O,Chosen,Loads)|Ys],
         [decision(V,L,Chosen,Lines,Attempts)|Ds]) :- !,
    IR=[load(V,P,I,K,O,W,L)|Xs],
    (Mode=off -> Chosen=W, Loads=[load(V,P,I,K,O,W,L)], Rest=Xs,
                 Attempts=[disabled]
    ; widths(W,Widths), choose(Widths,IR,Chosen,Loads,Rest,Attempts)),
    findall(Line,member(load(_,_,_,_,_,_,Line),Loads),Lines),
    planning(Mode,Rest,Ys,Ds).
planning(Mode,[X|Xs],[X|Ys],Ds) :- planning(Mode,Xs,Ys,Ds).
widths(W,Widths) :- findall(Size,(member(Size,[8,4,2]),Size>W),Widths).
choose([], [A|Xs], W, [A], Xs, []) :- A=load(_,_,_,_,_,W,_).
choose([Size|Sizes],IR,Chosen,Loads,Rest,[attempt(Size,Outcome)|Attempts]) :-
    IR=[load(_,P,I,K,O,_,_)|_],
    probe(IR,P,I,K,O,Size,Result),
    (Result=accepted(Loads,Rest) -> Chosen=Size,
        findall(L,member(load(_,_,_,_,_,_,L),Loads),Lines),
        Outcome=accepted(contiguous_reads(Lines)), Attempts=[]
    ; Result=rejected(Why), Outcome=rejected(Why),
      choose(Sizes,IR,Chosen,Loads,Rest,Attempts)).
probe(Rest,_,_,_,_,0,accepted([],Rest)) :- !.
probe([],_,_,_,_,Remaining,rejected(end_of_input(Remaining))) :- !.
probe([return(_)|_],_,_,_,_,Remaining,rejected(function_return(Remaining))) :- !.
probe([load(V,P1,I1,K1,O1,W,L)|Xs],P,I,K,O,Remaining,Result) :- !,
    compatibility(P,I,K,O,Remaining,P1,I1,K1,O1,W,Check),
    (Check=ok -> Next is O+W, Left is Remaining-W,
        probe(Xs,P,I,K,Next,Left,Tail),
        (Tail=accepted(Loads,Rest) -> Result=accepted([load(V,P1,I1,K1,O1,W,L)|Loads],Rest)
        ; Tail=rejected(Why), Result=rejected(Why))
    ; Check=blocked(Why), Result=rejected(at(L,Why))).
probe([Op|_],_,_,_,_,_,rejected(at(L,ordering_barrier(Kind)))) :-
    operation_origin(Op,L,Kind).
compatibility(P,_,_,_,_,P1,_,_,_,_,blocked(pointer_changed(P,P1))) :- P\==P1, !.
compatibility(_,I,_,_,_,_,I1,_,_,_,blocked(index_changed(I,I1))) :- I\==I1, !.
compatibility(_,_,K,_,_,_,_,K1,_,_,blocked(scale_changed(K,K1))) :- K\==K1, !.
compatibility(_,_,_,O,_,_,_,_,O1,_,blocked(noncontiguous(expected(O),actual(O1)))) :- O\==O1, !.
compatibility(_,_,_,_,Remaining,_,_,_,_,W,blocked(would_split_load(W,Remaining))) :- W>Remaining, !.
compatibility(_,_,_,_,_,_,_,_,_,_,ok).
operation_origin(assign(_,_,_,L),L,assignment).
operation_origin(binary(_,K,_,_,_,L),L,binary(K)).
operation_origin(pointer_copy(_,_,L),L,pointer_copy).
operation_origin(pointer_offset(_,_,_,_,_,L),L,pointer_offset).
operation_origin(store(_,_,_,_,_,_,L),L,store).
operation_origin(pointer_load(_,_,_,_,_,L),L,pointer_load).
operation_origin(pointer_store(_,_,_,_,_,L),L,pointer_store).
operation_origin(flag_values(_,_,_,_,_,L),L,flags).
operation_origin(compare(_,_,_,_,L),L,comparison).

% Validation deliberately does not call choose/probe/compatibility. It checks
% the proposal against the original ordered operations with its own coverage
% calculation. Invalid metadata is an error, never a successful empty proof.
validate(IR,Plan) :-
    demand(ground(IR-Plan),non_ground_input),
    (checked(IR,Plan) -> true; throw(error(invalid_access_plan(unrecognized_structure)))).
demand(Goal,Reason) :- (call(Goal) -> true; throw(error(invalid_access_plan(Reason)))).
checked([],[]).
checked(IR,[read(P,I,K,O,W,Loads)|Plans]) :- !,
    demand(Loads=[_|_],empty_read_group),
    demand(memberchk(W,[1,2,4,8]),unsupported_read_width(W)),
    demand(append(Loads,Rest,IR),not_an_original_prefix(Loads)),
    validate_members(Loads,P,I,K),
    findall(A-B,(member(load(_,_,_,_,A,Size,_),Loads),B is A+Size),Intervals),
    coverage(Intervals,O,End),
    demand(End=:=O+W,wrong_extent(expected(O+W),actual(End))),
    demand((O>=0,End=<18446744073709551616),range_overflow(O,End)),
    checked(Rest,Plans).
checked([X|Xs],[Y|Ps]) :-
    demand(X==Y,changed_operation(X,Y)),
    demand(X\=load(_,_,_,_,_,_,_),uncovered_load(X)), checked(Xs,Ps).
validate_members([],_,_,_).
validate_members([Load|Loads],P,I,K) :-
    demand(Load=load(_,P1,I1,K1,_,W,L),non_load_in_group(Load)),
    demand((P==P1,I==I1,K==K1),address_mismatch(L)),
    demand(memberchk(W,[1,2,4,8]),unsupported_load_width(L,W)),
    validate_members(Loads,P,I,K).
coverage([],End,End).
coverage([Start-End|Xs],Expected,Final) :-
    demand(Start=:=Expected,noncontiguous(expected(Expected),actual(Start))),
    demand(End>Start,empty_interval(Start,End)), coverage(Xs,End,Final).
