:- module(sp_report, [print_terms/1, explain/3, diagnostic/2]).
:- use_module(library(lists)).

print_terms(Functions) :- maplist(print_function,Functions).
print_function(function(N,A,Body)) :-
    format('function(~q,~q,[~n',[N,A]), print_steps(Body), format(']).~n',[]).
print_steps([]).
print_steps([P|Ps]) :- write('  '), write_term(P,[quoted(true)]),
    (Ps=[] -> nl; write(','),nl), print_steps(Ps).

explain(Path,Functions,Traces) :-
    format('~w: read grouping (runtime checks remain Fil-C obligations)~n',[Path]),
    maplist(explain_function,Functions,Traces).
explain_function(function(N,_,Plan),trace(N,Decisions)) :-
    format('~n~w:~n',[N]),
    (Decisions=[] -> format('  no memory reads~n',[]); maplist(explain_decision(Plan),Decisions)).
explain_decision(Plan,decision(V,L,W,Lines,Attempts)) :-
    member(read(P,I,K,O,W,[load(V,_,_,_,_,_,_)|_]),Plan), !,
    End is O+W,
    format('  line ~d: read ~q selects ~d bytes [~d,~d); source lines ~q~n',[L,V,W,O,End,Lines]),
    format('    address: pointer ~q, index ~q, scale ~d~n',[P,I,K]),
    (Attempts=[] -> format('    original read width; no larger supported candidate~n',[])
    ; maplist(explain_attempt,Attempts)).
explain_attempt(disabled) :- format('    grouping disabled; original read retained~n',[]).
explain_attempt(attempt(W,accepted(_))) :-
    format('    ~d bytes accepted: same pointer/index/scale, exact adjacent ranges, original order~n',[W]).
explain_attempt(attempt(W,rejected(Reason))) :-
    format('    ~d bytes rejected: ',[W]), reason(Reason), nl.
reason(at(L,R)) :- !, format('line ~d: ',[L]), reason(R).
reason(ordering_barrier(K)) :- !, format('~q is an ordering barrier',[K]).
reason(index_changed(A,B)) :- !, format('index value changed from ~q to ~q',[A,B]).
reason(pointer_changed(A,B)) :- !, format('pointer identity changed from ~q to ~q',[A,B]).
reason(scale_changed(A,B)) :- !, format('scale changed from ~d to ~d',[A,B]).
reason(noncontiguous(expected(A),actual(B))) :- !,
    format('non-adjacent range: expected offset ~d, got ~d',[A,B]).
reason(would_split_load(W,R)) :- !, format('would split a ~d-byte load with only ~d bytes left',[W,R]).
reason(function_return(R)) :- !, format('function returns before the remaining ~d bytes',[R]).
reason(end_of_input(R)) :- !, format('input ends before the remaining ~d bytes',[R]).
reason(R) :- write_term(R,[quoted(true)]).

% Retain structured reasons while making file and source line immediately visible.
diagnostic(Path,error(Reason)) :- !,
    (origin(Reason,L,R) -> format(user_error,'~w:~d: ~q~n',[Path,L,R])
    ; format(user_error,'~w: ~q~n',[Path,Reason])).
diagnostic(Path,E) :- format(user_error,'~w: ~q~n',[Path,E]).
origin(at(L,R),L,R).
origin(lexical(L,C),L,unexpected_character(C)).
origin(statement_syntax(L,T),L,statement_syntax(T)).
origin(signature_syntax(L),L,signature_syntax).
origin(unsupported_directive(L,N,O),L,unsupported_directive(N,O)).
origin(unsupported_signature(L,N,A),L,unsupported_signature(N,A)).
origin(expected_annotated_function(located(L,S)),L,expected_annotated_function(S)).
