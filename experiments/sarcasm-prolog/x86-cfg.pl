:- module(sp_x86_cfg, [emit_body/1, emit_edge/1]).
:- use_module(library(lists)).

emit_body(cfg(Entry,Blocks)) :-
    maplist(declare_inputs,Blocks),emit_edge(Entry),maplist(emit_block,Blocks).
declare_inputs(block(_,_,Params,_,_)) :- maplist(declare_input,Params).
declare_input(parameter(_,Type,V)) :- write('  '),c_type(Type),sp_x86_64:value(V),write(';'),nl.
c_type(integer) :- write('uint64_t ').
c_type(pointer) :- write('const unsigned char *').
c_type(boolean) :- write('unsigned ').
emit_block(block(B,_,_,Ops,Term)) :-
    format('sp_block~d: {~n',[B]),sp_x86_64:emit_plan(Ops,0),emit_term(Term),write('}'),nl.
emit_term(return(V)) :- write('  return '),sp_x86_64:value(V),write(';'),nl.
emit_term(jump(E)) :- emit_edge(E).
emit_term(branch(C,A,B)) :-
    write('  if ('),sp_x86_flags:emit_condition(C),write(')'),nl,
    emit_edge(A),write('  else'),nl,emit_edge(B).

% Evaluate every source before writing any destination. Each edge has a C
% scope, so even a self-edge or a cyclic register swap uses distinct temporaries.
emit_edge(edge(B,Copies)) :-
    write('  {'),nl,save_values(Copies,0),assign_values(Copies,0),
    format('    goto sp_block~d;~n  }~n',[B]).
save_values([],_).
save_values([set(_,Type,V)|Xs],N) :-
    write('    '),c_type(Type),format('edge_~d = ',[N]),sp_x86_64:value(V),write(';'),nl,
    Next is N+1,save_values(Xs,Next).
assign_values([],_).
assign_values([set(D,_,_)|Xs],N) :-
    write('    '),sp_x86_64:value(D),format(' = edge_~d;~n',[N]),
    Next is N+1,assign_values(Xs,Next).
