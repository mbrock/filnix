:- module(sp_ir, [lower/2, lower/3, plan/3, validate/2, constant/2]).
:- use_module(library(lists)).

% Typed SSA values distinguish changing registers from immutable address inputs.
lower(Statements, Functions) :- lower(Statements,Functions,_).
lower(Statements, Functions, Effects) :-
    strip_metadata(Statements, Code), functions(Code, Functions, Effects),
    findall(N, member(function(N,_,_),Functions), Names), sort(Names,Unique),
    (same_length(Names,Unique) -> true; throw(error(duplicate_function))).
strip_metadata([], []).
strip_metadata([located(L,directive(N,O))|Ss], Cs) :- !,
    (metadata(N,O) -> true; throw(error(unsupported_directive(L,N,O)))), strip_metadata(Ss,Cs).
strip_metadata([S|Ss],[S|Cs]) :- strip_metadata(Ss,Cs).
metadata('.text',[]).
metadata('.globl',[symbol(_)]).
metadata('.global',[symbol(_)]).
metadata('.type',[symbol(_),kind(function)]).
metadata('.size',[symbol(N),sub(symbol('.'),symbol(N))]).
metadata('.section',[symbol('.note.GNU-stack'),string([]),kind(progbits)]).
functions([], [], []).
functions([located(L,label(N)),located(SignatureLine,signature(u64,Args))|Ss], [function(N,Args,IR)|Fs], [function(N,Args,Effects)|Es]) :- !,
    (c_name(N), memberchk(Args,[[ptr],[ptr,u64]]) -> true; throw(error(unsupported_signature(L,N,Args)))),
    initial_state(Args,State), body(Ss,Rest,State,0,SignatureLine,IR,Effects), functions(Rest,Fs,Es).
functions([S|_], _, _) :- throw(error(expected_annotated_function(S))).
c_name(A) :- atom_chars(A,[C|Cs]), letter(C), maplist(name_char,Cs).
letter(C) :- char_code(C,N), (N>=65,N=<90; N>=97,N=<122; C='_').
name_char(C) :- letter(C); char_code(C,N), N>=48,N=<57.
initial_state([ptr],[rdi-ptr(arg0)]).
initial_state([ptr,u64],[rdi-ptr(arg0),rsi-int(arg1)]).
% Lowering uses the effect relation's normalized action and typed reads/writes.
body([located(L,Instruction)|Ss],Rest,State,N,_,[IR|IRs],[located(L,Semantics)|Effects]) :-
    instruction(Instruction), !,
    catch(sp_effects:instruction_effects(Instruction,Semantics),
          error(Reason),throw(error(at(L,Reason)))),
    Semantics=semantics(Action,effects(registers(Reads,Writes),_,_,Control,_)),
    resolve_reads(Reads,State,Bindings,L), lower_action(Action,Bindings,N,L,IR),
    (Control=control(return) -> Rest=Ss, IRs=[], Effects=[]
    ; apply_writes(Writes,Bindings,v(N),State,Next), N1 is N+1,
      body(Ss,Rest,Next,N1,L,IRs,Effects)).
body([located(L,S)|_],_,_,_,_,_,_) :- throw(error(at(L,unsupported_control_flow(S)))).
body([],_,_,_,LastLine,_,_) :- throw(error(at(LastLine,missing_return))).
instruction(instruction(_,_)).
instruction(instruction(_,_,_)).

resolve_reads([],_,[],_).
resolve_reads([read(R,Type)|Rs],State,[binding(R,Value)|Bs],L) :-
    R=register(Root,W),
    (memberchk(Root-Found,State) -> true; throw(error(at(L,uninitialized_register(Root))))),
    (memberchk(Type,[integer,value]), Found=int(V) -> Value=view(V,W)
    ; memberchk(Type,[pointer,value]), Found=ptr(P), W=64 -> Value=pointer(P)
    ; throw(error(at(L,register_type(Root,expected(Type),actual(Found)))))),
    resolve_reads(Rs,State,Bs,L).
resolved(immediate(N),_,literal(V)) :- V is N mod 18446744073709551616.
resolved(register(R,W),Bs,V) :- memberchk(binding(register(R,W),V),Bs).
lower_action(load(address(B,I,K,O),Bytes,_),Bs,N,L,load(v(N),P,Index,K,O,Bytes,L)) :-
    resolved(B,Bs,pointer(P)), resolved(I,Bs,Index).
lower_action(store(address(B,I,K,O),Bytes,S),Bs,_,L,store(P,Index,K,O,Bytes,Value,L)) :-
    resolved(B,Bs,pointer(P)), resolved(I,Bs,Index), resolved(S,Bs,Value).
lower_action(pointer_load(address(B,I,K,O),_),Bs,N,L,pointer_load(v(N),P,Index,K,O,L)) :-
    resolved(B,Bs,pointer(P)), resolved(I,Bs,Index).
lower_action(pointer_store(address(B,I,K,O),S),Bs,_,L,pointer_store(P,Index,K,O,Value,L)) :-
    resolved(B,Bs,pointer(P)), resolved(I,Bs,Index), resolved(S,Bs,pointer(Value)).
lower_action(move(S,register(_,W)),Bs,N,L,assign(v(N),W,V,L)) :- resolved(S,Bs,V).
lower_action(copy(S,_),Bs,N,L,IR) :-
    resolved(S,Bs,Value),
    (Value=pointer(P) -> IR=pointer_copy(v(N),P,L)
    ; IR=assign(v(N),64,Value,L)).
lower_action(pointer_offset(address(B,I,K,O),_),Bs,N,L,pointer_offset(v(N),P,Index,K,O,L)) :-
    resolved(B,Bs,pointer(P)), resolved(I,Bs,Index).
lower_action(binary(K,S,R),Bs,N,L,binary(v(N),K,W,A,B,L)) :-
    R=register(_,W), resolved(R,Bs,A), resolved(S,Bs,B).
lower_action(shift(K,Count,R),Bs,N,L,binary(v(N),K,W,A,literal(Count),L)) :-
    R=register(_,W), resolved(R,Bs,A).
lower_action(return(R),Bs,_,_,return(V)) :- resolved(R,Bs,V).
apply_writes([],_,_,State,State).
apply_writes([write(register(Root,_),Type,_)|Ws],Bindings,V,State,Next) :-
    written_value(Type,Bindings,V,Typed), remove_reg(Root,State,Rest),
    apply_writes(Ws,Bindings,V,[Root-Typed|Rest],Next).
written_value(integer,_,V,int(V)).
written_value(pointer,_,V,ptr(V)).
written_value(same_type_as(R),Bindings,V,Typed) :-
    resolved(R,Bindings,Source),
    (Source=pointer(_) -> Typed=ptr(V); Source=view(_,_) -> Typed=int(V)).
remove_reg(_,[],[]).
remove_reg(R,[R-_|Ss],Rest) :- !, remove_reg(R,Ss,Rest).
remove_reg(R,[X|Ss],[X|Rest]) :- remove_reg(R,Ss,Rest).

% Compatibility entrypoints; access planning is independent of register lowering.
plan(Mode,IR,Plan) :- sp_accesses:plan(Mode,IR,Plan,_).
validate(IR,Plan) :- sp_accesses:validate(IR,Plan).
constant(E,N) :- sp_effects:constant(E,N).
