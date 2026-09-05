:- module(sp_ir, [lower/2, plan/3, validate/2, constant/2]).
:- use_module(library(lists)).

% Scalar SSA values distinguish changing registers from immutable address inputs.
lower(Statements, Functions) :- strip_metadata(Statements, Code), functions(Code, Functions),
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
functions([], []).
functions([located(L,label(N)),located(_,signature(u64,Args))|Ss], [function(N,Args,IR)|Fs]) :- !,
    (c_name(N), memberchk(Args,[[ptr],[ptr,u64]]) -> true; throw(error(unsupported_signature(L,N,Args)))),
    initial_state(Args,State), body(Ss,Rest,State,0,IR), functions(Rest,Fs).
functions([S|_], _) :- throw(error(expected_annotated_function(S))).
c_name(A) :- atom_chars(A,[C|Cs]), letter(C), maplist(name_char,Cs).
letter(C) :- char_code(C,N), (N>=65,N=<90; N>=97,N=<122; C='_').
name_char(C) :- letter(C); char_code(C,N), N>=48,N=<57.
initial_state([ptr],[rdi-ptr(arg0)]).
initial_state([ptr,u64],[rdi-ptr(arg0),rsi-int(arg1)]).
body([located(L,instruction(ret,[]))|Rest],Rest,S,_,[return(V)]) :- !, integer_reg(rax,S,V,L).
body([located(L,instruction(Op,Args))|Ss],Rest,S,N,[IR|IRs]) :- !,
    (step(Op,Args,L,S,N,S1,IR) -> true; throw(error(unsupported_instruction(L,Op,Args)))),
    N1 is N+1, body(Ss,Rest,S1,N1,IRs).
body([S|_],_,_,_,_) :- throw(error(unsupported_control_flow(S))).
body([],_,_,_,_) :- throw(error(missing_return)).

% Only whole 32/64-bit destination writes: x86-64 32-bit writes zero-extend.
alias(rax,rax,64). alias(eax,rax,32).
alias(rcx,rcx,64). alias(ecx,rcx,32).
alias(rdx,rdx,64). alias(edx,rdx,32).
alias(rsi,rsi,64). alias(esi,rsi,32).
alias(rdi,rdi,64). alias(edi,rdi,32).
alias(r8,r8,64). alias(r8d,r8,32).
alias(r9,r9,64). alias(r9d,r9,32).
alias(r10,r10,64). alias(r10d,r10,32).
alias(r11,r11,64). alias(r11d,r11,32).
integer_reg(R,S,view(V,W),L) :-
    (alias(R,Root,W), memberchk(Root-int(V),S) -> true; throw(error(non_integer_or_uninitialized_register(L,R)))).
set_reg(R,V,S,[Root-int(V)|Rest]) :- alias(R,Root,_), remove_reg(Root,S,Rest).
remove_reg(_,[],[]).
remove_reg(R,[R-_|Ss],Rest) :- !, remove_reg(R,Ss,Rest).
remove_reg(R,[X|Ss],[X|Rest]) :- remove_reg(R,Ss,Rest).
input(reg(R),S,V,L) :- integer_reg(R,S,V,L).
input(imm(E),_,literal(N),_) :- constant(E,V), N is V mod 18446744073709551616.
constant(const(N),N).
constant(neg(A),N) :- constant(A,X), N is -X.
constant(add(A,B),N) :- constant(A,X), constant(B,Y), N is X+Y.
constant(sub(A,B),N) :- constant(A,X), constant(B,Y), N is X-Y.
constant(mul(A,B),N) :- constant(A,X), constant(B,Y), N is X*Y.
address(mem(D,B,I,Sc),S,P,Idx,Scale,Off,L) :-
    alias(B,Root,64), memberchk(Root-ptr(P),S),
    (I=none -> Idx=literal(0); alias(I,_,64), integer_reg(I,S,Idx,L)),
    constant(Sc,Scale), memberchk(Scale,[1,2,4,8]), constant(D,Off),
    Off>=0, Off=<18446744073709551615.
load_kind(movzbl,1,32). load_kind(movzwl,2,32).
load_kind(movl,4,32). load_kind(movq,8,64).
step(Op,[Mem,reg(D)],L,S,N,S1,load(v(N),P,I,K,O,W,L)) :-
    load_kind(Op,W,DW), Mem=mem(_,_,_,_), alias(D,_,DW),
    address(Mem,S,P,I,K,O,L), set_reg(D,v(N),S,S1).
step(Op,[Src,reg(D)],L,S,N,S1,assign(v(N),W,V,L)) :-
    memberchk(Op-W,[movq-64,movl-32]), alias(D,_,W),
    input(Src,S,V,L), source_width(Src,W), move_immediate(Src,W), set_reg(D,v(N),S,S1).
step(Op,[Src,reg(D)],L,S,N,S1,binary(v(N),Kind,W,A,B,L)) :-
    operation(Op,Kind,W), alias(D,_,W), integer_reg(D,S,A,L), input(Src,S,B,L),
    source_width(Src,W), arithmetic_operand(Kind,Src,W), set_reg(D,v(N),S,S1).
source_width(imm(_),_).
source_width(reg(R),W) :- alias(R,_,W).
move_immediate(reg(_),_).
move_immediate(imm(E),W) :- constant(E,N), Min is -(2^(W-1)), Max is 2^W-1, N>=Min, N=<Max.
arithmetic_operand(K,imm(E),_) :- memberchk(K,[shl,shr]), !, constant(E,N), N>=0, N=<255.
arithmetic_operand(K,reg(_),_) :- K \= shl, K \= shr.
arithmetic_operand(K,imm(E),W) :- K \= shl, K \= shr, constant(E,N),
    (W=64 -> Max=2147483647; Max=4294967295), N>= -2147483648, N=<Max.
operation(addq,add,64). operation(addl,add,32).
operation(xorq,xor,64). operation(xorl,xor,32).
operation(orq,or,64). operation(orl,or,32).
operation(andq,and,64). operation(andl,and,32).
operation(shlq,shl,64). operation(shrq,shr,64).
operation(shll,shl,32). operation(shrl,shr,32).

% The optimizer proposes a partition. It never emits unchecked accesses.
plan(off, IR, Plan) :- !, individual(IR,Plan).
plan(on, [], []).
plan(on, [load(V,P,I,K,O,W,L)|Xs], [read(P,I,K,O,Total,Loads)|Ys]) :- !,
    (member(Total,[8,4,2]), Total>W,
     adjacent([load(V,P,I,K,O,W,L)|Xs],P,I,K,O,Total,Loads,Rest) -> true
    ; Total=W, Loads=[load(V,P,I,K,O,W,L)], Rest=Xs),
    plan(on,Rest,Ys).
plan(on,[X|Xs],[X|Ys]) :- plan(on,Xs,Ys).
individual([],[]).
individual([load(V,P,I,K,O,W,L)|Xs],[read(P,I,K,O,W,[load(V,P,I,K,O,W,L)])|Ys]) :- !, individual(Xs,Ys).
individual([X|Xs],[X|Ys]) :- individual(Xs,Ys).
adjacent(Rest,_,_,_,_,0,[],Rest) :- !.
adjacent([load(V,P,I,K,O,W,L)|Xs],P,I,K,O,Remaining,[load(V,P,I,K,O,W,L)|Ls],Rest) :-
    W=<Remaining, Next is O+W, Left is Remaining-W,
    adjacent(Xs,P,I,K,Next,Left,Ls,Rest).

% Independent validation: exact ordered provenance, extent and coverage.
% This is a must-hold check on ground IR; failed/incomplete proofs reject.
validate(IR,Plan) :-
    (ground(IR-Plan), checked(IR,Plan) -> true; throw(error(invalid_access_plan))).
checked([],[]).
checked(IR,[read(P,I,K,O,W,Loads)|Plans]) :- !,
    Loads=[_|_], memberchk(W,[1,2,4,8]), append(Loads,Rest,IR),
    maplist(same_access(P,I,K),Loads),
    findall(A-B, (member(load(_,_,_,_,A,Size,_),Loads),B is A+Size), Intervals),
    coverage(Intervals,O,End), End =:= O+W, End=<18446744073709551616,
    checked(Rest,Plans).
checked([X|Xs],[X|Ps]) :- X \= load(_,_,_,_,_,_,_), checked(Xs,Ps).
same_access(P,I,K,load(_,P,I,K,_,_,_)).
coverage([],End,End).
coverage([Start-End|Xs],Start,Final) :- End>Start, coverage(Xs,End,Final).
