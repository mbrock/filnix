:- module(sp_check_model, [model/2, access/4, candidate/3, operation/3, incoming/3,
                          event/2, pullback/4, cycle_edge/3, valid_requirement/1]).
:- use_module(library(lists)).

% This is the semantic boundary for protection analysis. It describes the
% normal continuation of a checked access, not a machine-check instruction.
% The analyzed graph has already passed typed lowering and access validation.
model(cfg(Entry,Blocks),model(Blocks,Arcs)) :-
    findall(arc(B,Arm,T,Copies),
            (member(block(B,_,_,_,Term),Blocks),edge(Term,Arm,edge(T,Copies))),Normal),
    Entry=edge(B,C),Arcs=[arc(entry,entry,B,C)|Normal].
edge(jump(E),jump,E).
edge(branch(_,A,_),true,A).
edge(branch(_,_,B),false,B).
operation(model(Blocks,_),site(B,N),Op) :-
    memberchk(block(B,_,_,Ops,_),Blocks),nth0(N,Ops,Op).
incoming(model(_,Arcs),B,Incoming) :- include_target(Arcs,B,Incoming).
include_target([],_,[]).
include_target([arc(P,A,B,C)|Xs],T,Result) :-
    (B==T -> Result=[arc(P,A,B,C)|Ys];Result=Ys),include_target(Xs,T,Ys).

access(Model,Site,Requirement,After) :-
    Model=model(Blocks,_),member(block(B,_,_,Ops,_),Blocks),nth0(N,Ops,Op),
    Site=site(B,N),event(Op,effect(access(Requirement),After)).
candidate(Model,Site,R) :- access(Model,Site,R,preserve),valid_requirement(R).
event(read(P,I,S,O,W,_),effect(access(R),preserve)) :- !,
    requirement(P,I,S,O,W,read,1,integer,R).
event(store(P,I,S,O,W,_,_),effect(access(R),invalidate(store))) :- !,
    requirement(P,I,S,O,W,write,1,integer,R).
event(pointer_load(_,P,I,S,O,_),effect(access(R),invalidate(pointer_load))) :- !,
    requirement(P,I,S,O,8,read,8,pointer,R).
event(pointer_store(P,I,S,O,_,_),effect(access(R),invalidate(pointer_store))) :- !,
    requirement(P,I,S,O,8,write,8,pointer,R).
event(pointer_copy(_,_,_),effect(none,invalidate(pointer_copy))) :- !.
event(pointer_offset(_,_,_,_,_,_),effect(none,invalidate(pointer_offset))) :- !.
event(assign(_,_,_,_),effect(none,preserve)) :- !.
event(binary(_,_,_,_,_,_),effect(none,preserve)) :- !.
event(flag_values(_,_,_,_,_,_),effect(none,preserve)) :- !.
% Includes calls, frees, safepoints, concurrent mutation and future operations.
event(Op,effect(none,invalidate(unknown(Op)))).
requirement(P,I,S,O,W,Permission,Align,Kind,
            protection(value(P),capability(P),index(Index,S),range(O,End),permission(Permission),
                       alignment(Align),kind(Kind))) :-
    normalize(I,Index),End is O+W.
valid_requirement(protection(value(P),capability(P),index(_,S),range(O,E),permission(Perm),
                             alignment(A),kind(K))) :-
    integer(O),integer(E),O>=0,E>O,E=<9223372036854775807,
    memberchk(S,[1,2,4,8]),memberchk(Perm,[read,write]),
    memberchk(A,[1,8]),memberchk(K,[integer,pointer]).

% Pull a target's block-parameter identities back through one actual edge.
% Local definitions cannot be guessed equal to values from an earlier block.
pullback(B,Copies,
         protection(value(P),capability(C),index(I,S),R,Perm,A,K),
         protection(value(P1),capability(C1),index(I1,S),R,Perm,A,K)) :-
    input_value(B,Copies,pointer,P,P1),input_value(B,Copies,pointer,C,C1),
    input_value(B,Copies,integer,I,I1).
input_value(B,C,Type,param(B,reg(R)),V) :- !,
    memberchk(set(param(B,reg(R)),Type,Source),C),normalize(Source,V).
input_value(_,_,integer,literal(N),literal(N)) :- !.
input_value(B,C,integer,view(V,W),Out) :- !,
    input_value(B,C,integer,V,X),normalize(view(X,W),Out).
normalize(view(V,W),Out) :- !,normalize(V,X),
    (X=literal(N) -> Value is N mod (2^W),Out=literal(Value)
    ; X=view(Base,Inner) -> Width is min(W,Inner),normalize(view(Base,Width),Out)
    ; W=64 -> Out=X
    ; Out=view(X,W)).
normalize(V,V).

% Any edge belonging to a cycle is a conservative polling barrier, including
% irreducible cycles. Traversal has an explicit visited set and always ends.
cycle_edge(Model,From,To) :-
    Model=model(_,Arcs),memberchk(arc(From,_,To,_),Arcs),reachable([To],From,Model,[]).
reachable([Target|_],Target,_,_) :- !.
reachable([B|Bs],Target,Model,Seen) :-
    (memberchk(B,Seen) -> reachable(Bs,Target,Model,Seen)
    ; Model=model(_,Arcs),findall(T,member(arc(B,_,T,_),Arcs),Next),
      append(Next,Bs,Queue),reachable(Queue,Target,Model,[B|Seen])).
