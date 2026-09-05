:- module(sp_check_reuse, [analyze/2, analyze/3]).
:- use_module(library(lists)).

% A bounded witness search. Rejection is data, so it cannot roll back the
% resource counter; exceptions and exhaustion never become an empty proof.
analyze(Graph,Report) :- analyze(Graph,100000,Report).
analyze(Graph,Limit,report(Decisions,steps(Used,Limit))) :-
    require((ground(Graph-Limit),integer(Limit),Limit>=0),check_analysis_arguments),
    sp_check_model:model(Graph,Model),
    findall(S-R,sp_check_model:access(Model,S,R,_),Accesses),
    findall(S-R,sp_check_model:candidate(Model,S,R),Candidates),
    decisions(Accesses,Candidates,Model,Limit,Left,Decisions),
    Used is Limit-Left,
    forall(member(decision(_,covered(Proof)),Decisions),sp_check_validator:validate(Graph,Proof)).
decisions([],_,_,F,F,[]).
decisions([S-R|Xs],Candidates,M,F0,F,[decision(S,Outcome)|Ds]) :-
    (sp_check_model:valid_requirement(R) ->
       choose(Candidates,M,S,R,F0,F1,Outcome)
    ; Outcome=retained(unrepresentable_requirement(R)),F1=F0),
    decisions(Xs,Candidates,M,F1,F,Ds).
choose([],_,_,_,F,F,retained(no_dominating_covering_check)).
choose([Witness-_|Xs],M,S,R,F0,F,Outcome) :-
    path(M,S,R,Witness,F0,F1,Attempt),
    (Attempt=accepted(Tree) -> Outcome=covered(reuse(S,R,retained_offset_guard(S),Witness,Tree)),F=F1
    ; Attempt=rejected(_),choose(Xs,M,S,R,F1,F,Outcome)).
path(M,site(B,N),R,W,F0,F,Outcome) :-
    tick(F0,F1),
    (N>0 ->
       Prev is N-1,Site=site(B,Prev),sp_check_model:operation(M,Site,Op),
       sp_check_model:event(Op,Effect),
       (Effect=effect(_,invalidate(Why)) -> Outcome=rejected(barrier(Site,Why)),F=F1
       ; Site==W ->
           (Effect=effect(access(Have),preserve),covers(Have,R) ->
              Outcome=accepted(checked(Site,Have))
           ; Outcome=rejected(not_covering(Site))),F=F1
       ; path(M,Site,R,W,F1,F,Tail),
         (Tail=accepted(P) -> Outcome=accepted(through(Site,Effect,P));Outcome=Tail))
    ; sp_check_model:incoming(M,B,Arcs),
      paths(Arcs,M,B,R,W,F1,F,Paths),
      (Paths=accepted(Ps) -> Outcome=accepted(incoming(B,Ps));Outcome=Paths)).
paths([],_,_,_,_,F,F,accepted([])).
paths([arc(P,Arm,B,C)|Xs],M,B,R,W,F0,F,Outcome) :-
    tick(F0,F1),
    (P=entry -> Outcome=rejected(unprotected_entry),F=F1
    ; sp_check_model:cycle_edge(M,P,B) -> Outcome=rejected(polling_edge(P,B)),F=F1
    ; sp_check_model:pullback(B,C,R,Before) ->
      M=model(Blocks,_),memberchk(block(P,_,_,Ops,_),Blocks),length(Ops,N),
      path(M,site(P,N),Before,W,F1,F2,Here),
      (Here=accepted(Proof) ->
         paths(Xs,M,B,R,W,F2,F,Rest),
         (Rest=accepted(Ps) -> Outcome=accepted([via(arc(P,Arm,B,C),Before,Proof)|Ps]);Outcome=Rest)
      ; Outcome=Here,F=F2)
    ; Outcome=rejected(value_not_at_entry(B)),F=F1).
covers(protection(value(P),capability(C),index(I,S),range(L,H),permission(Perm),alignment(A),kind(K)),
       protection(value(P),capability(C),index(I,S),range(O,E),permission(Perm),alignment(B),kind(K))) :-
    L=<O,E=<H,A mod B=:=0,(O-L) mod B=:=0.
tick(F0,F) :- require(F0>0,check_analysis_limit),F is F0-1.
require(G,R) :- (call(G) -> true;throw(error(R))).
