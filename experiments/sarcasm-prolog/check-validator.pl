:- module(sp_check_validator, [validate/2]).
:- use_module(library(lists)).

% Follow a supplied certificate, checking local obligations. No candidate
% enumeration, witness search, or optimizer coverage predicate is called.
validate(Graph,Proof) :-
    require(ground(Graph-Proof),non_ground),
    (checked(Graph,Proof) -> true;throw(error(invalid_protection(structure)))).
checked(Graph,reuse(Target,Need,retained_offset_guard(Guard),Witness,Tree)) :-
    sp_check_model:model(Graph,M),
    require(Guard==Target,changed_offset_guard),
    require(sp_check_model:access(M,Target,Actual,_),missing_access(Target)),
    require(Need==Actual,changed_requirement(Target)),
    require(sp_check_model:valid_requirement(Need),unrepresentable_requirement),
    check_path(M,Target,Need,Witness,Tree).
check_path(M,site(B,N),Need,Witness,checked(Site,Claim)) :-
    Prev is N-1,require((N>0,Site==site(B,Prev),Site==Witness),changed_witness),
    require(sp_check_model:operation(M,Site,Op),missing_witness),
    sp_check_model:event(Op,Effect),
    require(Effect==effect(access(Claim),preserve),changed_witness_effect),
    require(sp_check_model:valid_requirement(Claim),invalid_witness_requirement),
    covered(Claim,Need).
check_path(M,site(B,N),Need,Witness,through(Site,Effect,Tail)) :-
    Prev is N-1,require((N>0,Site==site(B,Prev)),changed_interval),
    require(sp_check_model:operation(M,Site,Op),missing_operation),
    sp_check_model:event(Op,Actual),
    require(Effect==Actual,changed_effect),
    require(Actual=effect(_,preserve),invalidating_effect(Site)),
    check_path(M,Site,Need,Witness,Tail).
check_path(M,site(B,N),Need,Witness,incoming(Id,Paths)) :-
    require((N=:=0,Id==B),changed_join),
    sp_check_model:incoming(M,B,Arcs),
    findall(A,member(via(A,_,_),Paths),Recorded),
    require((Arcs=[_|_],Recorded==Arcs,same_length(Arcs,Paths)),missing_predecessor(B)),
    maplist(check_arc(M,B,Need,Witness),Arcs,Paths).
check_arc(M,B,Need,Witness,arc(P,Arm,B,C),via(Arc,Before,Proof)) :-
    require(Arc==arc(P,Arm,B,C),changed_edge),
    require(P\==entry,unprotected_entry),
    require(\+sp_check_model:cycle_edge(M,P,B),polling_edge(P,B)),
    require(sp_check_model:pullback(B,C,Need,Expected),value_not_at_entry(B)),
    require(Before==Expected,changed_edge_requirement),
    M=model(Blocks,_),memberchk(block(P,_,_,Ops,_),Blocks),length(Ops,N),
    check_path(M,site(P,N),Before,Witness,Proof).
covered(protection(value(P),capability(C),index(I,S),range(L,H),permission(R),alignment(A),kind(K)),
        protection(value(Q),capability(D),index(J,T),range(O,E),permission(U),alignment(B),kind(V))) :-
    require(P==Q,changed_pointer),require(C==D,changed_capability),
    require(I-S==J-T,changed_index),require(R==U,wrong_permission),require(K==V,wrong_access_kind),
    require((L=<O,H>=E),insufficient_range),
    require((A>=B,A mod B=:=0,(O-L) mod B=:=0),insufficient_alignment).
require(G,R) :- (call(G) -> true;throw(error(invalid_protection(R)))).
