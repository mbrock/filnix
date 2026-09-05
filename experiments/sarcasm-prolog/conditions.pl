:- module(sp_conditions, [optimize/4, validate/3]).
:- use_module(library(lists)).

% Only simplify a formula whose flag identities all name one local CMP.
% The captured operands remain valid even if the source registers change.
optimize(Mode,Original,Result,Proof) :-
    require((ground(Mode-Original),memberchk(Mode,[on,off])),arguments),
    Original=cfg(Entry,Blocks),Result=cfg(Entry,Next),
    maplist(propose_block(Mode),Blocks,Next,Proof),validate(Original,Result,Proof).
propose_block(Mode,block(B,N,P,Ops,Term),block(B,N,P,Ops,Next),Decision) :-
    (Mode=on,Term=branch(C,T,F),proposal(Ops,C,Id,Replacement) ->
       Next=branch(Replacement,T,F),Decision=rewrite(B,Id)
    ; Next=Term,Decision=keep(B)).
proposal(Ops,Condition,Id,comparison(Sign,Relation,W,A,B)) :-
    member(flag_values(Id,sub,W,A,B,_),Ops),
    relation(C,Sign,Relation),
    findall(F-flag_value(Id,F),member(F,[cf,pf,af,zf,sf,of]),State),
    sp_flags:condition(C,State,0,Formula),Condition==Formula.
relation(e,unsigned,eq). relation(ne,unsigned,ne).
relation(b,unsigned,lt). relation(ae,unsigned,ge).
relation(be,unsigned,le). relation(a,unsigned,gt).
relation(l,signed,lt). relation(ge,signed,ge).
relation(le,signed,le). relation(g,signed,gt).

% Validation checks the proposed graph and an explicit producer witness.
% It does not call proposal/4, relation/3 or the formula construction above.
validate(Original,Result,Proof) :-
    require(ground(Original-Result-Proof),non_ground),
    (check(Original,Result,Proof) -> true;throw(error(invalid_condition_rewrite(structure)))).
check(cfg(E,Bs),cfg(F,Cs),Proof) :-
    require(E==F,changed_entry),require((same_length(Bs,Cs),same_length(Bs,Proof)),changed_blocks),
    maplist(check_block,Bs,Cs,Proof).
check_block(block(B,N,P,Ops,T),block(C,M,Q,Other,U),Proof) :-
    require(B-N-P-Ops==C-M-Q-Other,changed_block(B)),
    (Proof=keep(B) -> require(T==U,changed_kept_condition(B))
    ; Proof=rewrite(B,Id),T=branch(Old,Yes,No),U=branch(New,A,Z),
      require(Yes-No==A-Z,changed_edges(B)),
      findall(Op,(member(Op,Ops),Op=flag_values(Id,_,_,_,_,_)),Producers),
      require(Producers=[flag_values(Id,sub,W,L,R,_)],invalid_producer(B,Id)),
      require(memberchk(W,[32,64]),invalid_width(W)),
      require(equivalent(Old,New,Id,W,L,R),changed_comparison(B))).
equivalent(truth(flag_value(N,zf)),comparison(unsigned,eq,W,A,B),N,W,A,B).
equivalent(not(truth(flag_value(N,zf))),comparison(unsigned,ne,W,A,B),N,W,A,B).
equivalent(truth(flag_value(N,cf)),comparison(unsigned,lt,W,A,B),N,W,A,B).
equivalent(not(truth(flag_value(N,cf))),comparison(unsigned,ge,W,A,B),N,W,A,B).
equivalent(either(truth(flag_value(N,cf)),truth(flag_value(N,zf))),comparison(unsigned,le,W,A,B),N,W,A,B).
equivalent(not(either(truth(flag_value(N,cf)),truth(flag_value(N,zf)))),comparison(unsigned,gt,W,A,B),N,W,A,B).
equivalent(different(truth(flag_value(N,sf)),truth(flag_value(N,of))),comparison(signed,lt,W,A,B),N,W,A,B).
equivalent(not(different(truth(flag_value(N,sf)),truth(flag_value(N,of)))),comparison(signed,ge,W,A,B),N,W,A,B).
equivalent(either(truth(flag_value(N,zf)),different(truth(flag_value(N,sf)),truth(flag_value(N,of)))),comparison(signed,le,W,A,B),N,W,A,B).
equivalent(not(either(truth(flag_value(N,zf)),different(truth(flag_value(N,sf)),truth(flag_value(N,of))))),comparison(signed,gt,W,A,B),N,W,A,B).
require(G,R) :- (call(G) -> true;throw(error(invalid_condition_rewrite(R)))).
