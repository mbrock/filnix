:- module(sp_flags, [branch_opcode/2, condition_reads/2, condition/4, transfer/7, bit/2]).
:- use_module(library(lists)).

branch_opcode(je,e).   branch_opcode(jne,ne).
branch_opcode(jb,b).   branch_opcode(jae,ae).
branch_opcode(jbe,be). branch_opcode(ja,a).
branch_opcode(jl,l).   branch_opcode(jge,ge).
branch_opcode(jle,le). branch_opcode(jg,g).
branch_opcode(js,s).   branch_opcode(jns,ns).
branch_opcode(jo,o).   branch_opcode(jno,no).
branch_opcode(jp,p).   branch_opcode(jnp,np).

formula(e,flag(zf)). formula(ne,not(flag(zf))).
formula(b,flag(cf)). formula(ae,not(flag(cf))).
formula(be,either(flag(cf),flag(zf))).
formula(a,not(either(flag(cf),flag(zf)))).
formula(l,different(flag(sf),flag(of))).
formula(ge,not(different(flag(sf),flag(of)))).
formula(le,either(flag(zf),different(flag(sf),flag(of)))).
formula(g,not(either(flag(zf),different(flag(sf),flag(of))))).
formula(s,flag(sf)). formula(ns,not(flag(sf))).
formula(o,flag(of)). formula(no,not(flag(of))).
formula(p,flag(pf)). formula(np,not(flag(pf))).
condition_reads(C,Reads) :- formula(C,F), findall(X,used(F,X),Xs),sort(Xs,Reads).
used(flag(F),F).
used(not(X),F) :- used(X,F).
used(either(X,Y),F) :- (used(X,F);used(Y,F)).
used(different(X,Y),F) :- (used(X,F);used(Y,F)).
condition(C,State,L,Expr) :- formula(C,F), bind(F,State,L,Expr).
bind(flag(F),State,L,truth(V)) :-
    (memberchk(F-V,State) -> true; throw(error(at(L,unavailable_flag(F))))).
bind(not(X),S,L,not(A)) :- bind(X,S,L,A).
bind(either(X,Y),S,L,either(A,B)) :- bind(X,S,L,A),bind(Y,S,L,B).
bind(different(X,Y),S,L,different(A,B)) :- bind(X,S,L,A),bind(Y,S,L,B).

% The effect partition controls availability; recipes compute the values.
% Undefined flags disappear, preserved flags retain their value identities.
transfer(semantics(Action,effects(_,_,Flags,_,_)),Bindings,N,L,Old,Ops,Next) :-
    Flags=flags(reads(Reads),defined(D),cleared(C),undefined(U),preserved(_)),
    forall(member(F,Reads),
        (memberchk(F-_,Old) -> true; throw(error(at(L,unavailable_flag(F)))))),
    append(D,C,Known), append(Known,U,Changed),
    findall(F-V,(member(F-V,Old),\+memberchk(F,Changed)),Kept),
    findall(F-flag_value(N,F),member(F,Known),Values), append(Values,Kept,Next),
    (Known=[] -> Ops=[]
    ; recipe(Action,Bindings,K,W,A,B) -> Ops=[flag_values(N,K,W,A,B,L)]
    ; throw(error(at(L,missing_flag_recipe(Action))))).
recipe(binary(K,S,R),Bs,K,W,A,B) :-
    R=register(_,W), sp_ir:resolved(R,Bs,A),sp_ir:resolved(S,Bs,B).
recipe(compare(K,S,R),Bs,K,W,A,B) :-
    R=register(_,W), sp_ir:resolved(R,Bs,A),sp_ir:resolved(S,Bs,B).
recipe(shift(K,C,R),Bs,K,W,A,literal(C)) :-
    R=register(_,W), sp_ir:resolved(R,Bs,A).
bit(cf,0). bit(pf,2). bit(af,4). bit(zf,6). bit(sf,7). bit(of,11).
