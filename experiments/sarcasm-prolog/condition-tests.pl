:- module(sp_condition_tests, [tests/0]).
:- use_module(library(lists)).
must(G) :- (call(G) -> true;throw(error(condition_assertion(G)))).
reject(G) :- catch((call(G),Outcome=returned),error(invalid_condition_rewrite(_)),Outcome=rejected),
             must(Outcome==rejected).
graph(Body,G) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Text),
    sp_parser:parse_chars(Text,S),sp_cfg:lower(S,[function(p,_,G)],_).
tests :-
    graph("movq %rsi,%rax\ncmpq $63,%rax\nmovq $0,%rax\nja .Lyes\nret\n.Lyes:\nmovq $1,%rax\nret\n",G),
    sp_conditions:optimize(on,G,R,Proof),
    G=cfg(E,[block(B,N,P,Ops,branch(Old,T,F))|Bs]),
    R=cfg(E,[block(B,N,P,Ops,branch(New,T,F))|Bs]),
    Proof=[rewrite(B,Id)|Rest],New=comparison(unsigned,gt,64,A,literal(63)),
    must(A\==literal(0)),
    sp_conditions:optimize(off,G,Unchanged,Keep),must(G==Unchanged),
    reject(sp_conditions:validate(G,R,Keep)),
    forall(member(Wrong,[comparison(unsigned,ge,64,A,literal(63)),
                         comparison(signed,gt,64,A,literal(63)),
                         comparison(unsigned,gt,32,A,literal(63)),
                         comparison(unsigned,gt,64,literal(0),literal(63)),
                         comparison(unsigned,gt,64,literal(63),A)]),
      reject(sp_conditions:validate(G,cfg(E,[block(B,N,P,Ops,branch(Wrong,T,F))|Bs]),Proof))),
    reject(sp_conditions:validate(G,cfg(E,[block(B,N,P,Ops,branch(New,F,T))|Bs]),Proof)),
    reject(sp_conditions:validate(G,cfg(E,[block(B,N,P,[],branch(New,T,F))|Bs]),Proof)),
    reject(sp_conditions:validate(G,R,[rewrite(B,999)|Rest])),
    reject(sp_conditions:validate(G,_,Proof)),
    % Mixed producer flags cannot become one compare, even with a plausible
    % local CMP. A flag parameter from a predecessor also remains a formula.
    Mixed=either(truth(flag_value(Id,cf)),truth(flag_value(999,zf))),
    MG=cfg(E,[block(B,N,P,Ops,branch(Mixed,T,F))|Bs]),
    sp_conditions:optimize(on,MG,MR,_),must(MR==MG),
    reject(sp_conditions:validate(MG,R,Proof)),
    forall(member(Middle,["addq $1,%rax\n", ".Ljoin:\n"]),
      (append("movq %rsi,%rax\ncmpq $63,%rax\n",Middle,Prefix),
       append(Prefix,"ja .Lyes\nret\n.Lyes:\nmovq $1,%rax\nret\n",Body),
       graph(Body,No),sp_conditions:optimize(on,No,Same,_),must(No==Same))),
    must(Old\==New),write('condition rewrite checks: ok'),nl.
