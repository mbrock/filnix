:- module(sp_cfg_tests, [tests/0]).
:- use_module(library(lists)).

must(G) :- (call(G) -> true; throw(error(cfg_assertion(G)))).
fails(G,R) :-
    catch((call(G),Outcome=returned),E,Outcome=threw(E)),
    must(Outcome=threw(error(R))).
lower(Body,G,Proof) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Chars),
    sp_parser:parse_chars(Chars,S),
    sp_cfg:lower(S,[function(p,_,G)],_,[Proof]).
rejects(Body,R) :- fails(lower(Body,_,_),R).

tests :-
    lower("cmpq $0,%rsi\nje .Lzero\nmovq $11,%rax\njmp .Ldone\n.Lzero:\nmovq $22,%rax\n.Ldone:\nret\n",G,P),
    G=cfg(Entry,[block(B,Names,Params,Ops,branch(C,EA,EB))|Rest]),
    must((member(block(J,[label('.Ldone',_)],JoinParams,_,_),Rest),
          memberchk(parameter(reg(rax),integer,param(J,reg(rax))),JoinParams))),
    fails(sp_cfg:validate_flow(cfg(Entry,[block(B,Names,Params,Ops,branch(C,EB,EA))|Rest]),P),
          invalid_control_flow(changed_target(_,_))),
    fails(sp_cfg:validate_flow(cfg(Entry,[block(B,Names,Params,Ops,branch(not(C),EA,EB))|Rest]),P),
          invalid_control_flow(changed_condition)),
    EA=edge(Target,[set(D,T,V)|Sets]),
    forall(member(Bad,[edge(Target,Sets),edge(Target,[set(D,wrong,V)|Sets]),
                       edge(Target,[set(wrong,T,V)|Sets]),edge(Target,[set(D,T,literal(0))|Sets])]),
           fails(sp_cfg:validate_flow(cfg(Entry,[block(B,Names,Params,Ops,branch(C,Bad,EB))|Rest]),P),
                 invalid_control_flow(_))),
    fails(sp_cfg:validate_flow(cfg(Entry,Rest),P),invalid_control_flow(changed_blocks)),
    fails(sp_cfg:validate_flow(_,P),invalid_control_flow(non_ground)),
    lower("testq %rsi,%rsi\nje .Lleft\nmovq 8(%rdi),%r8 #! ptr\njmp .Ljoin\n.Lleft:\nmovq (%rdi),%r8 #! ptr\n.Ljoin:\nmovzbl (%r8),%eax\nret\n",PG,_),
    must((PG=cfg(_,PB),member(block(PJ,[label('.Ljoin',_)],PP,_,_),PB),
          memberchk(parameter(reg(r8),pointer,param(PJ,reg(r8))),PP))),
    % Dead blocks never contribute values to joins; every instruction is
    % nevertheless decoded and its declared instruction form checked.
    lower("movq $9,%rax\njmp .Llive\n.Ldead:\nmovq (%rsi),%rax\njmp .Ldead\n.Llive:\nret\n",DG,_),
    must((DG=cfg(_,DB),\+ (member(block(_,Ls,_,_,_),DB),member(label('.Ldead',_),Ls)))),
    rejects("movq $9,%rax\njmp .Llive\n.Ldead:\nud2\n.Llive:\nret\n",at(5,unsupported_instruction(ud2))),
    rejects("jmp .Lmissing\n",at(2,unknown_label('.Lmissing'))),
    rejects("je p\n",at(2,missing_fallthrough)),
    lower("jmp p\n",_,_),
    rejects(".Lsame:\n.Lsame:\nmovq $1,%rax\nret\n",at(3,duplicate_label('.Lsame'))),
    rejects("je .Lyes\nmovq $0,%rax\n.Lyes:\nret\n",at(2,unavailable_flag(zf))),
    rejects("movq %rsi,%rax\ncmpq $0,%rax\nshlq $2,%rax\njo .Lyes\nret\n.Lyes:\nret\n",
            at(5,unavailable_flag(of))),
    rejects("testq %rsi,%rsi\nje .Ljoin\nmovq $1,%rax\n.Ljoin:\nret\n",
            at(6,uninitialized_register(rax))),
    rejects("testq %rsi,%rsi\nje .Lleft\nmovq $1,%rax\njmp .Ljoin\n.Lleft:\nmovq %rdi,%rax\n.Ljoin:\nret\n",
            at(9,incompatible_register_types(rax,[integer,pointer]))),
    lower("testq %rsi,%rsi\nje .Lleft\nmovq $1,%rax\njmp .Ljoin\n.Lleft:\nmovq %rdi,%rax\n.Ljoin:\nmovq $9,%rax\nret\n",_,_),
    rejects("movq %rsi,%rax\ntestq %rsi,%rsi\nje .Lleft\nshlq $2,%rax\njmp .Ljoin\n.Lleft:\naddq $1,%rax\n.Ljoin:\nmovq $7,%rax\njo .Lyes\nret\n.Lyes:\nret\n",
            at(11,unavailable_flag(of))),
    sp_effects:instruction_effects(instruction(shll,[imm(const(32)),reg(eax)]),Zero),
    sp_flags:transfer(Zero,[],1,1,[of-old],[],[of-old]),
    write('control-flow checks: ok'),nl.
