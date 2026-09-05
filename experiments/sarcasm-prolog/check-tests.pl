:- module(sp_check_tests, [tests/0]).
:- use_module(library(lists)).
must(G) :- (call(G) -> true;throw(error(check_assertion(G)))).
fails(G,R) :-
    catch((call(G),Outcome=returned),E,Outcome=threw(E)),
    must(Outcome=threw(error(R))).
graph(Body,G) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Text),
    sp_parser:parse_chars(Text,S),sp_cfg:lower(S,[F],_),
    sp_cfg:prepare(off,F,function(p,_,G),_).
proof(G,P) :-
    sp_check_reuse:analyze(G,report(Ds,_)),member(decision(_,covered(P)),Ds).
uncovered(Body) :-
    graph(Body,G),sp_check_reuse:analyze(G,report(Ds,_)),
    must(\+member(decision(_,covered(_)),Ds)).
replace_claim(checked(S,_),Have,checked(S,Have)).
replace_claim(through(S,E,T),Have,through(S,E,U)) :- replace_claim(T,Have,U).

tests :-
    graph("movq (%rdi),%rax\naddq %rsi,%rax\nmovzbl 3(%rdi),%ecx\naddq %rcx,%rax\nret\n",G),
    copy_term(G,Original),proof(G,P),must(G==Original),
    P=reuse(Target,Need,Guard,Witness,Tree),
    must(Target==site(0,3)),must(Witness==site(0,0)),
    Need=protection(V,C,I,R,Perm,A,K),
    forall(member(Bad,[protection(value(other),C,I,R,Perm,A,K),
                       protection(V,capability(other),I,R,Perm,A,K),
                       protection(V,C,index(literal(1),1),R,Perm,A,K),
                       protection(V,C,I,range(3,9),Perm,A,K),
                       protection(V,C,I,R,permission(write),A,K),
                       protection(V,C,I,R,Perm,alignment(8),K),
                       protection(V,C,I,R,Perm,A,kind(pointer))]),
           fails(sp_check_validator:validate(G,reuse(Target,Bad,Guard,Witness,Tree)),
                 invalid_protection(changed_requirement(Target)))),
    fails(sp_check_validator:validate(G,reuse(Target,Need,retained_offset_guard(Witness),Witness,Tree)),
          invalid_protection(changed_offset_guard)),
    fails(sp_check_validator:validate(G,reuse(Target,Need,Guard,Target,Tree)),
          invalid_protection(changed_witness)),
    Tree=through(_,_,Inner),
    fails(sp_check_validator:validate(G,reuse(Target,Need,Guard,Witness,Inner)),
          invalid_protection(changed_interval)),
    fails(sp_check_validator:validate(G,_),invalid_protection(non_ground)),
    % Change the real covering read and update its recorded descriptor, so
    % failure must come from insufficient coverage, not just stale metadata.
    G=cfg(E,[block(B,Names,Params,[read(Base,Idx,Scale,Offset,8,[load(LV,LP,LI,LS,LO,8,Line)])|Ops],Term)]),
    Small=cfg(E,[block(B,Names,Params,[read(Base,Idx,Scale,Offset,2,[load(LV,LP,LI,LS,LO,2,Line)])|Ops],Term)]),
    sp_check_model:model(Small,SM),sp_check_model:candidate(SM,Witness,SmallClaim),
    replace_claim(Tree,SmallClaim,SmallTree),
    fails(sp_check_validator:validate(Small,reuse(Target,Need,Guard,Witness,SmallTree)),
          invalid_protection(insufficient_range)),
    % A store needs write permission; an earlier read cannot supply it.
    graph("movq (%rdi),%rax\nmovq %rax,(%rdi)\nret\n",StoreGraph),
    sp_check_model:model(StoreGraph,StoreModel),
    sp_check_model:access(StoreModel,site(0,1),WriteNeed,_),
    sp_check_model:candidate(StoreModel,site(0,0),ReadHave),
    fails(sp_check_validator:validate(StoreGraph,
          reuse(site(0,1),WriteNeed,retained_offset_guard(site(0,1)),site(0,0),checked(site(0,0),ReadHave))),
          invalid_protection(wrong_permission)),
    ReadHave=protection(RV,RC,RI,RR,RP,_,RK),
    fails(sp_check_validator:covered(ReadHave,protection(RV,RC,RI,RR,RP,alignment(8),RK)),
          invalid_protection(insufficient_alignment)),
    % Give the checker an honest record of an inserted invalidation. It
    % still cannot accept a certificate passing through that operation.
    Ops=[Math,Flags|Rest],
    forall(member(Barrier,[call(opaque),free(object),safepoint(gc),concurrent_mutation,
                           pointer_copy(v(99),Base,1),pointer_offset(v(99),Base,literal(0),1,1,1)]),
      (Changed=cfg(E,[block(B,Names,Params,[read(Base,Idx,Scale,Offset,8,[load(LV,LP,LI,LS,LO,8,Line)]),
                                         Math,Barrier|Rest],Term)]),
       sp_check_model:event(Barrier,BarrierEffect),Tree=through(Site,_,Tail),
       fails(sp_check_validator:validate(Changed,reuse(Target,Need,Guard,Witness,through(Site,BarrierEffect,Tail))),
             invalid_protection(invalidating_effect(Site))))),
    must(Flags=flag_values(_,_,_,_,_,_)),
    graph("movq (%rdi),%rax\ntestq $1,%rsi\nje .Lleft\naddq %rsi,%rax\njmp .Ljoin\n.Lleft:\nxorq %rsi,%rax\n.Ljoin:\nmovzbl 3(%rdi),%ecx\naddq %rcx,%rax\nret\n",DG),
    proof(DG,DP),DP=reuse(DT,DN,DGuard,DW,incoming(DB,[Via,Other])),
    fails(sp_check_validator:validate(DG,reuse(DT,DN,DGuard,DW,incoming(DB,[Via]))),
          invalid_protection(missing_predecessor(DB))),
    Via=via(Arc,_,Path),
    fails(sp_check_validator:validate(DG,reuse(DT,DN,DGuard,DW,incoming(DB,[via(Arc,wrong,Path),Other]))),
          invalid_protection(changed_edge_requirement)),
    uncovered("testq $1,%rsi\nje .Lleft\nmovq (%rdi),%rax\njmp .Ljoin\n.Lleft:\nmovq $0,%rax\n.Ljoin:\nmovzbl 3(%rdi),%ecx\naddq %rcx,%rax\nret\n"),
    uncovered("movq (%rdi),%rax\nmovl %esi,1(%rdi)\nmovzbl 3(%rdi),%ecx\naddq %rcx,%rax\nret\n"),
    uncovered("movq (%rdi),%rax\nleaq 1(%rdi),%rdi\nmovzbl (%rdi),%ecx\naddq %rcx,%rax\nret\n"),
    uncovered("movq (%rdi,%rsi,1),%rax\naddq $1,%rsi\nmovzbl (%rdi,%rsi,1),%ecx\naddq %rcx,%rax\nret\n"),
    uncovered("movq (%rdi),%rax\n.Lloop:\nmovzbl 3(%rdi),%ecx\naddq %rcx,%rax\naddq $-1,%rsi\njne .Lloop\nret\n"),
    fails(sp_check_reuse:analyze(G,0,Partial),check_analysis_limit),must(var(Partial)),
    % The first decision fits in four steps. Exhaustion while constructing
    % a later answer must not return that prefix as a complete report.
    fails(sp_check_reuse:analyze(G,4,Prefix),check_analysis_limit),must(var(Prefix)),
    Broken=cfg(E,[block(B,Names,Params,[read(Base,Idx,Scale,invalid,8,[])],Term)]),
    catch(sp_check_reuse:analyze(Broken,BrokenReport),Exception,true),
    must(nonvar(Exception)),must(var(BrokenReport)),
    sp_check_model:model(G,Model),
    must(\+sp_check_model:cycle_edge(Model,0,0)),
    sp_check_model:valid_requirement(Need),
    must(\+sp_check_model:valid_requirement(protection(V,C,I,range(9223372036854775804,9223372036854775812),Perm,A,K))),
    write('protection certificate checks: ok'),nl.
