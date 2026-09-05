:- module(sp_dataflow_tests, [tests/0]).
:- use_module(library(lists)).
must(G) :- (call(G) -> true;throw(error(dataflow_assertion(G)))).
fails(G,R) :-
    catch((call(G),Outcome=returned),E,Outcome=threw(E)),
    must(Outcome=threw(error(R))).
steps(Text,Nodes) :- sp_parser:parse_chars(Text,S),sp_cfg:nodes(S,0,Nodes,_).
lower(Body,Graph) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Text),
    sp_parser:parse_chars(Text,S),sp_cfg:lower(S,[function(p,_,Graph)],_).
change_cell(K,Value,[K-_|Xs],[K-Value|Xs]) :- !.
change_cell(K,V,[X|Xs],[X|Ys]) :- change_cell(K,V,Xs,Ys).

tests :-
    sp_ir:initial_state([ptr,u64],Initial),
    steps("movq $1,%rax\naddq $1,%rsi\n",CycleNodes),
    Cycle=[flow_block(0,CycleNodes,[0])],
    sp_dataflow:analyze(Cycle,Initial,CycleStates,stats(Changes,Limit)),
    must((Changes>0,Changes=<Limit)),
    CycleStates=[block_state(0,abstract(Regs,Flags),Out)],
    must(memberchk(rax-[integer,uninitialized],Regs)),
    must(memberchk(of-[defined,undefined],Flags)),
    change_cell(rax,[integer],Regs,NoEntry),
    fails(sp_dataflow:validate(Cycle,Initial,[block_state(0,abstract(NoEntry,Flags),Out)]),
          invalid_dataflow(missing_incoming(0))),
    change_cell(of,[defined],Flags,NoUndefined),
    fails(sp_dataflow:validate(Cycle,Initial,[block_state(0,abstract(Regs,NoUndefined),Out)]),
          invalid_dataflow(missing_incoming(0))),
    change_cell(rax,[],Regs,Empty),
    fails(sp_dataflow:validate(Cycle,Initial,[block_state(0,abstract(Empty,Flags),Out)]),
          invalid_dataflow(domain(rax,[]))),
    Out=abstract(OR,OF),change_cell(rax,[uninitialized],OR,NoDefinition),
    fails(sp_dataflow:validate(Cycle,Initial,[block_state(0,abstract(Regs,Flags),abstract(NoDefinition,OF))]),
          invalid_dataflow(missing_outgoing(0))),
    fails(sp_dataflow:analyze(Cycle,Initial,0,Partial,_),dataflow_limit(0)),
    must(var(Partial)),
    fails(sp_dataflow:validate(Cycle,Initial,[]),invalid_dataflow(changed_blocks)),
    fails(sp_dataflow:validate(Cycle,Initial,_),invalid_dataflow(non_ground)),
    % A second predecessor introduces a different type. Omitting it from
    % the proposed join is rejected by the local obligation checker.
    steps("movq %rdi,%r8\n",Pointer),steps("movq %rsi,%r8\n",Integer),
    Diamond=[flow_block(0,[],[1,2]),flow_block(1,Pointer,[3]),
             flow_block(2,Integer,[3]),flow_block(3,[],[])],
    sp_dataflow:analyze(Diamond,Initial,DS,_),
    append(Prefix,[block_state(3,abstract(DR,DF),DO)],DS),
    must(memberchk(r8-[integer,pointer],DR)),
    change_cell(r8,[pointer],DR,Missing),
    append(Prefix,[block_state(3,abstract(Missing,DF),DO)],Bad),
    fails(sp_dataflow:validate(Diamond,Initial,Bad),invalid_dataflow(missing_incoming(3))),
    % Lowering waits for convergence: first-iteration state is not supplied
    % by a backedge, and a later undefined flag can invalidate a loop header.
    fails(lower("je .Ldone\naddq $1,%rsi\njmp p\n.Ldone:\nmovq $0,%rax\nret\n",_),
          at(2,unavailable_flag(zf))),
    fails(lower(".Lloop:\nmovq %rax,%rcx\nmovq $1,%rax\njmp .Lloop\n",_),
          at(3,uninitialized_register(rax))),
    fails(lower("movq %rdi,%r8\n.Lloop:\nmovq (%r8),%rax\nmovq %rsi,%r8\njmp .Lloop\n",_),
          at(4,incompatible_register_types(r8,[integer,pointer]))),
    fails(lower("movq %rsi,%rax\naddq $1,%rax\n.Lloop:\njo .Ldone\nshlq $2,%rax\njmp .Lloop\n.Ldone:\nret\n",_),
          at(5,unavailable_flag(of))),
    lower("movq $0,%rax\n.Lloop:\ncmpq %rsi,%rax\nje .Ldone\naddq $1,%rax\njmp .Lloop\n.Ldone:\nret\n",_),
    write('finite dataflow checks: ok'),nl.
