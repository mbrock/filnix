:- module(sp_store_tests, [tests/0]).
:- use_module(library(lists)).

must(G) :- (call(G) -> true; throw(error(store_assertion(G)))).
fails(G,Reason) :- catch((call(G),Result=returned),E,Result=threw(E)),
    must(Result=threw(error(Reason))).

tests :-
    A=load(v(0),arg0,literal(0),1,0,1,2),
    B=load(v(2),arg0,literal(0),1,1,1,4),
    Store=store(arg0,literal(0),1,0,4,literal(7),3),
    Return=return(view(v(2),64)),IR=[A,Store,B,Return],
    sp_accesses:plan(on,IR,Plan,Trace),sp_accesses:validate(IR,Plan),
    must(Plan=[read(arg0,literal(0),1,0,1,[A]),Store,read(arg0,literal(0),1,1,1,[B]),Return]),
    must(Trace=[decision(_,_,_,_,[attempt(8,rejected(at(3,ordering_barrier(store))))|_])|_]),
    fails(sp_accesses:validate(IR,[read(arg0,literal(0),1,0,2,[A,B]),Store,Return]),invalid_access_plan(_)),
    fails(sp_accesses:validate(IR,[read(arg0,literal(0),1,0,1,[A]),read(arg0,literal(0),1,1,1,[B]),Return]),invalid_access_plan(_)),
    % A store reads values but writes no register and leaves their identities intact.
    sp_parser:parse_chars("p: #! unsigned long(ptr, unsigned long)\nmovq %rsi,(%rdi)\nmovq %rsi,%rax\nret\n",Ss),
    sp_ir:lower(Ss,[function(p,_,[store(arg0,literal(0),1,0,8,view(arg1,64),2),
        assign(v(1),64,view(arg1,64),3),return(view(v(1),64))])]),
    forall(member(Op-Low-High,[movl-(-2147483648)-4294967295,movq-(-2147483648)-2147483647]),
      (store_immediate(Op,Low),store_immediate(Op,High),Below is Low-1,Above is High+1,
       fails(store_immediate(Op,Below),out_of_range(store_immediate,Below,Low,High)),
       fails(store_immediate(Op,Above),out_of_range(store_immediate,Above,Low,High)))),
    write('integer store checks: ok'),nl.
store_immediate(Op,N) :-
    sp_effects:instruction_effects(instruction(Op,[imm(const(N)),mem(const(0),rdi,none,const(1))]),_).
