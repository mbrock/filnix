:- module(sp_pointer_tests, [tests/0]).
:- use_module(library(lists)).

must(G) :- (call(G) -> true; throw(error(pointer_assertion(G)))).
fails(G,Reason) :- catch((call(G),Result=returned),E,Result=threw(E)),
    must(Result=threw(error(Reason))).
lower(Body,IR) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Chars),
    sp_parser:parse_chars(Chars,Statements), sp_ir:lower(Statements,[function(p,_,IR)]).

tests :-
    lower("movq %rdi,%r8\nleaq 3(%r8,%rsi,4),%r9\nmovq %r9,%r9\nmovzbl (%r9),%eax\nret\n",IR),
    must(IR=[pointer_copy(v(0),arg0,2),
             pointer_offset(v(1),v(0),view(arg1,64),4,3,3),
             pointer_copy(v(2),v(1),4),load(v(3),v(2),literal(0),1,0,1,5),
             return(view(v(3),64))]),
    sp_ir:plan(on,IR,Plan), sp_ir:validate(IR,Plan),
    % Reads of a destination's old integer or pointer precede its write.
    lower("leaq 2(%rdi,%rsi,4),%rsi\nmovq (%rsi),%rax\nret\n",Aliased),
    must(Aliased=[pointer_offset(v(0),arg0,view(arg1,64),4,2,2),
                  load(v(1),v(0),literal(0),1,0,8,3),return(view(v(1),64))]),
    lower("leaq 1(%rdi),%rdi\nmovzbl (%rdi),%eax\nret\n",_),
    lower("movq %rdi,%rax\nmovq $7,%rax\nret\n",Integer),
    must(Integer=[pointer_copy(v(0),arg0,2),assign(v(1),64,literal(7),3),return(view(v(1),64))]),
    forall(member(R,[rax,rcx,rdx,rsi,rdi,r8,r9,r10,r11]),copy_register(R)),
    fails(lower("movl %edi,%eax\nret\n",_),at(2,register_type(rdi,expected(integer),actual(ptr(arg0))))),
    fails(lower("movq %rsi,%r8\nmovq (%r8),%rax\nret\n",_),at(3,register_type(r8,expected(pointer),actual(int(v(0)))))),
    fails(lower("movq %rdi,%r8\naddq $1,%r8\nret\n",_),at(3,register_type(r8,expected(integer),actual(ptr(v(0)))))),
    fails(lower("movq %rdi,%rax\nret\n",_),at(3,register_type(rax,expected(integer),actual(ptr(v(0)))))),
    fails(lower("leaq (%rsi),%rax\nret\n",_),at(2,register_type(rsi,expected(pointer),actual(int(arg1))))),
    fails(lower("leaq (%rdi,%rdi,1),%rax\nret\n",_),at(2,register_type(rdi,expected(integer),actual(ptr(arg0))))),
    fails(lower("leaq -1(%rdi),%rax\nret\n",_),at(2,out_of_range(displacement,-1,0,18446744073709551615))),
    write('pointer value checks: ok'),nl.

copy_register(R) :-
    sp_ir:lower([located(1,label(p)),located(1,signature(u64,[ptr])),
       located(2,instruction(movq,[reg(rdi),reg(R)])),
       located(3,instruction(movzbl,[mem(const(0),R,none,const(1)),reg(eax)])),
       located(4,instruction(ret,[]))], [function(p,[ptr],IR)]),
    must(IR=[pointer_copy(v(0),arg0,2),load(v(1),v(0),literal(0),1,0,1,3),return(view(v(1),64))]).
