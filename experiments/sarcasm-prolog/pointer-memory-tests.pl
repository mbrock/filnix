:- module(sp_pointer_memory_tests, [tests/0]).
:- use_module(library(lists)).

must(G) :- (call(G) -> true; throw(error(pointer_memory_assertion(G)))).
fails(G,Reason) :- catch((call(G),Result=returned),E,Result=threw(E)),
    must(Result=threw(error(Reason))).
lower(Body,IR) :-
    append("p: #! unsigned long(ptr, unsigned long)\n",Body,Chars),
    sp_parser:parse_chars(Chars,Statements), sp_ir:lower(Statements,[function(p,_,IR)]).
tests :-
    lower("movq (%rdi),%r8 #! ptr\nmovq %r8,8(%rdi) ;! ptr\nmovq 8(%rdi),%r9 #! ptr\nmovzbl (%r9),%eax\nret\n",IR),
    must(IR=[pointer_load(v(0),arg0,literal(0),1,0,2),
        pointer_store(arg0,literal(0),1,8,v(0),3),
        pointer_load(v(2),arg0,literal(0),1,8,4),
        load(v(3),v(2),literal(0),1,0,1,5),return(view(v(3),64))]),
    sp_ir:plan(on,IR,Plan),sp_ir:validate(IR,Plan),
    % One operation may read the same pointer as its base and stored value.
    lower("movq %rdi,(%rdi) #! ptr\nmovq $1,%rax\nret\n",_),
    % A typed load can overwrite its own base using the old address value.
    lower("movq (%rdi),%rdi #! ptr\nmovzbl (%rdi),%eax\nret\n",Alias),
    must(Alias=[pointer_load(v(0),arg0,literal(0),1,0,2),
        load(v(1),v(0),literal(0),1,0,1,3),return(view(v(1),64))]),
    fails(lower("movq (%rdi),%r8\nmovq (%r8),%rax\nret\n",_),at(3,register_type(r8,expected(pointer),actual(int(v(0)))))),
    fails(lower("movq %rsi,(%rdi) #! ptr\nret\n",_),at(2,register_type(rsi,expected(pointer),actual(int(arg1))))),
    fails(lower("movl (%rdi),%eax #! ptr\nret\n",_),at(2,pointer_access_requires_movq(movl))),
    fails(lower("movq (%rdi),%eax #! ptr\nret\n",_),at(2,register_width(eax,expected(64),actual(32)))),
    fails(lower("movq $0,(%rdi) #! ptr\nret\n",_),at(2,pointer_memory_operands(imm(const(0)),_))),
    fails(lower("movq %rdi,%r8 #! ptr\nret\n",_),at(2,pointer_memory_operands(reg(rdi),reg(r8)))),
    fails(lower("#! ptr\n",_),at(2,orphan_pointer_annotation)),
    fails(lower("movq (%rdi),%r8\n#! ptr\n",_),at(3,orphan_pointer_annotation)),
    fails(lower("movq (%rdi),%r8 #! integer\n",_),at(2,pointer_annotation_syntax)),
    write('pointer memory checks: ok'),nl.
