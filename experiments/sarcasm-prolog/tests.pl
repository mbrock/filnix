:- use_module('effects.pl', []).
:- use_module('accesses.pl', []).
:- use_module('effects-tests.pl', []).
:- use_module('pointer-tests.pl', []).
:- use_module('parser.pl').
:- use_module('ir.pl').
:- use_module('x86_64.pl').
:- use_module('target.pl').
:- use_module(library(lists)).
:- initialization(main).
main :- catch((tests -> write('prolog checks: ok'),nl,halt(0); throw(error(test_failed))),E,
    (format(user_error,'~q~n',[E]),halt(1))).
must(G) :- (call(G) -> true; throw(error(assertion_failed(G)))).
rejects(G) :- catch((call(G),Result=accepted),_,Result=rejected), must(Result==rejected).

tests :-
    sp_effect_tests:tests,
    sp_pointer_tests:tests,
    parse_chars("f: #! unsigned long(ptr)\nmovq $0x10+2*3, %rax; ret # a comment\n",S),
    lower(S,[function(f,[ptr],[assign(v(0),64,literal(22),2),return(view(v(0),64))])]),
    parse_chars(".section .note.GNU-stack,\"\",@progbits\n",[_]),
    parse_chars(".ascii \"a;#b\\\"c\"\n",[located(1,directive('.ascii',[string("a;#b\"c")]))]),
    parse_chars("f: ;! unsigned long(ptr)\nmovq $(-2+3)*8, %rax; ret\n",S2), lower(S2,_),
    rejects(parse_chars("f: #! unsigned long(ptr)\nmovq $1,%rax ret\n",_)),
    parse_chars("f: #! unsigned long(ptr)\nmovq $010+0X10,%rax; ret\n",Oct),
    lower(Oct,[function(f,[ptr],[assign(v(0),64,literal(24),2),return(view(v(0),64))])]),
    rejects(parse_chars("f: #! unsigned long(ptr)\nmovq $08,%rax; ret\n",_)),
    rejects(parse_chars(".ascii \"unterminated\n",_)),
    rejects((parse_chars("f: #! unsigned long(ptr)\nret\n",R),lower(R,_))),
    rejects((parse_chars("f: #! unsigned long(ptr)\nmovq %rdi,%rax; ret\n",P),lower(P,_))),
    rejects((parse_chars("f: #! unsigned long(ptr)\njmp f\n",J),lower(J,_))),
    rejects((parse_chars("f: #! unsigned long(ptr)\nmovq $1,%rax; shlq %rax,%rax; ret\n",J2),lower(J2,_))),
    rejects(emit(aarch64,[])), rejects(emit(arm64,[])), rejects(emit(mips,[])),
    A=load(v(0),arg0,view(arg1,64),4,0,2,1),
    B=load(v(1),arg0,view(arg1,64),4,2,1,2),
    C=load(v(2),arg0,view(arg1,64),4,3,1,3),
    IR=[A,B,C,return(view(v(2),64))],
    plan(on,IR,Plan), validate(IR,Plan),
    must(Plan=[read(arg0,view(arg1,64),4,0,4,[A,B,C]),return(view(v(2),64))]),
    plan(off,IR,Plain), validate(IR,Plain), must(length(Plain,4)),
    rejects(validate(IR,[read(arg0,view(arg1,64),4,0,2,[A,B,C]),return(view(v(2),64))])),
    rejects(validate(IR,[read(arg0,literal(0),4,0,4,[A,B,C]),return(view(v(2),64))])),
    rejects(validate(IR,[read(arg0,view(arg1,64),4,0,4,[B,A,C]),return(view(v(2),64))])),
    rejects(validate(IR,[read(arg0,view(arg1,64),4,0,4,[A,B,C])])),
    rejects(validate(IR,_)),
    Barrier=assign(v(3),64,literal(7),4),
    plan(on,[A,Barrier,B,C],WithBarrier), validate([A,Barrier,B,C],WithBarrier),
    must(WithBarrier=[read(_,_,_,_,2,[A]),Barrier,read(_,_,_,_,2,[B,C])]),
    Different=load(v(4),arg0,view(v(3),64),4,2,2,5),
    plan(on,[A,Different],Separate), must(length(Separate,2)),
    rejects(validate([A,Different],[read(arg0,view(arg1,64),4,0,4,[A,Different])])).
