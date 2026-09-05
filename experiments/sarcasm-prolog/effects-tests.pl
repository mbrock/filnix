:- module(sp_effect_tests, [tests/0]).
:- use_module(library(lists)).

must(G) :- (call(G) -> true; throw(error(effect_assertion(G)))).
fails(G,Reason) :- catch((call(G),Result=returned),E,Result=threw(E)),
    must(Result=threw(error(Reason))).

% An independent table of executable forms: adding a form to the compiler
% without extending this acceptance table must fail the catalogue comparison.
case(Op,load(B,W),[mem(const(0),rdi,rsi,const(4)),reg(D)],load) :-
    member(Op-B-W-D,[movzbl-1-32-eax,movzwl-2-32-eax,movl-4-32-eax,movq-8-64-rax]).
case(Op,move(W,Kind),[S,reg(D)],move) :-
    member(Op-W-D-R,[movl-32-eax-ecx,movq-64-rax-rcx]),
    member(Kind-S,[register-reg(R),immediate-imm(const(7))]).
case(Op,store(B,Kind),[S,mem(const(0),rdi,rsi,const(4))],store) :-
    member(Op-B-R,[movl-4-eax,movq-8-rax]),
    member(Kind-S,[register-reg(R),immediate-imm(const(7))]).
case(Op,binary(K,W,Kind),[S,reg(D)],K) :-
    member(Op-K-W-D-R,[addl-add-32-eax-ecx,addq-add-64-rax-rcx,
        xorl-xor-32-eax-ecx,xorq-xor-64-rax-rcx,
        orl-or-32-eax-ecx,orq-or-64-rax-rcx,
        andl-and-32-eax-ecx,andq-and-64-rax-rcx]),
    member(Kind-S,[register-reg(R),immediate-imm(const(7))]).
case(Op,shift(K,W),[imm(const(1)),reg(D)],shift) :-
    member(Op-K-W-D,[shll-shl-32-eax,shlq-shl-64-rax,shrl-shr-32-eax,shrq-shr-64-rax]).
case(ret,return,[],return).
case(leaq,pointer_offset,[mem(const(0),rdi,rsi,const(4)),reg(rax)],pointer_offset).

tests :-
    findall(Op-Form,case(Op,Form,_,_),Expected0), sort(Expected0,Expected),
    findall(Op-Form,sp_effects:instruction_form(Op,Form),Actual0), sort(Actual0,Actual),
    must(Expected==Actual), must(length(Actual,34)),
    forall(case(Op,Form,Args,Kind),check_case(Op,Form,Args,Kind)),
    forall(member(Op-W-D,[shll-32-eax,shrl-32-eax,shlq-64-rax,shrq-64-rax]),
      forall(member(Raw,[0,1,2,31,32,63,64,65,255]),check_shift(Op,W,D,Raw))),
    fails(sp_effects:instruction_effects(_, _),non_ground_instruction),
    fails(sp_effects:instruction_effects(instruction(jmp,[symbol(f)]),_),unsupported_instruction(jmp)),
    fails(sp_effects:instruction_effects(instruction(ret,[imm(const(8))]),_),operand_count(expected(0),actual(1))),
    fails(sp_effects:instruction_effects(instruction(movl,[reg(rax),reg(eax)]),_),register_width(rax,expected(32),actual(64))),
    fails(sp_effects:instruction_effects(instruction(movq,[reg(ah),reg(rax)]),_),unsupported_register(ah)),
    fails(sp_effects:instruction_effects(instruction(shlq,[reg(rcx),reg(rax)]),_),immediate_shift_required(reg(rcx))),
    fails(sp_effects:instruction_effects(instruction(movq,[mem(const(0),rdi,none,const(3)),reg(rax)]),_),invalid_scale(3)),
    fails(sp_effects:instruction_effects(instruction(movq,[mem(symbol(x),rdi,none,const(1)),reg(rax)]),_),constant_expression_required(symbol(x))),
    fails(sp_effects:instruction_effects(instruction(addq,[reg(rax),mem(const(0),rdi,none,const(1))]),_),unsupported_memory_destination(addq)),
    immediate_limits,
    address_effects,
    trace_tests,
    write('effect and explanation checks: ok'),nl.
check_case(Op,Form,Args,Kind) :-
    sp_effects:instruction_effects(instruction(Op,Args),semantics(_,E)),
    must(ground(E)), E=effects(registers(Reads,Writes),memory(Mem),Flags,control(Control),may_trap(Traps)),
    check_flags(Flags),
    (Kind=return -> must(Reads=[read(register(rax,64),integer)]), must(Writes=[]), must(Control=return)
    ; Kind=store -> must(Writes=[]), must(Control=next)
    ; must(Control=next), Writes=[write(register(rax,W),Type,Policy)],
      (Kind=pointer_offset -> must(Type=pointer)
      ; Form=move(64,register) -> must(Type=same_type_as(register(rcx,64))), must(Reads=[read(register(rcx,64),value)])
      ; must(Type=integer)),
      (W=32 -> must(Policy=zero_extend(64)); must(Policy=replace))),
    (Kind=load -> Form=load(Bytes,_),
      must(Mem=[access(read,address(register(rdi,64),register(rsi,64),4,0),Bytes,alignment(1),ordinary)]),
      must(Reads=[read(register(rdi,64),pointer),read(register(rsi,64),integer)]),
      must(Traps=[address_overflow,invalid_read])
    ; Kind=pointer_offset -> must(Mem=[]),must(Traps=[address_overflow]),
      must(Reads=[read(register(rdi,64),pointer),read(register(rsi,64),integer)])
    ; Kind=store -> Form=store(Bytes,SourceKind),
      must(Mem=[access(write,address(register(rdi,64),register(rsi,64),4,0),Bytes,alignment(1),ordinary)]),
      must(Traps=[address_overflow,invalid_write]), W is Bytes*8,
      (SourceKind=register -> Tail=[read(register(rax,W),integer)]; Tail=[]),
      must(Reads=[read(register(rdi,64),pointer),read(register(rsi,64),integer)|Tail])
    ; must(Mem=[]),must(Traps=[])),
    (memberchk(Kind,[load,store,move,return,pointer_offset]) -> Flags=flags(reads([]),defined([]),cleared([]),undefined([]),preserved([cf,pf,af,zf,sf,of]))
    ; Kind=add -> Flags=flags(reads([]),defined([cf,pf,af,zf,sf,of]),cleared([]),undefined([]),preserved([]))
    ; memberchk(Kind,[and,or,xor]) -> Flags=flags(reads([]),defined([pf,zf,sf]),cleared([cf,of]),undefined([af]),preserved([]))
    ; true).
check_flags(flags(reads(R),defined(D),cleared(C),undefined(U),preserved(P))) :-
    append(D,C,A),append(A,U,B),append(B,P,All),sort(All,Set),
    must(Set=[af,cf,of,pf,sf,zf]),must(length(All,6)),must(R=[]).
check_shift(Op,W,D,Raw) :-
    sp_effects:instruction_effects(instruction(Op,[imm(const(Raw)),reg(D)]),
      semantics(shift(_,Count,_),effects(_,_,F,_,_))),
    C is Raw mod W,must(Count=:=C),check_flags(F),
    (C=0 -> F=flags(_,defined([]),cleared([]),undefined([]),preserved([cf,pf,af,zf,sf,of]))
    ; C=1 -> F=flags(_,defined([cf,pf,zf,sf,of]),cleared([]),undefined([af]),preserved([]))
    ; F=flags(_,defined([cf,pf,zf,sf]),cleared([]),undefined([af,of]),preserved([]))).
immediate_limits :-
    forall(member(Op-D-Low-High,[movl-eax-(-2147483648)-4294967295,
        movq-rax-(-9223372036854775808)-18446744073709551615,
        addl-eax-(-2147483648)-4294967295,addq-rax-(-2147483648)-2147483647,
        shlq-rax-0-255]),
      (must(sp_effects:instruction_effects(instruction(Op,[imm(const(Low)),reg(D)]),_)),
       must(sp_effects:instruction_effects(instruction(Op,[imm(const(High)),reg(D)]),_)),
       Below is Low-1,Above is High+1,
       fails(sp_effects:instruction_effects(instruction(Op,[imm(const(Below)),reg(D)]),_),out_of_range(_,Below,Low,High)),
       fails(sp_effects:instruction_effects(instruction(Op,[imm(const(Above)),reg(D)]),_),out_of_range(_,Above,Low,High)))).
address_effects :-
    sp_effects:instruction_effects(instruction(movzwl,[mem(const(2),rdi,none,const(1)),reg(eax)]),
      semantics(_,effects(registers(R,_),memory([access(read,_,2,alignment(1),ordinary)]),_,_,_))),
    must(R=[read(register(rdi,64),pointer)]).
trace_tests :-
    A=load(v(0),arg0,view(arg1,64),4,0,2,4),
    B=load(v(1),arg0,view(arg1,64),4,2,2,5),
    sp_accesses:plan(on,[A,B,return(view(v(1),64))],Plan,Ds),sp_accesses:validate([A,B,return(view(v(1),64))],Plan),
    must(Ds=[decision(v(0),4,4,[4,5],[attempt(8,rejected(function_return(4))),attempt(4,accepted(contiguous_reads([4,5])))])]),
    forall(member(C-Reason,[
        load(v(1),arg2,view(arg1,64),4,2,2,5)-pointer_changed(arg0,arg2),
        load(v(1),arg0,view(v(7),64),4,2,2,5)-index_changed(view(arg1,64),view(v(7),64)),
        load(v(1),arg0,view(arg1,64),8,2,2,5)-scale_changed(4,8),
        load(v(1),arg0,view(arg1,64),4,3,2,5)-noncontiguous(expected(2),actual(3)),
        assign(v(1),64,literal(7),5)-ordering_barrier(assignment),
        pointer_copy(v(1),arg0,5)-ordering_barrier(pointer_copy),
        pointer_offset(v(1),arg0,literal(0),1,2,5)-ordering_barrier(pointer_offset),
        store(arg0,literal(0),1,8,4,literal(7),5)-ordering_barrier(store)]),
      (sp_accesses:plan(on,[A,C],_,[decision(v(0),4,2,[4],[attempt(8,rejected(at(5,Reason)))|_])|_]))),
    sp_accesses:plan(off,[A],_,[decision(v(0),4,2,[4],[disabled])]),
    fails(sp_accesses:plan(on,_,_,_),invalid_access_plan(non_ground_input)).
