:- module(sp_effects, [instruction_form/2, instruction_effects/2, constant/2]).
:- use_module(library(lists)).

% A finite, queryable catalogue. It describes the accepted source forms,
% not every encoding of these x86 mnemonics.
instruction_form(movzbl, load(1,32)).
instruction_form(movzwl, load(2,32)).
instruction_form(movl, load(4,32)).
instruction_form(movq, load(8,64)).
instruction_form(Op, move(W,Source)) :-
    move_width(Op,W), member(Source,[register,immediate]).
instruction_form(Op, binary(K,W,Source)) :-
    binary_opcode(Op,K,W), member(Source,[register,immediate]).
instruction_form(Op, shift(K,W)) :- shift_opcode(Op,K,W).
instruction_form(leaq, pointer_offset).
instruction_form(ret, return).
move_width(movl,32). move_width(movq,64).
binary_opcode(addl,add,32). binary_opcode(addq,add,64).
binary_opcode(xorl,xor,32). binary_opcode(xorq,xor,64).
binary_opcode(orl,or,32). binary_opcode(orq,or,64).
binary_opcode(andl,and,32). binary_opcode(andq,and,64).
shift_opcode(shll,shl,32). shift_opcode(shlq,shl,64).
shift_opcode(shrl,shr,32). shift_opcode(shrq,shr,64).

% Ground input makes rejection distinct from an incomplete relational search.
% The action and its effects come from the same normalized operands.
instruction_effects(Instruction, semantics(Action,Effects)) :-
    require(ground(Instruction), non_ground_instruction),
    Instruction=instruction(Op,Operands),
    require(instruction_form(Op,_), unsupported_instruction(Op)),
    (Op=ret -> arity(Operands,0), Action=return(register(rax,64))
    ; arity(Operands,2), Operands=[Source,Dest],
      normalize(Op,Source,Dest,Action)),
    action_effects(Action,Effects).
require(Goal,Reason) :- (call(Goal) -> true; throw(error(Reason))).
arity(Operands,N) :- length(Operands,Actual),
    require(Actual=:=N, operand_count(expected(N),actual(Actual))).

normalize(leaq,mem(D,B,I,S),Dest,pointer_offset(Address,R)) :- !,
    destination(Dest,64,R), address(mem(D,B,I,S),Address).
normalize(movq,reg(Source),Dest,copy(R,D)) :- !,
    register(Source,64,R), destination(Dest,64,D).
normalize(Op,mem(D,B,I,S),Dest,load(Address,Bytes,R)) :- !,
    require(instruction_form(Op,load(Bytes,W)), unsupported_memory_source(Op)),
    destination(Dest,W,R), address(mem(D,B,I,S),Address).
normalize(Op,Source,Dest,move(Value,R)) :- move_width(Op,W), !,
    destination(Dest,W,R), scalar_source(Source,W,Value),
    (Value=immediate(N) -> Min is -(2^(W-1)), Max is 2^W-1,
      range(N,Min,Max,move_immediate); true).
normalize(Op,Source,Dest,binary(K,Value,R)) :- binary_opcode(Op,K,W), !,
    destination(Dest,W,R), scalar_source(Source,W,Value),
    (Value=immediate(N) -> (W=64 -> Max=2147483647; Max=4294967295),
      range(N,-2147483648,Max,arithmetic_immediate); true).
normalize(Op,Source,Dest,shift(K,Count,R)) :- shift_opcode(Op,K,W), !,
    destination(Dest,W,R),
    require(Source=imm(E), immediate_shift_required(Source)),
    expression(E,Raw), range(Raw,0,255,shift_immediate), Count is Raw mod W.
normalize(Op,_,_,_) :- throw(error(unsupported_operands(Op))).

scalar_source(reg(Name),W,R) :- !, register(Name,W,R).
scalar_source(imm(E),_,immediate(N)) :- !, expression(E,N).
scalar_source(Other,_,_) :- throw(error(integer_source_required(Other))).
destination(reg(Name),W,R) :- !, register(Name,W,R).
destination(Other,_,_) :- throw(error(register_destination_required(Other))).
register(Name,W,register(Root,W)) :-
    require(alias(Name,Root,Actual), unsupported_register(Name)),
    require(W=:=Actual, register_width(Name,expected(W),actual(Actual))).
alias(rax,rax,64). alias(eax,rax,32).
alias(rcx,rcx,64). alias(ecx,rcx,32).
alias(rdx,rdx,64). alias(edx,rdx,32).
alias(rsi,rsi,64). alias(esi,rsi,32).
alias(rdi,rdi,64). alias(edi,rdi,32).
alias(r8,r8,64). alias(r8d,r8,32).
alias(r9,r9,64). alias(r9d,r9,32).
alias(r10,r10,64). alias(r10d,r10,32).
alias(r11,r11,64). alias(r11d,r11,32).
address(mem(D,B,I,S),address(Base,Index,Scale,Offset)) :-
    register(B,64,Base),
    (I=none -> Index=immediate(0); register(I,64,Index)),
    expression(S,Scale), require(memberchk(Scale,[1,2,4,8]), invalid_scale(Scale)),
    expression(D,Offset), range(Offset,0,18446744073709551615,displacement).
expression(E,N) :- require(constant(E,N), constant_expression_required(E)).
range(N,Min,Max,Role) :-
    require((N>=Min,N=<Max), out_of_range(Role,N,Min,Max)).
constant(const(N),N) :- integer(N).
constant(neg(A),N) :- constant(A,X), N is -X.
constant(add(A,B),N) :- constant(A,X), constant(B,Y), N is X+Y.
constant(sub(A,B),N) :- constant(A,X), constant(B,Y), N is X-Y.
constant(mul(A,B),N) :- constant(A,X), constant(B,Y), N is X*Y.

% Effects are about this source-level function abstraction. In particular,
% return is an ABI return; its hardware stack read belongs to Fil-C lowering.
% read(R,Type) is a static type requirement, not an inferred capability.
action_effects(load(A,Bytes,R),
    effects(registers(Reads,[Write]),
            memory([access(read,A,Bytes,alignment(1),ordinary)]),
            Flags,control(next),may_trap([address_overflow,invalid_read]))) :-
    address_reads(A,Reads), integer_write(R,Write), preserve_flags(Flags).
action_effects(copy(S,D),
    effects(registers([read(S,value)],[write(D,same_type_as(S),replace)]),
            memory([]),Flags,control(next),may_trap([]))) :- preserve_flags(Flags).
action_effects(pointer_offset(A,D),
    effects(registers(Reads,[write(D,pointer,replace)]),memory([]),
            Flags,control(next),may_trap([address_overflow]))) :-
    address_reads(A,Reads), preserve_flags(Flags).
action_effects(move(V,R),
    effects(registers(Reads,[Write]),memory([]),Flags,control(next),may_trap([]))) :-
    source_reads(V,Reads), integer_write(R,Write), preserve_flags(Flags).
action_effects(binary(K,V,R),
    effects(registers(Reads,[Write]),memory([]),Flags,control(next),may_trap([]))) :-
    source_reads(V,SourceReads), Reads=[read(R,integer)|SourceReads],
    integer_write(R,Write), binary_flags(K,Flags).
action_effects(shift(_,Count,R),
    effects(registers([read(R,integer)],[Write]),memory([]),Flags,control(next),may_trap([]))) :-
    integer_write(R,Write), shift_flags(Count,Flags).
action_effects(return(R),
    effects(registers([read(R,integer)],[]),memory([]),Flags,control(return),may_trap([]))) :-
    preserve_flags(Flags).
source_reads(register(R,W),[read(register(R,W),integer)]).
source_reads(immediate(_),[]).
address_reads(address(Base,Index,_,_),[read(Base,pointer)|Reads]) :- source_reads(Index,Reads).
integer_write(register(R,32),write(register(R,32),integer,zero_extend(64))).
integer_write(register(R,64),write(register(R,64),integer,replace)).

% Partition all six arithmetic flags. "Defined" names effects, not computed
% flag values. Nothing in this subset consumes flags, so C lowering drops them.
% Future branches must implement their values before using this metadata.
preserve_flags(flags(reads([]),defined([]),cleared([]),undefined([]),preserved([cf,pf,af,zf,sf,of]))).
binary_flags(add,flags(reads([]),defined([cf,pf,af,zf,sf,of]),cleared([]),undefined([]),preserved([]))).
binary_flags(K,flags(reads([]),defined([pf,zf,sf]),cleared([cf,of]),undefined([af]),preserved([]))) :-
    memberchk(K,[and,or,xor]).
shift_flags(0,F) :- !, preserve_flags(F).
shift_flags(1,flags(reads([]),defined([cf,pf,zf,sf,of]),cleared([]),undefined([af]),preserved([]))) :- !.
shift_flags(N,flags(reads([]),defined([cf,pf,zf,sf]),cleared([]),undefined([af,of]),preserved([]))) :- N>1.
