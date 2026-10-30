/* Audited machine forms for the scalar stack cache. Unknown forms fail,
   selecting the unchanged implementation, rather than guessing effects.
   Reads name register families. write(Family,Bits) records partial writes:
   32 bits zero-extend, 8/16 preserve the rest. Memory effects include
   addressing-register reads; flags and control/frame effects are separate.
   This describes selected instructions, not IR liveness or GC roots.
   Calls are unconditional cache boundaries; their ABI argument reads are
   not enumerated. Do not use this as a general call-liveness contract. */
:- module(amd64_contract, [instruction_effects/2, register/3,
                           explicit_registers/2, operand_register/2]).
:- use_module(library(lists)).
:- discontiguous(instruction_effects/2).

% Concrete names index directly; family/width queries generate the name
% without searching every family for every operand in a large function.
register(rax,rax,64). register(eax,rax,32).
register(ax,rax,16). register(al,rax,8).
register(rcx,rcx,64). register(ecx,rcx,32).
register(cx,rcx,16). register(cl,rcx,8).
register(rdx,rdx,64). register(edx,rdx,32).
register(dx,rdx,16). register(dl,rdx,8).
register(rbx,rbx,64). register(ebx,rbx,32).
register(bx,rbx,16). register(bl,rbx,8).
register(rsi,rsi,64). register(esi,rsi,32).
register(si,rsi,16). register(sil,rsi,8).
register(rdi,rdi,64). register(edi,rdi,32).
register(di,rdi,16). register(dil,rdi,8).
register(rbp,rbp,64). register(ebp,rbp,32).
register(bp,rbp,16). register(bpl,rbp,8).
register(rsp,rsp,64). register(esp,rsp,32).
register(sp,rsp,16). register(spl,rsp,8).
register(r8,r8,64). register(r8d,r8,32).
register(r8w,r8,16). register(r8b,r8,8).
register(r9,r9,64). register(r9d,r9,32).
register(r9w,r9,16). register(r9b,r9,8).
register(r10,r10,64). register(r10d,r10,32).
register(r10w,r10,16). register(r10b,r10,8).
register(r11,r11,64). register(r11d,r11,32).
register(r11w,r11,16). register(r11b,r11,8).
register(r12,r12,64). register(r12d,r12,32).
register(r12w,r12,16). register(r12b,r12,8).
register(r13,r13,64). register(r13d,r13,32).
register(r13w,r13,16). register(r13b,r13,8).
register(r14,r14,64). register(r14d,r14,32).
register(r14w,r14,16). register(r14b,r14,8).
register(r15,r15,64). register(r15d,r15,32).
register(r15w,r15,16). register(r15b,r15,8).
register(xmm0,xmm0,128). register(xmm1,xmm1,128).
register(xmm2,xmm2,128). register(xmm3,xmm3,128).
register(xmm4,xmm4,128). register(xmm5,xmm5,128).
register(xmm6,xmm6,128). register(xmm7,xmm7,128).

width(b,8). width(w,16). width(l,32). width(q,64).
expression(E) :- integer(E), !.
expression(E) :- atom(E), !.
expression(A+B) :- expression(A), expression(B).
address(mem(D,B), [B]) :- integer(D), register(B,B,64).
address(mem(D,B,I), [B,I]) :- integer(D), register(B,B,64), register(I,I,64).
address(rip(E), []) :- expression(E).
address(gotpcrel(S), []) :- atom(S).

explicit_registers(ins(_,_,Os), Rs) :- !,
    findall(R, (member(O,Os), operand_register(O,R)), Rs).
explicit_registers(_, []).
operand_register(reg(N), F) :- register(N,F,_).
operand_register(O, R) :- address(O,Rs), member(R,Rs).
operand_register(ind(O), R) :- operand_register(O,R).

source(reg(R), W, [F], []) :- register(R,F,W).
source(imm(E), _, [], []) :- expression(E).
source(M, W, Rs, [read(M,N)]) :- address(M,Rs), N is W//8.
destination(reg(R), W, [], [write(F,W)], []) :- register(R,F,W).
destination(M, W, Rs, [], [write(M,N)]) :- address(M,Rs), N is W//8.
% x86 does not admit a memory-to-memory two-operand instruction.
not_two_memory(A,B) :- \+ (address(A,_), address(B,_)).

instruction_effects(ins(mov,S,[A,B]), effect(Rs,Ws,preserve,Ms,next)) :-
    width(S,W), source(A,W,R1,M1), destination(B,W,R2,Ws,M2),
    not_two_memory(A,B), append(R1,R2,Rs), append(M1,M2,Ms).
instruction_effects(ins(movabs,q,[imm(N),reg(R)]),
                    effect([],[write(F,64)],preserve,[],next)) :-
    integer(N), register(R,F,64).
instruction_effects(ins(Op,S,[A,reg(R)]), effect(Rs,[write(F,W)],preserve,Ms,next)) :-
    extension(Op,From), width(S,W), W > From,
    source(A,From,Rs,Ms), A \= imm(_), register(R,F,W).
instruction_effects(ins(lea,q,[M,reg(R)]), effect(Rs,[write(F,64)],preserve,[],next)) :-
    address(M,Rs), register(R,F,64).
instruction_effects(ins(Op,S,[A,B]), effect(Rs,Ws,write,Ms,next)) :-
    memberchk(Op,[add,sub,and,or,xor,imul,btc]), width(S,W),
    ( memberchk(Op,[imul,btc]) -> W >= 16, B = reg(_) ; true ),
    source(A,W,R1,M1), source(B,W,R2,M2), B \= imm(_),
    destination(B,W,_,Ws,M3), not_two_memory(A,B),
    append(R1,R2,Rs), append([M1,M2,M3],Ms).
instruction_effects(ins(Op,S,[A,B]), effect(Rs,[],write,Ms,next)) :-
    memberchk(Op,[cmp,test]), width(S,W),
    source(A,W,R1,M1), source(B,W,R2,M2), B \= imm(_),
    not_two_memory(A,B), append(R1,R2,Rs), append(M1,M2,Ms).
instruction_effects(ins(neg,S,[A]), effect(Rs,Ws,write,Ms,next)) :-
    width(S,W), source(A,W,Rs,M1), destination(A,W,_,Ws,M2),
    append(M1,M2,Ms).
instruction_effects(ins(Op,S,[Count,A]), effect(Rs,Ws,read_write,Ms,next)) :-
    memberchk(Op,[shl,shr,sar]), width(S,W), shift_count(Count,R1),
    source(A,W,R2,M1), destination(A,W,_,Ws,M2),
    append(R1,R2,Rs), append(M1,M2,Ms).
instruction_effects(ins(Op,none,[reg(R)]), effect([F],[write(F,8)],read,[],next)) :-
    atom_concat(set,CC,Op), condition(CC), register(R,F,8).
instruction_effects(ins(cltd,none,[]), effect([rax],[write(rdx,32)],preserve,[],next)).
instruction_effects(ins(cqto,none,[]), effect([rax],[write(rdx,64)],preserve,[],next)).
instruction_effects(ins(Op,S,[A]), effect([rax,rdx|Rs],Ws,write,Ms,next)) :-
    memberchk(Op,[div,idiv]), width(S,W), memberchk(W,[32,64]),
    source(A,W,Rs,Ms), A \= imm(_), Ws = [write(rax,W),write(rdx,W)].

extension(movzb,8). extension(movsb,8).
extension(movzw,16). extension(movsw,16). extension(movsl,32).
shift_count(reg(cl),[rcx]).
shift_count(imm(N),[]) :- integer(N), N >= 0, N =< 255.
condition(CC) :- memberchk(CC,[e,ne,z,nz,b,be,a,ae,l,le,g,ge,s,ns,p,np]).

% SSE forms use full-family symbolic outputs: the cache never changes
% one, so the validator need not emulate floating arithmetic or lanes.
instruction_effects(ins(Op,none,[A,B]), effect(Rs,Ws,preserve,Ms,next)) :-
    sse_move(Op,W), sse_transfer(A,B,W,Rs,Ws,Ms).
instruction_effects(ins(Op,S,[reg(A),reg(B)]),
                    effect([A,B],[write(B,128)],preserve,[],next)) :-
    memberchk(Op,[add,sub,mul,div]), memberchk(S,[ss,sd]),
    register(A,A,128), register(B,B,128).
instruction_effects(ins(Op,none,[reg(A),reg(B)]), effect([A,B],[],write,[],next)) :-
    memberchk(Op,[ucomiss,ucomisd]), register(A,A,128), register(B,B,128).
instruction_effects(ins(Op,none,[reg(A),reg(B)]),
                    effect([A,B],[write(B,128)],preserve,[],next)) :-
    memberchk(Op,[cvtss2sd,cvtsd2ss]), register(A,A,128), register(B,B,128).
instruction_effects(ins(Op,S,[reg(A),reg(B)]),
                    effect([A],[write(F,W)],preserve,[],next)) :-
    memberchk(Op,[cvttss2si,cvttsd2si]), width(S,W), memberchk(W,[32,64]),
    register(A,A,128), register(B,F,W).
instruction_effects(ins(Op,S,[reg(A),reg(B)]),
                    effect([F,B],[write(B,128)],preserve,[],next)) :-
    memberchk(Op,[cvtsi2ss,cvtsi2sd]), width(S,W), memberchk(W,[32,64]),
    register(A,F,W), register(B,B,128).
sse_move(movd,32). sse_move(movq,64).
sse_transfer(reg(A),reg(B),W,[F],[write(B,128)],[]) :-
    register(A,F,W), register(B,B,128).
sse_transfer(reg(A),reg(B),W,[A],[write(F,W)],[]) :-
    register(A,A,128), register(B,F,W).

instruction_effects(ins(jmp,none,[T]), effect(Rs,[],preserve,Ms,branch)) :-
    target(T,Rs,Ms).
instruction_effects(ins(Op,none,[T]), effect([],[],read,[],branch)) :-
    atom_concat(j,CC,Op), condition(CC), target(T,[],[]).
instruction_effects(ins(call,S,[T]), effect([rsp|Rs],Ws,write,Ms,call)) :-
    memberchk(S,[none,q]), target(T,Rs,M),
    findall(write(R,W), caller_clobber(R,W), Ws),
    append(M,[read_write(runtime,unknown)],Ms).
instruction_effects(ins(push,q,[reg(R)]),
                    effect([F,rsp],[write(rsp,64)],preserve,[write(stack,8)],frame)) :-
    register(R,F,64).
instruction_effects(ins(pop,q,[reg(R)]),
                    effect([rsp],[write(F,64),write(rsp,64)],preserve,[read(stack,8)],frame)) :-
    register(R,F,64).
instruction_effects(ins(leave,none,[]),
                    effect([rbp],[write(rbp,64),write(rsp,64)],preserve,[read(stack,8)],frame)).
instruction_effects(ins(ret,none,[]),
                    effect([rsp],[write(rsp,64)],preserve,[read(stack,8)],terminal)).
instruction_effects(ins(ud2,none,[]), effect([],[],preserve,[],terminal)).
% A fence orders memory; it reads and writes no register or frame slot.
instruction_effects(ins(mfence,none,[]), effect([],[],preserve,[],next)).
% lock cmpxchg R, M compares %rax's low W bits with M; equal, it writes
% R to M, else M to them. It reads rax, R and M's addressing registers,
% reads and writes M (the write happens either way), and defines the
% flags. At 32 bits a failure zero-extends rax and a success leaves it,
% so 32 and 64 record a whole write of an unknown value; 8 and 16
% preserve the rest either way. A locked access is also a full fence.
instruction_effects(ins('lock cmpxchg',S,[reg(R),M]),
                    effect([rax,F|Rs],[write(rax,WA)],write,[read(M,N),write(M,N)],next)) :-
    width(S,W), register(R,F,W), address(M,Rs), N is W//8,
    ( W >= 32 -> WA = 64 ; WA = W ).
% A fixed-register asm line (docs/asm-fixed.md) is not an ins/3, so the
% register checker treats it as a region boundary. Its writes are 32
% bits; cpuid's line saves rbx in rsi and brings its b result out in edi,
% so rbx is preserved. None of them changes the flags.
instruction_effects(asm_fixed(cpuid),
    effect([rax,rcx],[write(rax,32),write(rcx,32),write(rdx,32),write(rsi,64),write(rdi,32)],
           preserve,[],next)).
instruction_effects(asm_fixed(xgetbv), effect([rcx],[write(rax,32),write(rdx,32)],preserve,[],next)).
instruction_effects(asm_fixed(rdtsc), effect([],[write(rax,32),write(rdx,32)],preserve,[],next)).
instruction_effects(asm_fixed(rdtscp),
    effect([],[write(rax,32),write(rcx,32),write(rdx,32)],preserve,[],next)).
instruction_effects(asm_fixed(M), effect([],[],preserve,[],next)) :-
    memberchk(M, [lfence, sfence, pause]).
instruction_effects(label(S), effect([],[],preserve,[],label)) :- atom(S).
instruction_effects(D, effect([],[],preserve,[],directive)) :- directive(D).

target(sym(S),[],[]) :- atom(S).
target(plt(S),[],[]) :- atom(S).
target(ind(O),Rs,Ms) :- source(O,64,Rs,Ms), O \= imm(_).
caller_clobber(R,64) :- member(R,[rax,rcx,rdx,rsi,rdi,r8,r9,r10,r11,rsp]).
caller_clobber(R,128) :- register(R,R,128).
directive(section(text)).
directive(p2align(N)) :- integer(N).
directive(globl(S)) :- atom(S).
directive(type(S,function)) :- atom(S).
directive(size(S)) :- atom(S).
