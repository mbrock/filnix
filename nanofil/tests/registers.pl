/* Public native-emission contracts of the allocating selection: branch
   and immediate selection really change the stream, and setjmp
   implementations are left alone. Native arithmetic/ABI outcomes use the
   differential and interop suites; regs_check.pl attacks the translation
   validators themselves. (M6's local scalar cache and its tests were
   retired in October 2026, docs/m6.md.) */
:- module(register_tests, [scalar_cache/0]).
:- use_module('../src/filc_amd64').
:- use_module('../src/filc_abi', [lower_function/4]).
:- use_module('../src/ir').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module(library(lists)).

scalar_cache :- dead_setjmp, immediate_selection, branch_selection.

% Branch selection (docs/perf.md): a comparison only its branch reads
% becomes cmp and a conditional jump to the arm that is not next, with
% no boolean; a register or an imm32 operand; temps' checkers accept the
% selected stream. A comparison also returned stays a boolean.
branch_selection :-
    forall(member(Y-Cmp, [tmp(b)-ins(cmp,l,[reg(ecx),reg(eax)]),
                          const(-7)-ins(cmp,l,[imm(-7),reg(eax)])]),
           ( branch_module(Y, const(1), M),
             filc_module_asm(M, stack, Ref, _),
             filc_module_asm(M, emit(stack,selected), Sel, _),
             filc_module_asm(M, emit(temps,selected), _, [function(b,_)]),
             memberchk(ins(setl,none,_), Ref),
             \+ memberchk(ins(setl,none,_), Sel),
             append(_, [Cmp, ins(jge,none,[sym(F)])|_], Sel),
             atom_concat(_, '.f', F),
             \+ ( member(ins(jmp,none,[sym(T)]), Sel), atom_concat(_, '.t', T) ) )),
    branch_module(tmp(b), tmp(c), Kept),
    filc_module_asm(Kept, emit(stack,selected), KeptSel, _),
    memberchk(ins(setl,none,_), KeptSel).

% b(a, b): c = a < Y; branch on c to t (next) or f; t returns R.
branch_module(Y, R, module([func(b,export,w,[param(w,tmp(a)),param(w,tmp(b))],[
    block(s,[],[let(tmp(c),w,cmp(slt,w),[tmp(a),Y])],branch(tmp(c),t,f)),
    block(t,[],[],ret(R)),
    block(f,[],[],ret(const(2)))])])).

% Public emission: temps' selection saves the constant's scratch move,
% while stack stays the reference. Expected encodings are hand-derived,
% especially the qword cases where an imm32 would change the high bits.
immediate_selection :-
    forall((member(Op-Insn,[add-add,sub-sub,mul-imul,and-and,or-or,xor-xor]),
            member(K-N-V,[w-17-17,w-2147483648-(-2147483648),
                          w-4294967295-(-1),w-4294967313-17,
                          w-(-4294967313)-(-17),
                          l-2147483647-2147483647,
                          l-(-2147483648)-(-2147483648),
                          l-18446744071562067968-(-2147483648),
                          l-18446744073709551615-(-1),
                          l-18446744073709551633-17,
                          l-(-18446744073709551599)-17])),
           selected_immediate(Op,Insn,K,N,V)),
    forall((member(Op,[shl,shr,sar]),
            member(K-N-V,[w-0-0,w-1-1,w-31-31,w-32-0,w-63-31,w-64-0,
                          w-65-1,w-(-1)-31,w-255-31,w-256-0,
                          w-4294967329-1,
                          l-0-0,l-1-1,l-31-31,l-32-32,l-63-63,l-64-0,
                          l-65-1,l-(-1)-63,l-255-63,l-256-0,
                          l-4294967329-33])),
           selected_immediate(Op,Op,K,N,V)),
    forall((member(Op,[add,sub,mul,and,or,xor]),
            member(N,[2147483648,4294967295,-2147483649,
                      9223372036854775807])),
           (immediate_module(Op,l,N,M),
            filc_module_asm(M,temps,Lines,_),
            memberchk(ins(movabs,q,[imm(N),reg(rcx)]),Lines))).

selected_immediate(Op,Insn,K,N,V) :-
    immediate_module(Op,K,N,M),
    filc_module_asm(M,stack,Stack,_),
    filc_module_asm(M,temps,Local,[function(immediate,_)]),
    ( K == w -> S = l, R = eax ; S = q, R = rax ),
    memberchk(ins(Insn,S,[imm(V),reg(R)]),Local),
    \+ memberchk(ins(Insn,S,[imm(V),reg(R)]),Stack),
    \+ memberchk(ins(movabs,q,[_,reg(rcx)]),Local),
    \+ memberchk(ins(mov,l,[_,reg(ecx)]),Local).

immediate_module(Op,K,N,module([func(immediate,export,K,[param(K,tmp(x))],[
    block(s,[],[let(tmp(y),K,Op,[tmp(x),const(N)])],ret(tmp(y)))])])).

dead_setjmp :-
    M = module([func(dead_jump,export,l,[param(p,tmp(buf)),param(l,tmp(x))],[
        block(s,[],[let(tmp(y),l,add,[tmp(x),const(7)])],ret(tmp(y))),
        block(dead,[],[let(tmp(j),w,setjmp('_setjmp'),[tmp(buf),const(0)])],
              ret(const(0)))])]),
    valid_module(M),
    forall(member(O,[o0,o1]),
           (optimize(O,M,Optimized),pizlonate_module(Optimized,C),
            filc_module_asm(C,temps,_,[function(dead_jump,excluded(setjmp))]))).

frame_moves(Lines,N) :-
    findall(1,(member(ins(mov,_,Ops),Lines),member(mem(_,rbp),Ops)),Xs),
    length(Xs,N).
