/* Public native-emission contracts: the local mode really changes scalar
   traffic, but never setjmp implementations, float-shared homes or unknown
   machine forms. Native arithmetic/ABI outcomes use the differential and
   interop suites; cache_check.pl attacks the translation validator itself. */
:- module(register_tests, [scalar_cache/0]).
:- use_module('../src/amd64_cache').
:- use_module('../src/filc_amd64').
:- use_module('../src/filc_abi', [lower_function/4]).
:- use_module('../src/ir').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module(library(lists)).

scalar_cache :- pressure, redundant_loads, exclusions, backend,
                mixed_homes, dead_setjmp, immediate_selection.

% Public emission: local selection saves the constant's scratch move,
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
            filc_module_asm(M,local,Lines,_),
            memberchk(ins(movabs,q,[imm(N),reg(rcx)]),Lines))).

selected_immediate(Op,Insn,K,N,V) :-
    immediate_module(Op,K,N,M),
    filc_module_asm(M,stack,Stack,_),
    filc_module_asm(M,local,Local,[function(immediate,cached(_, _))]),
    ( K == w -> S = l, R = eax ; S = q, R = rax ),
    memberchk(ins(Insn,S,[imm(V),reg(R)]),Local),
    \+ memberchk(ins(Insn,S,[imm(V),reg(R)]),Stack),
    \+ memberchk(ins(movabs,q,[_,reg(rcx)]),Local),
    \+ memberchk(ins(mov,l,[_,reg(ecx)]),Local).

immediate_module(Op,K,N,module([func(immediate,export,K,[param(K,tmp(x))],[
    block(s,[],[let(tmp(y),K,Op,[tmp(x),const(N)])],ret(tmp(y)))])])).

% The result still in the scratch register needs no trip through the
% cache bank. A word read is redundant only if it also clears no high bits.
redundant_loads :-
    M = cache_metadata(false,[home(-8,[w,l])]),
    Frame = ins(mov,q,[reg(rsp),reg(rbp)]),
    Store = ins(mov,q,[reg(rax),mem(-8,rbp)]),
    Q = ins(mov,q,[mem(-8,rbp),reg(rax)]),
    L = ins(mov,l,[mem(-8,rbp),reg(eax)]),
    End = ins(leave,none,[]),
    cache_asm(local,M,[Frame,Store,Q,End],[Frame,Store,End],_),
    % Incoming upper bits are unknown, so the first movl must remain.
    cache_asm(local,M,[Frame,Store,L,L,End],Word,_),
    findall(S,member(ins(mov,l,[S,reg(eax)]),Word),[_]),
    Zero = ins(add,l,[imm(17),reg(eax)]),
    cache_asm(local,M,[Frame,Zero,Store,L,Q,End],
                      [Frame,Zero,Store,End],_),
    % A boundary forgets even a zeroing load's result. Partial writes
    % likewise forget the whole register rather than carrying stale facts.
    forall(member(Prefix,[[ins(mov,l,[mem(0,rdi),reg(eax)])],
                          [Zero,ins(setne,none,[reg(al)])]]),
           (append([Frame|Prefix],[Store,L,End],Code),
            cache_asm(local,M,Code,New,_),
            memberchk(ins(mov,l,[_,reg(eax)]),New))),
    % Both implicit/partial register writes and home overwrites invalidate.
    forall(member(Change,[ins(idiv,q,[reg(rcx)]),
                          ins(setne,none,[reg(al)]),
                          ins(mov,q,[reg(rcx),reg(rax)]),
                          ins(mov,l,[reg(ecx),reg(eax)]),
                          ins(mov,q,[reg(rcx),mem(-8,rbp)]),
                          ins(call,none,[plt(filc_pollcheck_slow)]),
                          label(join)]),
           (Changed = [Frame,Store,Change,Q,End],
            cache_asm(local,M,Changed,Kept,_),
            memberchk(ins(mov,q,[_,reg(rax)]),Kept))).

pressure :-
    M = cache_metadata(false,[home(-8,[w,l]),home(-16,[l]),home(-24,[w])]),
    Code = [ins(mov,q,[reg(rsp),reg(rbp)]),
            ins(mov,q,[reg(rax),mem(-8,rbp)]),
            ins(mov,q,[reg(rcx),mem(-16,rbp)]),
            ins(mov,q,[reg(rdx),mem(-24,rbp)]),
            ins(mov,l,[mem(-8,rbp),reg(ecx)]),
            ins(mov,q,[mem(-16,rbp),reg(rax)]),
            ins(cqto,none,[]), ins(idiv,q,[reg(rcx)]),
            ins(mov,q,[mem(-24,rbp),reg(rcx)]),
            ins(shl,q,[reg(cl),reg(rax)]),
            ins(mov,q,[mem(-8,rbp),reg(rdx)]),
            ins(mov,q,[mem(-16,rbp),reg(rcx)]),
            ins(mov,q,[mem(-24,rbp),reg(rax)]),
            ins(leave,none,[]),ins(ret,none,[])],
    cache_asm(local,M,Code,New,cached(3,1)),
    cache_asm(local,M,Code,Again,_), New == Again,
    frame_moves(Code,Before), frame_moves(New,After), After < Before,
    % Three overlapping homes exceed the bank: the third stays on stack.
    memberchk(ins(mov,q,[reg(rdx),mem(-24,rbp)]),New).

exclusions :-
    Code = [ins(mov,q,[reg(rsp),reg(rbp)]),
            ins(mov,q,[reg(rax),mem(-8,rbp)]),
            ins(mov,q,[mem(-8,rbp),reg(rcx)]),ins(leave,none,[])],
    forall(member(Ks,[[l,d],[s,w],[unknown],[]]),
           cache_asm(local,cache_metadata(false,[home(-8,Ks)]),Code,Code,_)),
    cache_asm(local,cache_metadata(true,[home(-8,[w])]),Code,Code,excluded(setjmp)),
    forall(member(I,[ins(mystery,q,[]),ins(mov,q,[mem(0,r10),reg(rax)])]),
           (append(Code,[I],Unsupported),
            cache_asm(local,cache_metadata(false,[home(-8,[w])]),
                      Unsupported,Unsupported,excluded(unsupported)))).

backend :-
    M = module([func(calc,export,l,[param(p,tmp(p)),param(l,tmp(x))],[
        block(s,[],[let(tmp(y),l,add,[tmp(x),const(17)]),
                    let(tmp(z),l,mul,[tmp(y),tmp(y)]),
                    let(tmp(r),l,sub,[tmp(z),tmp(y)])],ret(tmp(r)))])]),
    valid_module(M), pizlonate_module(M,C),
    filc_module_asm(C,Stack), filc_module_asm(C,stack,Stack,_),
    filc_module_asm(C,local,Cached,[function(calc,cached(_,N))]),
    N > 0, Stack \== Cached,
    frame_moves(Stack,Before), frame_moves(Cached,After), After < Before.

% Exercise the emitter's inventory, not hand-authored cache metadata.
% The integer region is profitable, but its homes later hold floats.
mixed_homes :-
    forall((member(I,[w,l]),member(F,[s,d])), mixed_home(I,F)).

mixed_home(I,F) :-
    Prefix = [let(tmp(y),I,add,[tmp(x),tmp(x)]),
              let(tmp(z),I,add,[tmp(y),tmp(x)])],
    Tail = [let(tmp(a),F,copy,[const(0)]),
            let(tmp(b),F,add,[tmp(a),tmp(a)])],
    append(Prefix,Tail,Is),
    Bs = [block(s,[],Is,ret(tmp(b)))],
    Func = func(mixed,export,F,[param(I,tmp(x))],Bs),
    M = module([Func]), valid_module(M),
    lower_function(M,Func,Bs,Product),
    Product = abi_function(_,_,_,_,frame(_,_,Aliases),_,_,_,_,_),
    memberchk(tmp(x)-Home,Aliases), memberchk(tmp(a)-Home,Aliases),
    memberchk(tmp(y)-Other,Aliases), memberchk(tmp(b)-Other,Aliases),
    filc_module_asm(M,Stack),
    filc_module_asm(M,local,Stack,[function(mixed,cached(_,0))]),
    % Without the later float aliases, those same integer reads cache.
    Control = module([func(integer,export,I,[param(I,tmp(x))],
                           [block(s,[],Prefix,ret(tmp(z)))])]),
    filc_module_asm(Control,local,_,[function(integer,cached(_,N))]), N > 0.

dead_setjmp :-
    M = module([func(dead_jump,export,l,[param(p,tmp(buf)),param(l,tmp(x))],[
        block(s,[],[let(tmp(y),l,add,[tmp(x),const(7)])],ret(tmp(y))),
        block(dead,[],[let(tmp(j),w,setjmp('_setjmp'),[tmp(buf),const(0)])],
              ret(const(0)))])]),
    valid_module(M),
    forall(member(O,[o0,o1]),
           (optimize(O,M,Optimized),pizlonate_module(Optimized,C),
            filc_module_asm(C,Stack),
            filc_module_asm(C,local,Stack,[function(dead_jump,excluded(setjmp))]))).

frame_moves(Lines,N) :-
    findall(1,(member(ins(mov,_,Ops),Lines),member(mem(_,rbp),Ops)),Xs),
    length(Xs,N).
