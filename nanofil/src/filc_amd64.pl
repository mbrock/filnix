/*  Naive Fil-C lowering for x86-64 (milestone 3).

    Emits GNU as text that links with clang-built Fil-C code at the filnix
    pin (Fil-C 0.686). The rules are in docs/m3.md; in short:

    - Every temporary has an 8-byte frame slot, as in amd64.pl. A p
      temporary's slot holds its address, and its lower lives in a
      lowers[] entry of a filc_frame pushed on thread->top_frame, for the
      whole function. Values are never kept in registers across a call or
      safepoint, so every live capability is always in a scanned slot.
    - Every access gets the full check sequence; pointer loads and stores
      go through the aux array, with ensure-aux and the store barrier.
    - alloc is a heap allocation. Back edges in block order pollcheck.
    - Calls use the fast convention (thread, callee lower, words...) and
      propagate has_exception by popping the frame and returning AL = 1.
    - Exported functions get an alias, a getter, a function object and a
      generic entry, so clang code can call them directly or indirectly.

    Integer instructions are emitted by amd64:op//4 unchanged.
*/
:- module(filc_amd64, [print_filc_asm/1, signature/3]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).
:- use_module(amd64).

print_filc_asm(module(Items)) :-
    maplist(item_chars(module(Items)), Items, Css),
    append(Css, Cs0),
    append(Cs0, "\t.section .note.GNU-stack,\"\",@progbits\n", Cs),
    format("~s", [Cs]).

item_chars(M, I, Cs) :-
    (   phrase(item(M, I), Cs) -> true
    ;   arg(1, I, Name),
        format(atom(Msg), 'Fil-C backend cannot emit $~w', [Name]),
        throw(nanofil_error(Msg))
    ).

%% Signatures (docs/abi-findings.md): each word class is a bijective
%% base-11 digit, i64 = 0 and ptr = 7, and sig = 1 + ret + 133 * args.

signature(Ret, ParamKs, Sig) :-
    ret_digits(Ret, RDs),
    maplist(class_digit, ParamKs, ADs),
    length(ADs, NA),
    (   NA =< 16 -> true
    ;   throw(nanofil_error('more than 16 arguments'))
    ),
    bijective(RDs, R),
    bijective(ADs, A),
    Sig is 1 + R + 133 * A.

ret_digits(void, []).
ret_digits(K, [D]) :- class_digit(K, D).

class_digit(w, 0).
class_digit(l, 0).
class_digit(p, 7).

bijective([], 0).
bijective([D|Ds], V) :- bijective(Ds, V1), V is D + 1 + 11 * V1.

fn_sig(func(_, _, Ret, Params, _), Sig) :-
    findall(K, member(par(K, _), Params), Ks),
    signature(Ret, Ks, Sig).

%% Frame layout

/* Slots maps t(N), shadow(N) to address slots and lower(Key) to lowers[]
   entries, all as offsets below %rbp; thread and aux are scratch slots.
   The filc_frame {parent, origin, lowers[NL]} sits at -FB(%rbp). */
layout(Params, Blocks, Slots, FB, NL, Size) :-
    findall(N-K, ( member(par(K, t(N)), Params)
                 ; member(blk(_, Phis, Insts, _), Blocks),
                   (   member(phi(t(N), K, _), Phis)
                   ;   member(I, Insts), defines(I, N, K)
                   ) ), TKs0),
    sort(TKs0, TKs),
    findall(N-K, ( member(blk(_, Phis, _, _), Blocks),
                   member(phi(t(N), K, _), Phis) ), SKs0),
    sort(SKs0, SKs),
    findall(t(N), member(N-_, TKs), Ts),
    findall(shadow(N), member(N-_, SKs), Ss),
    append([Ts, Ss, [thread, aux]], Plain),
    findall(lower(t(N)), member(N-p, TKs), L1),
    findall(lower(shadow(N)), member(N-p, SKs), L2),
    append(L1, L2, Lowers),
    length(Plain, NP), length(Lowers, NL),
    FB is 8 * NP + 16 + 8 * NL,
    empty_assoc(E),
    foldl(plain_slot, Plain, E-0, S1-_),
    foldl(lower_slot(FB), Lowers, S1-0, Slots-_),
    Size is (FB + 15) // 16 * 16.

defines(ins(t(N), K, _, _), N, K).
defines(call(to(t(N), K), _, _), N, K).

plain_slot(Key, A0-I0, A-I) :-
    I is I0 + 1, Off is 8 * I, put_assoc(Key, A0, Off, A).

lower_slot(FB, Key, A0-I0, A-I) :-
    Off is FB - 16 - 8 * I0, I is I0 + 1, put_assoc(Key, A0, Off, A).

slot(c(_, _, Slots, _, _), Key, Off) :- get_assoc(Key, Slots, Off).

%% Functions

/* Ctx = c(Name, Ret, Slots, Blocks, x(Module, FB, Labels)), shaped so
   amd64's helpers, which read the first four arguments of f/4, work on
   f(Name, Ret, Slots, Blocks). */
item(M, F) -->
    { F = func(Name, Lk, Ret, Params, Blocks),
      fn_sig(F, Sig),
      layout(Params, Blocks, Slots, FB, NL, Size),
      findall(L, member(blk(L, _, _, _), Blocks), Labels),
      Ctx = c(Name, Ret, Slots, Blocks, x(M, FB, Labels)),
      impl_symbol(Name, Sig, Impl),
      check_kinds(Blocks, Kinds) },
    "\t.text\n\t.p2align 4\n",
    (   { Lk == export } -> fmt("\t.globl ~w~n", [Impl]) ; [] ),
    fmt("\t.type ~w, @function~n~w:~n", [Impl, Impl]),
    ins("pushq %rbp"), ins("movq %rsp, %rbp"),
    ins("subq $~w, %rsp", [Size]),
    ins("cmpq %rsp, (%rdi)"),
    ins("jae filc_stack_overflow_failure@PLT"),
    to_slot('%rdi', thread, Ctx),
    zero_lowers(NL, FB),
    ins("movq 16(%rdi), %rax"), ins("movq %rax, -~w(%rbp)", [FB]),
    set_origin(Ctx, c),
    ins("leaq -~w(%rbp), %rax", [FB]), ins("movq %rax, 16(%rdi)"),
    { param_words(Params, Words) },
    receive_words(Words, 0, Ctx),
    blocks(Blocks, Ctx),
    special(Ctx, exc), ":\n",
    pop_frame(Ctx), ins("movb $1, %al"), ins("leave"), ins("ret"),
    fail_blocks(Kinds, Ctx),
    fmt("\t.size ~w, .-~w~n", [Impl, Impl]),
    (   { Lk == export } -> exported(Name, Ret, Params, Sig, Impl) ; [] ),
    origins(Name, NL, Kinds).
item(_, data(Name, _, _, _)) -->
    { format(atom(Msg), 'data $~w is not supported in Fil-C mode yet', [Name]),
      throw(nanofil_error(Msg)) }.

impl_symbol(Name, Sig, Impl) :- format(atom(Impl), 'pizlonatedFIP~w_~w', [Sig, Name]).

zero_lowers(0, _) --> !.
zero_lowers(N, FB) -->
    ins("xorl %eax, %eax"),
    { N1 is N - 1, numlist(0, N1, Is) },
    zero_each(Is, FB).

zero_each([], _) --> [].
zero_each([I|Is], FB) -->
    { Off is FB - 16 - 8 * I },
    ins("movq %rax, -~w(%rbp)", [Off]),
    zero_each(Is, FB).

% The frame's origin: c (calls, can_catch) or n (pollchecks and checks).
set_origin(Ctx, Which) -->
    { Ctx = c(Name, _, _, _, x(_, FB, _)), O is FB - 8 },
    ins("leaq .L~w..origin_~w(%rip), %rax", [Name, Which]),
    ins("movq %rax, -~w(%rbp)", [O]).

pop_frame(Ctx) -->
    { Ctx = c(_, _, _, _, x(_, FB, _)) },
    from_slot(thread, '%rsi', Ctx),
    ins("movq -~w(%rbp), %rdi", [FB]),
    ins("movq %rdi, 16(%rsi)").

special(c(Name, _, _, _, _), Tag) --> fmt(".L~w..~w", [Name, Tag]).

label(c(Name, _, _, _, _), L) --> fmt(".L~w.~w", [Name, L]).

local(c(Name, _, _, _, _), B, I, Tag) --> fmt(".L~w.~w..~w.~w", [Name, B, I, Tag]).

to_slot(Reg, Key, Ctx) --> { slot(Ctx, Key, Off) }, ins("movq ~w, -~w(%rbp)", [Reg, Off]).
from_slot(Key, Reg, Ctx) --> { slot(Ctx, Key, Off) }, ins("movq -~w(%rbp), ~w", [Off, Reg]).

f4(c(N, R, S, B, _), f(N, R, S, B)).

%% Words: a p value is two words (address, lower); w and l are one.

param_words(Params, Words) :-
    foldl(param_words_, Params, Words, []).
param_words_(par(p, t(N)), [t(N), lower(t(N))|Ws], Ws) :- !.
param_words_(par(_, t(N)), [t(N)|Ws], Ws).

word_reg(0, '%rdx'). word_reg(1, '%rcx'). word_reg(2, '%r8'). word_reg(3, '%r9').

receive_words([], _, _) --> [].
receive_words([W|Ws], I, Ctx) -->
    (   { word_reg(I, R) } -> to_slot(R, W, Ctx)
    ;   { Off is 16 + 8 * (I - 4) },
        ins("movq ~w(%rbp), %rax", [Off]),
        to_slot('%rax', W, Ctx)
    ),
    { I1 is I + 1 },
    receive_words(Ws, I1, Ctx).

%% Blocks and jumps

blocks([], _) --> [].
blocks([blk(L, _, Insts, J)|Bs], Ctx) -->
    label(Ctx, L), ":\n",
    insts(Insts, 0, L, Ctx),
    jump(J, L, Ctx),
    blocks(Bs, Ctx).

jump(jmp(T), From, Ctx) --> edge(From, T, j, Ctx).
jump(jnz(V, T, F), From, Ctx) -->
    { f4(Ctx, F4) },
    load(V, w, a, F4),
    ins("testl %eax, %eax"),
    "\tjz ", local(Ctx, From, jnz, false), "\n",
    edge(From, T, t, Ctx),
    local(Ctx, From, jnz, false), ":\n",
    edge(From, F, f, Ctx).
jump(ret(V), _, Ctx) -->
    { Ctx = c(_, K, _, _, _), f4(Ctx, F4) },
    (   { K == p } -> load(V, l, d, F4), lower_of(V, '%rcx', Ctx)
    ;   load(V, K, d, F4)
    ),
    pop_frame(Ctx), ins("xorl %eax, %eax"), ins("leave"), ins("ret").
jump(ret, _, Ctx) -->
    pop_frame(Ctx), ins("xorl %eax, %eax"), ins("leave"), ins("ret").
jump(hlt, _, _) --> ins("ud2").

% Phi copies for the edge, a pollcheck if it goes backwards in block
% order, then the jump.
edge(From, To, Tag, Ctx) -->
    { Ctx = c(_, _, _, Blocks, x(_, _, Labels)),
      memberchk(blk(To, Phis, _, _), Blocks) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    (   { nth0(IF, Labels, From), nth0(IT, Labels, To), IT =< IF }
    ->  pollcheck(Ctx, From, Tag)
    ;   []
    ),
    "\tjmp ", label(Ctx, To), "\n".

pollcheck(Ctx, B, Tag) -->
    { Ctx = c(Name, _, _, _, _) },
    from_slot(thread, '%rdi', Ctx),
    ins("testb $14, 8(%rdi)"),
    "\tjz ", local(Ctx, B, Tag, poll), "\n",
    ins("leaq .L~w..origin_n(%rip), %rsi", [Name]),
    ins("call filc_pollcheck_slow@PLT"),
    local(Ctx, B, Tag, poll), ":\n".

phi_reads([], _, _) --> [].
phi_reads([phi(t(D), K, Pairs)|Ps], From, Ctx) -->
    { memberchk(From-V, Pairs), f4(Ctx, F4) },
    (   { K == p }
    ->  load(V, l, a, F4), to_slot('%rax', shadow(D), Ctx),
        lower_of(V, '%rax', Ctx), to_slot('%rax', lower(shadow(D)), Ctx)
    ;   load(V, K, a, F4), to_slot('%rax', shadow(D), Ctx)
    ),
    phi_reads(Ps, From, Ctx).

phi_writes([], _) --> [].
phi_writes([phi(t(D), K, _)|Ps], Ctx) -->
    from_slot(shadow(D), '%rax', Ctx), to_slot('%rax', t(D), Ctx),
    (   { K == p }
    ->  from_slot(lower(shadow(D)), '%rax', Ctx), to_slot('%rax', lower(t(D)), Ctx)
    ;   []
    ),
    phi_writes(Ps, Ctx).

% The lower of a p value: its lowers[] entry, or 0 for a constant.
lower_of(t(N), Reg, Ctx) --> from_slot(lower(t(N)), Reg, Ctx).
lower_of(c(_), Reg, _) --> ins("movq $0, ~w", [Reg]).

% A p value's address into %rax and lower into %rcx.
flight(V, Ctx) --> { f4(Ctx, F4) }, load(V, l, a, F4), lower_of(V, '%rcx', Ctx).

%% Instructions

insts([], _, _, _) --> [].
insts([I|Is], N, B, Ctx) --> inst(I, N, B, Ctx), { N1 is N + 1 }, insts(Is, N1, B, Ctx).

inst(ins(t(D), p, copy, [V]), _, _, Ctx) --> !,
    flight(V, Ctx), set_p(D, Ctx).
inst(ins(t(D), p, Op, [P, X]), _, _, Ctx) --> { memberchk(Op, [add, sub]) }, !,
    { f4(Ctx, F4) },
    flight(P, Ctx), load(X, l, d, F4),
    ins("~wq %rdx, %rax", [Op]),
    set_p(D, Ctx).
inst(ins(t(D), l, ptoi, [P]), _, _, Ctx) --> !,
    { f4(Ctx, F4) }, load(P, l, a, F4), to_slot('%rax', t(D), Ctx).
inst(ins(t(D), p, itop, [X]), _, _, Ctx) --> !,
    { f4(Ctx, F4) }, load(X, l, a, F4), ins("xorl %ecx, %ecx"), set_p(D, Ctx).
inst(ins(t(D), p, alloc(Align), [N]), _, _, Ctx) --> !,
    { f4(Ctx, F4) },
    load(N, l, si, F4),
    from_slot(thread, '%rdi', Ctx),
    (   { Align == 16 }
    ->  ins("movl $16, %edx"), ins("call filc_allocate_with_alignment@PLT")
    ;   ins("call filc_allocate@PLT")
    ),
    ins("leaq 16(%rax), %rax"), ins("movq %rax, %rcx"),
    set_p(D, Ctx).
inst(ins(t(D), p, load(p), [A]), N, B, Ctx) --> !,
    flight(A, Ctx),
    check(k(8, 0, 8), Ctx),
    ins("movq -8(%rcx), %rdx"),
    ins("movabsq $281474976710655, %rsi"),
    ins("andq %rsi, %rdx"),
    "\tjz ", local(Ctx, B, N, nolower), "\n",
    ins("movq %rax, %rsi"), ins("subq %rcx, %rsi"),
    ins("movq (%rdx,%rsi), %rsi"),
    ins("testb $1, %sil"),
    "\tjz ", local(Ctx, B, N, have), "\n",
    ins("andq $-2, %rsi"), ins("movq 8(%rsi), %rsi"),
    "\tjmp ", local(Ctx, B, N, have), "\n",
    local(Ctx, B, N, nolower), ":\n",
    ins("xorl %esi, %esi"),
    local(Ctx, B, N, have), ":\n",
    ins("movq (%rax), %rax"), ins("movq %rsi, %rcx"),
    set_p(D, Ctx).
inst(ins(t(D), K, load(T), [A]), _, _, Ctx) --> !,
    { width_of_load(T, S), load_insn(T, K, I) },
    flight(A, Ctx),
    check(k(S, 0, 1), Ctx),
    ins(I),
    to_slot('%rax', t(D), Ctx).
inst(ins(t(D), K, Op, Args), _, _, Ctx) -->
    { f4(Ctx, F4) },
    op(Op, K, Args, F4),
    to_slot('%rax', t(D), Ctx).
inst(store(p, V, A), N, B, Ctx) --> !,
    { f4(Ctx, F4) },
    flight(A, Ctx),
    check(k(8, 1, 8), Ctx),
    ins("movq -8(%rcx), %rdx"),
    ins("movabsq $281474976710655, %rsi"),
    ins("andq %rsi, %rdx"),
    "\tjnz ", local(Ctx, B, N, haveaux), "\n",
    from_slot(thread, '%rdi', Ctx),
    ins("leaq -16(%rcx), %rsi"),
    ins("call filc_object_ensure_aux_ptr_outline@PLT"),
    ins("movq %rax, %rdx"),
    local(Ctx, B, N, haveaux), ":\n",
    to_slot('%rdx', aux, Ctx),
    lower_of(V, '%rsi', Ctx),
    ins("testq %rsi, %rsi"),
    "\tjz ", local(Ctx, B, N, nobarrier), "\n",
    ins("movq filc_current_marking_state@GOTPCREL(%rip), %rax"),
    ins("cmpl $0, (%rax)"),
    "\tje ", local(Ctx, B, N, nobarrier), "\n",
    from_slot(thread, '%rdi', Ctx),
    ins("call filc_store_barrier_for_lower_slow@PLT"),
    local(Ctx, B, N, nobarrier), ":\n",
    flight(A, Ctx),
    from_slot(aux, '%rdx', Ctx),
    ins("movq %rax, %r8"), ins("subq %rcx, %r8"),
    lower_of(V, '%rsi', Ctx),
    load(V, l, r9, F4),
    ins("movq %rsi, (%rdx,%r8)"),
    ins("movq %r9, (%rax)").
inst(store(W, V, A), _, _, Ctx) -->
    { f4(Ctx, F4), width_bytes(W, S), ( W == l -> VK = l ; VK = w ), store_d(W, I) },
    flight(A, Ctx),
    check(k(S, 1, 1), Ctx),
    load(V, VK, d, F4),
    ins(I).
inst(call(Res, glo(F), Args), _, _, Ctx) -->
    { f4(Ctx, F4),
      call_target(Ctx, F, Res, Args, Target),
      foldl(arg_words, Args, Words, []),
      length(Words, NW),
      (   NW > 4 -> length(RegWs, 4), append(RegWs, StackWs, Words)
      ;   RegWs = Words, StackWs = []
      ),
      length(StackWs, NS),
      Pad is NS mod 2,
      Pop is 8 * (NS + Pad),
      reverse(StackWs, RevStack) },
    set_origin(Ctx, c),
    (   { Pad =:= 1 } -> ins("subq $8, %rsp") ; [] ),
    push_words(RevStack, F4, Ctx),
    reg_words(RegWs, 0, F4, Ctx),
    from_slot(thread, '%rdi', Ctx),
    ins("xorl %esi, %esi"),
    ins("call ~w", [Target]),
    (   { Pop > 0 } -> ins("addq $~w, %rsp", [Pop]) ; [] ),
    ins("testb $1, %al"),
    "\tjnz ", special(Ctx, exc), "\n",
    call_result(Res, Ctx).

set_p(D, Ctx) --> to_slot('%rax', t(D), Ctx), to_slot('%rcx', lower(t(D)), Ctx).

width_of_load(T, S) :- memberchk(T-S, [l-8, sw-4, uw-4, sh-2, uh-2, sb-1, ub-1]).

store_d(b, "movb %dl, (%rax)").
store_d(h, "movw %dx, (%rax)").
store_d(w, "movl %edx, (%rax)").
store_d(l, "movq %rdx, (%rax)").

% Functions in the module are called at their implementation; others at
% their pizlonatedFI symbol, which a clang definition with the same
% signature provides.
call_target(Ctx, F, Res, Args, Target) :-
    Ctx = c(_, _, _, _, x(M, _, _)),
    (   func_named(M, F, Fn)
    ->  fn_sig(Fn, Sig), impl_symbol(F, Sig, Target)
    ;   ( Res = to(_, RK) -> true ; RK = void ),
        findall(K, member(arg(K, _), Args), Ks),
        signature(RK, Ks, Sig),
        format(atom(Target), 'pizlonatedFI~w_~w@PLT', [Sig, F])
    ).

arg_words(arg(p, V), [addr(V), lower(V)|Ws], Ws) :- !.
arg_words(arg(K, V), [val(K, V)|Ws], Ws).

word_into(addr(V), R, F4, _) --> load(V, l, R, F4).
word_into(val(K, V), R, F4, _) --> load(V, K, R, F4).
word_into(lower(V), R, _, Ctx) --> { reg(R, l, RN) }, lower_of(V, RN, Ctx).

push_words([], _, _) --> [].
push_words([W|Ws], F4, Ctx) --> word_into(W, a, F4, Ctx), ins("pushq %rax"), push_words(Ws, F4, Ctx).

reg_words([], _, _, _) --> [].
reg_words([W|Ws], I, F4, Ctx) -->
    { nth0(I, [d, c, r8, r9], R), I1 is I + 1 },
    word_into(W, R, F4, Ctx),
    reg_words(Ws, I1, F4, Ctx).

call_result(void, _) --> [].
call_result(to(t(D), p), Ctx) --> !, ins("movq %rdx, %rax"), set_p(D, Ctx).
call_result(to(t(D), _), Ctx) --> to_slot('%rdx', t(D), Ctx).

%% Checks: k(Size, Write, Align), with the pointer in %rax and its lower
%% in %rcx, which the failure block passes on.

check(k(S, W, A), Ctx) -->
    { fail_label(Ctx, k(S, W, A), FL) },
    ins("testq %rcx, %rcx"), ins("jz ~w", [FL]),
    ins("cmpq %rcx, %rax"), ins("jb ~w", [FL]),
    ins("movq -16(%rcx), %rdx"), ins("subq $~w, %rdx", [S]),
    ins("cmpq %rdx, %rax"), ins("ja ~w", [FL]),
    (   { W =:= 1 } -> ins("testb $6, -2(%rcx)"), ins("jnz ~w", [FL]) ; [] ),
    (   { A =:= 8 } -> ins("testb $7, %al"), ins("jnz ~w", [FL]) ; [] ).

fail_label(c(Name, _, _, _, _), k(S, W, A), L) :-
    format(atom(L), '.L~w..fail.~w.~w.~w', [Name, S, W, A]).

check_kinds(Blocks, Kinds) :-
    findall(K, ( member(blk(_, _, Is, _), Blocks), member(I, Is), inst_check(I, K) ), K0),
    sort(K0, Kinds).

inst_check(ins(_, _, load(p), _), k(8, 0, 8)) :- !.
inst_check(ins(_, _, load(T), _), k(S, 0, 1)) :- width_of_load(T, S).
inst_check(store(p, _, _), k(8, 1, 8)) :- !.
inst_check(store(W, _, _), k(S, 1, 1)) :- width_bytes(W, S).

fail_blocks([], _) --> [].
fail_blocks([K|Ks], Ctx) -->
    { fail_label(Ctx, K, L), Ctx = c(Name, _, _, _, _), K = k(S, W, A) },
    fmt("~w:~n", [L]),
    ins("movq %rax, %rdi"), ins("movq %rcx, %rsi"),
    ins("leaq .L~w..chk.~w.~w.~w(%rip), %rdx", [Name, S, W, A]),
    ins("call filc_optimized_access_check_fail@PLT"),
    ins("ud2"),
    fail_blocks(Ks, Ctx).

%% Exported functions: alias, getter, generic entry, function object.

exported(Name, Ret, Params, Sig, Impl) -->
    { format(atom(FI), 'pizlonatedFI~w_~w', [Sig, Name]),
      format(atom(FO), 'pizlonatedFO_~w', [Name]),
      format(atom(G), 'pizlonated_~w', [Name]),
      format(atom(Gen), '.L~w..generic', [Name]) },
    fmt("\t.globl ~w~n\t.type ~w, @function~n\t.set ~w, ~w~n", [FI, FI, FI, Impl]),
    fmt("\t.globl ~w~n\t.type ~w, @function~n~w:~n", [G, G, G]),
    ins("leaq ~w+16(%rip), %rax", [FO]), ins("movq %rax, %rdx"), ins("ret"),
    generic(Gen, Ret, Params),
    fmt("\t.section .data.rel.ro,\"aw\",@progbits~n\t.p2align 4~n\t.type ~w, @object~n~w:~n", [FO, FO]),
    ins(".quad ~w+16", [FO]),
    ins(".quad (~w+16)+36873221949095936", [FO]),
    ins(".quad ~w", [Impl]),
    ins(".quad ~w", [Gen]),
    ins(".quad ~w", [Sig]),
    fmt("\t.size ~w, 40~n", [FO]).

/* The generic entry: {i1, i64 ret_size} (thread, callee_lower, args_size).
   Argument i is 8 bytes at thread+128+8i, with its lower (for p) at
   thread+384+8i. It calls the fast entry through callee_lower. */
generic(Gen, Ret, Params) -->
    { length(Params, NA), Need is 8 * NA,
      findall(W, ( nth0(I, Params, par(K, _)), generic_word(K, I, W) ), Ws0),
      append(Ws0, Words),
      length(Words, NW),
      (   NW > 4 -> length(RegWs, 4), append(RegWs, StackWs, Words)
      ;   RegWs = Words, StackWs = []
      ),
      length(StackWs, NS), Pad is NS mod 2, Pop is 8 * (NS + Pad),
      reverse(StackWs, Rev) },
    "\t.text\n",
    fmt("~w:~n", [Gen]),
    ins("pushq %rbx"),
    (   { NA > 0 }
    ->  ins("cmpq $~w, %rdx", [Need]),
        fmt("\tjb ~w.short~n", [Gen])
    ;   []
    ),
    ins("movq %rdi, %rbx"),
    (   { Pad =:= 1 } -> ins("subq $8, %rsp") ; [] ),
    gen_push(Rev),
    gen_regs(RegWs, ['%rdx', '%rcx', '%r8', '%r9']),
    ins("callq *(%rsi)"),
    (   { Pop > 0 } -> ins("addq $~w, %rsp", [Pop]) ; [] ),
    ins("testb $1, %al"),
    fmt("\tjnz ~w.done~n", [Gen]),
    (   { Ret == p } -> ins("movq %rdx, 128(%rbx)"), ins("movq %rcx, 384(%rbx)")
    ;   { Ret == void } -> ins("movq $0, 128(%rbx)"), ins("movq $0, 384(%rbx)")
    ;   ins("movq %rdx, 128(%rbx)"), ins("movq $0, 384(%rbx)")
    ),
    ins("movl $8, %edx"),
    fmt("~w.done:~n", [Gen]),
    ins("popq %rbx"), ins("ret"),
    (   { NA > 0 }
    ->  fmt("~w.short:~n", [Gen]),
        ins("movq %rdx, %rdi"), ins("movl $~w, %esi", [Need]), ins("xorl %edx, %edx"),
        ins("call filc_cc_args_check_failure@PLT"), ins("ud2")
    ;   []
    ).

generic_word(p, I, [D, A]) :- !, D is 128 + 8 * I, A is 384 + 8 * I.
generic_word(_, I, [D]) :- D is 128 + 8 * I.

gen_push([]) --> [].
gen_push([Off|Os]) --> ins("pushq ~w(%rbx)", [Off]), gen_push(Os).

gen_regs([], _) --> [].
gen_regs([Off|Os], [R|Rs]) --> ins("movq ~w(%rbx), ~w", [Off, R]), gen_regs(Os, Rs).

%% Static data: function origins (the pin's 40-byte layout), origins,
%% and one access-check origin per check kind.

origins(Name, NL, Kinds) -->
    fmt("\t.section .rodata~n.L~w..name:~n\t.asciz \"~w\"~n", [Name, Name]),
    "\t.section .data.rel.ro,\"aw\",@progbits\n\t.p2align 4\n",
    function_origin(Name, NL, c, 1),
    function_origin(Name, NL, n, 0),
    check_origins(Kinds, Name).

function_origin(Name, NL, Which, CanCatch) -->
    fmt(".L~w..forigin_~w:~n", [Name, Which]),
    ins(".quad .L~w..name", [Name]),
    ins(".quad 0"),
    ins(".long ~w", [NL]), ins(".zero 4"),
    ins(".quad 0"),
    ins(".byte 0, ~w, 0", [CanCatch]), ins(".zero 1"),
    ins(".long 0"),
    fmt(".L~w..origin_~w:~n", [Name, Which]),
    ins(".quad .L~w..forigin_~w", [Name, Which]),
    ins(".long 0"), ins(".long 0").

check_origins([], _) --> [].
check_origins([k(S, W, A)|Ks], Name) -->
    "\t.p2align 4\n",
    fmt(".L~w..chk.~w.~w.~w:~n", [Name, S, W, A]),
    ins(".long ~w", [S]),
    ins(".byte ~w, 0, ~w", [A, W]), ins(".zero 1"),
    ins(".quad .L~w..origin_n", [Name]),
    ins(".quad .L~w..origin_n", [Name]),
    ins(".quad 0"),
    check_origins(Ks, Name).

% library(format)'s format_//2 rejects an argument of ''.
fmt(F, As) --> { format(chars(Cs), F, As) }, seq(Cs).
