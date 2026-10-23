/*  Naive Fil-C lowering for x86-64 (milestone 3).

    Emits asm.pl lines whose GNU as text links with clang-built Fil-C code at the filnix
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
:- module(filc_amd64, [filc_module_asm/2, signature/3]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).
:- use_module(amd64).

% filc_module_asm(+Module, -Lines): the module as asm.pl lines.
filc_module_asm(module(Items), Lines) :-
    M = module(Items),
    maplist(item_lines(M), Items, Ls),
    append(Ls, Lines0),
    external_callees(M, Ts),
    maplist(thunk_lines, Ts, TLs),
    append(TLs, Lines1),
    append([Lines0, Lines1, [section(note_gnu_stack)]], Lines).

thunk_lines(T, Ls) :- phrase(thunk(T), Ls).

item_lines(M, I, Ls) :-
    (   phrase(item(M, I), Ls) -> true
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
ret_digits(tuple(Ks), Ds) :- !, maplist(class_digit, Ks, Ds).
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
layout(Form, Params, Blocks, Slots, FB, NL, Size) :-
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
    ( Form = mem(_) -> Extra = [retbuf] ; Extra = [] ),
    append([Ts, Ss, [thread, aux], Extra], Plain),
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
defines(call(tuple(Tos), _, _), N, K) :- member(to(t(N), K), Tos).

plain_slot(Key, A0-I0, A-I) :-
    I is I0 + 1, Off is 8 * I, put_assoc(Key, A0, Off, A).

lower_slot(FB, Key, A0-I0, A-I) :-
    Off is FB - 16 - 8 * I0, I is I0 + 1, put_assoc(Key, A0, Off, A).

slot(c(_, _, Slots, _, _), Key, Off) :- get_assoc(Key, Slots, Off).

%% Functions

/* Ctx = c(Name, Ret, Slots, Blocks, x(Module, FB, Labels)), shaped so
   amd64's helpers, which read the first four arguments of f/4, work on
   f(Name, Ret, Slots, Blocks). Labels indexes each block's position and
   phis once, instead of searching Blocks on every edge. */
item(M, F) -->
    { F = func(Name, Lk, Ret, Params, Blocks),
      fn_sig(F, Sig),
      ret_kinds(Ret, RKs), ret_form(RKs, Form),
      layout(Form, Params, Blocks, Slots, FB, NL, Size),
      findall(L-block(I, Ps), nth0(I, Blocks, blk(L, Ps, _, _)), LPs),
      list_to_assoc(LPs, Labels),
      Ctx = c(Name, Ret, Slots, Blocks, x(M, FB, Labels)),
      impl_symbol(Name, Sig, Impl),
      check_kinds(Blocks, Kinds),
      special(Ctx, exc, Exc), NFB is -FB },
    [section(text), p2align(4)],
    (   { Lk == export } -> [globl(Impl)] ; [] ),
    [type(Impl, function), label(Impl),
     ins(push, q, [reg(rbp)]), ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(sub, q, [imm(Size), reg(rsp)])],
    (   { Form = mem(_) } -> [ins(mov, q, [reg(rdi), reg(rax)]), ins(mov, q, [reg(rsi), reg(rdi)])] ; [] ),
    [ins(cmp, q, [reg(rsp), mem(0, rdi)]),
     ins(jae, none, [plt(filc_stack_overflow_failure)])],
    to_slot(rdi, thread, Ctx),
    (   { Form = mem(_) } -> to_slot(rax, retbuf, Ctx) ; [] ),
    zero_lowers(NL, FB),
    [ins(mov, q, [mem(16, rdi), reg(rax)]), ins(mov, q, [reg(rax), mem(NFB, rbp)])],
    set_origin(Ctx, c),
    [ins(lea, q, [mem(NFB, rbp), reg(rax)]), ins(mov, q, [reg(rax), mem(16, rdi)])],
    { param_words(Params, Words), form_regs(Form, Regs) },
    receive_words(Words, Regs, 0, Ctx),
    blocks(Blocks, Ctx),
    [label(Exc)],
    pop_frame(Ctx),
    (   { Form = mem(_) }
    ->  from_slot(retbuf, rax, Ctx), [ins(mov, b, [imm(1), mem(0, rax)])]
    ;   [ins(mov, b, [imm(1), reg(al)])]
    ),
    [ins(leave, none, []), ins(ret, none, [])],
    fail_blocks(Kinds, Ctx),
    (   { member(blk(_, _, Is, _), Blocks), memberchk(call(_, t(_), _), Is) }
    ->  { special(Ctx, notfn, NotFn) },
        [label(NotFn), ins(mov, q, [reg(rax), reg(rdi)]), ins(mov, q, [reg(rcx), reg(rsi)]),
         ins(call, none, [plt(filc_check_function_call_fail)]), ins(ud2, none, [])]
    ;   []
    ),
    [size(Impl)],
    function_object(Name, Lk, Ret, Params, Sig, Impl),
    origins(Name, NL, Kinds).
item(_, data(Name, Lk, _, Items)) --> data_object(Name, Lk, Items).

impl_symbol(Name, Sig, Impl) :- format(atom(Impl), 'pizlonatedFIP~w_~w', [Sig, Name]).

zero_lowers(0, _) --> !.
zero_lowers(N, FB) -->
    [ins(xor, l, [reg(eax), reg(eax)])],
    { N1 is N - 1, numlist(0, N1, Is) },
    zero_each(Is, FB).

zero_each([], _) --> [].
zero_each([I|Is], FB) -->
    { Off is 16 + 8 * I - FB },
    [ins(mov, q, [reg(rax), mem(Off, rbp)])],
    zero_each(Is, FB).

% The frame's origin: c (calls, can_catch) or n (pollchecks and checks).
set_origin(Ctx, Which) -->
    { Ctx = c(Name, _, _, _, x(_, FB, _)), O is 8 - FB, origin(Name, Which, Org) },
    [ins(lea, q, [rip(Org), reg(rax)]), ins(mov, q, [reg(rax), mem(O, rbp)])].

origin(Name, Which, A) :- format(atom(A), '.L~w..origin_~w', [Name, Which]).

pop_frame(Ctx) -->
    { Ctx = c(_, _, _, _, x(_, FB, _)), NFB is -FB },
    from_slot(thread, rsi, Ctx),
    [ins(mov, q, [mem(NFB, rbp), reg(rdi)]), ins(mov, q, [reg(rdi), mem(16, rsi)])].

special(c(Name, _, _, _, _), Tag, A) :- format(atom(A), '.L~w..~w', [Name, Tag]).

label(c(Name, _, _, _, _), L, A) :- format(atom(A), '.L~w.~w', [Name, L]).

local(c(Name, _, _, _, _), B, I, Tag, A) :- format(atom(A), '.L~w.~w..~w.~w', [Name, B, I, Tag]).

to_slot(Reg, Key, Ctx) -->
    { slot(Ctx, Key, Off), D is -Off }, [ins(mov, q, [reg(Reg), mem(D, rbp)])].
from_slot(Key, Reg, Ctx) -->
    { slot(Ctx, Key, Off), D is -Off }, [ins(mov, q, [mem(D, rbp), reg(Reg)])].

f4(c(N, R, S, B, _), f(N, R, S, B)).

%% Words: a p value is two words (address, lower); w and l are one.

param_words(Params, Words) :-
    foldl(param_words_, Params, Words, []).
param_words_(par(p, t(N)), [t(N), lower(t(N))|Ws], Ws) :- !.
param_words_(par(_, t(N)), [t(N)|Ws], Ws).

receive_words([], _, _, _) --> [].
receive_words([W|Ws], Regs, I, Ctx) -->
    (   { nth0(I, Regs, R) } -> to_slot(R, W, Ctx)
    ;   { length(Regs, NR), Off is 16 + 8 * (I - NR) },
        [ins(mov, q, [mem(Off, rbp), reg(rax)])],
        to_slot(rax, W, Ctx)
    ),
    { I1 is I + 1 },
    receive_words(Ws, Regs, I1, Ctx).

%% Results: none, one word or a tuple of two. A p word is two slots,
%% address and lower. Up to two slots come back in %rdx:%rcx; more go in
%% a buffer the caller passes in %rdi, {i8 has_exception, slots at 8..},
%% with the thread in %rsi, the callee lower in %rdx and the argument
%% words from %rcx (docs/abi-findings.md).

ret_kinds(void, []) :- !.
ret_kinds(tuple(Ks), Ks) :- !.
ret_kinds(K, [K]).

res_tos(void, []).
res_tos(to(T, K), [to(T, K)]).
res_tos(tuple(Tos), Tos).

res_ret(void, void).
res_ret(to(_, K), K).
res_ret(tuple(Tos), tuple(Ks)) :- findall(K, member(to(_, K), Tos), Ks).

% ret_form(Kinds, Form): reg, or mem(BufferBytes) rounded to 16.
ret_form(Ks, mem(BS)) :- foldl(slot_n, Ks, 0, N), N > 2, !, BS is (8 + 8 * N + 15) // 16 * 16.
ret_form(_, reg).

slot_n(p, N0, N) :- !, N is N0 + 2.
slot_n(_, N0, N) :- N is N0 + 1.

form_regs(reg, [rdx, rcx, r8, r9]).
form_regs(mem(_), [rcx, r8, r9]).

% The slots of a result, in order, as the frame slots they fill.
res_dests(Res, Ds) :- res_tos(Res, Tos), foldl(word_dests, Tos, Ds, []).
word_dests(to(T, p), [T, lower(T)|Ds], Ds) :- !.
word_dests(to(T, _), [T|Ds], Ds).

% gw(Kind, GenericOffset, Slot) for each result word: word I of a
% generic return is at thread+128+8I with its lower at thread+384+8I.
generic_words(Ks, GWs) :- generic_words(Ks, 0, 0, GWs).
generic_words([], _, _, []).
generic_words([K|Ks], I, J, [gw(K, D, J)|GWs]) :-
    D is 128 + 8 * I, I1 is I + 1, slot_n(K, J, J1),
    generic_words(Ks, I1, J1, GWs).

reserve(reg) --> [].
reserve(mem(BS)) --> [ins(sub, q, [imm(BS), reg(rsp)])].
release(reg) --> [].
release(mem(BS)) --> [ins(add, q, [imm(BS), reg(rsp)])].

%% Blocks and jumps

blocks([], _) --> [].
blocks([blk(L, _, Insts, J)|Bs], Ctx) -->
    { label(Ctx, L, A) },
    [label(A)],
    insts(Insts, 0, L, Ctx),
    jump(J, L, Ctx),
    blocks(Bs, Ctx).

jump(jmp(T), From, Ctx) --> edge(From, T, j, Ctx).
jump(jnz(V, T, F), From, Ctx) -->
    { f4(Ctx, F4), local(Ctx, From, jnz, false, FL) },
    load(V, w, a, F4),
    [ins(test, l, [reg(eax), reg(eax)]), ins(jz, none, [sym(FL)])],
    edge(From, T, t, Ctx),
    [label(FL)],
    edge(From, F, f, Ctx).
jump(ret(V), _, Ctx) -->
    { Ctx = c(_, K, _, _, _), f4(Ctx, F4) },
    (   { K == p } -> load(V, l, d, F4), lower_of(V, rcx, Ctx)
    ;   load(V, K, d, F4)
    ),
    return(Ctx).
jump(rets(Vs), _, Ctx) -->
    { Ctx = c(_, tuple(Ks), _, _, _), f4(Ctx, F4), ret_form(Ks, Form) },
    (   { Form == reg }
    ->  { Vs = [V1, V2] }, load(V1, l, d, F4), load(V2, l, c, F4), return(Ctx)
    ;   from_slot(retbuf, rax, Ctx),
        buffer_words(Ks, Vs, 8, Ctx),
        [ins(mov, b, [imm(0), mem(0, rax)])],
        pop_frame(Ctx),
        [ins(leave, none, []), ins(ret, none, [])]
    ).
jump(ret, _, Ctx) --> return(Ctx).
jump(hlt, _, _) --> [ins(ud2, none, [])].

% The words of a buffered return, into the buffer at %rax.
buffer_words([], [], _, _) --> [].
buffer_words([K|Ks], [V|Vs], Off, Ctx) -->
    { f4(Ctx, F4) },
    load(V, l, d, F4), [ins(mov, q, [reg(rdx), mem(Off, rax)])],
    (   { K == p }
    ->  { O1 is Off + 8, Off1 is Off + 16 },
        lower_of(V, rcx, Ctx), [ins(mov, q, [reg(rcx), mem(O1, rax)])]
    ;   { Off1 is Off + 8 }
    ),
    buffer_words(Ks, Vs, Off1, Ctx).

return(Ctx) -->
    pop_frame(Ctx),
    [ins(xor, l, [reg(eax), reg(eax)]), ins(leave, none, []), ins(ret, none, [])].

% Phi copies for the edge, a pollcheck if it goes backwards in block
% order, then the jump.
edge(From, To, Tag, Ctx) -->
    { Ctx = c(_, _, _, _, x(_, _, Labels)),
      get_assoc(From, Labels, block(IF, _)),
      get_assoc(To, Labels, block(IT, Phis)),
      label(Ctx, To, TL) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    (   { IT =< IF }
    ->  pollcheck(Ctx, From, Tag)
    ;   []
    ),
    [ins(jmp, none, [sym(TL)])].

pollcheck(Ctx, B, Tag) -->
    { Ctx = c(Name, _, _, _, _), local(Ctx, B, Tag, poll, PL), origin(Name, n, Org) },
    from_slot(thread, rdi, Ctx),
    [ins(test, b, [imm(14), mem(8, rdi)]),
     ins(jz, none, [sym(PL)]),
     ins(lea, q, [rip(Org), reg(rsi)]),
     ins(call, none, [plt(filc_pollcheck_slow)]),
     label(PL)].

phi_reads([], _, _) --> [].
phi_reads([phi(t(D), K, Pairs)|Ps], From, Ctx) -->
    { memberchk(From-V, Pairs), f4(Ctx, F4) },
    (   { K == p }
    ->  load(V, l, a, F4), to_slot(rax, shadow(D), Ctx),
        lower_of(V, rax, Ctx), to_slot(rax, lower(shadow(D)), Ctx)
    ;   load(V, K, a, F4), to_slot(rax, shadow(D), Ctx)
    ),
    phi_reads(Ps, From, Ctx).

phi_writes([], _) --> [].
phi_writes([phi(t(D), K, _)|Ps], Ctx) -->
    from_slot(shadow(D), rax, Ctx), to_slot(rax, t(D), Ctx),
    (   { K == p }
    ->  from_slot(lower(shadow(D)), rax, Ctx), to_slot(rax, lower(t(D)), Ctx)
    ;   []
    ),
    phi_writes(Ps, Ctx).

% The lower of a p value: its lowers[] entry, or 0 for a constant.
lower_of(t(N), Reg, Ctx) --> from_slot(lower(t(N)), Reg, Ctx).
lower_of(c(_), Reg, _) --> [ins(mov, q, [imm(0), reg(Reg)])].

% A p value's address into %rax and lower into %rcx.
flight(V, Ctx) --> { f4(Ctx, F4) }, load(V, l, a, F4), lower_of(V, rcx, Ctx).

%% Instructions

insts([], _, _, _) --> [].
insts([I|Is], N, B, Ctx) --> inst(I, N, B, Ctx), { N1 is N + 1 }, insts(Is, N1, B, Ctx).

inst(ins(t(D), p, copy, [glo(S)]), _, _, Ctx) --> !,
    { Ctx = c(Name, _, _, _, x(M, _, _)), getter(M, S, G), origin(Name, c, Org) },
    set_origin(Ctx, c),
    from_slot(thread, rdi, Ctx),
    [ins(lea, q, [rip(Org), reg(rsi)]), ins(call, none, [G]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    set_p(D, Ctx).
inst(ins(t(D), p, copy, [V]), _, _, Ctx) --> !,
    flight(V, Ctx), set_p(D, Ctx).
inst(ins(t(D), p, Op, [P, X]), _, _, Ctx) --> { memberchk(Op, [add, sub]) }, !,
    { f4(Ctx, F4) },
    flight(P, Ctx), load(X, l, d, F4),
    [ins(Op, q, [reg(rdx), reg(rax)])],
    set_p(D, Ctx).
inst(ins(t(D), l, ptoi, [P]), _, _, Ctx) --> !,
    { f4(Ctx, F4) }, load(P, l, a, F4), to_slot(rax, t(D), Ctx).
inst(ins(t(D), p, itop, [X]), _, _, Ctx) --> !,
    { f4(Ctx, F4) }, load(X, l, a, F4),
    [ins(xor, l, [reg(ecx), reg(ecx)])],
    set_p(D, Ctx).
inst(ins(t(D), p, alloc(Align), [N]), _, _, Ctx) --> !,
    { f4(Ctx, F4) },
    load(N, l, si, F4),
    from_slot(thread, rdi, Ctx),
    (   { Align == 16 }
    ->  [ins(mov, l, [imm(16), reg(edx)]),
         ins(call, none, [plt(filc_allocate_with_alignment)])]
    ;   [ins(call, none, [plt(filc_allocate)])]
    ),
    [ins(lea, q, [mem(16, rax), reg(rax)]), ins(mov, q, [reg(rax), reg(rcx)])],
    set_p(D, Ctx).
inst(ins(t(D), p, load(p), [A]), N, B, Ctx) --> !,
    { local(Ctx, B, N, nolower, NoLower), local(Ctx, B, N, have, Have) },
    flight(A, Ctx),
    check(k(8, 0, 8), Ctx),
    aux_of_lower,
    [ins(jz, none, [sym(NoLower)]),
     ins(mov, q, [reg(rax), reg(rsi)]), ins(sub, q, [reg(rcx), reg(rsi)]),
     ins(mov, q, [mem(0, rdx, rsi), reg(rsi)]),
     ins(test, b, [imm(1), reg(sil)]),
     ins(jz, none, [sym(Have)]),
     ins(and, q, [imm(-2), reg(rsi)]), ins(mov, q, [mem(8, rsi), reg(rsi)]),
     ins(jmp, none, [sym(Have)]),
     label(NoLower),
     ins(xor, l, [reg(esi), reg(esi)]),
     label(Have),
     ins(mov, q, [mem(0, rax), reg(rax)]), ins(mov, q, [reg(rsi), reg(rcx)])],
    set_p(D, Ctx).
inst(ins(t(D), K, load(T), [A]), _, _, Ctx) --> !,
    { width_of_load(T, S), load_insn(T, K, I) },
    flight(A, Ctx),
    check(k(S, 0, 1), Ctx),
    [I],
    to_slot(rax, t(D), Ctx).
inst(ins(t(D), K, Op, Args), _, _, Ctx) -->
    { f4(Ctx, F4) },
    op(Op, K, Args, F4),
    to_slot(rax, t(D), Ctx).
inst(store(p, V, A), N, B, Ctx) --> !,
    { f4(Ctx, F4), local(Ctx, B, N, haveaux, HaveAux), local(Ctx, B, N, nobarrier, NoBarrier) },
    flight(A, Ctx),
    check(k(8, 1, 8), Ctx),
    aux_of_lower,
    [ins(jnz, none, [sym(HaveAux)])],
    from_slot(thread, rdi, Ctx),
    [ins(lea, q, [mem(-16, rcx), reg(rsi)]),
     ins(call, none, [plt(filc_object_ensure_aux_ptr_outline)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     label(HaveAux)],
    to_slot(rdx, aux, Ctx),
    lower_of(V, rsi, Ctx),
    [ins(test, q, [reg(rsi), reg(rsi)]),
     ins(jz, none, [sym(NoBarrier)]),
     ins(mov, q, [gotpcrel(filc_current_marking_state), reg(rax)]),
     ins(cmp, l, [imm(0), mem(0, rax)]),
     ins(je, none, [sym(NoBarrier)])],
    from_slot(thread, rdi, Ctx),
    [ins(call, none, [plt(filc_store_barrier_for_lower_slow)]),
     label(NoBarrier)],
    flight(A, Ctx),
    from_slot(aux, rdx, Ctx),
    [ins(mov, q, [reg(rax), reg(r8)]), ins(sub, q, [reg(rcx), reg(r8)])],
    lower_of(V, rsi, Ctx),
    load(V, l, r9, F4),
    [ins(mov, q, [reg(rsi), mem(0, rdx, r8)]), ins(mov, q, [reg(r9), mem(0, rax)])].
inst(store(W, V, A), _, _, Ctx) -->
    { f4(Ctx, F4), width_bytes(W, S), ( W == l -> VK = l ; VK = w ), store_insn(W, d, I) },
    flight(A, Ctx),
    check(k(S, 1, 1), Ctx),
    load(V, VK, d, F4),
    [I].
inst(call(Res, glo(F), Args), _, _, Ctx) -->
    { call_target(Ctx, F, Res, Args, Target),
      res_tos(Res, Tos), findall(K, member(to(_, K), Tos), RKs), ret_form(RKs, Form) },
    set_origin(Ctx, c),
    reserve(Form),
    fast_call(Form, Args, direct(Target), Ctx),
    fast_result(Form, Res, Ctx),
    release(Form).

/* A call through a p value. The callee must be a function object: lower
   not 0, ptr equal to the object's aux pointer, and special type
   function. Then the fast entry if the signature matches the call site's,
   else the generic entry with every argument as an 8-byte word at
   thread+128+8i and its lower at thread+384+8i (docs/abi-findings.md). */
inst(call(Res, t(C), Args), N, B, Ctx) -->
    { f4(Ctx, F4),
      call_sig(Res, Args, _, _, Sig),
      res_tos(Res, Tos), findall(K, member(to(_, K), Tos), RKs), ret_form(RKs, Form),
      special(Ctx, notfn, NotFn),
      length(Args, NA), Size is 8 * NA,
      local(Ctx, B, N, generic, Generic), local(Ctx, B, N, done, Done),
      local(Ctx, B, N, retok, RetOk) },
    set_origin(Ctx, c),
    reserve(Form),
    flight(t(C), Ctx),
    function_check(NotFn),
    to_slot(rcx, aux, Ctx),
    [ins(movabs, q, [imm(Sig), reg(rsi)]), ins(cmp, q, [reg(rsi), mem(16, rcx)]),
     ins(jne, none, [sym(Generic)])],
    fast_call(Form, Args, indirect, Ctx),
    fast_result(Form, Res, Ctx),
    [ins(jmp, none, [sym(Done)]), label(Generic)],
    generic_args(Args, 0, F4, Ctx),
    from_slot(thread, rdi, Ctx),
    from_slot(aux, rsi, Ctx),
    { special(Ctx, exc, Exc) },
    [ins(mov, l, [imm(Size), reg(edx)]), ins(call, q, [ind(mem(8, rsi))]),
     ins(test, b, [imm(1), reg(al)]), ins(jnz, none, [sym(Exc)])],
    (   { Tos == [] } -> []
    ;   { length(Tos, NW), Need is 8 * NW, generic_words(RKs, GWs) },
        from_slot(thread, rsi, Ctx),
        rets_check(Need, RetOk),
        generic_into_slots(GWs, Tos, Ctx)
    ),
    [label(Done)],
    release(Form).

% Arguments, the entry registers and the call itself, for the fast
% convention in form Form; Callee is direct(Symbol) or indirect (through
% the aux slot).
fast_call(Form, Args, Callee, Ctx) -->
    { f4(Ctx, F4),
      foldl(arg_words, Args, Words, []),
      ( Form == reg -> Ls = [d, c, r8, r9] ; Ls = [c, r8, r9] ),
      length(Ls, NR), length(Words, NW),
      (   NW > NR -> length(RegWs, NR), append(RegWs, StackWs, Words)
      ;   RegWs = Words, StackWs = []
      ),
      length(StackWs, NS), Pad is NS mod 2, Pop is 8 * (NS + Pad),
      reverse(StackWs, RevStack) },
    (   { Pad =:= 1 } -> [ins(sub, q, [imm(8), reg(rsp)])] ; [] ),
    push_words(RevStack, F4, Ctx),
    reg_words(RegWs, Ls, F4, Ctx),
    entry_call(Form, Callee, Pop, Ctx),
    (   { Pop > 0 } -> [ins(add, q, [imm(Pop), reg(rsp)])] ; [] ).

entry_call(reg, direct(T), _, Ctx) -->
    from_slot(thread, rdi, Ctx), [ins(xor, l, [reg(esi), reg(esi)]), ins(call, none, [T])].
entry_call(reg, indirect, _, Ctx) -->
    from_slot(thread, rdi, Ctx), from_slot(aux, rsi, Ctx), [ins(call, q, [ind(mem(0, rsi))])].
entry_call(mem(_), direct(T), Pop, Ctx) -->
    from_slot(thread, rsi, Ctx),
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]), ins(xor, l, [reg(edx), reg(edx)]), ins(call, none, [T])].
entry_call(mem(_), indirect, Pop, Ctx) -->
    from_slot(thread, rsi, Ctx), from_slot(aux, rdx, Ctx),
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]), ins(call, q, [ind(mem(0, rdx))])].

% has_exception, then the result slots from %rdx:%rcx or the buffer.
fast_result(reg, Res, Ctx) -->
    { special(Ctx, exc, Exc), res_dests(Res, Ds) },
    [ins(test, b, [imm(1), reg(al)]), ins(jnz, none, [sym(Exc)])],
    regs_into_slots(Ds, [rdx, rcx], Ctx).
fast_result(mem(_), Res, Ctx) -->
    { special(Ctx, exc, Exc), res_dests(Res, Ds) },
    [ins(cmp, b, [imm(0), mem(0, rsp)]), ins(jne, none, [sym(Exc)])],
    buffer_into_slots(Ds, 8, Ctx).

regs_into_slots([], _, _) --> [].
regs_into_slots([D|Ds], [R|Rs], Ctx) --> to_slot(R, D, Ctx), regs_into_slots(Ds, Rs, Ctx).

buffer_into_slots([], _, _) --> [].
buffer_into_slots([D|Ds], Off, Ctx) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)])], to_slot(rax, D, Ctx),
    { Off1 is Off + 8 }, buffer_into_slots(Ds, Off1, Ctx).

% A generic return's words, from the thread at %rsi, into the slots.
generic_into_slots([], [], _) --> [].
generic_into_slots([gw(K, D, _)|GWs], [to(T, _)|Tos], Ctx) -->
    [ins(mov, q, [mem(D, rsi), reg(rax)])], to_slot(rax, T, Ctx),
    (   { K == p } -> { X is D + 256 }, [ins(mov, q, [mem(X, rsi), reg(rax)])], to_slot(rax, lower(T), Ctx)
    ;   []
    ),
    generic_into_slots(GWs, Tos, Ctx).

% Fail unless the generic return size in %rdx is at least Need.
rets_check(Need, RetOk) -->
    [ins(cmp, q, [imm(Need), reg(rdx)]), ins(jae, none, [sym(RetOk)]),
     ins(mov, q, [reg(rdx), reg(rdi)]), ins(mov, l, [imm(Need), reg(esi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [plt(filc_cc_rets_check_failure)]), ins(ud2, none, []),
     label(RetOk)].

generic_args([], _, _, _) --> [].
generic_args([arg(K, V)|As], I, F4, Ctx) -->
    { D is 128 + 8 * I, X is 384 + 8 * I },
    (   { K == p }
    ->  load(V, l, a, F4), lower_of(V, rcx, Ctx)
    ;   load(V, K, a, F4), [ins(xor, l, [reg(ecx), reg(ecx)])]
    ),
    from_slot(thread, rdx, Ctx),
    [ins(mov, q, [reg(rax), mem(D, rdx)]), ins(mov, q, [reg(rcx), mem(X, rdx)])],
    { I1 is I + 1 },
    generic_args(As, I1, F4, Ctx).

% With a flight pointer in %rax:%rcx, jump to Fail unless it points at a
% function object. Clobbers %rdx and %rsi.
function_check(Fail) -->
    [ins(test, q, [reg(rcx), reg(rcx)]), ins(jz, none, [sym(Fail)]),
     ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(540431955284459520), reg(rsi)]),
     ins(and, q, [reg(rdx), reg(rsi)]),
     ins(movabs, q, [imm(36028797018963968), reg(rdi)]),
     ins(cmp, q, [reg(rdi), reg(rsi)]), ins(jne, none, [sym(Fail)]),
     ins(movabs, q, [imm(281474976710655), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]), ins(jne, none, [sym(Fail)])].

% The getter for symbol S: local if the module defines S.
getter(module(Items), S, G) :-
    format(atom(N), 'pizlonated_~w', [S]),
    (   ( memberchk(func(S, _, _, _, _), Items) ; memberchk(data(S, _, _, _), Items) )
    ->  G = sym(N)
    ;   G = plt(N)
    ).

% The aux pointer of the object at lower %rcx into %rdx, setting ZF if
% it has none.
aux_of_lower -->
    [ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(281474976710655), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)])].

set_p(D, Ctx) --> to_slot(rax, t(D), Ctx), to_slot(rcx, lower(t(D)), Ctx).

width_of_load(T, S) :- memberchk(T-S, [l-8, sw-4, uw-4, sh-2, uh-2, sb-1, ub-1]).

% Functions in the module are called at their implementation; others at
% their pizlonatedFI symbol: a weak thunk this module emits (thunk//1),
% overridden by a clang definition with the same signature if one is
% linked in.
call_target(Ctx, F, Res, Args, sym(Target)) :-
    Ctx = c(_, _, _, _, x(M, _, _)),
    (   func_named(M, F, Fn)
    ->  fn_sig(Fn, Sig), impl_symbol(F, Sig, Target)
    ;   call_sig(Res, Args, _, _, Sig),
        format(atom(Target), 'pizlonatedFI~w_~w', [Sig, F])
    ).

call_sig(Res, Args, RK, Ks, Sig) :-
    res_ret(Res, RK),
    findall(K, member(arg(K, _), Args), Ks),
    signature(RK, Ks, Sig).

arg_words(arg(p, V), [addr(V), lower(V)|Ws], Ws) :- !.
arg_words(arg(K, V), [val(K, V)|Ws], Ws).

word_into(addr(V), R, F4, _) --> load(V, l, R, F4).
word_into(val(K, V), R, F4, _) --> load(V, K, R, F4).
word_into(lower(V), R, _, Ctx) --> { reg(R, l, RN) }, lower_of(V, RN, Ctx).

push_words([], _, _) --> [].
push_words([W|Ws], F4, Ctx) -->
    word_into(W, a, F4, Ctx), [ins(push, q, [reg(rax)])], push_words(Ws, F4, Ctx).

reg_words([], _, _, _) --> [].
reg_words([W|Ws], [R|Rs], F4, Ctx) -->
    word_into(W, R, F4, Ctx),
    reg_words(Ws, Rs, F4, Ctx).

%% Checks: k(Size, Write, Align), with the pointer in %rax and its lower
%% in %rcx, which the failure block passes on.

check(k(S, W, A), Ctx) -->
    { fail_label(Ctx, k(S, W, A), FL) },
    [ins(test, q, [reg(rcx), reg(rcx)]), ins(jz, none, [sym(FL)]),
     ins(cmp, q, [reg(rcx), reg(rax)]), ins(jb, none, [sym(FL)]),
     ins(mov, q, [mem(-16, rcx), reg(rdx)]), ins(sub, q, [imm(S), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]), ins(ja, none, [sym(FL)])],
    (   { W =:= 1 }
    ->  [ins(test, b, [imm(6), mem(-2, rcx)]), ins(jnz, none, [sym(FL)])]
    ;   []
    ),
    (   { A =:= 8 }
    ->  [ins(test, b, [imm(7), reg(al)]), ins(jnz, none, [sym(FL)])]
    ;   []
    ).

fail_label(c(Name, _, _, _, _), k(S, W, A), L) :-
    format(atom(L), '.L~w..fail.~w.~w.~w', [Name, S, W, A]).

check_origin(Name, k(S, W, A), L) :-
    format(atom(L), '.L~w..chk.~w.~w.~w', [Name, S, W, A]).

check_kinds(Blocks, Kinds) :-
    findall(K, ( member(blk(_, _, Is, _), Blocks), member(I, Is), inst_check(I, K) ), K0),
    sort(K0, Kinds).

inst_check(ins(_, _, load(p), _), k(8, 0, 8)) :- !.
inst_check(ins(_, _, load(T), _), k(S, 0, 1)) :- width_of_load(T, S).
inst_check(store(p, _, _), k(8, 1, 8)) :- !.
inst_check(store(W, _, _), k(S, 1, 1)) :- width_bytes(W, S).

fail_blocks([], _) --> [].
fail_blocks([K|Ks], Ctx) -->
    { fail_label(Ctx, K, L), Ctx = c(Name, _, _, _, _), check_origin(Name, K, O) },
    [label(L),
     ins(mov, q, [reg(rax), reg(rdi)]), ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(lea, q, [rip(O), reg(rdx)]),
     ins(call, none, [plt(filc_optimized_access_check_fail)]),
     ins(ud2, none, [])],
    fail_blocks(Ks, Ctx).

%% Function objects: every function gets a getter, a generic entry and a
%% function object, so its address can be taken; exported ones also get
%% the FI alias and a global getter.

function_object(Name, Lk, Ret, Params, Sig, Impl) -->
    { format(atom(FI), 'pizlonatedFI~w_~w', [Sig, Name]),
      format(atom(FO), 'pizlonatedFO_~w', [Name]),
      format(atom(G), 'pizlonated_~w', [Name]),
      format(atom(Gen), '.L~w..generic', [Name]) },
    (   { Lk == export } -> [globl(FI), type(FI, function), set(FI, Impl), globl(G)] ; [] ),
    [type(G, function), label(G),
     ins(lea, q, [rip(FO+16), reg(rax)]), ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])],
    generic(Gen, Ret, Params),
    [section(data_rel_ro), p2align(4), type(FO, object), label(FO),
     quad(FO+16),
     quad(FO+16+36873221949095936),
     quad(Impl),
     quad(Gen),
     quad(Sig),
     size(FO, 40)].

%% Data objects, as clang lays out globals (docs/abi-findings.md):
%% DO_d = {upper, aux} then the payload rounded up to 8 bytes, a 16-byte
%% cache GP_d, an aux array DA_d if the payload holds pointers, and a
%% getter whose slow path registers the object and runs the relocations
%% that fill in its pointers.

data_object(Name, Lk0, Items) -->
    { ( Lk0 = ro(Lk) -> RO = 2 ; Lk = Lk0, RO = 0 ),
      format(atom(DO), 'pizlonatedDO_~w', [Name]),
      format(atom(DA), 'pizlonatedDA_~w', [Name]),
      format(atom(GP), '.LpizlonatedGP_~w', [Name]),
      format(atom(G), 'pizlonated_~w', [Name]),
      format(atom(RT), '.Lpizlonated_~w..relocs', [Name]),
      format(atom(Slow), '.Lpizlonated_~w..slow', [Name]),
      format(atom(Init), '.Lpizlonated_~w..inited', [Name]),
      foldl(payload_item, Items, Ps, 0-[], Size0-Rs0),
      reverse(Rs0, Rs), length(Rs, NR),
      Size is (Size0 + 7) // 8 * 8, Pad is Size - Size0,
      (   Rs == [] -> Aux = 0, Flags is 1 + RO
      ;   Aux = DA, Flags is 17 + RO
      ),
      FlagBits is Flags << 48,
      ( Aux == 0 -> AuxE = FlagBits ; AuxE = DA+FlagBits ) },
    [section(data), p2align(4), type(DO, object), label(DO),
     quad(DO+16+Size), quad(AuxE)],
    seq(Ps),
    (   { Pad > 0 } -> [zero(Pad)] ; [] ),
    { Total is 16 + Size },
    [size(DO, Total)],
    [section(bss), p2align(4), label(GP), zero(16)],
    (   { Rs == [] } -> [] ; [p2align(4), label(DA), zero(Size)] ),
    (   { Rs == [] } -> []
    ;   [section(data_rel_ro), p2align(4), label(RT)],
        relocations(Rs, Name)
    ),
    [section(text), p2align(4)],
    (   { Lk == export } -> [globl(G)] ; [] ),
    [type(G, function), label(G),
     ins(mov, q, [rip(GP), reg(rax)]), ins(mov, q, [rip(GP+8), reg(rdx)]),
     ins(test, q, [reg(rax), reg(rax)]), ins(jz, none, [sym(Slow)]),
     ins(test, q, [reg(rdx), reg(rdx)]), ins(jz, none, [sym(Slow)]),
     ins(ret, none, []),
     label(Slow),
     ins(push, q, [reg(rbx)]), ins(mov, q, [reg(rdi), reg(rbx)]),
     ins(lea, q, [rip(GP), reg(rdx)]), ins(lea, q, [rip(DO), reg(rcx)]),
     ins(call, none, [plt(filc_global_initialization_start)]),
     ins(test, b, [imm(1), reg(al)]), ins(jz, none, [sym(Init)])],
    (   { NR > 0 }
    ->  [ins(mov, q, [reg(rbx), reg(rdi)]), ins(lea, q, [rip(DO), reg(rsi)]),
         ins(lea, q, [rip(RT), reg(rdx)]), ins(mov, l, [imm(NR), reg(ecx)]),
         ins(call, none, [plt(filc_execute_constant_relocations)])]
    ;   []
    ),
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(call, none, [plt(filc_global_initialization_end)]),
     label(Init),
     ins(pop, q, [reg(rbx)]),
     ins(lea, q, [rip(DO+16), reg(rax)]), ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])].

% payload_item(Item, Lines, Off0-Rs0, Off-Rs): the payload directives, and
% a relocation r(Offset, Symbol, Addend) for each pointer, whose slot
% stays 0 until the relocation fills it in.
payload_item(zero(N), zero(N), O0-Rs, O-Rs) :- O is O0 + N.
payload_item(item(b, str(Cs)), ascii(Cs), O0-Rs, O-Rs) :- !,
    phrase(asm_string_length(N), Cs), O is O0 + N.
payload_item(item(p, sym(S, Off)), quad(0), O0-Rs, O-[r(O0, S, Off)|Rs]) :- !,
    (   O0 mod 8 =:= 0 -> true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    O is O0 + 8.
payload_item(item(W, c(N)), D, O0-Rs, O-Rs) :-
    width_bytes(W, B), Bits is 8 * B, U is N mod (1 << Bits),
    memberchk(B-D, [1-byte([U]), 2-short(U), 4-long(U), 8-quad(U)]),
    O is O0 + B.

% The byte length of an ascii string with GNU as escapes.
asm_string_length(0) --> [].
asm_string_length(N) --> ['\\'], !, escape_tail, asm_string_length(N0), { N is N0 + 1 }.
asm_string_length(N) --> [_], asm_string_length(N0), { N is N0 + 1 }.

escape_tail --> [D], { char_code(D, C), C >= 0'0, C =< 0'7 }, !, octal_upto(2).
escape_tail --> [_].
octal_upto(0) --> !.
octal_upto(K) --> [D], { char_code(D, C), C >= 0'0, C =< 0'7 }, !, { K1 is K - 1 }, octal_upto(K1).
octal_upto(_) --> [].

% Each relocation is {u64 offset, u32 kind, pad, target}: kind 0 calls a
% getter, kind 1 a constexpr node {u32 add-immediate = 0, u32 0, getter,
% u64 addend}.
relocations(Rs, Name) -->
    reloc_entries(Rs, 0, Name),
    reloc_nodes(Rs, 0, Name).

reloc_entries([], _, _) --> [].
reloc_entries([r(O, S, A)|Rs], I, Name) -->
    { reloc_getter(S, G) },
    (   { A =:= 0 } -> [quad(O), long(0), zero(4), quad(G)]
    ;   { format(atom(Nd), '.Lpizlonated_~w..node~w', [Name, I]) },
        [quad(O), long(1), zero(4), quad(Nd)]
    ),
    { I1 is I + 1 },
    reloc_entries(Rs, I1, Name).

reloc_nodes([], _, _) --> [].
reloc_nodes([r(_, S, A)|Rs], I, Name) -->
    (   { A =:= 0 } -> []
    ;   { reloc_getter(S, G), format(atom(Nd), '.Lpizlonated_~w..node~w', [Name, I]),
          U is A mod 18446744073709551616 },
        [label(Nd), long(0), long(0), quad(G), quad(U)]
    ),
    { I1 is I + 1 },
    reloc_nodes(Rs, I1, Name).

reloc_getter(S, G) :- format(atom(G), 'pizlonated_~w', [S]).

%% Thunks for functions outside the module, as clang emits them: a hidden
%% weak pizlonatedFI<sig>_f that gets f's function object from its getter,
%% checks it, and calls the fast entry if the signature matches or the
%% generic entry otherwise. A clang definition of the same symbol wins.

external_callees(M, Ts) :-
    M = module(Items),
    findall(t(F, Sig, RK, Ks),
            ( member(func(_, _, _, _, Bs), Items), member(blk(_, _, Is, _), Bs),
              member(call(Res, glo(F), Args), Is), \+ func_named(M, F, _),
              call_sig(Res, Args, RK, Ks, Sig) ),
            Ts0),
    sort(Ts0, Ts1),
    one_per_symbol(Ts1, Ts).

% w and l are the same word, so call sites that differ only there share a
% thunk.
one_per_symbol([], []).
one_per_symbol([T|Ts0], [T|Ts]) :-
    T = t(F, Sig, _, _),
    exclude(same_symbol(F, Sig), Ts0, Ts1),
    one_per_symbol(Ts1, Ts).

same_symbol(F, Sig, t(F, Sig, _, _)).

/* Frame: rbp, then rbx = thread and r12..r15 = the register words, one
   slot at -48(%rbp) for the callee's lower. Stack words are at
   16(%rbp) and up. With a buffered return r12 holds the buffer and
   r13..r15 the three register words. */
thunk(t(F, Sig, RK, Ks)) -->
    { format(atom(FI), 'pizlonatedFI~w_~w', [Sig, F]),
      format(atom(G), 'pizlonated_~w', [F]),
      atom_concat('.L', FI, L0),
      atom_concat(L0, '..fail', Fail), atom_concat(L0, '..generic', Gen),
      atom_concat(L0, '..out', Out), atom_concat(L0, '..retok', RetOk),
      atom_concat(L0, '..exc', GenExc),
      ret_kinds(RK, RKs), ret_form(RKs, Form), form_regs(Form, Regs), length(Regs, NR),
      foldl(class_words, Ks, Words, 0, NW),
      NS is max(0, NW - NR), Pad is NS mod 2,
      length(Ks, NA), Size is 8 * NA,
      ( NS > 0 -> NS1 is NS - 1, numlist(0, NS1, SIs0), reverse(SIs0, SIs) ; SIs = [] ) },
    [section(text), p2align(4), hidden(FI), weak(FI), type(FI, function), label(FI),
     ins(push, q, [reg(rbp)]), ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(push, q, [reg(rbx)]), ins(push, q, [reg(r12)]), ins(push, q, [reg(r13)]),
     ins(push, q, [reg(r14)]), ins(push, q, [reg(r15)]), ins(sub, q, [imm(8), reg(rsp)])],
    (   { Form == reg }
    ->  [ins(mov, q, [reg(rdi), reg(rbx)]),
         ins(mov, q, [reg(rdx), reg(r12)]), ins(mov, q, [reg(rcx), reg(r13)]),
         ins(mov, q, [reg(r8), reg(r14)]), ins(mov, q, [reg(r9), reg(r15)])]
    ;   [ins(mov, q, [reg(rsi), reg(rbx)]), ins(mov, q, [reg(rdi), reg(r12)]),
         ins(mov, q, [reg(rcx), reg(r13)]), ins(mov, q, [reg(r8), reg(r14)]),
         ins(mov, q, [reg(r9), reg(r15)]), ins(mov, q, [reg(rsi), reg(rdi)])]
    ),
    [ins(xor, l, [reg(esi), reg(esi)]),
     ins(call, none, [plt(G)]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    function_check(Fail),
    [ins(mov, q, [reg(rcx), mem(-48, rbp)]),
     ins(movabs, q, [imm(Sig), reg(rsi)]), ins(cmp, q, [reg(rsi), mem(16, rcx)]),
     ins(jne, none, [sym(Gen)])],
    (   { Pad =:= 1 } -> [ins(sub, q, [imm(8), reg(rsp)])] ; [] ),
    thunk_push(SIs, Form),
    (   { Form == reg }
    ->  [ins(mov, q, [reg(rbx), reg(rdi)]), ins(mov, q, [mem(-48, rbp), reg(rsi)]),
         ins(mov, q, [reg(r12), reg(rdx)]), ins(mov, q, [reg(r13), reg(rcx)]),
         ins(mov, q, [reg(r14), reg(r8)]), ins(mov, q, [reg(r15), reg(r9)]),
         ins(call, q, [ind(mem(0, rsi))])]
    ;   [ins(mov, q, [reg(r12), reg(rdi)]), ins(mov, q, [reg(rbx), reg(rsi)]),
         ins(mov, q, [mem(-48, rbp), reg(rdx)]), ins(mov, q, [reg(r13), reg(rcx)]),
         ins(mov, q, [reg(r14), reg(r8)]), ins(mov, q, [reg(r15), reg(r9)]),
         ins(call, q, [ind(mem(0, rdx))])]
    ),
    [label(Out),
     ins(lea, q, [mem(-40, rbp), reg(rsp)]),
     ins(pop, q, [reg(r15)]), ins(pop, q, [reg(r14)]), ins(pop, q, [reg(r13)]),
     ins(pop, q, [reg(r12)]), ins(pop, q, [reg(rbx)]), ins(pop, q, [reg(rbp)]),
     ins(ret, none, []),
     label(Gen)],
    thunk_generic(Ks, Words, 0, Form),
    [ins(mov, q, [reg(rbx), reg(rdi)]), ins(mov, q, [mem(-48, rbp), reg(rsi)]),
     ins(mov, l, [imm(Size), reg(edx)]), ins(call, q, [ind(mem(8, rsi))]),
     ins(test, b, [imm(1), reg(al)])],
    { length(RKs, NRW), Need is 8 * NRW, generic_words(RKs, GWs) },
    (   { Form == reg }
    ->  [ins(jnz, none, [sym(Out)])],
        (   { RKs == [] } -> []
        ;   rets_check(Need, RetOk),
            { foldl(generic_srcs, GWs, Srcs, []) },
            thunk_regs(Srcs, [rdx, rcx])
        ),
        [ins(xor, l, [reg(eax), reg(eax)]), ins(jmp, none, [sym(Out)])]
    ;   [ins(jnz, none, [sym(GenExc)])],
        rets_check(Need, RetOk),
        { foldl(generic_srcs, GWs, Srcs, []) },
        thunk_buffer(Srcs, 8),
        [ins(mov, b, [imm(0), mem(0, r12)]), ins(mov, q, [reg(r12), reg(rax)]),
         ins(jmp, none, [sym(Out)]),
         label(GenExc),
         ins(mov, b, [imm(1), mem(0, r12)]), ins(mov, q, [reg(r12), reg(rax)]),
         ins(jmp, none, [sym(Out)])]
    ),
    [label(Fail),
     ins(mov, q, [reg(rax), reg(rdi)]), ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(call, none, [plt(filc_check_function_call_fail)]), ins(ud2, none, []),
     size(FI)].

% The thread offsets of a generic return's slots, in slot order.
generic_srcs(gw(p, D, _), [D, X|Ss], Ss) :- !, X is D + 256.
generic_srcs(gw(_, D, _), [D|Ss], Ss).

thunk_regs([], _) --> [].
thunk_regs([D|Ds], [R|Rs]) --> [ins(mov, q, [mem(D, rbx), reg(R)])], thunk_regs(Ds, Rs).

thunk_buffer([], _) --> [].
thunk_buffer([D|Ds], Off) -->
    [ins(mov, q, [mem(D, rbx), reg(rax)]), ins(mov, q, [reg(rax), mem(Off, r12)])],
    { Off1 is Off + 8 }, thunk_buffer(Ds, Off1).

% class_words(K, Ws, I0, I): the word positions of an argument of class K.
class_words(p, [I0, I1], I0, I) :- !, I1 is I0 + 1, I is I0 + 2.
class_words(_, [I0], I0, I) :- I is I0 + 1.

% Where incoming word J lives, as an operand.
thunk_word(Form, J, reg(R)) :- form_regs(Form, Regs), length(Regs, NR), J < NR, !,
    ( Form == reg -> nth0(J, [r12, r13, r14, r15], R) ; nth0(J, [r13, r14, r15], R) ).
thunk_word(Form, J, mem(D, rbp)) :- form_regs(Form, Regs), length(Regs, NR), D is 16 + 8 * (J - NR).

thunk_push([], _) --> [].
thunk_push([I|Is], Form) -->
    { form_regs(Form, Regs), length(Regs, NR), J is I + NR, thunk_word(Form, J, W) },
    [ins(push, q, [W])], thunk_push(Is, Form).

thunk_generic([], [], _, _) --> [].
thunk_generic([K|Ks], [Ws|Wss], I, Form) -->
    { D is 128 + 8 * I, X is 384 + 8 * I },
    (   { K == p, Ws = [A, L] }
    ->  thunk_store(A, D, Form), thunk_store(L, X, Form)
    ;   { Ws = [A] }, thunk_store(A, D, Form), [ins(mov, q, [imm(0), mem(X, rbx)])]
    ),
    { I1 is I + 1 },
    thunk_generic(Ks, Wss, I1, Form).

thunk_store(J, D, Form) -->
    { thunk_word(Form, J, W) },
    (   { W = reg(_) } -> [ins(mov, q, [W, mem(D, rbx)])]
    ;   [ins(mov, q, [W, reg(rax)]), ins(mov, q, [reg(rax), mem(D, rbx)])]
    ).

/* The generic entry: {i1, i64 ret_size} (thread, callee_lower, args_size).
   Argument i is 8 bytes at thread+128+8i, with its lower (for p) at
   thread+384+8i, and so is result word i. It calls the fast entry
   through callee_lower, with a buffer on the stack for a buffered
   return. */
generic(Gen, Ret, Params) -->
    { length(Params, NA), Need is 8 * NA,
      findall(W, ( nth0(I, Params, par(K, _)), generic_word(K, I, W) ), Ws0),
      append(Ws0, Words),
      ret_kinds(Ret, RKs), ret_form(RKs, Form), form_regs(Form, Regs), length(Regs, NR),
      length(Words, NW),
      (   NW > NR -> length(RegWs, NR), append(RegWs, StackWs, Words)
      ;   RegWs = Words, StackWs = []
      ),
      length(StackWs, NS), Pad is NS mod 2, Pop is 8 * (NS + Pad),
      reverse(StackWs, Rev),
      length(RKs, NRW), RetSize is 8 * max(1, NRW),
      generic_words(RKs, GWs),
      atom_concat(Gen, '.short', Short),
      atom_concat(Gen, '.done', Done) },
    [section(text), label(Gen), ins(push, q, [reg(rbx)])],
    (   { NA > 0 }
    ->  [ins(cmp, q, [imm(Need), reg(rdx)]), ins(jb, none, [sym(Short)])]
    ;   []
    ),
    [ins(mov, q, [reg(rdi), reg(rbx)])],
    reserve(Form),
    (   { Pad =:= 1 } -> [ins(sub, q, [imm(8), reg(rsp)])] ; [] ),
    gen_push(Rev),
    gen_regs(RegWs, Regs),
    (   { Form == reg }
    ->  [ins(call, q, [ind(mem(0, rsi))])],
        (   { Pop > 0 } -> [ins(add, q, [imm(Pop), reg(rsp)])] ; [] ),
        [ins(test, b, [imm(1), reg(al)]), ins(jnz, none, [sym(Done)])],
        (   { RKs == [] } -> [ins(mov, q, [imm(0), mem(128, rbx)]), ins(mov, q, [imm(0), mem(384, rbx)])]
        ;   { foldl(generic_srcs, GWs, Ds, []) }, gen_from_regs(Ds, [rdx, rcx]), gen_zero_lowers(GWs)
        ),
        [ins(mov, l, [imm(RetSize), reg(edx)]),
         label(Done)]
    ;   [ins(mov, q, [reg(rsi), reg(rdx)]), ins(mov, q, [reg(rbx), reg(rsi)]),
         ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
         ins(call, q, [ind(mem(0, rdx))])],
        (   { Pop > 0 } -> [ins(add, q, [imm(Pop), reg(rsp)])] ; [] ),
        [ins(mov, b, [mem(0, rsp), reg(al)]), ins(test, b, [reg(al), reg(al)]),
         ins(jnz, none, [sym(Done)])],
        { foldl(generic_srcs, GWs, Ds, []) },
        gen_from_buffer(Ds, 8),
        gen_zero_lowers(GWs),
        [ins(mov, l, [imm(RetSize), reg(edx)]), ins(xor, l, [reg(eax), reg(eax)]),
         label(Done)],
        release(Form)
    ),
    [ins(pop, q, [reg(rbx)]), ins(ret, none, [])],
    (   { NA > 0 }
    ->  [label(Short),
         ins(mov, q, [reg(rdx), reg(rdi)]), ins(mov, l, [imm(Need), reg(esi)]),
         ins(xor, l, [reg(edx), reg(edx)]),
         ins(call, none, [plt(filc_cc_args_check_failure)]), ins(ud2, none, [])]
    ;   []
    ).

gen_from_regs([], _) --> [].
gen_from_regs([D|Ds], [R|Rs]) --> [ins(mov, q, [reg(R), mem(D, rbx)])], gen_from_regs(Ds, Rs).

gen_from_buffer([], _) --> [].
gen_from_buffer([D|Ds], Off) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)]), ins(mov, q, [reg(rax), mem(D, rbx)])],
    { Off1 is Off + 8 }, gen_from_buffer(Ds, Off1).

% An integer result word has no lower.
gen_zero_lowers([]) --> [].
gen_zero_lowers([gw(K, D, _)|GWs]) -->
    (   { K == p } -> [] ; { X is D + 256 }, [ins(mov, q, [imm(0), mem(X, rbx)])] ),
    gen_zero_lowers(GWs).

generic_word(p, I, [D, A]) :- !, D is 128 + 8 * I, A is 384 + 8 * I.
generic_word(_, I, [D]) :- D is 128 + 8 * I.

gen_push([]) --> [].
gen_push([Off|Os]) --> [ins(push, q, [mem(Off, rbx)])], gen_push(Os).

gen_regs([], _) --> [].
gen_regs([Off|Os], [R|Rs]) --> [ins(mov, q, [mem(Off, rbx), reg(R)])], gen_regs(Os, Rs).

%% Static data: function origins (the pin's 40-byte layout), origins,
%% and one access-check origin per check kind.

origins(Name, NL, Kinds) -->
    { format(atom(N), '.L~w..name', [Name]) },
    [section(rodata), label(N), asciz(Name),
     section(data_rel_ro), p2align(4)],
    function_origin(Name, N, NL, c, 1),
    function_origin(Name, N, NL, n, 0),
    check_origins(Kinds, Name).

function_origin(Name, N, NL, Which, CanCatch) -->
    { format(atom(FO), '.L~w..forigin_~w', [Name, Which]), origin(Name, Which, O) },
    [label(FO),
     quad(N), quad(0),
     long(NL), zero(4),
     quad(0),
     byte([0, CanCatch, 0]), zero(1),
     long(0),
     label(O),
     quad(FO), long(0), long(0)].

check_origins([], _) --> [].
check_origins([K|Ks], Name) -->
    { K = k(S, W, A), check_origin(Name, K, L), origin(Name, n, O) },
    [p2align(4), label(L),
     long(S), byte([A, 0, W]), zero(1),
     quad(O), quad(O), quad(0)],
    check_origins(Ks, Name).
