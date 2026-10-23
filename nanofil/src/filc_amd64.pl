/*  Naive Fil-C lowering for x86-64 (milestone 3).

    Emits asm.pl lines whose GNU as text links with clang-built Fil-C
    code at the filnix pin (Fil-C 0.686). The rules are in docs/m3.md;
    in short:

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
    Module = module(Items),
    maplist(item_lines(Module), Items, ItemLines),
    append(ItemLines, Lines0),
    external_callees(Module, Callees),
    maplist(thunk_lines, Callees, ThunkLines),
    append(ThunkLines, Lines1),
    append([Lines0, Lines1, [section(note_gnu_stack)]], Lines).

thunk_lines(Callee, Lines) :-
    phrase(thunk(Callee), Lines).

item_lines(Module, Item, Lines) :-
    (   phrase(item(Module, Item), Lines) -> true
    ;   arg(1, Item, Name),
        format(atom(Msg), 'Fil-C backend cannot emit $~w', [Name]),
        throw(nanofil_error(Msg))
    ).

%% Signatures (docs/abi-findings.md): each word class is a bijective
%% base-11 digit, i64 = 0 and ptr = 7, and sig = 1 + ret + 133 * args.

signature(Ret, ParamKs, Sig) :-
    ret_digits(Ret, RetDigits),
    maplist(class_digit, ParamKs, ArgDigits),
    length(ArgDigits, NArgs),
    (   NArgs =< 16 -> true
    ;   throw(nanofil_error('more than 16 arguments'))
    ),
    bijective(RetDigits, R),
    bijective(ArgDigits, A),
    Sig is 1 + R + 133 * A.

ret_digits(void, []).
ret_digits(tuple(Ks), Ds) :- !, maplist(class_digit, Ks, Ds).
ret_digits(K, [D]) :- class_digit(K, D).

class_digit(w, 0).
class_digit(l, 0).
class_digit(p, 7).

% bijective(Digits, Value): Digits, least significant first, in
% bijective base 11.
bijective([], 0).
bijective([D|Ds], V) :- bijective(Ds, V1), V is D + 1 + 11 * V1.

fn_sig(func(_, _, Ret, Params, _), Sig) :-
    findall(K, member(par(K, _), Params), Ks),
    signature(Ret, Ks, Sig).

impl_symbol(Name, Sig, Impl) :-
    format(atom(Impl), 'pizlonatedFIP~w_~w', [Sig, Name]).

%% Frame layout

/* Slots maps t(N), shadow(N) to address slots and lower(Key) to lowers[]
   entries, all as offsets below %rbp; thread and aux are scratch slots,
   and retbuf holds the return buffer of a buffered return. The
   filc_frame {parent, origin, lowers[NLowers]} sits at -FrameBase(%rbp). */
layout(Form, Params, Blocks, Slots, FrameBase, NLowers, Size) :-
    findall(N-K,
            (   member(par(K, t(N)), Params)
            ;   member(blk(_, Phis, Insts, _), Blocks),
                (   member(phi(t(N), K, _), Phis)
                ;   member(I, Insts),
                    defines(I, N, K)
                )
            ),
            Temps0),
    sort(Temps0, Temps),
    findall(N-K,
            (   member(blk(_, Phis, _, _), Blocks),
                member(phi(t(N), K, _), Phis)
            ),
            Shadows0),
    sort(Shadows0, Shadows),
    findall(t(N), member(N-_, Temps), TempKeys),
    findall(shadow(N), member(N-_, Shadows), ShadowKeys),
    (   Form = mem(_) -> Extra = [retbuf] ; Extra = [] ),
    append([TempKeys, ShadowKeys, [thread, aux], Extra], Plain),
    findall(lower(t(N)), member(N-p, Temps), TempLowers),
    findall(lower(shadow(N)), member(N-p, Shadows), ShadowLowers),
    append(TempLowers, ShadowLowers, Lowers),
    length(Plain, NPlain),
    length(Lowers, NLowers),
    FrameBase is 8 * NPlain + 16 + 8 * NLowers,
    empty_assoc(Slots0),
    foldl(plain_slot, Plain, Slots0-0, Slots1-_),
    foldl(lower_slot(FrameBase), Lowers, Slots1-0, Slots-_),
    Size is (FrameBase + 15) // 16 * 16.

defines(ins(t(N), K, _, _), N, K).
defines(call(to(t(N), K), _, _), N, K).
defines(call(tuple(Tos), _, _), N, K) :- member(to(t(N), K), Tos).

plain_slot(Key, Slots0-I0, Slots-I) :-
    I is I0 + 1,
    Off is 8 * I,
    put_assoc(Key, Slots0, Off, Slots).

lower_slot(FrameBase, Key, Slots0-I0, Slots-I) :-
    Off is FrameBase - 16 - 8 * I0,
    I is I0 + 1,
    put_assoc(Key, Slots0, Off, Slots).

%% The function context

/* Ctx = ctx(Fn, Module, FrameBase, Labels), where Fn = f(Name, Ret,
   Slots, Blocks) is the context amd64's load//4 and op//4 take. Labels
   maps each block label to block(Index, Phis), so an edge finds its
   target's position and phis without searching Blocks. */
function_ctx(Name, Ret, Slots, Blocks, Module, FrameBase, Ctx) :-
    findall(Label-block(Index, Phis),
            nth0(Index, Blocks, blk(Label, Phis, _, _)),
            LabelBlocks),
    list_to_assoc(LabelBlocks, Labels),
    Ctx = ctx(f(Name, Ret, Slots, Blocks), Module, FrameBase, Labels).

amd64_ctx(ctx(Fn, _, _, _), Fn).

ctx_name(ctx(f(Name, _, _, _), _, _, _), Name).

ctx_ret(ctx(f(_, Ret, _, _), _, _, _), Ret).

ctx_module(ctx(_, Module, _, _), Module).

ctx_frame_base(ctx(_, _, FrameBase, _), FrameBase).

ctx_labels(ctx(_, _, _, Labels), Labels).

slot(ctx(f(_, _, Slots, _), _, _, _), Key, Off) :-
    get_assoc(Key, Slots, Off).

to_slot(Reg, Key, Ctx) -->
    { slot(Ctx, Key, Off), D is -Off },
    [ins(mov, q, [reg(Reg), mem(D, rbp)])].

from_slot(Key, Reg, Ctx) -->
    { slot(Ctx, Key, Off), D is -Off },
    [ins(mov, q, [mem(D, rbp), reg(Reg)])].

%% Local labels

% A label shared by the whole function, e.g. exc for exception exits.
special_label(Ctx, Tag, A) :-
    ctx_name(Ctx, Name),
    format(atom(A), '.L~w..~w', [Name, Tag]).

block_label(Ctx, Label, A) :-
    ctx_name(Ctx, Name),
    format(atom(A), '.L~w.~w', [Name, Label]).

% A label inside the code of instruction Index (or a jump) in Block.
local_label(Ctx, Block, Index, Tag, A) :-
    ctx_name(Ctx, Name),
    format(atom(A), '.L~w.~w..~w.~w', [Name, Block, Index, Tag]).

% The frame's origin: c (calls, can_catch) or n (pollchecks and checks).
origin(Name, Which, A) :-
    format(atom(A), '.L~w..origin_~w', [Name, Which]).

%% Functions

item(Module, Func) -->
    { Func = func(_, _, _, _, _) },
    function(Module, Func).
item(_, data(Name, Linkage, _, Items)) -->
    data_object(Name, Linkage, Items).

function(Module, Func) -->
    { Func = func(Name, Linkage, Ret, Params, Blocks),
      fn_sig(Func, Sig),
      ret_kinds(Ret, RetKs),
      ret_form(RetKs, Form),
      layout(Form, Params, Blocks, Slots, FrameBase, NLowers, Size),
      function_ctx(Name, Ret, Slots, Blocks, Module, FrameBase, Ctx),
      impl_symbol(Name, Sig, Impl),
      access_check_kinds(Blocks, CheckKinds),
      special_label(Ctx, exc, Exc) },
    [section(text), p2align(4)],
    (   { Linkage == export } -> [globl(Impl)] ; [] ),
    [type(Impl, function), label(Impl)],
    prologue(Form, Size, NLowers, Ctx),
    { param_words(Params, Words),
      form_regs(Form, Regs) },
    receive_words(Words, Regs, 0, Ctx),
    blocks(Blocks, Ctx),
    [label(Exc)],
    exception_exit(Form, Ctx),
    check_fail_blocks(CheckKinds, Ctx),
    not_function_block(Blocks, Ctx),
    [size(Impl)],
    function_object(Name, Linkage, Ret, Params, Sig, Impl),
    origins(Name, NLowers, CheckKinds).

% Allocate the frame, check for stack overflow, save the thread (and the
% return buffer), zero lowers[] and push the filc_frame.
prologue(Form, Size, NLowers, Ctx) -->
    { ctx_frame_base(Ctx, FrameBase),
      NegFrameBase is -FrameBase },
    [ins(push, q, [reg(rbp)]),
     ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(sub, q, [imm(Size), reg(rsp)])],
    (   { Form = mem(_) }
    ->  [ins(mov, q, [reg(rdi), reg(rax)]),
         ins(mov, q, [reg(rsi), reg(rdi)])]
    ;   []
    ),
    [ins(cmp, q, [reg(rsp), mem(0, rdi)]),
     ins(jae, none, [plt(filc_stack_overflow_failure)])],
    to_slot(rdi, thread, Ctx),
    (   { Form = mem(_) } -> to_slot(rax, retbuf, Ctx) ; [] ),
    zero_lowers(NLowers, FrameBase),
    [ins(mov, q, [mem(16, rdi), reg(rax)]),
     ins(mov, q, [reg(rax), mem(NegFrameBase, rbp)])],
    set_origin(Ctx, c),
    [ins(lea, q, [mem(NegFrameBase, rbp), reg(rax)]),
     ins(mov, q, [reg(rax), mem(16, rdi)])].

zero_lowers(0, _) --> !.
zero_lowers(N, FrameBase) -->
    [ins(xor, l, [reg(eax), reg(eax)])],
    { N1 is N - 1,
      numlist(0, N1, Is) },
    zero_lower_entries(Is, FrameBase).

zero_lower_entries([], _) --> [].
zero_lower_entries([I|Is], FrameBase) -->
    { Off is 16 + 8 * I - FrameBase },
    [ins(mov, q, [reg(rax), mem(Off, rbp)])],
    zero_lower_entries(Is, FrameBase).

set_origin(Ctx, Which) -->
    { ctx_name(Ctx, Name),
      ctx_frame_base(Ctx, FrameBase),
      Off is 8 - FrameBase,
      origin(Name, Which, Origin) },
    [ins(lea, q, [rip(Origin), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Off, rbp)])].

pop_frame(Ctx) -->
    { ctx_frame_base(Ctx, FrameBase),
      NegFrameBase is -FrameBase },
    from_slot(thread, rsi, Ctx),
    [ins(mov, q, [mem(NegFrameBase, rbp), reg(rdi)]),
     ins(mov, q, [reg(rdi), mem(16, rsi)])].

% Propagate an exception: pop the frame and return has_exception = 1.
exception_exit(Form, Ctx) -->
    pop_frame(Ctx),
    (   { Form = mem(_) }
    ->  from_slot(retbuf, rax, Ctx),
        [ins(mov, b, [imm(1), mem(0, rax)])]
    ;   [ins(mov, b, [imm(1), reg(al)])]
    ),
    [ins(leave, none, []), ins(ret, none, [])].

% The failure block of function_check//1, if the function calls through
% a pointer.
not_function_block(Blocks, Ctx) -->
    (   { member(blk(_, _, Insts, _), Blocks),
          memberchk(call(_, t(_), _), Insts) }
    ->  { special_label(Ctx, notfn, NotFn) },
        [label(NotFn),
         ins(mov, q, [reg(rax), reg(rdi)]),
         ins(mov, q, [reg(rcx), reg(rsi)]),
         ins(call, none, [plt(filc_check_function_call_fail)]),
         ins(ud2, none, [])]
    ;   []
    ).

%% Words: a p value is two words (address, lower); w and l are one.

param_words(Params, Words) :-
    foldl(param_word, Params, Words, []).

param_word(par(p, t(N)), [t(N), lower(t(N))|Ws], Ws) :- !.
param_word(par(_, t(N)), [t(N)|Ws], Ws).

% Incoming word I is in register I of Regs, or on the stack above the
% return address.
receive_words([], _, _, _) --> [].
receive_words([Word|Words], Regs, I, Ctx) -->
    (   { nth0(I, Regs, Reg) }
    ->  to_slot(Reg, Word, Ctx)
    ;   { length(Regs, NRegs),
          Off is 16 + 8 * (I - NRegs) },
        [ins(mov, q, [mem(Off, rbp), reg(rax)])],
        to_slot(rax, Word, Ctx)
    ),
    { I1 is I + 1 },
    receive_words(Words, Regs, I1, Ctx).

%% Results: none, one word or a tuple of two. A p word is two slots,
%% address and lower. Up to two slots come back in %rdx:%rcx; more go in
%% a buffer the caller passes in %rdi, {i8 has_exception, slots at 8..},
%% with the thread in %rsi, the callee lower in %rdx and the argument
%% words from %rcx (docs/abi-findings.md).

ret_kinds(void, []) :- !.
ret_kinds(tuple(Ks), Ks) :- !.
ret_kinds(K, [K]).

result_tos(void, []).
result_tos(to(T, K), [to(T, K)]).
result_tos(tuple(Tos), Tos).

result_ret(void, void).
result_ret(to(_, K), K).
result_ret(tuple(Tos), tuple(Ks)) :- findall(K, member(to(_, K), Tos), Ks).

% result_form(Res, Tos, Kinds, Form): a call result's destinations,
% their classes and its return form.
result_form(Res, Tos, Kinds, Form) :-
    result_tos(Res, Tos),
    findall(K, member(to(_, K), Tos), Kinds),
    ret_form(Kinds, Form).

% ret_form(Kinds, Form): reg, or mem(BufferBytes) rounded to 16.
ret_form(Ks, mem(Bytes)) :-
    foldl(count_slots, Ks, 0, N),
    N > 2,
    !,
    Bytes is (8 + 8 * N + 15) // 16 * 16.
ret_form(_, reg).

count_slots(p, N0, N) :- !, N is N0 + 2.
count_slots(_, N0, N) :- N is N0 + 1.

% The registers that carry argument words in each form.
form_regs(reg, [rdx, rcx, r8, r9]).
form_regs(mem(_), [rcx, r8, r9]).

% The slots of a result, in order, as the frame slots they fill.
result_slots(Res, Slots) :-
    result_tos(Res, Tos),
    foldl(to_slots, Tos, Slots, []).

to_slots(to(T, p), [T, lower(T)|Ss], Ss) :- !.
to_slots(to(T, _), [T|Ss], Ss).

% Word I of a generic call's arguments or results is at thread+128+8I,
% with its lower at thread+384+8I.
generic_offsets(I, Addr, Lower) :-
    Addr is 128 + 8 * I,
    Lower is 384 + 8 * I.

% gw(Kind, Offset) for each result word: its thread offset in a generic
% return (its lower, for p, is 256 further on).
generic_words(Ks, GWs) :-
    generic_words(Ks, 0, GWs).

generic_words([], _, []).
generic_words([K|Ks], I, [gw(K, Off)|GWs]) :-
    generic_offsets(I, Off, _),
    I1 is I + 1,
    generic_words(Ks, I1, GWs).

% The thread offsets of a generic return's slots, in slot order.
generic_srcs(gw(p, Off), [Off, LowerOff|Os], Os) :- !,
    LowerOff is Off + 256.
generic_srcs(gw(_, Off), [Off|Os], Os).

% Stack space for a buffered return, around a call.
reserve_ret_buffer(reg) --> [].
reserve_ret_buffer(mem(Bytes)) --> [ins(sub, q, [imm(Bytes), reg(rsp)])].

release_ret_buffer(reg) --> [].
release_ret_buffer(mem(Bytes)) --> [ins(add, q, [imm(Bytes), reg(rsp)])].

% split_words(Words, NRegs, RegWords, StackWords): the first NRegs words
% go in registers, the rest on the stack.
split_words(Words, NRegs, RegWords, StackWords) :-
    length(Words, NWords),
    (   NWords > NRegs
    ->  length(RegWords, NRegs),
        append(RegWords, StackWords, Words)
    ;   RegWords = Words,
        StackWords = []
    ).

% Keep %rsp 16-aligned at a call that pushes an odd number of words.
align_pad(Pad) -->
    (   { Pad =:= 1 } -> [ins(sub, q, [imm(8), reg(rsp)])] ; [] ).

pop_stack(Bytes) -->
    (   { Bytes > 0 } -> [ins(add, q, [imm(Bytes), reg(rsp)])] ; [] ).

%% Blocks and jumps

blocks([], _) --> [].
blocks([blk(Label, _, Insts, Jump)|Blocks], Ctx) -->
    { block_label(Ctx, Label, A) },
    [label(A)],
    insts(Insts, 0, Label, Ctx),
    jump(Jump, Label, Ctx),
    blocks(Blocks, Ctx).

jump(jmp(To), From, Ctx) -->
    edge(From, To, j, Ctx).
jump(jnz(V, True, False), From, Ctx) -->
    { amd64_ctx(Ctx, Fn),
      local_label(Ctx, From, jnz, false, FalseLabel) },
    load(V, w, a, Fn),
    [ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(FalseLabel)])],
    edge(From, True, t, Ctx),
    [label(FalseLabel)],
    edge(From, False, f, Ctx).
jump(ret(V), _, Ctx) -->
    { ctx_ret(Ctx, K),
      amd64_ctx(Ctx, Fn) },
    (   { K == p }
    ->  load(V, l, d, Fn),
        lower_of(V, rcx, Ctx)
    ;   load(V, K, d, Fn)
    ),
    return(Ctx).
jump(rets(Vs), _, Ctx) -->
    { ctx_ret(Ctx, tuple(Ks)),
      amd64_ctx(Ctx, Fn),
      ret_form(Ks, Form) },
    (   { Form == reg }
    ->  { Vs = [V1, V2] },
        load(V1, l, d, Fn),
        load(V2, l, c, Fn),
        return(Ctx)
    ;   from_slot(retbuf, rax, Ctx),
        buffer_words(Ks, Vs, 8, Ctx),
        [ins(mov, b, [imm(0), mem(0, rax)])],
        pop_frame(Ctx),
        [ins(leave, none, []), ins(ret, none, [])]
    ).
jump(ret, _, Ctx) -->
    return(Ctx).
jump(hlt, _, _) -->
    [ins(ud2, none, [])].

% The words of a buffered return, into the buffer at %rax.
buffer_words([], [], _, _) --> [].
buffer_words([K|Ks], [V|Vs], Off, Ctx) -->
    { amd64_ctx(Ctx, Fn) },
    load(V, l, d, Fn),
    [ins(mov, q, [reg(rdx), mem(Off, rax)])],
    (   { K == p }
    ->  { LowerOff is Off + 8,
          Off1 is Off + 16 },
        lower_of(V, rcx, Ctx),
        [ins(mov, q, [reg(rcx), mem(LowerOff, rax)])]
    ;   { Off1 is Off + 8 }
    ),
    buffer_words(Ks, Vs, Off1, Ctx).

return(Ctx) -->
    pop_frame(Ctx),
    [ins(xor, l, [reg(eax), reg(eax)]),
     ins(leave, none, []),
     ins(ret, none, [])].

% Phi copies for the edge, a pollcheck if it goes backwards in block
% order, then the jump.
edge(From, To, Tag, Ctx) -->
    { ctx_labels(Ctx, Labels),
      get_assoc(From, Labels, block(FromIndex, _)),
      get_assoc(To, Labels, block(ToIndex, Phis)),
      block_label(Ctx, To, ToLabel) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    (   { ToIndex =< FromIndex }
    ->  pollcheck(Ctx, From, Tag)
    ;   []
    ),
    [ins(jmp, none, [sym(ToLabel)])].

pollcheck(Ctx, Block, Tag) -->
    { ctx_name(Ctx, Name),
      local_label(Ctx, Block, Tag, poll, NoPoll),
      origin(Name, n, Origin) },
    from_slot(thread, rdi, Ctx),
    [ins(test, b, [imm(14), mem(8, rdi)]),
     ins(jz, none, [sym(NoPoll)]),
     ins(lea, q, [rip(Origin), reg(rsi)]),
     ins(call, none, [plt(filc_pollcheck_slow)]),
     label(NoPoll)].

% The parallel copy of an edge's phis: first every incoming value into
% its phi's shadow slots, then every shadow into the phi.
phi_reads([], _, _) --> [].
phi_reads([phi(t(D), K, Pairs)|Phis], From, Ctx) -->
    { memberchk(From-V, Pairs),
      amd64_ctx(Ctx, Fn) },
    (   { K == p }
    ->  load(V, l, a, Fn),
        to_slot(rax, shadow(D), Ctx),
        lower_of(V, rax, Ctx),
        to_slot(rax, lower(shadow(D)), Ctx)
    ;   load(V, K, a, Fn),
        to_slot(rax, shadow(D), Ctx)
    ),
    phi_reads(Phis, From, Ctx).

phi_writes([], _) --> [].
phi_writes([phi(t(D), K, _)|Phis], Ctx) -->
    from_slot(shadow(D), rax, Ctx),
    to_slot(rax, t(D), Ctx),
    (   { K == p }
    ->  from_slot(lower(shadow(D)), rax, Ctx),
        to_slot(rax, lower(t(D)), Ctx)
    ;   []
    ),
    phi_writes(Phis, Ctx).

% The lower of a p value: its lowers[] entry, or 0 for a constant.
lower_of(t(N), Reg, Ctx) --> from_slot(lower(t(N)), Reg, Ctx).
lower_of(c(_), Reg, _) --> [ins(mov, q, [imm(0), reg(Reg)])].

% A p value's address into %rax and lower into %rcx.
load_flight(V, Ctx) -->
    { amd64_ctx(Ctx, Fn) },
    load(V, l, a, Fn),
    lower_of(V, rcx, Ctx).

% The flight pointer in %rax:%rcx into t(D) and its lower.
store_flight(D, Ctx) -->
    to_slot(rax, t(D), Ctx),
    to_slot(rcx, lower(t(D)), Ctx).

%% Instructions

insts([], _, _, _) --> [].
insts([Inst|Insts], Index, Block, Ctx) -->
    inst(Inst, Index, Block, Ctx),
    { Index1 is Index + 1 },
    insts(Insts, Index1, Block, Ctx).

inst(ins(t(D), p, copy, [glo(S)]), _, _, Ctx) --> !,
    { ctx_name(Ctx, Name),
      ctx_module(Ctx, Module),
      getter(Module, S, Getter),
      origin(Name, c, Origin) },
    set_origin(Ctx, c),
    from_slot(thread, rdi, Ctx),
    [ins(lea, q, [rip(Origin), reg(rsi)]),
     ins(call, none, [Getter]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    store_flight(D, Ctx).
inst(ins(t(D), p, copy, [V]), _, _, Ctx) --> !,
    load_flight(V, Ctx),
    store_flight(D, Ctx).
inst(ins(t(D), p, Op, [P, X]), _, _, Ctx) -->
    { memberchk(Op, [add, sub]) }, !,
    { amd64_ctx(Ctx, Fn) },
    load_flight(P, Ctx),
    load(X, l, d, Fn),
    [ins(Op, q, [reg(rdx), reg(rax)])],
    store_flight(D, Ctx).
inst(ins(t(D), l, ptoi, [P]), _, _, Ctx) --> !,
    { amd64_ctx(Ctx, Fn) },
    load(P, l, a, Fn),
    to_slot(rax, t(D), Ctx).
inst(ins(t(D), p, itop, [X]), _, _, Ctx) --> !,
    { amd64_ctx(Ctx, Fn) },
    load(X, l, a, Fn),
    [ins(xor, l, [reg(ecx), reg(ecx)])],
    store_flight(D, Ctx).
inst(ins(t(D), p, alloc(Align), [N]), _, _, Ctx) --> !,
    { amd64_ctx(Ctx, Fn) },
    load(N, l, si, Fn),
    from_slot(thread, rdi, Ctx),
    (   { Align == 16 }
    ->  [ins(mov, l, [imm(16), reg(edx)]),
         ins(call, none, [plt(filc_allocate_with_alignment)])]
    ;   [ins(call, none, [plt(filc_allocate)])]
    ),
    [ins(lea, q, [mem(16, rax), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rcx)])],
    store_flight(D, Ctx).
inst(ins(t(D), p, load(p), [A]), Index, Block, Ctx) --> !,
    { local_label(Ctx, Block, Index, nolower, NoLower),
      local_label(Ctx, Block, Index, have, Have) },
    load_flight(A, Ctx),
    access_check(k(8, 0, 8), Ctx),
    aux_of_lower,
    [ins(jz, none, [sym(NoLower)]),
     ins(mov, q, [reg(rax), reg(rsi)]),
     ins(sub, q, [reg(rcx), reg(rsi)]),
     ins(mov, q, [mem(0, rdx, rsi), reg(rsi)]),
     ins(test, b, [imm(1), reg(sil)]),
     ins(jz, none, [sym(Have)]),
     ins(and, q, [imm(-2), reg(rsi)]),
     ins(mov, q, [mem(8, rsi), reg(rsi)]),
     ins(jmp, none, [sym(Have)]),
     label(NoLower),
     ins(xor, l, [reg(esi), reg(esi)]),
     label(Have),
     ins(mov, q, [mem(0, rax), reg(rax)]),
     ins(mov, q, [reg(rsi), reg(rcx)])],
    store_flight(D, Ctx).
inst(ins(t(D), K, load(T), [A]), _, _, Ctx) --> !,
    { load_width(T, Size),
      load_insn(T, K, LoadInsn) },
    load_flight(A, Ctx),
    access_check(k(Size, 0, 1), Ctx),
    [LoadInsn],
    to_slot(rax, t(D), Ctx).
inst(ins(t(D), K, Op, Args), _, _, Ctx) -->
    { amd64_ctx(Ctx, Fn) },
    op(Op, K, Args, Fn),
    to_slot(rax, t(D), Ctx).
inst(store(p, V, A), Index, Block, Ctx) --> !,
    { amd64_ctx(Ctx, Fn),
      local_label(Ctx, Block, Index, haveaux, HaveAux),
      local_label(Ctx, Block, Index, nobarrier, NoBarrier) },
    load_flight(A, Ctx),
    access_check(k(8, 1, 8), Ctx),
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
    load_flight(A, Ctx),
    from_slot(aux, rdx, Ctx),
    [ins(mov, q, [reg(rax), reg(r8)]),
     ins(sub, q, [reg(rcx), reg(r8)])],
    lower_of(V, rsi, Ctx),
    load(V, l, r9, Fn),
    [ins(mov, q, [reg(rsi), mem(0, rdx, r8)]),
     ins(mov, q, [reg(r9), mem(0, rax)])].
inst(store(W, V, A), _, _, Ctx) -->
    { amd64_ctx(Ctx, Fn),
      width_bytes(W, Size),
      (   W == l -> ValueK = l ; ValueK = w ),
      store_insn(W, d, StoreInsn) },
    load_flight(A, Ctx),
    access_check(k(Size, 1, 1), Ctx),
    load(V, ValueK, d, Fn),
    [StoreInsn].
inst(call(Res, glo(F), Args), _, _, Ctx) -->
    { call_target(Ctx, F, Res, Args, Target),
      result_form(Res, _, _, Form) },
    set_origin(Ctx, c),
    reserve_ret_buffer(Form),
    fast_call(Form, Args, direct(Target), Ctx),
    fast_result(Form, Res, Ctx),
    release_ret_buffer(Form).

/* A call through a p value. The callee must be a function object: lower
   not 0, ptr equal to the object's aux pointer, and special type
   function. Then the fast entry if the signature matches the call site's,
   else the generic entry with every argument as an 8-byte word at
   thread+128+8i and its lower at thread+384+8i (docs/abi-findings.md). */
inst(call(Res, t(C), Args), Index, Block, Ctx) -->
    { amd64_ctx(Ctx, Fn),
      call_sig(Res, Args, _, _, Sig),
      result_form(Res, Tos, RetKs, Form),
      special_label(Ctx, notfn, NotFn),
      special_label(Ctx, exc, Exc),
      length(Args, NArgs),
      ArgsSize is 8 * NArgs,
      local_label(Ctx, Block, Index, generic, Generic),
      local_label(Ctx, Block, Index, done, Done),
      local_label(Ctx, Block, Index, retok, RetOk) },
    set_origin(Ctx, c),
    reserve_ret_buffer(Form),
    load_flight(t(C), Ctx),
    function_check(NotFn),
    to_slot(rcx, aux, Ctx),
    [ins(movabs, q, [imm(Sig), reg(rsi)]),
     ins(cmp, q, [reg(rsi), mem(16, rcx)]),
     ins(jne, none, [sym(Generic)])],
    fast_call(Form, Args, indirect, Ctx),
    fast_result(Form, Res, Ctx),
    [ins(jmp, none, [sym(Done)]),
     label(Generic)],
    generic_call_args(Args, 0, Fn, Ctx),
    from_slot(thread, rdi, Ctx),
    from_slot(aux, rsi, Ctx),
    [ins(mov, l, [imm(ArgsSize), reg(edx)]),
     ins(call, q, [ind(mem(8, rsi))]),
     ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    (   { Tos == [] } -> []
    ;   { length(Tos, NRetWords),
          Need is 8 * NRetWords,
          generic_words(RetKs, GWs) },
        from_slot(thread, rsi, Ctx),
        rets_check(Need, RetOk),
        generic_into_slots(GWs, Tos, Ctx)
    ),
    [label(Done)],
    release_ret_buffer(Form).

% Arguments, the entry registers and the call itself, for the fast
% convention in form Form; Callee is direct(Symbol) or indirect (through
% the aux slot).
fast_call(Form, Args, Callee, Ctx) -->
    { amd64_ctx(Ctx, Fn),
      foldl(arg_words, Args, Words, []),
      (   Form == reg -> Regs = [d, c, r8, r9] ; Regs = [c, r8, r9] ),
      length(Regs, NRegs),
      split_words(Words, NRegs, RegWords, StackWords),
      length(StackWords, NStack),
      Pad is NStack mod 2,
      Pop is 8 * (NStack + Pad),
      reverse(StackWords, Pushes) },
    align_pad(Pad),
    push_words(Pushes, Fn, Ctx),
    reg_words(RegWords, Regs, Fn, Ctx),
    entry_call(Form, Callee, Pop, Ctx),
    pop_stack(Pop).

% Pop is the stack words' size, which a buffered return's buffer sits
% above.
entry_call(reg, direct(Target), _, Ctx) -->
    from_slot(thread, rdi, Ctx),
    [ins(xor, l, [reg(esi), reg(esi)]),
     ins(call, none, [Target])].
entry_call(reg, indirect, _, Ctx) -->
    from_slot(thread, rdi, Ctx),
    from_slot(aux, rsi, Ctx),
    [ins(call, q, [ind(mem(0, rsi))])].
entry_call(mem(_), direct(Target), Pop, Ctx) -->
    from_slot(thread, rsi, Ctx),
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [Target])].
entry_call(mem(_), indirect, Pop, Ctx) -->
    from_slot(thread, rsi, Ctx),
    from_slot(aux, rdx, Ctx),
    [ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
     ins(call, q, [ind(mem(0, rdx))])].

% has_exception, then the result slots from %rdx:%rcx or the buffer.
fast_result(reg, Res, Ctx) -->
    { special_label(Ctx, exc, Exc),
      result_slots(Res, Slots) },
    [ins(test, b, [imm(1), reg(al)]),
     ins(jnz, none, [sym(Exc)])],
    regs_into_slots(Slots, [rdx, rcx], Ctx).
fast_result(mem(_), Res, Ctx) -->
    { special_label(Ctx, exc, Exc),
      result_slots(Res, Slots) },
    [ins(cmp, b, [imm(0), mem(0, rsp)]),
     ins(jne, none, [sym(Exc)])],
    buffer_into_slots(Slots, 8, Ctx).

regs_into_slots([], _, _) --> [].
regs_into_slots([Slot|Slots], [Reg|Regs], Ctx) -->
    to_slot(Reg, Slot, Ctx),
    regs_into_slots(Slots, Regs, Ctx).

buffer_into_slots([], _, _) --> [].
buffer_into_slots([Slot|Slots], Off, Ctx) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)])],
    to_slot(rax, Slot, Ctx),
    { Off1 is Off + 8 },
    buffer_into_slots(Slots, Off1, Ctx).

% A generic return's words, from the thread at %rsi, into the slots.
generic_into_slots([], [], _) --> [].
generic_into_slots([gw(K, Off)|GWs], [to(T, _)|Tos], Ctx) -->
    [ins(mov, q, [mem(Off, rsi), reg(rax)])],
    to_slot(rax, T, Ctx),
    (   { K == p }
    ->  { LowerOff is Off + 256 },
        [ins(mov, q, [mem(LowerOff, rsi), reg(rax)])],
        to_slot(rax, lower(T), Ctx)
    ;   []
    ),
    generic_into_slots(GWs, Tos, Ctx).

% Fail unless the generic return size in %rdx is at least Need.
rets_check(Need, RetOk) -->
    [ins(cmp, q, [imm(Need), reg(rdx)]),
     ins(jae, none, [sym(RetOk)]),
     ins(mov, q, [reg(rdx), reg(rdi)]),
     ins(mov, l, [imm(Need), reg(esi)]),
     ins(xor, l, [reg(edx), reg(edx)]),
     ins(call, none, [plt(filc_cc_rets_check_failure)]),
     ins(ud2, none, []),
     label(RetOk)].

% Each argument into the thread's generic argument area.
generic_call_args([], _, _, _) --> [].
generic_call_args([arg(K, V)|Args], I, Fn, Ctx) -->
    { generic_offsets(I, Addr, Lower) },
    (   { K == p }
    ->  load(V, l, a, Fn),
        lower_of(V, rcx, Ctx)
    ;   load(V, K, a, Fn),
        [ins(xor, l, [reg(ecx), reg(ecx)])]
    ),
    from_slot(thread, rdx, Ctx),
    [ins(mov, q, [reg(rax), mem(Addr, rdx)]),
     ins(mov, q, [reg(rcx), mem(Lower, rdx)])],
    { I1 is I + 1 },
    generic_call_args(Args, I1, Fn, Ctx).

% With a flight pointer in %rax:%rcx, jump to Fail unless it points at a
% function object. Clobbers %rdx and %rsi.
function_check(Fail) -->
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)]),
     ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(540431955284459520), reg(rsi)]),
     ins(and, q, [reg(rdx), reg(rsi)]),
     ins(movabs, q, [imm(36028797018963968), reg(rdi)]),
     ins(cmp, q, [reg(rdi), reg(rsi)]),
     ins(jne, none, [sym(Fail)]),
     ins(movabs, q, [imm(281474976710655), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(jne, none, [sym(Fail)])].

% The getter for symbol S: local if the module defines S.
getter(module(Items), S, Getter) :-
    format(atom(Name), 'pizlonated_~w', [S]),
    (   (   memberchk(func(S, _, _, _, _), Items)
        ;   memberchk(data(S, _, _, _), Items)
        )
    ->  Getter = sym(Name)
    ;   Getter = plt(Name)
    ).

% The aux pointer of the object at lower %rcx into %rdx, setting ZF if
% it has none.
aux_of_lower -->
    [ins(mov, q, [mem(-8, rcx), reg(rdx)]),
     ins(movabs, q, [imm(281474976710655), reg(rsi)]),
     ins(and, q, [reg(rsi), reg(rdx)])].

load_width(T, Size) :-
    memberchk(T-Size, [l-8, sw-4, uw-4, sh-2, uh-2, sb-1, ub-1]).

% Functions in the module are called at their implementation; others at
% their pizlonatedFI symbol: a weak thunk this module emits (thunk//1),
% overridden by a clang definition with the same signature if one is
% linked in.
call_target(Ctx, F, Res, Args, sym(Target)) :-
    ctx_module(Ctx, Module),
    (   func_named(Module, F, Func)
    ->  fn_sig(Func, Sig),
        impl_symbol(F, Sig, Target)
    ;   call_sig(Res, Args, _, _, Sig),
        format(atom(Target), 'pizlonatedFI~w_~w', [Sig, F])
    ).

% call_sig(Res, Args, RetKind, ArgKinds, Sig): a call site's signature.
call_sig(Res, Args, RetKind, ArgKinds, Sig) :-
    result_ret(Res, RetKind),
    findall(K, member(arg(K, _), Args), ArgKinds),
    signature(RetKind, ArgKinds, Sig).

% An argument's words: addr(V) and lower(V) for p, else val(K, V).
arg_words(arg(p, V), [addr(V), lower(V)|Ws], Ws) :- !.
arg_words(arg(K, V), [val(K, V)|Ws], Ws).

% A word into register R, an amd64 register short name (a, d, c, r8...).
word_into(addr(V), R, Fn, _) --> load(V, l, R, Fn).
word_into(val(K, V), R, Fn, _) --> load(V, K, R, Fn).
word_into(lower(V), R, _, Ctx) --> { reg(R, l, RN) }, lower_of(V, RN, Ctx).

push_words([], _, _) --> [].
push_words([Word|Words], Fn, Ctx) -->
    word_into(Word, a, Fn, Ctx),
    [ins(push, q, [reg(rax)])],
    push_words(Words, Fn, Ctx).

reg_words([], _, _, _) --> [].
reg_words([Word|Words], [R|Rs], Fn, Ctx) -->
    word_into(Word, R, Fn, Ctx),
    reg_words(Words, Rs, Fn, Ctx).

%% Access checks: k(Size, Write, Align), with the pointer in %rax and its
%% lower in %rcx, which the failure block passes on.

access_check(k(Size, Write, Align), Ctx) -->
    { check_fail_label(Ctx, k(Size, Write, Align), Fail) },
    [ins(test, q, [reg(rcx), reg(rcx)]),
     ins(jz, none, [sym(Fail)]),
     ins(cmp, q, [reg(rcx), reg(rax)]),
     ins(jb, none, [sym(Fail)]),
     ins(mov, q, [mem(-16, rcx), reg(rdx)]),
     ins(sub, q, [imm(Size), reg(rdx)]),
     ins(cmp, q, [reg(rdx), reg(rax)]),
     ins(ja, none, [sym(Fail)])],
    (   { Write =:= 1 }
    ->  [ins(test, b, [imm(6), mem(-2, rcx)]),
         ins(jnz, none, [sym(Fail)])]
    ;   []
    ),
    (   { Align =:= 8 }
    ->  [ins(test, b, [imm(7), reg(al)]),
         ins(jnz, none, [sym(Fail)])]
    ;   []
    ).

check_fail_label(Ctx, k(Size, Write, Align), Label) :-
    ctx_name(Ctx, Name),
    format(atom(Label), '.L~w..fail.~w.~w.~w', [Name, Size, Write, Align]).

check_origin(Name, k(Size, Write, Align), Label) :-
    format(atom(Label), '.L~w..chk.~w.~w.~w', [Name, Size, Write, Align]).

% The distinct check kinds the function's accesses need.
access_check_kinds(Blocks, Kinds) :-
    findall(Kind,
            (   member(blk(_, _, Insts, _), Blocks),
                member(Inst, Insts),
                inst_check_kind(Inst, Kind)
            ),
            Kinds0),
    sort(Kinds0, Kinds).

inst_check_kind(ins(_, _, load(p), _), k(8, 0, 8)) :- !.
inst_check_kind(ins(_, _, load(T), _), k(Size, 0, 1)) :- load_width(T, Size).
inst_check_kind(store(p, _, _), k(8, 1, 8)) :- !.
inst_check_kind(store(W, _, _), k(Size, 1, 1)) :- width_bytes(W, Size).

check_fail_blocks([], _) --> [].
check_fail_blocks([Kind|Kinds], Ctx) -->
    { check_fail_label(Ctx, Kind, Fail),
      ctx_name(Ctx, Name),
      check_origin(Name, Kind, Origin) },
    [label(Fail),
     ins(mov, q, [reg(rax), reg(rdi)]),
     ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(lea, q, [rip(Origin), reg(rdx)]),
     ins(call, none, [plt(filc_optimized_access_check_fail)]),
     ins(ud2, none, [])],
    check_fail_blocks(Kinds, Ctx).

%% Function objects: every function gets a getter, a generic entry and a
%% function object, so its address can be taken; exported ones also get
%% the FI alias and a global getter.

function_object(Name, Linkage, Ret, Params, Sig, Impl) -->
    { format(atom(FI), 'pizlonatedFI~w_~w', [Sig, Name]),
      format(atom(FO), 'pizlonatedFO_~w', [Name]),
      format(atom(Getter), 'pizlonated_~w', [Name]),
      format(atom(Generic), '.L~w..generic', [Name]) },
    (   { Linkage == export }
    ->  [globl(FI), type(FI, function), set(FI, Impl), globl(Getter)]
    ;   []
    ),
    [type(Getter, function), label(Getter),
     ins(lea, q, [rip(FO+16), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])],
    generic_entry(Generic, Ret, Params),
    [section(data_rel_ro), p2align(4), type(FO, object), label(FO),
     quad(FO+16),
     quad(FO+16+36873221949095936),
     quad(Impl),
     quad(Generic),
     quad(Sig),
     size(FO, 40)].

%% Data objects, as clang lays out globals (docs/abi-findings.md):
%% DO_d = {upper, aux} then the payload rounded up to 8 bytes, a 16-byte
%% cache GP_d, an aux array DA_d if the payload holds pointers, and a
%% getter whose slow path registers the object and runs the relocations
%% that fill in its pointers.

data_object(Name, Linkage0, Items) -->
    { (   Linkage0 = ro(Linkage) -> ReadOnly = 2
      ;   Linkage = Linkage0, ReadOnly = 0
      ),
      format(atom(DO), 'pizlonatedDO_~w', [Name]),
      format(atom(DA), 'pizlonatedDA_~w', [Name]),
      format(atom(GP), '.LpizlonatedGP_~w', [Name]),
      format(atom(Getter), 'pizlonated_~w', [Name]),
      format(atom(Relocs), '.Lpizlonated_~w..relocs', [Name]),
      format(atom(Slow), '.Lpizlonated_~w..slow', [Name]),
      format(atom(Inited), '.Lpizlonated_~w..inited', [Name]),
      foldl(payload_item, Items, Payload, 0-[], Size0-Rs0),
      reverse(Rs0, Rs),
      length(Rs, NRelocs),
      Size is (Size0 + 7) // 8 * 8,
      Pad is Size - Size0,
      (   Rs == [] -> Aux = 0, Flags is 1 + ReadOnly
      ;   Aux = DA, Flags is 17 + ReadOnly
      ),
      FlagBits is Flags << 48,
      (   Aux == 0 -> AuxWord = FlagBits ; AuxWord = DA+FlagBits ),
      Total is 16 + Size },
    [section(data), p2align(4), type(DO, object), label(DO),
     quad(DO+16+Size), quad(AuxWord)],
    seq(Payload),
    (   { Pad > 0 } -> [zero(Pad)] ; [] ),
    [size(DO, Total)],
    [section(bss), p2align(4), label(GP), zero(16)],
    (   { Rs == [] } -> [] ; [p2align(4), label(DA), zero(Size)] ),
    (   { Rs == [] } -> []
    ;   [section(data_rel_ro), p2align(4), label(Relocs)],
        relocations(Rs, Name)
    ),
    [section(text), p2align(4)],
    (   { Linkage == export } -> [globl(Getter)] ; [] ),
    [type(Getter, function), label(Getter),
     ins(mov, q, [rip(GP), reg(rax)]),
     ins(mov, q, [rip(GP+8), reg(rdx)]),
     ins(test, q, [reg(rax), reg(rax)]),
     ins(jz, none, [sym(Slow)]),
     ins(test, q, [reg(rdx), reg(rdx)]),
     ins(jz, none, [sym(Slow)]),
     ins(ret, none, []),
     label(Slow),
     ins(push, q, [reg(rbx)]),
     ins(mov, q, [reg(rdi), reg(rbx)]),
     ins(lea, q, [rip(GP), reg(rdx)]),
     ins(lea, q, [rip(DO), reg(rcx)]),
     ins(call, none, [plt(filc_global_initialization_start)]),
     ins(test, b, [imm(1), reg(al)]),
     ins(jz, none, [sym(Inited)])],
    (   { NRelocs > 0 }
    ->  [ins(mov, q, [reg(rbx), reg(rdi)]),
         ins(lea, q, [rip(DO), reg(rsi)]),
         ins(lea, q, [rip(Relocs), reg(rdx)]),
         ins(mov, l, [imm(NRelocs), reg(ecx)]),
         ins(call, none, [plt(filc_execute_constant_relocations)])]
    ;   []
    ),
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(call, none, [plt(filc_global_initialization_end)]),
     label(Inited),
     ins(pop, q, [reg(rbx)]),
     ins(lea, q, [rip(DO+16), reg(rax)]),
     ins(mov, q, [reg(rax), reg(rdx)]),
     ins(ret, none, [])].

% payload_item(Item, Line, Off0-Rs0, Off-Rs): the payload directive, and
% a relocation r(Offset, Symbol, Addend) for each pointer, whose slot
% stays 0 until the relocation fills it in.
payload_item(zero(N), zero(N), Off0-Rs, Off-Rs) :-
    Off is Off0 + N.
payload_item(item(b, str(Cs)), ascii(Cs), Off0-Rs, Off-Rs) :- !,
    phrase(asm_string_length(N), Cs),
    Off is Off0 + N.
payload_item(item(p, sym(S, Addend)), quad(0), Off0-Rs,
             Off-[r(Off0, S, Addend)|Rs]) :- !,
    (   Off0 mod 8 =:= 0 -> true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    Off is Off0 + 8.
payload_item(item(W, c(N)), Directive, Off0-Rs, Off-Rs) :-
    width_bytes(W, Bytes),
    Bits is 8 * Bytes,
    U is N mod (1 << Bits),
    memberchk(Bytes-Directive,
              [1-byte([U]), 2-short(U), 4-long(U), 8-quad(U)]),
    Off is Off0 + Bytes.

% The byte length of an ascii string with GNU as escapes.
asm_string_length(0) --> [].
asm_string_length(N) -->
    ['\\'], !,
    escape_tail,
    asm_string_length(N0),
    { N is N0 + 1 }.
asm_string_length(N) -->
    [_],
    asm_string_length(N0),
    { N is N0 + 1 }.

% After a backslash: up to three octal digits, or one other character.
escape_tail --> octal_digit, !, octal_upto(2).
escape_tail --> [_].

octal_upto(0) --> !.
octal_upto(K) --> octal_digit, !, { K1 is K - 1 }, octal_upto(K1).
octal_upto(_) --> [].

octal_digit --> [D], { char_code(D, C), C >= 0'0, C =< 0'7 }.

% Each relocation is {u64 offset, u32 kind, pad, target}: kind 0 calls a
% getter, kind 1 a constexpr node {u32 add-immediate = 0, u32 0, getter,
% u64 addend}.
relocations(Rs, Name) -->
    reloc_entries(Rs, 0, Name),
    reloc_nodes(Rs, 0, Name).

reloc_entries([], _, _) --> [].
reloc_entries([r(Off, S, Addend)|Rs], I, Name) -->
    { reloc_getter(S, Getter) },
    (   { Addend =:= 0 }
    ->  [quad(Off), long(0), zero(4), quad(Getter)]
    ;   { reloc_node(Name, I, Node) },
        [quad(Off), long(1), zero(4), quad(Node)]
    ),
    { I1 is I + 1 },
    reloc_entries(Rs, I1, Name).

reloc_nodes([], _, _) --> [].
reloc_nodes([r(_, S, Addend)|Rs], I, Name) -->
    (   { Addend =:= 0 } -> []
    ;   { reloc_getter(S, Getter),
          reloc_node(Name, I, Node),
          U is Addend mod 18446744073709551616 },
        [label(Node), long(0), long(0), quad(Getter), quad(U)]
    ),
    { I1 is I + 1 },
    reloc_nodes(Rs, I1, Name).

reloc_getter(S, Getter) :-
    format(atom(Getter), 'pizlonated_~w', [S]).

reloc_node(Name, I, Node) :-
    format(atom(Node), '.Lpizlonated_~w..node~w', [Name, I]).

%% Thunks for functions outside the module, as clang emits them: a hidden
%% weak pizlonatedFI<sig>_f that gets f's function object from its getter,
%% checks it, and calls the fast entry if the signature matches or the
%% generic entry otherwise. A clang definition of the same symbol wins.

% external_callees(Module, Callees): t(F, Sig, RetKind, ArgKinds) for
% each thunk the module needs.
external_callees(Module, Callees) :-
    Module = module(Items),
    findall(t(F, Sig, RetKind, ArgKinds),
            (   member(func(_, _, _, _, Blocks), Items),
                member(blk(_, _, Insts, _), Blocks),
                member(call(Res, glo(F), Args), Insts),
                \+ func_named(Module, F, _),
                call_sig(Res, Args, RetKind, ArgKinds, Sig)
            ),
            Callees0),
    sort(Callees0, Callees1),
    one_per_symbol(Callees1, Callees).

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
thunk(t(F, Sig, RetKind, ArgKs)) -->
    { format(atom(FI), 'pizlonatedFI~w_~w', [Sig, F]),
      format(atom(Getter), 'pizlonated_~w', [F]),
      atom_concat('.L', FI, Local),
      atom_concat(Local, '..fail', Fail),
      atom_concat(Local, '..generic', Generic),
      atom_concat(Local, '..out', Out),
      atom_concat(Local, '..retok', RetOk),
      atom_concat(Local, '..exc', GenericExc),
      ret_kinds(RetKind, RetKs),
      ret_form(RetKs, Form),
      form_regs(Form, Regs),
      length(Regs, NRegs),
      foldl(class_words, ArgKs, Words, 0, NWords),
      NStack is max(0, NWords - NRegs),
      Pad is NStack mod 2,
      length(ArgKs, NArgs),
      ArgsSize is 8 * NArgs,
      (   NStack > 0
      ->  NStack1 is NStack - 1,
          numlist(0, NStack1, StackIs0),
          reverse(StackIs0, StackIs)
      ;   StackIs = []
      ),
      length(RetKs, NRetWords),
      Need is 8 * NRetWords,
      generic_words(RetKs, GWs) },
    [section(text), p2align(4),
     hidden(FI), weak(FI), type(FI, function), label(FI)],
    thunk_prologue(Form),
    [ins(xor, l, [reg(esi), reg(esi)]),
     ins(call, none, [plt(Getter)]),
     ins(mov, q, [reg(rdx), reg(rcx)])],
    function_check(Fail),
    [ins(mov, q, [reg(rcx), mem(-48, rbp)]),
     ins(movabs, q, [imm(Sig), reg(rsi)]),
     ins(cmp, q, [reg(rsi), mem(16, rcx)]),
     ins(jne, none, [sym(Generic)])],
    align_pad(Pad),
    thunk_push(StackIs, Form),
    thunk_fast_call(Form),
    [label(Out),
     ins(lea, q, [mem(-40, rbp), reg(rsp)]),
     ins(pop, q, [reg(r15)]),
     ins(pop, q, [reg(r14)]),
     ins(pop, q, [reg(r13)]),
     ins(pop, q, [reg(r12)]),
     ins(pop, q, [reg(rbx)]),
     ins(pop, q, [reg(rbp)]),
     ins(ret, none, []),
     label(Generic)],
    thunk_generic(ArgKs, Words, 0, Form),
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(mov, q, [mem(-48, rbp), reg(rsi)]),
     ins(mov, l, [imm(ArgsSize), reg(edx)]),
     ins(call, q, [ind(mem(8, rsi))]),
     ins(test, b, [imm(1), reg(al)])],
    (   { Form == reg }
    ->  [ins(jnz, none, [sym(Out)])],
        (   { RetKs == [] } -> []
        ;   rets_check(Need, RetOk),
            { foldl(generic_srcs, GWs, Srcs, []) },
            thunk_regs(Srcs, [rdx, rcx])
        ),
        [ins(xor, l, [reg(eax), reg(eax)]),
         ins(jmp, none, [sym(Out)])]
    ;   [ins(jnz, none, [sym(GenericExc)])],
        rets_check(Need, RetOk),
        { foldl(generic_srcs, GWs, Srcs, []) },
        thunk_buffer(Srcs, 8),
        [ins(mov, b, [imm(0), mem(0, r12)]),
         ins(mov, q, [reg(r12), reg(rax)]),
         ins(jmp, none, [sym(Out)]),
         label(GenericExc),
         ins(mov, b, [imm(1), mem(0, r12)]),
         ins(mov, q, [reg(r12), reg(rax)]),
         ins(jmp, none, [sym(Out)])]
    ),
    [label(Fail),
     ins(mov, q, [reg(rax), reg(rdi)]),
     ins(mov, q, [reg(rcx), reg(rsi)]),
     ins(call, none, [plt(filc_check_function_call_fail)]),
     ins(ud2, none, []),
     size(FI)].

% Save the callee-saved registers and move the thread and register words
% into them; leaves the thread in %rdi for the getter call.
thunk_prologue(Form) -->
    [ins(push, q, [reg(rbp)]),
     ins(mov, q, [reg(rsp), reg(rbp)]),
     ins(push, q, [reg(rbx)]),
     ins(push, q, [reg(r12)]),
     ins(push, q, [reg(r13)]),
     ins(push, q, [reg(r14)]),
     ins(push, q, [reg(r15)]),
     ins(sub, q, [imm(8), reg(rsp)])],
    (   { Form == reg }
    ->  [ins(mov, q, [reg(rdi), reg(rbx)]),
         ins(mov, q, [reg(rdx), reg(r12)]),
         ins(mov, q, [reg(rcx), reg(r13)]),
         ins(mov, q, [reg(r8), reg(r14)]),
         ins(mov, q, [reg(r9), reg(r15)])]
    ;   [ins(mov, q, [reg(rsi), reg(rbx)]),
         ins(mov, q, [reg(rdi), reg(r12)]),
         ins(mov, q, [reg(rcx), reg(r13)]),
         ins(mov, q, [reg(r8), reg(r14)]),
         ins(mov, q, [reg(r9), reg(r15)]),
         ins(mov, q, [reg(rsi), reg(rdi)])]
    ).

% The fast entry, with the incoming words back in their registers.
thunk_fast_call(reg) -->
    [ins(mov, q, [reg(rbx), reg(rdi)]),
     ins(mov, q, [mem(-48, rbp), reg(rsi)]),
     ins(mov, q, [reg(r12), reg(rdx)]),
     ins(mov, q, [reg(r13), reg(rcx)]),
     ins(mov, q, [reg(r14), reg(r8)]),
     ins(mov, q, [reg(r15), reg(r9)]),
     ins(call, q, [ind(mem(0, rsi))])].
thunk_fast_call(mem(_)) -->
    [ins(mov, q, [reg(r12), reg(rdi)]),
     ins(mov, q, [reg(rbx), reg(rsi)]),
     ins(mov, q, [mem(-48, rbp), reg(rdx)]),
     ins(mov, q, [reg(r13), reg(rcx)]),
     ins(mov, q, [reg(r14), reg(r8)]),
     ins(mov, q, [reg(r15), reg(r9)]),
     ins(call, q, [ind(mem(0, rdx))])].

thunk_regs([], _) --> [].
thunk_regs([Off|Offs], [Reg|Regs]) -->
    [ins(mov, q, [mem(Off, rbx), reg(Reg)])],
    thunk_regs(Offs, Regs).

thunk_buffer([], _) --> [].
thunk_buffer([Src|Srcs], Off) -->
    [ins(mov, q, [mem(Src, rbx), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Off, r12)])],
    { Off1 is Off + 8 },
    thunk_buffer(Srcs, Off1).

% class_words(K, Ws, I0, I): the word positions of an argument of class K.
class_words(p, [I0, I1], I0, I) :- !, I1 is I0 + 1, I is I0 + 2.
class_words(_, [I0], I0, I) :- I is I0 + 1.

% The callee-saved registers that hold the incoming register words.
thunk_saved_regs(reg, [r12, r13, r14, r15]).
thunk_saved_regs(mem(_), [r13, r14, r15]).

% Where incoming word J lives, as an operand.
thunk_word(Form, J, reg(R)) :-
    form_regs(Form, Regs),
    length(Regs, NRegs),
    J < NRegs,
    !,
    thunk_saved_regs(Form, Saved),
    nth0(J, Saved, R).
thunk_word(Form, J, mem(Off, rbp)) :-
    form_regs(Form, Regs),
    length(Regs, NRegs),
    Off is 16 + 8 * (J - NRegs).

% Push stack word I (counting from the first stack word) for each I.
thunk_push([], _) --> [].
thunk_push([I|Is], Form) -->
    { form_regs(Form, Regs),
      length(Regs, NRegs),
      J is I + NRegs,
      thunk_word(Form, J, Word) },
    [ins(push, q, [Word])],
    thunk_push(Is, Form).

% Each argument's words into the thread's generic argument area.
thunk_generic([], [], _, _) --> [].
thunk_generic([K|Ks], [Ws|Wss], I, Form) -->
    { generic_offsets(I, Addr, Lower) },
    (   { K == p, Ws = [A, L] }
    ->  thunk_store(A, Addr, Form),
        thunk_store(L, Lower, Form)
    ;   { Ws = [A] },
        thunk_store(A, Addr, Form),
        [ins(mov, q, [imm(0), mem(Lower, rbx)])]
    ),
    { I1 is I + 1 },
    thunk_generic(Ks, Wss, I1, Form).

% Incoming word J into the thread at offset Off.
thunk_store(J, Off, Form) -->
    { thunk_word(Form, J, Word) },
    (   { Word = reg(_) }
    ->  [ins(mov, q, [Word, mem(Off, rbx)])]
    ;   [ins(mov, q, [Word, reg(rax)]),
         ins(mov, q, [reg(rax), mem(Off, rbx)])]
    ).

/* The generic entry: {i1, i64 ret_size} (thread, callee_lower, args_size).
   Argument i is 8 bytes at thread+128+8i, with its lower (for p) at
   thread+384+8i, and so is result word i. It calls the fast entry
   through callee_lower, with a buffer on the stack for a buffered
   return. */
generic_entry(Generic, Ret, Params) -->
    { length(Params, NArgs),
      Need is 8 * NArgs,
      findall(Offs,
              (   nth0(I, Params, par(K, _)),
                  generic_param_offsets(K, I, Offs)
              ),
              Offss),
      append(Offss, Words),
      ret_kinds(Ret, RetKs),
      ret_form(RetKs, Form),
      form_regs(Form, Regs),
      length(Regs, NRegs),
      split_words(Words, NRegs, RegWords, StackWords),
      length(StackWords, NStack),
      Pad is NStack mod 2,
      Pop is 8 * (NStack + Pad),
      reverse(StackWords, Pushes),
      length(RetKs, NRetWords),
      RetSize is 8 * max(1, NRetWords),
      generic_words(RetKs, GWs),
      foldl(generic_srcs, GWs, Dests, []),
      atom_concat(Generic, '.short', Short),
      atom_concat(Generic, '.done', Done) },
    [section(text), label(Generic), ins(push, q, [reg(rbx)])],
    (   { NArgs > 0 }
    ->  [ins(cmp, q, [imm(Need), reg(rdx)]),
         ins(jb, none, [sym(Short)])]
    ;   []
    ),
    [ins(mov, q, [reg(rdi), reg(rbx)])],
    reserve_ret_buffer(Form),
    align_pad(Pad),
    generic_push(Pushes),
    generic_regs(RegWords, Regs),
    (   { Form == reg }
    ->  [ins(call, q, [ind(mem(0, rsi))])],
        pop_stack(Pop),
        [ins(test, b, [imm(1), reg(al)]),
         ins(jnz, none, [sym(Done)])],
        (   { RetKs == [] }
        ->  [ins(mov, q, [imm(0), mem(128, rbx)]),
             ins(mov, q, [imm(0), mem(384, rbx)])]
        ;   generic_from_regs(Dests, [rdx, rcx]),
            generic_zero_lowers(GWs)
        ),
        [ins(mov, l, [imm(RetSize), reg(edx)]),
         label(Done)]
    ;   [ins(mov, q, [reg(rsi), reg(rdx)]),
         ins(mov, q, [reg(rbx), reg(rsi)]),
         ins(lea, q, [mem(Pop, rsp), reg(rdi)]),
         ins(call, q, [ind(mem(0, rdx))])],
        pop_stack(Pop),
        [ins(mov, b, [mem(0, rsp), reg(al)]),
         ins(test, b, [reg(al), reg(al)]),
         ins(jnz, none, [sym(Done)])],
        generic_from_buffer(Dests, 8),
        generic_zero_lowers(GWs),
        [ins(mov, l, [imm(RetSize), reg(edx)]),
         ins(xor, l, [reg(eax), reg(eax)]),
         label(Done)],
        release_ret_buffer(Form)
    ),
    [ins(pop, q, [reg(rbx)]),
     ins(ret, none, [])],
    (   { NArgs > 0 }
    ->  [label(Short),
         ins(mov, q, [reg(rdx), reg(rdi)]),
         ins(mov, l, [imm(Need), reg(esi)]),
         ins(xor, l, [reg(edx), reg(edx)]),
         ins(call, none, [plt(filc_cc_args_check_failure)]),
         ins(ud2, none, [])]
    ;   []
    ).

% The thread offsets of parameter I's words.
generic_param_offsets(p, I, [Addr, Lower]) :- !,
    generic_offsets(I, Addr, Lower).
generic_param_offsets(_, I, [Addr]) :-
    generic_offsets(I, Addr, _).

generic_push([]) --> [].
generic_push([Off|Offs]) -->
    [ins(push, q, [mem(Off, rbx)])],
    generic_push(Offs).

generic_regs([], _) --> [].
generic_regs([Off|Offs], [Reg|Regs]) -->
    [ins(mov, q, [mem(Off, rbx), reg(Reg)])],
    generic_regs(Offs, Regs).

generic_from_regs([], _) --> [].
generic_from_regs([Off|Offs], [Reg|Regs]) -->
    [ins(mov, q, [reg(Reg), mem(Off, rbx)])],
    generic_from_regs(Offs, Regs).

generic_from_buffer([], _) --> [].
generic_from_buffer([Dest|Dests], Off) -->
    [ins(mov, q, [mem(Off, rsp), reg(rax)]),
     ins(mov, q, [reg(rax), mem(Dest, rbx)])],
    { Off1 is Off + 8 },
    generic_from_buffer(Dests, Off1).

% An integer result word has no lower.
generic_zero_lowers([]) --> [].
generic_zero_lowers([gw(K, Off)|GWs]) -->
    (   { K == p } -> []
    ;   { LowerOff is Off + 256 },
        [ins(mov, q, [imm(0), mem(LowerOff, rbx)])]
    ),
    generic_zero_lowers(GWs).

%% Static data: function origins (the pin's 40-byte layout), origins,
%% and one access-check origin per check kind.

origins(Name, NLowers, CheckKinds) -->
    { format(atom(NameLabel), '.L~w..name', [Name]) },
    [section(rodata), label(NameLabel), asciz(Name),
     section(data_rel_ro), p2align(4)],
    function_origin(Name, NameLabel, NLowers, c, 1),
    function_origin(Name, NameLabel, NLowers, n, 0),
    check_origins(CheckKinds, Name).

function_origin(Name, NameLabel, NLowers, Which, CanCatch) -->
    { format(atom(FOrigin), '.L~w..forigin_~w', [Name, Which]),
      origin(Name, Which, Origin) },
    [label(FOrigin),
     quad(NameLabel), quad(0),
     long(NLowers), zero(4),
     quad(0),
     byte([0, CanCatch, 0]), zero(1),
     long(0),
     label(Origin),
     quad(FOrigin), long(0), long(0)].

check_origins([], _) --> [].
check_origins([Kind|Kinds], Name) -->
    { Kind = k(Size, Write, Align),
      check_origin(Name, Kind, Label),
      origin(Name, n, Origin) },
    [p2align(4), label(Label),
     long(Size), byte([Align, 0, Write]), zero(1),
     quad(Origin), quad(Origin), quad(0)],
    check_origins(Kinds, Name).
