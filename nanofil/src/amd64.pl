/*  The naive x86-64 SysV backend for the phase-one IR in plain
    (non-Fil-C) mode (milestone 2). It is the reference the later
    instruction selection and register allocation milestones are
    checked against, so it favours being obviously right over being
    fast.

    The output is a list of asm.pl lines, instruction and directive
    terms, which asm:print_asm/1 prints as GNU as text. Functions that
    call setjmp are refused.

    ## The frame

    Every temporary lives in its own 8-byte slot below %rbp, and each
    phi destination also has a shadow slot. `alloc` moves %rsp down by
    its size rounded up to 16, which keeps calls aligned.

    ```diagram
    ┌──────────────────────────┐ ← %rbp
    │ tmp(N) slots, 8 bytes    │   -8, -16, …
    │ shadow(N) slots, 8 bytes │
    │ padding to 16 bytes      │
    ├──────────────────────────┤ ← %rsp after the prologue
    │ alloc'd blocks, each a   │
    │ multiple of 16 bytes     │
    └──────────────────────────┘ ← %rsp
    ```

    ## Instructions

    Every instruction loads its operands into fixed scratch registers
    (%rax, %rcx, %rdx, %xmm0, %xmm1), computes, and stores %rax back to
    its destination's slot. A float computation moves the bits into
    the SSE2 scratch registers and its result back to %rax: slots hold
    bits, not floats. A `w` result is always zero-extended into %rax, so
    every slot is 8 bytes and a `w` read is the low 4 bytes of its slot.

    Phis are lowered on each incoming edge as a parallel copy: every
    incoming value goes into its phi's shadow slot, then every shadow
    into its phi. A `branch(V, IfTrue, IfFalse)` gets a labelled edge
    for its false side, so each edge carries its own copies.

    ## Variable conventions

    | Variable | Means |
    |---|---|
    | K | a class, `w`, `l`, `s` or `d`, or where stated a store width, `b`, `h`, `w`, `l`, `s` or `d` |
    | S | an AT&T suffix |
    | R | a register: `a`, `c`, `d`, `si`, `di`, `r8` or `r9` |
    | RN | the name of R at a width |
    | Ctx | the function context, `f(Name, Ret, Slots, Blocks)` |
*/
:- module(amd64, [module_asm/2, compute_op//4, compute_op//5, load//4, load_slot//4,
                  asm_fixed_inputs//2, asm_fixed_out_reg/2,
                  store_reg//3, store_insn/3, reg_name/3, load_insn/3, ext_insn/3,
                  cond_code/2, integer_immediate/3,
                  att_suffix/2, float_class/1,
                  to_xmm//3, from_xmm//3, bank_locations/5,
                  float_condition//1]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).

%! module_asm(+Module, -Lines) is det.
%
%  Lines are the asm.pl lines of the plain (non-Fil-C) Module. Throws a
%  nanofil_error naming the first item the backend cannot emit.
module_asm(Module, Lines) :-
    without_locs(Module, module(Items)),
    ( member(F, Items), setjmp_func(F)
    -> throw(nanofil_error('plain backend does not support setjmp/nonlocal returns'))
    ; true ),
    maplist(item_lines, Items, Liness),
    append(Liness, Lines0),
    append(Lines0, [section(note_gnu_stack)], Lines).

% item_lines(+Item, -Lines): Lines are the asm.pl lines of Item.
item_lines(Item, Lines) :-
    (   phrase(item(Item), Lines) -> true
    ;   arg(1, Item, Name),
        format(atom(Msg), 'backend cannot emit ~w', [Name]),
        throw(nanofil_error(Msg))
    ).

%% Functions

/* The context of a function's code is f(Name, Ret, Slots, Blocks).
   filc_amd64 builds the same term to call the exported nonterminals,
   so its shape is shared. */

% item(+Item)//: the lines of a function or data definition.
item(func(Name, Linkage, Ret, Params, Blocks)) -->
    { frame(Params, Blocks, Slots, Size),
      Ctx = f(Name, Ret, Slots, Blocks) },
    [section(text), p2align(4)],
    global(Linkage, Name),
    [type(Name, function),
     label(Name),
     ins(push, q, [reg(rbp)]),
     ins(mov, q, [reg(rsp), reg(rbp)])],
    (   { Size > 0 } -> [ins(sub, q, [imm(Size), reg(rsp)])] ; [] ),
    plain_params(Params, Ctx),
    blocks(Blocks, Ctx),
    [size(Name)].
item(data(Name, Linkage0, Align, Items)) -->
    { linkage_section(Linkage0, Linkage, Section) },
    [section(Section), balign(Align)],
    global(Linkage, Name),
    [label(Name)],
    data_items(Items).

% linkage_section(?Linkage0, ?Linkage, ?Section): data with linkage
% Linkage0 goes in Section with symbol linkage Linkage.
linkage_section(export, export, data).
linkage_section(local, local, data).
linkage_section(ro(Linkage), Linkage, rodata).

% global(+Linkage, +Name)//: the .globl directive an export needs.
global(export, Name) --> [globl(Name)].
global(local, _) --> [].

/* frame(+Params, +Blocks, -Slots, -Size): one slot per temporary name and
   one shadow slot per phi destination. Slots maps a key, tmp(N) or
   shadow(N), to its offset below %rbp. */
frame(Params, Blocks, Slots, Size) :-
    findall(tmp(N),
            (   member(param(_, tmp(N)), Params)
            ;   member(block(_, Phis, Insts, _), Blocks),
                (   member(phi(tmp(N), _, _), Phis)
                ;   member(Inst, Insts),
                    defines(Inst, N)
                )
            ),
            Temps0),
    findall(shadow(N),
            ( member(block(_, Phis, _, _), Blocks),
              member(phi(tmp(N), _, _), Phis) ),
            Shadows0),
    sort(Temps0, Temps),
    sort(Shadows0, Shadows),
    append(Temps, Shadows, Keys),
    empty_assoc(Slots0),
    foldl(assign_slot, Keys, Slots0-0, Slots-Count),
    Size is (Count * 8 + 15) // 16 * 16.

% defines(+Inst, -N): Inst writes temporary tmp(N).
defines(let(tmp(N), _, _, _), N).
defines(call(result(tmp(N), _), _, _), N).
defines(asm_fixed(_, _, Outs), N) :- member(_-tmp(N), Outs).

% The next 8-byte slot below %rbp, counting slots in Count.
assign_slot(Key, Slots0-Count0, Slots-Count) :-
    Count is Count0 + 1,
    Offset is Count * 8,
    put_assoc(Key, Slots0, Offset, Slots).

% Float arguments use an independent bank, with source-ordered stack
% overflow. Keep the integer-only emission unchanged.
plain_params(Params, Ctx) -->
    (   { member(param(F,_), Params), float_class(F) }
    ->  { findall(K, member(param(K,_), Params), Ks),
          bank_locations(Ks, [di,si,d,c,r8,r9], Locs, _, _) },
        plain_incoming(Params, Locs, Ctx)
    ;   store_params(Params, 0, Ctx)
    ).

plain_incoming([], [], _) --> [].
plain_incoming([param(K, T)|Ps], [L|Ls], Ctx) -->
    plain_incoming_value(L, K), store_reg(rax, T, Ctx),
    plain_incoming(Ps, Ls, Ctx).
plain_incoming_value(reg(R), _) -->
    { reg_name(R, l, RN) }, [ins(mov, q, [reg(RN), reg(rax)])].
plain_incoming_value(xreg(X), K) --> from_xmm(K, X, a).
plain_incoming_value(stack(I), _) -->
    { Off is 16 + 8 * I }, [ins(mov, q, [mem(Off, rbp), reg(rax)])].

% store_params(+Params, +I, +Ctx)//: spill the incoming argument
% registers, from the I-th on, to the slots of Params.
store_params([], _, _) --> [].
store_params([param(_, Temp)|Params], I, Ctx) -->
    (   { arg_reg(I, Reg) } -> []
    ;   { Ctx = f(Fn, _, _, _),
          format(atom(Msg), 'in ~w: more than six parameters', [Fn]),
          throw(nanofil_error(Msg)) }
    ),
    { reg_name(Reg, l, RegName) },
    store_reg(RegName, Temp, Ctx),
    { I1 is I + 1 },
    store_params(Params, I1, Ctx).

% arg_reg(?I, ?Reg): Reg is the I-th (from 0) SysV integer argument
% register.
arg_reg(0, di). arg_reg(1, si). arg_reg(2, d).
arg_reg(3, c).  arg_reg(4, r8). arg_reg(5, r9).

%! reg_name(+Reg, +Width, -Name) is semidet.
%
%  Name is the name of register Reg at Width, a store width b, h or a
%  class w, l. Only a, c and d have byte and halfword names.
reg_name(a, b, al).    reg_name(a, h, ax).
reg_name(a, w, eax).   reg_name(a, l, rax).
reg_name(c, b, cl).    reg_name(c, h, cx).
reg_name(c, w, ecx).   reg_name(c, l, rcx).
reg_name(d, b, dl).    reg_name(d, h, dx).
reg_name(d, w, edx).   reg_name(d, l, rdx).
reg_name(si, w, esi).  reg_name(si, l, rsi).
reg_name(di, w, edi).  reg_name(di, l, rdi).
reg_name(r8, w, r8d).  reg_name(r8, l, r8).
reg_name(r9, w, r9d).  reg_name(r9, l, r9).
reg_name(R, s, RN) :- reg_name(R, w, RN).
reg_name(R, d, RN) :- reg_name(R, l, RN).

%! att_suffix(+Width, -Suffix) is semidet.
%
%  Suffix is the AT&T suffix for a store width or class Width.
att_suffix(b, b). att_suffix(h, w). att_suffix(w, l). att_suffix(l, q).
att_suffix(s, l). att_suffix(d, q).

%% Blocks and jumps

% blocks(+Blocks, +Ctx)//: each block's label, instructions and jump.
blocks([], _) --> [].
blocks([block(Label, _, Insts, Jump)|Blocks], Ctx) -->
    { block_label(Ctx, Label, AsmLabel) },
    [label(AsmLabel)],
    insts(Insts, Ctx),
    jump(Jump, Label, Ctx),
    blocks(Blocks, Ctx).

% block_label(+Ctx, +Label, -AsmLabel): AsmLabel is the local assembly
% label of block Label.
block_label(f(Fn, _, _, _), Label, AsmLabel) :-
    format(atom(AsmLabel), '.L~w.~w', [Fn, Label]).

% false_label(+Ctx, +Label, -AsmLabel): AsmLabel labels the edge block
% for the false side of the jnz ending block Label.
false_label(f(Fn, _, _, _), Label, AsmLabel) :-
    format(atom(AsmLabel), '.L~w.~w.false', [Fn, Label]).

% jump(+Jump, +From, +Ctx)//: the code for the jump ending block From.
jump(goto(To), From, Ctx) --> edge(From, To, Ctx).
jump(branch(V, IfTrue, IfFalse), From, Ctx) -->
    { false_label(Ctx, From, FalseLabel) },
    load(V, w, a, Ctx),
    [ins(test, l, [reg(eax), reg(eax)]),
     ins(jz, none, [sym(FalseLabel)])],
    edge(From, IfTrue, Ctx),
    [label(FalseLabel)],
    edge(From, IfFalse, Ctx).
jump(ret(V), _, Ctx) -->
    { Ctx = f(_, Class, _, _) },
    load(V, Class, a, Ctx),
    ( { float_class(Class) } -> to_xmm(Class,a,xmm0) ; [] ),
    epilogue.
jump(ret, _, _) --> epilogue.
jump(unreachable, _, _) --> [ins(ud2, none, [])].

epilogue --> [ins(leave, none, []), ins(ret, none, [])].

% edge(+From, +To, +Ctx)//: the copies for the phis of To on the edge
% From -> To, then the jump. All sources are read before any
% destination is written.
edge(From, To, Ctx) -->
    { Ctx = f(_, _, _, Blocks),
      memberchk(block(To, Phis, _, _), Blocks),
      block_label(Ctx, To, ToLabel) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    [ins(jmp, none, [sym(ToLabel)])].

% phi_reads(+Phis, +From, +Ctx)//: copy each phi's incoming value from
% From into its shadow slot.
phi_reads([], _, _) --> [].
phi_reads([phi(tmp(D), Class, Incoming)|Phis], From, Ctx) -->
    { memberchk(From-V, Incoming) },
    load(V, Class, a, Ctx),
    store_reg(rax, shadow(D), Ctx),
    phi_reads(Phis, From, Ctx).

% phi_writes(+Phis, +Ctx)//: copy each phi's shadow slot into its
% destination's slot.
phi_writes([], _) --> [].
phi_writes([phi(tmp(D), _, _)|Phis], Ctx) -->
    load_slot(shadow(D), l, rax, Ctx),
    store_reg(rax, tmp(D), Ctx),
    phi_writes(Phis, Ctx).

%% Instructions

insts([], _) --> [].
insts([Inst|Insts], Ctx) -->
    inst(Inst, Ctx),
    insts(Insts, Ctx).

% inst(+Inst, +Ctx)//: the code for one instruction.
inst(let(D, Class, Op, Args), Ctx) -->
    compute_op(Op, Class, Args, Ctx),
    store_reg(rax, D, Ctx).
inst(fence, _) --> [ins(mfence, none, [])].
% In plain mode C's semantics are the chunks' (docs/vector-access.md).
inst(access(_, _, _, _), _) --> [].
inst(asm_fixed(M, Ins, Outs), Ctx) -->
    asm_fixed_inputs(Ins, Ctx),
    [asm_fixed(M)],
    asm_fixed_outputs(Outs, Ctx).

inst(store(Width, V, Addr), Ctx) -->
    { width_class(Width, Class) },
    load(V, Class, c, Ctx),
    load(Addr, l, a, Ctx),
    { store_insn(Width, c, Store) },
    [Store].
inst(call(Res, global(F), Args), Ctx) -->
    { member(arg(FK,_),Args), float_class(FK) }, !,
    { findall(K,member(arg(K,_),Args),Ks),
      bank_locations(Ks,[di,si,d,c,r8,r9],Ls,NS,NX),
      Pop is ((NS+1)//2)*16 },
    ( { Pop > 0 } -> [ins(sub,q,[imm(Pop),reg(rsp)])] ; [] ),
    plain_stack_args(Args,Ls,Ctx), plain_register_args(Args,Ls,Ctx),
    [ins(mov,b,[imm(NX),reg(al)]),ins(call,none,[sym(F)])],
    ( { Pop > 0 } -> [ins(add,q,[imm(Pop),reg(rsp)])] ; [] ),
    call_result(Res,Ctx).
inst(call(Res, global(F), Args), Ctx) -->
    { length(Args, N),
      (   N =< 6 -> true
      ;   Ctx = f(Fn, _, _, _),
          format(atom(Msg), 'in ~w: call with more than six arguments',
                 [Fn]),
          throw(nanofil_error(Msg))
      ) },
    call_args(Args, 0, Ctx),
    [ins(call, none, [sym(F)])],
    call_result(Res, Ctx).

% width_class(?Width, ?Class): a store of Width reads its value at Class.
width_class(b, w).
width_class(h, w).
width_class(w, w).
width_class(l, l).
width_class(s, s).
width_class(d, d).

% call_result(+Res, +Ctx)//: the store of a call's result Res from %rax;
% nothing for void, and the plain backend has no tuple results.
call_result(void, _) --> [].
call_result(result(D, K), Ctx) -->
    { float_class(K) }, !, from_xmm(K,xmm0,a), store_reg(rax,D,Ctx).
call_result(result(D, _), Ctx) --> store_reg(rax, D, Ctx).
call_result(tuple(_), _) --> [].

% call_args(+Args, +I, +Ctx)//: load each argument, from the I-th on,
% into its argument register.
call_args([], _, _) --> [].
call_args([arg(Class, V)|Args], I, Ctx) -->
    { arg_reg(I, Reg),
      I1 is I + 1 },
    load(V, Class, Reg, Ctx),
    call_args(Args, I1, Ctx).

%! store_insn(+Width, +Reg, -Ins) is semidet.
%
%  Ins stores the Width-sized part of register Reg to (%rax).
store_insn(W, R, ins(mov, S, [reg(RN), mem(0, rax)])) :-
    att_suffix(W, S),
    reg_name(R, W, RN).

% Local Fil-C selection can encode an integer RHS directly. The reference
% selector below stays unchanged. Only RCX's dead scratch result differs;
% RAX and the operation's defined flags agree, even for a zero shift.
compute_op(local, Op, K, [X,const(N)], Ctx) -->
    { integer(N), immediate_instruction(Op,K,N,Insn) }, !,
    load(X, K, a, Ctx), [Insn].
compute_op(_, Op, K, Args, Ctx) --> compute_op(Op, K, Args, Ctx).

immediate_instruction(Op,K,N,ins(Insn,S,[imm(V),reg(A)])) :-
    ( Op == mul -> Insn = imul
    ; memberchk(Op,[add,sub,and,or,xor]), Insn = Op ),
    integer_immediate(K,N,V), att_suffix(K,S), reg_name(a,K,A).
immediate_instruction(Op,K,N,ins(Op,S,[imm(V),reg(A)])) :-
    memberchk(Op,[shl,shr,sar]),
    ( K == w -> Mask = 31 ; K == l, Mask = 63 ),
    V is N /\ Mask, att_suffix(K,S), reg_name(a,K,A).

% GNU as accepts the signed spelling of every imm32 bit pattern. Qword
% operations sign-extend that encoding: e.g. +0xffffffff is NOT -1.
integer_immediate(w,N,V) :- V is (N + 2147483648) mod 4294967296 - 2147483648.
integer_immediate(l,N,V) :-
    U is N mod 18446744073709551616,
    ( U >= 9223372036854775808 -> V is U - 18446744073709551616
    ; V = U ),
    V >= -2147483648, V =< 2147483647.

%! compute_op(+Op, +Class, +Args, +Ctx)//
%
%  The code that computes Op at Class on Args into %rax, zero-extended
%  for class w. Ctx is the f/4 context; filc_amd64 also calls this for
%  its integer instructions.
compute_op(Op, K, Args, Ctx) -->
    { float_compute(Op, K) }, !,
    float_op(Op, K, Args, Ctx).
compute_op(copy, K, [X], Ctx) --> load(X, K, a, Ctx).
compute_op(neg, K, [X], Ctx) -->
    load(X, K, a, Ctx),
    { att_suffix(K, S),
      reg_name(a, K, A) },
    [ins(neg, S, [reg(A)])].
compute_op(add, K, Args, Ctx) --> alu(add, K, Args, Ctx).
compute_op(sub, K, Args, Ctx) --> alu(sub, K, Args, Ctx).
compute_op(mul, K, Args, Ctx) --> alu(imul, K, Args, Ctx).
compute_op(and, K, Args, Ctx) --> alu(and, K, Args, Ctx).
compute_op(or, K, Args, Ctx) --> alu(or, K, Args, Ctx).
compute_op(xor, K, Args, Ctx) --> alu(xor, K, Args, Ctx).
% x86 masks the count in %cl to the operand width, as the IR specifies.
compute_op(shl, K, Args, Ctx) --> shift(shl, K, Args, Ctx).
compute_op(shr, K, Args, Ctx) --> shift(shr, K, Args, Ctx).
compute_op(sar, K, Args, Ctx) --> shift(sar, K, Args, Ctx).
compute_op(div, K, Args, Ctx) --> division(signed, quot, K, Args, Ctx).
compute_op(rem, K, Args, Ctx) --> division(signed, rem, K, Args, Ctx).
compute_op(udiv, K, Args, Ctx) --> division(unsigned, quot, K, Args, Ctx).
compute_op(urem, K, Args, Ctx) --> division(unsigned, rem, K, Args, Ctx).
compute_op(cmp(Cond, CmpClass), _, [X, Y], Ctx) -->
    load(X, CmpClass, a, Ctx),
    load(Y, CmpClass, c, Ctx),
    { att_suffix(CmpClass, S),
      reg_name(a, CmpClass, A),
      reg_name(c, CmpClass, C),
      cond_code(Cond, CC),
      atom_concat(set, CC, Set) },
    [ins(cmp, S, [reg(C), reg(A)]),
     ins(Set, none, [reg(al)]),
     ins(movzb, l, [reg(al), reg(eax)])].
compute_op(ext(Type), K, [X], Ctx) -->
    load(X, w, a, Ctx),
    { ext_insn(Type, K, Insn) },
    [Insn].
compute_op(load(Type), K, [Addr], Ctx) -->
    load(Addr, l, a, Ctx),
    { load_insn(Type, K, Insn) },
    [Insn].
compute_op(alloc(Align), _, [Size], Ctx) -->
    load(Size, l, a, Ctx),
    [ins(add, q, [imm(15), reg(rax)]),
     ins(and, q, [imm(-16), reg(rax)]),
     ins(sub, q, [reg(rax), reg(rsp)])],
    (   { Align > 16 }
    ->  { Mask is -Align }, [ins(and, q, [imm(Mask), reg(rsp)])]
    ;   []
    ),
    [ins(mov, q, [reg(rsp), reg(rax)])].

% alu(+Insn, +K, +Args, +Ctx)//: the x86 two-operand instruction Insn
% on Args.
alu(Insn, K, [X, Y], Ctx) -->
    load(X, K, a, Ctx),
    load(Y, K, c, Ctx),
    { att_suffix(K, S),
      reg_name(a, K, A),
      reg_name(c, K, C) },
    [ins(Insn, S, [reg(C), reg(A)])].

% shift(+Insn, +K, +Args, +Ctx)//: the x86 shift Insn of the first of
% Args by the second, a w count in %cl.
shift(Insn, K, [X, Y], Ctx) -->
    load(X, K, a, Ctx),
    load(Y, w, c, Ctx),
    { att_suffix(K, S),
      reg_name(a, K, A) },
    [ins(Insn, S, [reg(cl), reg(A)])].

% division(+Signedness, +Result, +K, +Args, +Ctx)//: the division of
% that Signedness of the first of Args by the second, leaving in %rax
% its Result, the quotient (quot) or remainder (rem).
division(Signedness, Result, K, [X, Y], Ctx) -->
    load(X, K, a, Ctx),
    load(Y, K, c, Ctx),
    { att_suffix(K, S),
      reg_name(c, K, C) },
    divide(Signedness, K, S, C),
    division_result(Result, K, S).

% divide(+Signedness, +K, +S, +C)//: %rdx:%rax (or %edx:%eax) divided
% by register C, extended from %rax by Signedness.
divide(signed, K, S, C) -->
    { sign_extension(K, SignExtend) },
    [ins(SignExtend, none, []), ins(idiv, S, [reg(C)])].
divide(unsigned, _, S, C) -->
    [ins(xor, l, [reg(edx), reg(edx)]), ins(div, S, [reg(C)])].

% sign_extension(?K, ?Insn): Insn sign-extends %eax or %rax at K into
% %edx or %rdx.
sign_extension(w, cltd).
sign_extension(l, cqto).

% division_result(+Result, +K, +S)//: the move of the remainder from
% %rdx to %rax; the quotient is already there.
division_result(quot, _, _) --> [].
division_result(rem, K, S) -->
    { reg_name(d, K, D),
      reg_name(a, K, A) },
    [ins(mov, S, [reg(D), reg(A)])].

% cond_code(?Cond, ?CC): CC is the x86 condition code suffix for the
% comparison Cond.
cond_code(eq, e).  cond_code(ne, ne).
cond_code(slt, l). cond_code(sle, le).
cond_code(sgt, g). cond_code(sge, ge).
cond_code(ult, b). cond_code(ule, be).
cond_code(ugt, a). cond_code(uge, ae).

% ext_insn(+Type, +Class, -Ins): Ins extends the low part of %rax that
% Type names into %rax at Class.
ext_insn(Type, K, ins(Op, S, [reg(From), reg(To)])) :-
    ext_op(Type, K, Op, S, To),
    ext_from(Type, From).

% ext_op(?Type, ?Class, ?Op, ?Suffix, ?To): Op with Suffix is the move
% that extends Type to Class, and To its destination register.
ext_op(sb, w, movsb, l, eax). ext_op(sb, l, movsb, q, rax).
ext_op(ub, _, movzb, l, eax).
ext_op(sh, w, movsw, l, eax). ext_op(sh, l, movsw, q, rax).
ext_op(uh, _, movzw, l, eax).
ext_op(sw, l, movsl, q, rax).
ext_op(uw, l, mov, l, eax).

% ext_from(?Type, ?From): From is the part of %rax that Type extends.
ext_from(sb, al). ext_from(ub, al). ext_from(sh, ax). ext_from(uh, ax).
ext_from(sw, eax). ext_from(uw, eax).

%! load_insn(+Type, +Class, -Ins) is semidet.
%
%  Ins loads a Type value from (%rax) into %rax, extended to Class.
load_insn(Type, K, ins(Op, S, [mem(0, rax), reg(To)])) :-
    load_op(Type, K, Op, S, To).

% load_op(+Type, +Class, -Op, -Suffix, -To): as ext_op/5, for a load
% from memory; a uw load, or an sw load at w, needs only a 32-bit move.
load_op(l, l, mov, q, rax).
load_op(s, s, mov, l, eax).
load_op(d, d, mov, q, rax).
load_op(sw, K, Op, S, To) :- sw_load_op(K, Op, S, To).
load_op(uw, _, mov, l, eax).
load_op(sb, K, Op, S, To) :- ext_op(sb, K, Op, S, To).
load_op(ub, K, Op, S, To) :- ext_op(ub, K, Op, S, To).
load_op(sh, K, Op, S, To) :- ext_op(sh, K, Op, S, To).
load_op(uh, K, Op, S, To) :- ext_op(uh, K, Op, S, To).

sw_load_op(w, mov, l, eax).
sw_load_op(l, Op, S, To) :- ext_op(sw, l, Op, S, To).

%! asm_fixed_inputs(+Ins, +Frame)//
%
%  The moves of a fixed-register asm's w inputs (docs/asm-fixed.md) into
%  the registers it reads, eax and ecx; each move writes only its own.
asm_fixed_inputs([], _) --> [].
asm_fixed_inputs([R-V|Ins], F) --> load(V, w, R, F), asm_fixed_inputs(Ins, F).

% asm_fixed_out_reg(?R, ?Reg): the register holding result R after the
% asm line; cpuid's b comes out in rdi (asm.pl), its upper half zeroed.
asm_fixed_out_reg(a, rax). asm_fixed_out_reg(b, rdi).
asm_fixed_out_reg(c, rcx). asm_fixed_out_reg(d, rdx).

asm_fixed_outputs([], _) --> [].
asm_fixed_outputs([R-T|Outs], F) -->
    { asm_fixed_out_reg(R, Reg) }, store_reg(Reg, T, F), asm_fixed_outputs(Outs, F).

%% Operands

%! load(+Value, +Class, +Reg, +Ctx)//
%
%  The code that puts Value, read at Class, in register Reg.
load(tmp(N), K, R, Ctx) -->
    { reg_name(R, K, RN) },
    load_slot(tmp(N), K, RN, Ctx).
load(const(N), K, R, _) --> load_constant(K, N, R).
load(global(G), _, R, _) -->
    { reg_name(R, l, RN) },
    [ins(lea, q, [rip(G), reg(RN)])].

% load_constant(+Class, +N, +Reg)//: the move of the constant N, reduced
% modulo Class, into Reg.
load_constant(w, N, R) -->
    { reg_name(R, w, RN),
      V is N mod 4294967296 },
    [ins(mov, l, [imm(V), reg(RN)])].
load_constant(l, N, R) -->
    { reg_name(R, l, RN),
      U is N mod 18446744073709551616,
      (   U >= 9223372036854775808 -> V is U - 18446744073709551616
      ;   V = U
      ) },
    [ins(movabs, q, [imm(V), reg(RN)])].
load_constant(s, N, R) --> load_constant(w, N, R).
load_constant(d, N, R) --> load_constant(l, N, R).

%! load_slot(+Key, +Class, +RegName, +Ctx)// is semidet.
%
%  The move that reads Key's frame slot at Class into RegName. Fails if
%  Key has no slot in Ctx.
load_slot(Key, K, RN, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Offset),
      att_suffix(K, S),
      Disp is -Offset },
    [ins(mov, S, [mem(Disp, rbp), reg(RN)])].

%! store_reg(+RegName, +Key, +Ctx)// is semidet.
%
%  The move that writes all 8 bytes of register RegName to Key's frame
%  slot. Fails if Key has no slot in Ctx.
store_reg(RN, Key, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Offset),
      Disp is -Offset },
    [ins(mov, q, [reg(RN), mem(Disp, rbp)])].

%% Data

% data_items(+Items)//: the directives for the data items.
data_items([]) --> [].
data_items([Item|Items]) -->
    data_item(Item),
    data_items(Items).

data_item(zero(N)) --> [zero(N)].
data_item(item(W, Value)) --> item_value(Value, W).

% item_value(+Value, +W)//: the directive for a data item of width W and
% value Value.
item_value(str(Cs), b) --> [ascii(Cs)].
item_value(sym(S, Off), l) --> [quad(S+Off)].
item_value(const(N), W) -->
    { data_directive(W, U, Directive, Bits),
      U is N mod (1 << Bits) },
    [Directive].

% data_directive(?Width, ?Value, ?Directive, ?Bits): Directive emits
% the unsigned Value as one Width item of Bits bits.
data_directive(b, U, byte([U]), 8).
data_directive(h, U, short(U), 16).
data_directive(w, U, int(U), 32).
data_directive(l, U, quad(U), 64).
data_directive(s, U, int(U), 32).
data_directive(d, U, quad(U), 64).

%% SSE2. Private slots and compute_op's result hold bits, not host floats.
%% Only ABI boundaries use XMM registers as the persistent value carrier.
float_class(s). float_class(d).
float_bits(s, w). float_bits(d, l).
float_suffix(s, ss). float_suffix(d, sd).
xmm_reg(I, R) :- format(atom(R), 'xmm~d', [I]).

% Shared SysV bank allocation for a flattened scalar/flight-word list.
% Each exhausted bank spills independently; stack positions retain order.
bank_locations(Ks, Regs, Ls, NS, NX) :-
    bank_locations(Ks, Regs, 0, 0, Ls, NS, NX).
bank_locations([], _, X, S, [], S, X).
bank_locations([K|Ks], Rs, X0, S0, [L|Ls], S, X) :-
    ( float_class(K)
    -> ( X0 < 8 -> xmm_reg(X0,R), L=xreg(R), X1 is X0+1, S1=S0
       ; L=stack(S0), S1 is S0+1, X1=X0 ), Rs1=Rs
    ;  X1=X0,
       ( Rs=[R|Rs1] -> L=reg(R), S1=S0
       ; Rs1=[], L=stack(S0), S1 is S0+1 )
    ),
    bank_locations(Ks,Rs1,X1,S1,Ls,S,X).

plain_stack_args([], [], _) --> [].
plain_stack_args([arg(K,V)|As],[L|Ls],Ctx) -->
    ( { L=stack(I), Off is 8*I }
    -> load(V,K,a,Ctx), [ins(mov,q,[reg(rax),mem(Off,rsp)])]
    ; [] ), plain_stack_args(As,Ls,Ctx).
plain_register_args([], [], _) --> [].
plain_register_args([arg(K,V)|As],[L|Ls],Ctx) -->
    plain_register_arg(L,K,V,Ctx), plain_register_args(As,Ls,Ctx).
plain_register_arg(stack(_),_,_,_) --> [].
plain_register_arg(reg(R),K,V,Ctx) --> load(V,K,R,Ctx).
plain_register_arg(xreg(X),K,V,Ctx) --> float_load(V,K,X,Ctx).

to_xmm(K, R, X) -->
    { float_bits(K, B), reg_name(R, B, RN), xmm_move(K, Op) },
    [ins(Op, none, [reg(RN), reg(X)])].
from_xmm(K, X, R) -->
    { float_bits(K, B), reg_name(R, B, RN), xmm_move(K, Op) },
    [ins(Op, none, [reg(X), reg(RN)])].
xmm_move(s, movd). xmm_move(d, movq).

float_compute(Op, K) :- float_class(K), memberchk(Op, [add,sub,mul,div,neg]).
float_compute(cmp(_, K), _) :- float_class(K).
float_compute(ext(s), d).
float_compute(truncd, s).
float_compute(cast, _).
float_compute(Op, _) :- memberchk(Op, [stosi,stoui,dtosi,dtoui,swtof,uwtof,sltof,ultof]).

float_load(V, K, X, Ctx) --> load(V, K, a, Ctx), to_xmm(K, a, X).

float_op(Op, K, [X,Y], Ctx) -->
    { memberchk(Op, [add,sub,mul,div]), float_suffix(K, S) },
    float_load(X, K, xmm0, Ctx), float_load(Y, K, xmm1, Ctx),
    [ins(Op, S, [reg(xmm1),reg(xmm0)])], from_xmm(K, xmm0, a).
float_op(neg, K, [X], Ctx) -->
    load(X, K, a, Ctx),
    { float_bits(K, B), reg_name(a, B, A), att_suffix(B, S),
      ( K == s -> Mask = 2147483648 ; Mask = 9223372036854775808 ) },
    load(const(Mask), B, c, Ctx),
    { reg_name(c, B, C) },
    [ins(xor, S, [reg(C),reg(A)])].
float_op(cmp(Cond,K), w, [X,Y], Ctx) -->
    float_load(X, K, xmm0, Ctx), float_load(Y, K, xmm1, Ctx),
    { float_compare(K, Op) },
    [ins(Op, none, [reg(xmm1),reg(xmm0)])],
    float_condition(Cond),
    [ins(movzb, l, [reg(al),reg(eax)])].
float_op(ext(s), d, [X], Ctx) -->
    float_load(X, s, xmm0, Ctx),
    [ins(cvtss2sd, none, [reg(xmm0),reg(xmm0)])], from_xmm(d, xmm0, a).
float_op(truncd, s, [X], Ctx) -->
    float_load(X, d, xmm0, Ctx),
    [ins(cvtsd2ss, none, [reg(xmm0),reg(xmm0)])], from_xmm(s, xmm0, a).
float_op(cast, K, [X], Ctx) --> load(X, K, a, Ctx).
float_op(Op, K, [X], Ctx) -->
    { float_to_int(Op, F, Sign) },
    float_load(X, F, xmm0, Ctx), float_integer(Sign, F, K, Ctx).
float_op(Op, F, [X], Ctx) -->
    { int_to_float(Op, K, Sign) },
    load(X, K, a, Ctx), integer_float(Sign, K, F), from_xmm(F, xmm0, a).

float_compare(s, ucomiss). float_compare(d, ucomisd).
float_condition(eq) --> [ins(sete, none, [reg(al)]),ins(setnp, none, [reg(cl)]),ins(and,b,[reg(cl),reg(al)])].
float_condition(ne) --> [ins(setne, none, [reg(al)]),ins(setp, none, [reg(cl)]),ins(or,b,[reg(cl),reg(al)])].
float_condition(lt) --> [ins(setb, none, [reg(al)]),ins(setnp, none, [reg(cl)]),ins(and,b,[reg(cl),reg(al)])].
float_condition(le) --> [ins(setbe, none, [reg(al)]),ins(setnp, none, [reg(cl)]),ins(and,b,[reg(cl),reg(al)])].
float_condition(gt) --> [ins(seta, none, [reg(al)])].
float_condition(ge) --> [ins(setae, none, [reg(al)])].
float_condition(o) --> [ins(setnp, none, [reg(al)])].
float_condition(uo) --> [ins(setp, none, [reg(al)])].

float_to_int(stosi,s,signed). float_to_int(stoui,s,unsigned).
float_to_int(dtosi,d,signed). float_to_int(dtoui,d,unsigned).
int_to_float(swtof,w,signed). int_to_float(uwtof,w,unsigned).
int_to_float(sltof,l,signed). int_to_float(ultof,l,unsigned).

truncate_float(F, K) -->
    { float_suffix(F, S), atom_concat(cvtt, S, P), atom_concat(P, '2si', Op),
      att_suffix(K, W), reg_name(a, K, R) },
    [ins(Op,W,[reg(xmm0),reg(R)])].
float_integer(signed, F, K, _) --> truncate_float(F, K).
float_integer(unsigned, F, w, _) -->
    truncate_float(F, l), [ins(mov,l,[reg(eax),reg(eax)])].
% SSE2 has no unsigned qword conversion. Subtract 2^63 in the high
% half, convert the now signed-representable value, then restore bit 63.
% Numeric labels are local to each sequence, including repeated calls.
float_integer(unsigned, F, l, Ctx) -->
    { ( F == s -> Bits = 1593835520 ; Bits = 4890909195324358656 ),
      float_compare(F, Cmp), float_suffix(F,S) },
    float_load(const(Bits), F, xmm1, Ctx),
    [ins(Cmp,none,[reg(xmm1),reg(xmm0)]),ins(jb,none,[sym('1f')]),
     ins(sub,S,[reg(xmm1),reg(xmm0)])],
    truncate_float(F,l),
    [ins(btc,q,[imm(63),reg(rax)]),ins(jmp,none,[sym('2f')]),label('1')],
    truncate_float(F,l), [label('2')].

convert_integer(K, F) -->
    { float_suffix(F,S), atom_concat(cvtsi2,S,Op), att_suffix(K,W), reg_name(a,K,R) },
    [ins(Op,W,[reg(R),reg(xmm0)])].
integer_float(signed, K, F) --> convert_integer(K,F).
integer_float(unsigned, w, F) --> convert_integer(l,F).
% Preserve a sticky low bit before halving; converting then doubling is
% correctly rounded even above 2^63, unlike subtract/convert/add.
integer_float(unsigned, l, F) -->
    { float_suffix(F,S) },
    [ins(test,q,[reg(rax),reg(rax)]),ins(jns,none,[sym('1f')]),
     ins(mov,q,[reg(rax),reg(rcx)]),ins(and,l,[imm(1),reg(ecx)]),
     ins(shr,q,[imm(1),reg(rax)]),ins(or,q,[reg(rcx),reg(rax)])],
    convert_integer(l,F),
    [ins(add,S,[reg(xmm0),reg(xmm0)]),ins(jmp,none,[sym('2f')]),label('1')],
    convert_integer(l,F), [label('2')].
