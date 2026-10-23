/*  Naive x86-64 SysV backend for the phase-one IR (milestone 2).

    Every temporary lives in its own 8-byte frame slot below %rbp, and
    every instruction loads its operands into fixed scratch registers
    (%rax, %rcx, %rdx), computes, and stores %rax back. A w result is
    always zero-extended into %rax, so slots are uniformly 8 bytes and a
    w read is simply the low 4 bytes of the slot.

    Phis are lowered on each incoming edge as a parallel copy through
    per-phi shadow slots. jnz gets an edge block for its false side so
    each edge carries its own copies. alloc moves %rsp down by the size
    rounded up to 16, which keeps calls aligned.

    The output is a list of asm.pl lines (instruction and directive
    terms), which asm:print_asm/1 prints as GNU as text. This backend is
    the reference the later isel and register allocation milestones are
    checked against, so it favours being obviously right over being fast.
*/
:- module(amd64, [module_asm/2, op//4, load//4, load_slot//4,
                  store_reg//3, store_insn/3, reg/3, load_insn/3, sfx/2]).

:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).

% module_asm(+Module, -Lines): the module as asm.pl lines.
module_asm(module(Items), Lines) :-
    maplist(item_lines, Items, Liness),
    append(Liness, Lines0),
    append(Lines0, [section(note_gnu_stack)], Lines).

item_lines(Item, Lines) :-
    (   phrase(item(Item), Lines) -> true
    ;   arg(1, Item, Name),
        format(atom(Msg), 'backend cannot emit $~w', [Name]),
        throw(nanofil_error(Msg))
    ).

%% Functions

/* The context of a function's code is f(Name, Ret, Slots, Blocks).
   filc_amd64 builds the same term to call the exported nonterminals,
   so its shape is shared. */
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
    store_params(Params, 0, Ctx),
    blocks(Blocks, Ctx),
    [size(Name)].
item(data(Name, Linkage0, Align, Items)) -->
    {   Linkage0 = ro(Linkage) -> Section = rodata
    ;   Linkage = Linkage0, Section = data
    },
    [section(Section), balign(Align)],
    global(Linkage, Name),
    [label(Name)],
    data_items(Items).

global(export, Name) --> [globl(Name)].
global(local, _) --> [].

/* frame(+Params, +Blocks, -Slots, -Size): one slot per temporary name and
   one shadow slot per phi destination. Slots maps a key, t(N) or
   shadow(N), to its offset below %rbp. */
frame(Params, Blocks, Slots, Size) :-
    findall(t(N),
            (   member(par(_, t(N)), Params)
            ;   member(blk(_, Phis, Insts, _), Blocks),
                (   member(phi(t(N), _, _), Phis)
                ;   member(Inst, Insts),
                    defines(Inst, N)
                )
            ),
            Temps0),
    findall(shadow(N),
            ( member(blk(_, Phis, _, _), Blocks),
              member(phi(t(N), _, _), Phis) ),
            Shadows0),
    sort(Temps0, Temps),
    sort(Shadows0, Shadows),
    append(Temps, Shadows, Keys),
    empty_assoc(Slots0),
    foldl(assign_slot, Keys, Slots0-0, Slots-Count),
    Size is (Count * 8 + 15) // 16 * 16.

defines(ins(t(N), _, _, _), N).
defines(call(to(t(N), _), _, _), N).

% The next 8-byte slot below %rbp, counting slots in Count.
assign_slot(Key, Slots0-Count0, Slots-Count) :-
    Count is Count0 + 1,
    Offset is Count * 8,
    put_assoc(Key, Slots0, Offset, Slots).

% Spill the incoming argument registers to the parameters' slots.
store_params([], _, _) --> [].
store_params([par(_, Temp)|Params], I, Ctx) -->
    (   { arg_reg(I, Reg) } -> []
    ;   { Ctx = f(Fn, _, _, _),
          format(atom(Msg), 'in $~w: more than six parameters', [Fn]),
          throw(nanofil_error(Msg)) }
    ),
    { reg(Reg, l, RegName) },
    store_reg(RegName, Temp, Ctx),
    { I1 is I + 1 },
    store_params(Params, I1, Ctx).

% The SysV integer argument registers, in order.
arg_reg(0, di). arg_reg(1, si). arg_reg(2, d).
arg_reg(3, c).  arg_reg(4, r8). arg_reg(5, r9).

% reg(Reg, Width, Name): Width is a store width b, h or a class w, l.
reg(a, b, al).    reg(a, h, ax).    reg(a, w, eax).   reg(a, l, rax).
reg(c, b, cl).    reg(c, h, cx).    reg(c, w, ecx).   reg(c, l, rcx).
reg(d, b, dl).    reg(d, h, dx).    reg(d, w, edx).   reg(d, l, rdx).
reg(si, w, esi).  reg(si, l, rsi).
reg(di, w, edi).  reg(di, l, rdi).
reg(r8, w, r8d).  reg(r8, l, r8).
reg(r9, w, r9d).  reg(r9, l, r9).

% sfx(Width, Suffix): the AT&T suffix for a store width or class.
sfx(b, b). sfx(h, w). sfx(w, l). sfx(l, q).

%% Blocks and jumps

blocks([], _) --> [].
blocks([blk(Label, _, Insts, Jump)|Blocks], Ctx) -->
    { block_label(Ctx, Label, AsmLabel) },
    [label(AsmLabel)],
    insts(Insts, Ctx),
    jump(Jump, Label, Ctx),
    blocks(Blocks, Ctx).

block_label(f(Fn, _, _, _), Label, AsmLabel) :-
    format(atom(AsmLabel), '.L~w.~w', [Fn, Label]).

% The edge block for the false side of a jnz ending block Label.
false_label(f(Fn, _, _, _), Label, AsmLabel) :-
    format(atom(AsmLabel), '.L~w.~w.false', [Fn, Label]).

jump(jmp(To), From, Ctx) --> edge(From, To, Ctx).
jump(jnz(V, IfTrue, IfFalse), From, Ctx) -->
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
    epilogue.
jump(ret, _, _) --> epilogue.
jump(hlt, _, _) --> [ins(ud2, none, [])].

epilogue --> [ins(leave, none, []), ins(ret, none, [])].

% The copies for the phis of To on the edge From -> To, then the jump.
% All sources are read before any destination is written.
edge(From, To, Ctx) -->
    { Ctx = f(_, _, _, Blocks),
      memberchk(blk(To, Phis, _, _), Blocks),
      block_label(Ctx, To, ToLabel) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    [ins(jmp, none, [sym(ToLabel)])].

% Each phi's incoming value from From into its shadow slot.
phi_reads([], _, _) --> [].
phi_reads([phi(t(D), Class, Incoming)|Phis], From, Ctx) -->
    { memberchk(From-V, Incoming) },
    load(V, Class, a, Ctx),
    store_reg(rax, shadow(D), Ctx),
    phi_reads(Phis, From, Ctx).

% Each phi's shadow slot into its destination's slot.
phi_writes([], _) --> [].
phi_writes([phi(t(D), _, _)|Phis], Ctx) -->
    load_slot(shadow(D), l, rax, Ctx),
    store_reg(rax, t(D), Ctx),
    phi_writes(Phis, Ctx).

%% Instructions

insts([], _) --> [].
insts([Inst|Insts], Ctx) --> inst(Inst, Ctx), insts(Insts, Ctx).

inst(ins(D, Class, Op, Args), Ctx) -->
    op(Op, Class, Args, Ctx),
    store_reg(rax, D, Ctx).
inst(store(Width, V, Addr), Ctx) -->
    { Width == l -> Class = l ; Class = w },
    load(V, Class, c, Ctx),
    load(Addr, l, a, Ctx),
    { store_insn(Width, c, Store) },
    [Store].
inst(call(Res, glo(F), Args), Ctx) -->
    { length(Args, N),
      (   N =< 6 -> true
      ;   Ctx = f(Fn, _, _, _),
          format(atom(Msg), 'in $~w: call with more than six arguments',
                 [Fn]),
          throw(nanofil_error(Msg))
      ) },
    call_args(Args, 0, Ctx),
    [ins(call, none, [sym(F)])],
    (   { Res = to(D, _) } -> store_reg(rax, D, Ctx) ; [] ).

call_args([], _, _) --> [].
call_args([arg(Class, V)|Args], I, Ctx) -->
    { arg_reg(I, Reg),
      I1 is I + 1 },
    load(V, Class, Reg, Ctx),
    call_args(Args, I1, Ctx).

% store_insn(Width, Reg, Ins): store Width bytes of Reg to (%rax).
store_insn(W, R, ins(mov, S, [reg(RN), mem(0, rax)])) :-
    sfx(W, S),
    reg(R, W, RN).

% op(Op, Class, Args, Ctx): compute the result into %rax (zero-extended
% for class w).
op(copy, K, [X], Ctx) --> load(X, K, a, Ctx).
op(neg, K, [X], Ctx) -->
    load(X, K, a, Ctx),
    { sfx(K, S), reg(a, K, A) },
    [ins(neg, S, [reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { alu_insn(Op, Insn) }, !,
    load(X, K, a, Ctx),
    load(Y, K, c, Ctx),
    { sfx(K, S), reg(a, K, A), reg(c, K, C) },
    [ins(Insn, S, [reg(C), reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { shift_insn(Op, Insn) }, !,
    load(X, K, a, Ctx),
    load(Y, w, c, Ctx),
    { sfx(K, S), reg(a, K, A) },
    [ins(Insn, S, [reg(cl), reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { division(Op, Signedness, Result) }, !,
    load(X, K, a, Ctx),
    load(Y, K, c, Ctx),
    { sfx(K, S), reg(c, K, C) },
    (   { Signedness == signed }
    ->  { K == w -> SignExtend = cltd ; SignExtend = cqto },
        [ins(SignExtend, none, []), ins(idiv, S, [reg(C)])]
    ;   [ins(xor, l, [reg(edx), reg(edx)]), ins(div, S, [reg(C)])]
    ),
    (   { Result == rem }
    ->  { reg(d, K, D), reg(a, K, A) },
        [ins(mov, S, [reg(D), reg(A)])]
    ;   []
    ).
op(cmp(Cond, CmpClass), _, [X, Y], Ctx) -->
    load(X, CmpClass, a, Ctx),
    load(Y, CmpClass, c, Ctx),
    { sfx(CmpClass, S),
      reg(a, CmpClass, A),
      reg(c, CmpClass, C),
      cond_code(Cond, CC),
      atom_concat(set, CC, Set) },
    [ins(cmp, S, [reg(C), reg(A)]),
     ins(Set, none, [reg(al)]),
     ins(movzb, l, [reg(al), reg(eax)])].
op(ext(Type), K, [X], Ctx) -->
    load(X, w, a, Ctx),
    { ext_insn(Type, K, Insn) },
    [Insn].
op(load(Type), K, [Addr], Ctx) -->
    load(Addr, l, a, Ctx),
    { load_insn(Type, K, Insn) },
    [Insn].
op(alloc(_), _, [Size], Ctx) -->
    load(Size, l, a, Ctx),
    [ins(add, q, [imm(15), reg(rax)]),
     ins(and, q, [imm(-16), reg(rax)]),
     ins(sub, q, [reg(rax), reg(rsp)]),
     ins(mov, q, [reg(rsp), reg(rax)])].

alu_insn(add, add). alu_insn(sub, sub). alu_insn(mul, imul).
alu_insn(and, and). alu_insn(or, or).   alu_insn(xor, xor).

% x86 masks the count in %cl to the operand width, as the IR specifies.
shift_insn(shl, shl). shift_insn(shr, shr). shift_insn(sar, sar).

% division(Op, Signedness, Result): Result is the quotient or remainder.
division(div, signed, quot).    division(rem, signed, rem).
division(udiv, unsigned, quot). division(urem, unsigned, rem).

% cond_code(Cond, CC): the x86 condition code suffix for a comparison.
cond_code(eq, e).  cond_code(ne, ne).
cond_code(slt, l). cond_code(sle, le). cond_code(sgt, g).  cond_code(sge, ge).
cond_code(ult, b). cond_code(ule, be). cond_code(ugt, a).  cond_code(uge, ae).

% ext_insn(Type, Class, Ins): extend the low part of %rax into %rax.
ext_insn(Type, K, ins(Op, S, [reg(From), reg(To)])) :-
    ext_op(Type, K, Op, S, To),
    ext_from(Type, From).

% ext_op(Type, Class, Op, Suffix, To): the extending move and its
% destination register.
ext_op(sb, w, movsb, l, eax). ext_op(sb, l, movsb, q, rax).
ext_op(ub, _, movzb, l, eax).
ext_op(sh, w, movsw, l, eax). ext_op(sh, l, movsw, q, rax).
ext_op(uh, _, movzw, l, eax).
ext_op(sw, l, movsl, q, rax).
ext_op(uw, l, mov, l, eax).

% ext_from(Type, From): the part of %rax that Type extends.
ext_from(sb, al). ext_from(ub, al). ext_from(sh, ax). ext_from(uh, ax).
ext_from(sw, eax). ext_from(uw, eax).

% load_insn(Type, Class, Ins): load from (%rax) into %rax, extended.
load_insn(Type, K, ins(Op, S, [mem(0, rax), reg(To)])) :-
    load_op(Type, K, Op, S, To).

load_op(l, l, mov, q, rax).
load_op(sw, w, mov, l, eax).
load_op(uw, _, mov, l, eax).
load_op(Type, K, Op, S, To) :- Type \== uw, ext_op(Type, K, Op, S, To).

%% Operands

% load(Value, Class, Reg, Ctx): put Value, read at Class, in register Reg.
load(t(N), K, R, Ctx) -->
    { reg(R, K, RN) },
    load_slot(t(N), K, RN, Ctx).
load(c(N), w, R, _) -->
    { reg(R, w, RN),
      V is N mod 4294967296 },
    [ins(mov, l, [imm(V), reg(RN)])].
load(c(N), l, R, _) -->
    { reg(R, l, RN),
      U is N mod 18446744073709551616,
      (   U >= 9223372036854775808 -> V is U - 18446744073709551616
      ;   V = U
      ) },
    [ins(movabs, q, [imm(V), reg(RN)])].
load(glo(G), _, R, _) -->
    { reg(R, l, RN) },
    [ins(lea, q, [rip(G), reg(RN)])].

% load_slot(Key, Class, RegName, Ctx): read Key's frame slot at Class.
load_slot(Key, K, RN, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Offset),
      sfx(K, S),
      Disp is -Offset },
    [ins(mov, S, [mem(Disp, rbp), reg(RN)])].

% store_reg(RegName, Key, Ctx): write all 8 bytes of a register to Key's
% frame slot.
store_reg(RN, Key, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Offset),
      Disp is -Offset },
    [ins(mov, q, [reg(RN), mem(Disp, rbp)])].

%% Data

data_items([]) --> [].
data_items([Item|Items]) --> data_item(Item), data_items(Items).

data_item(zero(N)) --> [zero(N)].
data_item(item(b, str(Cs))) --> !, [ascii(Cs)].
data_item(item(l, sym(S, Off))) --> !, [quad(S+Off)].
data_item(item(W, c(N))) -->
    { data_directive(W, U, Directive, Bits),
      U is N mod (1 << Bits) },
    [Directive].

% data_directive(Width, Value, Directive, Bits)
data_directive(b, U, byte([U]), 8).
data_directive(h, U, short(U), 16).
data_directive(w, U, int(U), 32).
data_directive(l, U, quad(U), 64).
