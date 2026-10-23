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
    maplist(emit_item, Items, Ls),
    append(Ls, Lines0),
    append(Lines0, [section(note_gnu_stack)], Lines).

emit_item(I, Ls) :-
    (   phrase(item(I), Ls) -> true
    ;   arg(1, I, Name),
        format(atom(M), 'backend cannot emit $~w', [Name]),
        throw(nanofil_error(M))
    ).

%% Functions

item(func(Name, Lk, Ret, Params, Blocks)) -->
    { frame(Params, Blocks, Slots, Size),
      Ctx = f(Name, Ret, Slots, Blocks) },
    [section(text), p2align(4)],
    global(Lk, Name),
    [type(Name, function), label(Name),
     ins(push, q, [reg(rbp)]), ins(mov, q, [reg(rsp), reg(rbp)])],
    (   { Size > 0 } -> [ins(sub, q, [imm(Size), reg(rsp)])] ; [] ),
    params(Params, 0, Ctx),
    blocks(Blocks, Ctx),
    [size(Name)].
item(data(Name, Lk, Align, Items)) -->
    [section(data), balign(Align)],
    global(Lk, Name),
    [label(Name)],
    data_items(Items).

global(export, Name) --> [globl(Name)].
global(local, _) --> [].

/* frame(+Params, +Blocks, -Slots, -Size): one slot per temporary name and
   one shadow slot per phi destination. Slots maps a key, t(N) or
   shadow(N), to its offset below %rbp. */
frame(Params, Blocks, Slots, Size) :-
    findall(t(N), ( member(par(_, t(N)), Params)
                  ; member(blk(_, Phis, Insts, _), Blocks),
                    (   member(phi(t(N), _, _), Phis)
                    ;   member(I, Insts), defines(I, N)
                    ) ), Ts0),
    findall(shadow(N), ( member(blk(_, Phis, _, _), Blocks),
                         member(phi(t(N), _, _), Phis) ), Ss0),
    sort(Ts0, Ts), sort(Ss0, Ss),
    append(Ts, Ss, Keys),
    empty_assoc(E),
    foldl(slot, Keys, E-0, Slots-N),
    Size is (N * 8 + 15) // 16 * 16.

defines(ins(t(N), _, _, _), N).
defines(call(to(t(N), _), _, _), N).

slot(Key, A0-N0, A-N) :-
    N is N0 + 1,
    Off is N * 8,
    put_assoc(Key, A0, Off, A).

params([], _, _) --> [].
params([par(_, T)|Ps], I, Ctx) -->
    (   { arg_reg(I, R) } -> []
    ;   { Ctx = f(Fn, _, _, _),
          format(atom(M), 'in $~w: more than six parameters', [Fn]),
          throw(nanofil_error(M)) }
    ),
    { reg(R, l, RN) },
    store_reg(RN, T, Ctx),
    { I1 is I + 1 },
    params(Ps, I1, Ctx).

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
blocks([blk(L, _, Insts, J)|Bs], Ctx) -->
    { label(Ctx, L, A) },
    [label(A)],
    insts(Insts, Ctx),
    jump(J, L, Ctx),
    blocks(Bs, Ctx).

label(f(Fn, _, _, _), L, A) :- format(atom(A), '.L~w.~w', [Fn, L]).

false_label(f(Fn, _, _, _), L, A) :- format(atom(A), '.L~w.~w.false', [Fn, L]).

jump(jmp(T), From, Ctx) --> edge(From, T, Ctx).
jump(jnz(V, T, F), From, Ctx) -->
    { false_label(Ctx, From, FL) },
    load(V, w, a, Ctx),
    [ins(test, l, [reg(eax), reg(eax)]), ins(jz, none, [sym(FL)])],
    edge(From, T, Ctx),
    [label(FL)],
    edge(From, F, Ctx).
jump(ret(V), _, Ctx) --> { Ctx = f(_, K, _, _) }, load(V, K, a, Ctx), epilogue.
jump(ret, _, _) --> epilogue.
jump(hlt, _, _) --> [ins(ud2, none, [])].

epilogue --> [ins(leave, none, []), ins(ret, none, [])].

% The copies for the phis of To on the edge From -> To, then the jump.
% All sources are read before any destination is written.
edge(From, To, Ctx) -->
    { Ctx = f(_, _, _, Blocks),
      memberchk(blk(To, Phis, _, _), Blocks),
      label(Ctx, To, TL) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    [ins(jmp, none, [sym(TL)])].

phi_reads([], _, _) --> [].
phi_reads([phi(t(D), K, Pairs)|Ps], From, Ctx) -->
    { memberchk(From-V, Pairs) },
    load(V, K, a, Ctx),
    store_reg(rax, shadow(D), Ctx),
    phi_reads(Ps, From, Ctx).

phi_writes([], _) --> [].
phi_writes([phi(t(D), _, _)|Ps], Ctx) -->
    load_slot(shadow(D), l, rax, Ctx),
    store_reg(rax, t(D), Ctx),
    phi_writes(Ps, Ctx).

%% Instructions

insts([], _) --> [].
insts([I|Is], Ctx) --> inst(I, Ctx), insts(Is, Ctx).

inst(ins(D, K, Op, Args), Ctx) --> op(Op, K, Args, Ctx), store_reg(rax, D, Ctx).
inst(store(W, V, A), Ctx) -->
    { W == l -> VK = l ; VK = w },
    load(V, VK, c, Ctx),
    load(A, l, a, Ctx),
    { store_insn(W, c, S) },
    [S].
inst(call(Res, glo(F), Args), Ctx) -->
    { length(Args, N),
      (   N =< 6 -> true
      ;   Ctx = f(Fn, _, _, _),
          format(atom(M), 'in $~w: call with more than six arguments', [Fn]),
          throw(nanofil_error(M))
      ) },
    call_args(Args, 0, Ctx),
    [ins(call, none, [sym(F)])],
    (   { Res = to(D, _) } -> store_reg(rax, D, Ctx) ; [] ).

call_args([], _, _) --> [].
call_args([arg(K, V)|As], I, Ctx) -->
    { arg_reg(I, R), I1 is I + 1 },
    load(V, K, R, Ctx),
    call_args(As, I1, Ctx).

% store_insn(Width, Reg, Ins): store Width bytes of Reg to (%rax).
store_insn(W, R, ins(mov, S, [reg(RN), mem(0, rax)])) :- sfx(W, S), reg(R, W, RN).

% op(Op, Class, Args, Ctx): compute the result into %rax (zero-extended
% for class w).
op(copy, K, [X], Ctx) --> load(X, K, a, Ctx).
op(neg, K, [X], Ctx) --> load(X, K, a, Ctx), { sfx(K, S), reg(a, K, A) }, [ins(neg, S, [reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { alu_insn(Op, I) }, !,
    load(X, K, a, Ctx), load(Y, K, c, Ctx),
    { sfx(K, S), reg(a, K, A), reg(c, K, C) },
    [ins(I, S, [reg(C), reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { shift_insn(Op, I) }, !,
    load(X, K, a, Ctx), load(Y, w, c, Ctx),
    { sfx(K, S), reg(a, K, A) },
    [ins(I, S, [reg(cl), reg(A)])].
op(Op, K, [X, Y], Ctx) -->
    { division(Op, Signed, Result) }, !,
    load(X, K, a, Ctx), load(Y, K, c, Ctx),
    { sfx(K, S), reg(c, K, C) },
    (   { Signed == signed }
    ->  { K == w -> E = cltd ; E = cqto },
        [ins(E, none, []), ins(idiv, S, [reg(C)])]
    ;   [ins(xor, l, [reg(edx), reg(edx)]), ins(div, S, [reg(C)])]
    ),
    (   { Result == rem } -> { reg(d, K, D), reg(a, K, A) }, [ins(mov, S, [reg(D), reg(A)])]
    ;   []
    ).
op(cmp(C, CK), _, [X, Y], Ctx) -->
    load(X, CK, a, Ctx), load(Y, CK, c, Ctx),
    { sfx(CK, S), reg(a, CK, A), reg(c, CK, R), cc(C, CC), atom_concat(set, CC, Set) },
    [ins(cmp, S, [reg(R), reg(A)]),
     ins(Set, none, [reg(al)]),
     ins(movzb, l, [reg(al), reg(eax)])].
op(ext(T), K, [X], Ctx) -->
    load(X, w, a, Ctx),
    { ext_insn(T, K, I) },
    [I].
op(load(T), K, [A], Ctx) -->
    load(A, l, a, Ctx),
    { load_insn(T, K, I) },
    [I].
op(alloc(_), _, [N], Ctx) -->
    load(N, l, a, Ctx),
    [ins(add, q, [imm(15), reg(rax)]), ins(and, q, [imm(-16), reg(rax)]),
     ins(sub, q, [reg(rax), reg(rsp)]), ins(mov, q, [reg(rsp), reg(rax)])].

alu_insn(add, add). alu_insn(sub, sub). alu_insn(mul, imul).
alu_insn(and, and). alu_insn(or, or).   alu_insn(xor, xor).

% x86 masks the count in %cl to the operand width, as the IR specifies.
shift_insn(shl, shl). shift_insn(shr, shr). shift_insn(sar, sar).

division(div, signed, quot).    division(rem, signed, rem).
division(udiv, unsigned, quot). division(urem, unsigned, rem).

cc(eq, e).  cc(ne, ne).
cc(slt, l). cc(sle, le). cc(sgt, g).  cc(sge, ge).
cc(ult, b). cc(ule, be). cc(ugt, a).  cc(uge, ae).

% ext_insn(Type, Class, Ins): extend the low part of %rax into %rax.
ext_insn(T, K, ins(Op, S, [reg(From), reg(To)])) :-
    ext_op(T, K, Op, S, To), ext_from(T, From).

ext_op(sb, w, movsb, l, eax). ext_op(sb, l, movsb, q, rax).
ext_op(ub, _, movzb, l, eax).
ext_op(sh, w, movsw, l, eax). ext_op(sh, l, movsw, q, rax).
ext_op(uh, _, movzw, l, eax).
ext_op(sw, l, movsl, q, rax).
ext_op(uw, l, mov, l, eax).

ext_from(sb, al). ext_from(ub, al). ext_from(sh, ax). ext_from(uh, ax).
ext_from(sw, eax). ext_from(uw, eax).

% load_insn(Type, Class, Ins): load from (%rax) into %rax, extended.
load_insn(T, K, ins(Op, S, [mem(0, rax), reg(To)])) :- load_op(T, K, Op, S, To).

load_op(l, l, mov, q, rax).
load_op(sw, w, mov, l, eax).
load_op(uw, _, mov, l, eax).
load_op(T, K, Op, S, To) :- T \== uw, ext_op(T, K, Op, S, To).

%% Operands

% load(Value, Class, Reg, Ctx): put Value, read at Class, in register Reg.
load(t(N), K, R, Ctx) --> { reg(R, K, RN) }, load_slot(t(N), K, RN, Ctx).
load(c(N), w, R, _) -->
    { reg(R, w, RN), V is N mod 4294967296 },
    [ins(mov, l, [imm(V), reg(RN)])].
load(c(N), l, R, _) -->
    { reg(R, l, RN), U is N mod 18446744073709551616,
      ( U >= 9223372036854775808 -> V is U - 18446744073709551616 ; V = U ) },
    [ins(movabs, q, [imm(V), reg(RN)])].
load(glo(G), _, R, _) --> { reg(R, l, RN) }, [ins(lea, q, [rip(G), reg(RN)])].

load_slot(Key, K, RN, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Off), sfx(K, S), D is -Off },
    [ins(mov, S, [mem(D, rbp), reg(RN)])].

store_reg(RN, Key, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Off), D is -Off },
    [ins(mov, q, [reg(RN), mem(D, rbp)])].

%% Data

data_items([]) --> [].
data_items([I|Is]) --> data_item(I), data_items(Is).

data_item(zero(N)) --> [zero(N)].
data_item(item(b, str(Cs))) --> !, [ascii(Cs)].
data_item(item(l, sym(S, Off))) --> !, [quad(S+Off)].
data_item(item(W, c(N))) -->
    { directive(W, U, D, Bits), U is N mod (1 << Bits) },
    [D].

directive(b, U, byte([U]), 8).
directive(h, U, short(U), 16).
directive(w, U, int(U), 32).
directive(l, U, quad(U), 64).
