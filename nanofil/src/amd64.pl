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

    The output is GNU as text. This backend is the reference the later
    isel and register allocation milestones are checked against, so it
    favours being obviously right over being fast.
*/
:- module(amd64, [emit_module//1, print_asm/1, op//4, load//4, load_slot//4,
                  store_reg//3, ins//1, ins//2, reg/3, load_insn/3]).


:- use_module(library(lists)).
:- use_module(library(dcgs)).
:- use_module(library(format)).
:- use_module(library(assoc)).
:- use_module(ir).

print_asm(module(Items)) :-
    maplist(emit_item, Items, Css),
    append(Css, Cs0),
    phrase(emit_module(module([])), Tail),
    append(Cs0, Tail, Cs),
    format("~s", [Cs]).

emit_item(I, Cs) :-
    (   phrase(item(I), Cs) -> true
    ;   arg(1, I, Name),
        format(atom(M), 'backend cannot emit $~w', [Name]),
        throw(nanofil_error(M))
    ).

emit_module(module(Items)) -->
    items(Items),
    "\t.section .note.GNU-stack,\"\",@progbits\n".

items([]) --> [].
items([I|Is]) --> item(I), items(Is).

%% Functions

item(func(Name, Lk, Ret, Params, Blocks)) -->
    { frame(Params, Blocks, Slots, Size),
      Ctx = f(Name, Ret, Slots, Blocks) },
    "\t.text\n\t.p2align 4\n",
    global(Lk, Name),
    format_("\t.type ~w, @function~n~w:~n", [Name, Name]),
    ins("pushq %rbp"), ins("movq %rsp, %rbp"),
    (   { Size > 0 } -> ins("subq $~w, %rsp", [Size]) ; [] ),
    params(Params, 0, Ctx),
    blocks(Blocks, Ctx),
    format_("\t.size ~w, .-~w~n", [Name, Name]).
item(data(Name, Lk, Align, Items)) -->
    format_("\t.data\n\t.balign ~w~n", [Align]),
    global(Lk, Name),
    format_("~w:~n", [Name]),
    data_items(Items).

global(export, Name) --> format_("\t.globl ~w~n", [Name]).
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

reg(a, w, '%eax').  reg(a, l, '%rax').
reg(c, w, '%ecx').  reg(c, l, '%rcx').
reg(d, w, '%edx').  reg(d, l, '%rdx').
reg(si, w, '%esi'). reg(si, l, '%rsi').
reg(di, w, '%edi'). reg(di, l, '%rdi').
reg(r8, w, '%r8d'). reg(r8, l, '%r8').
reg(r9, w, '%r9d'). reg(r9, l, '%r9').

suffix(w, l).
suffix(l, q).

%% Blocks and jumps

blocks([], _) --> [].
blocks([blk(L, _, Insts, J)|Bs], Ctx) -->
    label(Ctx, L), ":\n",
    insts(Insts, Ctx),
    jump(J, L, Ctx),
    blocks(Bs, Ctx).

label(f(Fn, _, _, _), L) --> format_(".L~w.~w", [Fn, L]).

jump(jmp(T), From, Ctx) --> edge(From, T, Ctx).
jump(jnz(V, T, F), From, Ctx) -->
    load(V, w, a, Ctx),
    ins("testl %eax, %eax"),
    "\tjz ", label(Ctx, From), ".false\n",
    edge(From, T, Ctx),
    label(Ctx, From), ".false:\n",
    edge(From, F, Ctx).
jump(ret(V), _, Ctx) --> { Ctx = f(_, K, _, _) }, load(V, K, a, Ctx), epilogue.
jump(ret, _, _) --> epilogue.
jump(hlt, _, _) --> ins("ud2").

epilogue --> ins("leave"), ins("ret").

% The copies for the phis of To on the edge From -> To, then the jump.
% All sources are read before any destination is written.
edge(From, To, Ctx) -->
    { Ctx = f(_, _, _, Blocks),
      memberchk(blk(To, Phis, _, _), Blocks) },
    phi_reads(Phis, From, Ctx),
    phi_writes(Phis, Ctx),
    "\tjmp ", label(Ctx, To), "\n".

phi_reads([], _, _) --> [].
phi_reads([phi(t(D), K, Pairs)|Ps], From, Ctx) -->
    { memberchk(From-V, Pairs) },
    load(V, K, a, Ctx),
    store_reg('%rax', shadow(D), Ctx),
    phi_reads(Ps, From, Ctx).

phi_writes([], _) --> [].
phi_writes([phi(t(D), _, _)|Ps], Ctx) -->
    load_slot(shadow(D), l, '%rax', Ctx),
    store_reg('%rax', t(D), Ctx),
    phi_writes(Ps, Ctx).

%% Instructions

insts([], _) --> [].
insts([I|Is], Ctx) --> inst(I, Ctx), insts(Is, Ctx).

inst(ins(D, K, Op, Args), Ctx) --> op(Op, K, Args, Ctx), store_reg('%rax', D, Ctx).
inst(store(W, V, A), Ctx) -->
    { W == l -> VK = l ; VK = w },
    load(V, VK, c, Ctx),
    load(A, l, a, Ctx),
    { store_insn(W, S) },
    ins(S).
inst(call(Res, glo(F), Args), Ctx) -->
    { length(Args, N),
      (   N =< 6 -> true
      ;   Ctx = f(Fn, _, _, _),
          format(atom(M), 'in $~w: call with more than six arguments', [Fn]),
          throw(nanofil_error(M))
      ) },
    call_args(Args, 0, Ctx),
    ins("call ~w", [F]),
    (   { Res = to(D, _) } -> store_reg('%rax', D, Ctx) ; [] ).

call_args([], _, _) --> [].
call_args([arg(K, V)|As], I, Ctx) -->
    { arg_reg(I, R), I1 is I + 1 },
    load(V, K, R, Ctx),
    call_args(As, I1, Ctx).

store_insn(b, "movb %cl, (%rax)").
store_insn(h, "movw %cx, (%rax)").
store_insn(w, "movl %ecx, (%rax)").
store_insn(l, "movq %rcx, (%rax)").

% op(Op, Class, Args, Ctx): compute the result into %rax (zero-extended
% for class w).
op(copy, K, [X], Ctx) --> load(X, K, a, Ctx).
op(neg, K, [X], Ctx) --> load(X, K, a, Ctx), { suffix(K, S), reg(a, K, A) }, ins("neg~w ~w", [S, A]).
op(Op, K, [X, Y], Ctx) -->
    { alu_insn(Op, I) }, !,
    load(X, K, a, Ctx), load(Y, K, c, Ctx),
    { suffix(K, S), reg(a, K, A), reg(c, K, C) },
    ins("~w~w ~w, ~w", [I, S, C, A]).
op(Op, K, [X, Y], Ctx) -->
    { shift_insn(Op, I) }, !,
    load(X, K, a, Ctx), load(Y, w, c, Ctx),
    { suffix(K, S), reg(a, K, A) },
    ins("~w~w %cl, ~w", [I, S, A]).
op(Op, K, [X, Y], Ctx) -->
    { division(Op, Signed, Result) }, !,
    load(X, K, a, Ctx), load(Y, K, c, Ctx),
    { suffix(K, S), reg(c, K, C) },
    (   { Signed == signed } -> { K == w -> E = "cltd" ; E = "cqto" }, ins(E), ins("idiv~w ~w", [S, C])
    ;   ins("xorl %edx, %edx"), ins("div~w ~w", [S, C])
    ),
    (   { Result == rem } -> { reg(d, K, D), reg(a, K, A) }, ins("mov~w ~w, ~w", [S, D, A])
    ;   []
    ).
op(cmp(C, CK), _, [X, Y], Ctx) -->
    load(X, CK, a, Ctx), load(Y, CK, c, Ctx),
    { suffix(CK, S), reg(a, CK, A), reg(c, CK, R), cc(C, CC) },
    ins("cmp~w ~w, ~w", [S, R, A]),
    ins("set~w %al", [CC]),
    ins("movzbl %al, %eax").
op(ext(T), K, [X], Ctx) -->
    load(X, w, a, Ctx),
    { ext_insn(T, K, I) },
    ins(I).
op(load(T), K, [A], Ctx) -->
    load(A, l, a, Ctx),
    { load_insn(T, K, I) },
    ins(I).
op(alloc(_), _, [N], Ctx) -->
    load(N, l, a, Ctx),
    ins("addq $15, %rax"), ins("andq $-16, %rax"),
    ins("subq %rax, %rsp"), ins("movq %rsp, %rax").

alu_insn(add, add). alu_insn(sub, sub). alu_insn(mul, imul).
alu_insn(and, and). alu_insn(or, or).   alu_insn(xor, xor).

% x86 masks the count in %cl to the operand width, as the IR specifies.
shift_insn(shl, shl). shift_insn(shr, shr). shift_insn(sar, sar).

division(div, signed, quot).    division(rem, signed, rem).
division(udiv, unsigned, quot). division(urem, unsigned, rem).

cc(eq, e).  cc(ne, ne).
cc(slt, l). cc(sle, le). cc(sgt, g).  cc(sge, ge).
cc(ult, b). cc(ule, be). cc(ugt, a).  cc(uge, ae).

ext_insn(sb, w, "movsbl %al, %eax").  ext_insn(sb, l, "movsbq %al, %rax").
ext_insn(ub, _, "movzbl %al, %eax").
ext_insn(sh, w, "movswl %ax, %eax").  ext_insn(sh, l, "movswq %ax, %rax").
ext_insn(uh, _, "movzwl %ax, %eax").
ext_insn(sw, l, "movslq %eax, %rax").
ext_insn(uw, l, "movl %eax, %eax").

load_insn(l, l, "movq (%rax), %rax").
load_insn(sw, w, "movl (%rax), %eax").  load_insn(sw, l, "movslq (%rax), %rax").
load_insn(uw, _, "movl (%rax), %eax").
load_insn(sh, w, "movswl (%rax), %eax"). load_insn(sh, l, "movswq (%rax), %rax").
load_insn(uh, _, "movzwl (%rax), %eax").
load_insn(sb, w, "movsbl (%rax), %eax"). load_insn(sb, l, "movsbq (%rax), %rax").
load_insn(ub, _, "movzbl (%rax), %eax").

%% Operands

% load(Value, Class, Reg, Ctx): put Value, read at Class, in register Reg.
load(t(N), K, R, Ctx) --> { reg(R, K, RN) }, load_slot(t(N), K, RN, Ctx).
load(c(N), w, R, _) -->
    { reg(R, w, RN), V is N mod 4294967296 },
    ins("movl $~w, ~w", [V, RN]).
load(c(N), l, R, _) -->
    { reg(R, l, RN), U is N mod 18446744073709551616,
      ( U >= 9223372036854775808 -> V is U - 18446744073709551616 ; V = U ) },
    ins("movabsq $~w, ~w", [V, RN]).
load(glo(G), _, R, _) --> { reg(R, l, RN) }, ins("leaq ~w(%rip), ~w", [G, RN]).

load_slot(Key, K, RN, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Off), suffix(K, S) },
    ins("mov~w -~w(%rbp), ~w", [S, Off, RN]).

store_reg(RN, Key, f(_, _, Slots, _)) -->
    { get_assoc(Key, Slots, Off) },
    ins("movq ~w, -~w(%rbp)", [RN, Off]).

%% Data

data_items([]) --> [].
data_items([I|Is]) --> data_item(I), data_items(Is).

data_item(zero(N)) --> ins(".zero ~w", [N]).
data_item(item(b, str(Cs))) --> !, "\t.ascii \"", seq(Cs), "\"\n".
data_item(item(l, sym(S, Off))) --> !, ins(".quad ~w+~w", [S, Off]).
data_item(item(W, c(N))) -->
    { directive(W, D, Bits), U is N mod (1 << Bits) },
    ins("~w ~w", [D, U]).

directive(b, '.byte', 8).
directive(h, '.short', 16).
directive(w, '.int', 32).
directive(l, '.quad', 64).

%% Text helpers

ins(S) --> "\t", seq(S), "\n".
ins(F, As) --> "\t", format_(F, As), "\n".
