/*  Relational semantics of the phase-one IR.

    run(+Module, +Fn, ?Args, +Fuel, ?Outcome)

    Args are integers or CLP(Z) variables, one per parameter, in the range
    of the parameter's class. Outcome is one of
      ret(V)          returned V (an integer or constrained variable)
      ret             returned from a void function
      hlt             executed hlt
      ub(Reason)      undefined behaviour: division by zero or overflow,
                      a memory access outside every live allocation
      out_of_fuel     executed Fuel blocks without finishing

    Arithmetic and branches are CLP(Z) constraints, so the relation runs
    in every direction: Args and Outcome can both be partially unknown.
    Memory addresses and allocation sizes must be known when an access or
    alloc runs; otherwise the run raises an instantiation error, which is
    incomplete but never wrong.

    Memory is mem(Bytes, Regions, Next): an assoc from address to byte, the
    list of live Base-End regions, and the next free stack address. A byte
    nobody wrote is a fresh variable in 0..255, so reading uninitialized
    memory gives an unknown value rather than a made-up one. A function's
    allocations die when it returns, and addresses are never reused, so
    use after return is an out-of-bounds access.
*/
:- module(interp, [run/5, outcome_text/2]).

:- use_module(library(clpz)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(dif)).
:- use_module(ir).

run(M, Fn, Args, Fuel, Outcome) :-
    module_mode(M, Mode),
    initial_memory(M, G, Mem0),
    func_named(M, Fn, func(_, _, _, Params, _)),
    maplist(arg_in_range, Params, Args),
    call_fn(M, G, Mode, Fn, Args, s(Mem0, Fuel), Outcome, _).

arg_in_range(par(p, _), ptr(_, _)) :- !.
arg_in_range(par(K, _), A) :-
    modulus(K, Mod),
    Top #= Mod - 1,
    A in 0..Top.

% In plain mode a callee's allocations die when it returns; in filc mode
% every allocation is a heap object that lives on.
call_fn(M, G, Mode, Fn, Args, S0, Out, S) :-
    (   func_named(M, Fn, func(_, _, Ret, Params, Blocks)) -> true
    ;   format(atom(Msg), 'cannot interpret a call to external $~w', [Fn]),
        throw(nanofil_error(Msg))
    ),
    empty_assoc(E0),
    foldl(bind_param, Params, Args, E0, Env),
    Blocks = [blk(Entry, _, _, _)|_],
    exec(c(M, G, Blocks, Ret, Mode), Entry, none, Env, S0, Out, S1),
    S0 = s(mem(_, Regions, _, _), _),
    S1 = s(mem(B, _, N, Aux), F),
    (   Mode == plain -> S = s(mem(B, Regions, N, Aux), F) ; S = S1 ).

bind_param(par(_, t(N)), X, E0, E) :- put_assoc(N, E0, X, E).

%% Blocks

exec(Ctx, L, Pred, Env0, s(Mem, F0), Out, S) :-
    (   F0 #= 0, Out = out_of_fuel, S = s(Mem, F0)
    ;   F0 #> 0, F1 #= F0 - 1,
        Ctx = c(_, _, Blocks, _, _),
        memberchk(blk(L, Phis, Insts, J), Blocks),
        phis(Phis, Ctx, Pred, Env0, Env0, Env1),
        insts(Insts, Ctx, Env1, s(Mem, F1), R),
        after(R, J, Ctx, L, Out, S)
    ).

% Phis read the environment as it was on entry, then all bind at once.
phis([], _, _, _, Env, Env).
phis([phi(t(D), K, Pairs)|Ps], Ctx, Pred, Old, Env0, Env) :-
    memberchk(Pred-V, Pairs),
    read(K, V, Ctx, Old, X),
    put_assoc(D, Env0, X, Env1),
    phis(Ps, Ctx, Pred, Old, Env1, Env).

after(cont(Env, S0), J, Ctx, L, Out, S) :- jump(J, Ctx, L, Env, S0, Out, S).
after(stop(Out, S), _, _, _, Out, S).

jump(jmp(L), Ctx, From, Env, S0, Out, S) :- exec(Ctx, L, From, Env, S0, Out, S).
jump(jnz(V, L1, L2), Ctx, From, Env, S0, Out, S) :-
    read(w, V, Ctx, Env, X),
    (   X #\= 0, exec(Ctx, L1, From, Env, S0, Out, S)
    ;   X #= 0, exec(Ctx, L2, From, Env, S0, Out, S)
    ).
jump(ret(V), Ctx, _, Env, S, ret(X), S) :-
    Ctx = c(_, _, _, K, _),
    read(K, V, Ctx, Env, X).
jump(ret, _, _, _, S, ret, S).
jump(hlt, _, _, _, S, hlt, S).

%% Instructions

insts([], _, Env, S, cont(Env, S)).
insts([I|Is], Ctx, Env0, S0, R) :-
    step(I, Ctx, Env0, S0, R0),
    insts_(R0, Is, Ctx, R).

insts_(cont(Env, S), Is, Ctx, R) :- insts(Is, Ctx, Env, S, R).
insts_(stop(Out, S), _, _, stop(Out, S)).

step(ins(t(D), K, Op, Args), Ctx, Env0, S0, R) :-
    Ctx = c(_, _, _, _, Mode),
    op_arg_classes(Op, K, Mode, AKs),
    maplist(read_in(Ctx, Env0), AKs, Args, Xs),
    eval(Op, K, Mode, Xs, S0, Res, S),
    bind_result(Res, D, Env0, S, R).
step(store(W, V, A), Ctx, Env, s(Mem0, F), R) :-
    Ctx = c(_, _, _, _, Mode),
    (   memberchk(W, [l, p]) -> VK = W ; VK = w ),
    read(VK, V, Ctx, Env, X),
    addr_class(Mode, AK),
    read(AK, A, Ctx, Env, Addr),
    store(Mode, W, Mem0, Addr, X, Res, Mem),
    store_result(Res, Env, s(Mem, F), R).
step(call(Res, glo(F), Args), Ctx, Env0, S0, R) :-
    Ctx = c(M, G, _, _, Mode),
    maplist(read_arg(Ctx, Env0), Args, Xs),
    call_fn(M, G, Mode, F, Xs, S0, Out, S),
    call_result(Out, Res, Env0, S, R).

read_in(Ctx, Env, K, V, X) :- read(K, V, Ctx, Env, X).
read_arg(Ctx, Env, arg(K, V), X) :- read(K, V, Ctx, Env, X).

bind_result(val(X), D, Env0, S, cont(Env, S)) :- put_assoc(D, Env0, X, Env).
bind_result(ub(Why), _, _, S, stop(ub(Why), S)).
bind_result(trap(Why), _, _, S, stop(trap(Why), S)).

store_result(ok, Env, S, cont(Env, S)).
store_result(ub(Why), _, S, stop(ub(Why), S)).
store_result(trap(Why), _, S, stop(trap(Why), S)).

call_result(ret(X), to(t(D), p), Env0, S, cont(Env, S)) :- !,
    put_assoc(D, Env0, X, Env).
call_result(ret(X), to(t(D), K), Env0, S, cont(Env, S)) :-
    modulus(K, Mod),
    Y #= X mod Mod,
    put_assoc(D, Env0, Y, Env).
call_result(ret(_), void, Env, S, cont(Env, S)).
call_result(ret, void, Env, S, cont(Env, S)).
call_result(hlt, _, _, S, stop(hlt, S)).
call_result(ub(Why), _, _, S, stop(ub(Why), S)).
call_result(trap(Why), _, _, S, stop(trap(Why), S)).
call_result(out_of_fuel, _, _, S, stop(out_of_fuel, S)).

% Reading a value at class K takes its low bits(K) bits.
read(K, V, Ctx, Env, X) :- read_(V, K, Ctx, Env, X).

read_(t(N), K, _, Env, X) :-
    (   get_assoc(N, Env, X0) -> true
    ;   format(atom(M), 'read of %~w before any assignment', [N]),
        throw(nanofil_error(M))
    ),
    (   K == p -> X = X0
    ;   modulus(K, Mod),
        X #= X0 mod Mod
    ).
read_(c(N), K, _, _, X) :-
    modulus(K, Mod),
    A is N mod Mod,
    (   K == p -> X = ptr(A, none) ; X = A ).
read_(glo(N), _, c(_, G, _, _, _), _, X) :-
    get_assoc(N, G, X).

%% Operations. eval(Op, Class, Mode, Args, S0, val(X) | ub(Why) | trap(Why), S)

eval(load(p), _, filc, [ptr(A, Cap)], s(Mem0, F), Res, s(Mem, F)) :- !,
    checked(Mem0, A, Cap, 8, read, 8, Res0),
    (   Res0 == ok
    ->  load_bytes(filc, Mem0, A, 8, val(U), Mem),
        Mem = mem(_, _, _, Aux),
        (   get_assoc(A, Aux, C) -> true ; C = none ),
        Res = val(ptr(U, C))
    ;   Mem = Mem0, Res = Res0
    ).
eval(load(T), K, Mode, [A0], s(Mem0, F), Res, s(Mem, F)) :- !,
    load_type(T, N, Ext),
    (   Mode == filc
    ->  A0 = ptr(A, Cap), checked(Mem0, A, Cap, N, read, 1, Res0)
    ;   A = A0, Res0 = ok
    ),
    (   Res0 == ok
    ->  load_bytes(Mode, Mem0, A, N, R0, Mem),
        load_value(R0, Ext, K, Res)
    ;   Mem = Mem0, Res = Res0
    ).
eval(alloc(Align), _, Mode, [Size], s(Mem0, F), val(P), s(Mem, F)) :- !,
    alloc(Mode, Mem0, Align, Size, Base, Mem),
    (   Mode == filc -> P = ptr(Base, obj(Base)) ; P = Base ).
eval(Op, K, _, Xs, S, Res, S) :-
    alu(Op, K, Xs, Res).

% Pointer arithmetic keeps the capability. ptoi drops it; itop has none.
alu(add, p, [ptr(A, C), X], val(ptr(R, C))) :- !, modulus(l, M), R #= (A + X) mod M.
alu(sub, p, [ptr(A, C), X], val(ptr(R, C))) :- !, modulus(l, M), R #= (A - X) mod M.
alu(ptoi, _, [ptr(A, _)], val(A)).
alu(itop, _, [X], val(ptr(X, none))).

alu(add, K, [X, Y], val(R)) :- modulus(K, M), R #= (X + Y) mod M.
alu(sub, K, [X, Y], val(R)) :- modulus(K, M), R #= (X - Y) mod M.
alu(mul, K, [X, Y], val(R)) :- modulus(K, M), R #= (X * Y) mod M.
alu(neg, K, [X], val(R)) :- modulus(K, M), R #= (-X) mod M.
alu(copy, _, [X], val(X)).
alu(and, _, [X, Y], val(R)) :- R #= X /\ Y.
alu(or, _, [X, Y], val(R)) :- R #= X \/ Y.
alu(xor, _, [X, Y], val(R)) :- R #= xor(X, Y).
alu(udiv, _, [X, Y], Res) :-
    (   Y #= 0, Res = ub(division_by_zero)
    ;   Y #\= 0, R #= X // Y, Res = val(R)
    ).
alu(urem, _, [X, Y], Res) :-
    (   Y #= 0, Res = ub(division_by_zero)
    ;   Y #\= 0, R #= X mod Y, Res = val(R)
    ).
alu(div, K, [X, Y], Res) :- signed_division(K, X, Y, //, Res).
alu(rem, K, [X, Y], Res) :- signed_division(K, X, Y, rem, Res).
alu(shl, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), modulus(K, M), R #= (X * P) mod M.
alu(shr, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), R #= X // P.
alu(sar, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), signed(K, X, SX), modulus(K, M), R #= (SX div P) mod M.
alu(ext(T), K, [X], val(R)) :- extend(T, X, S), modulus(K, M), R #= S mod M.
alu(cmp(C, CK), _, [X, Y], val(B)) :-
    B in 0..1,
    compare_(C, CK, X, Y, B).

% x86 idiv traps on both a zero divisor and the one quotient that
% overflows, so both are undefined here.
signed_division(K, X, Y, Fn, Res) :-
    signed(K, X, SX), signed(K, Y, SY),
    half(K, H), Min #= -H,
    (   SY #= 0, Res = ub(division_by_zero)
    ;   SY #= -1, SX #= Min, Res = ub(division_overflow)
    ;   SY #\= 0, #\ (SY #= -1 #/\ SX #= Min),
        modulus(K, M),
        division(Fn, SX, SY, Q),
        R #= Q mod M,
        Res = val(R)
    ).

division(//, X, Y, Q) :- Q #= X // Y.
division(rem, X, Y, Q) :- Q #= X rem Y.

% The shift count is taken modulo the class width.
shift_factor(K, Y, P) :-
    class_bits(K, Bits),
    C #= Y mod Bits,
    P #= 2 ^ C.

compare_(eq, _, X, Y, B) :- B #<==> (X #= Y).
compare_(ne, _, X, Y, B) :- B #<==> (X #\= Y).
compare_(ult, _, X, Y, B) :- B #<==> (X #< Y).
compare_(ule, _, X, Y, B) :- B #<==> (X #=< Y).
compare_(ugt, _, X, Y, B) :- B #<==> (X #> Y).
compare_(uge, _, X, Y, B) :- B #<==> (X #>= Y).
compare_(slt, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), B #<==> (SX #< SY).
compare_(sle, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), B #<==> (SX #=< SY).
compare_(sgt, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), B #<==> (SX #> SY).
compare_(sge, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), B #<==> (SX #>= SY).

signed(K, U, S) :-
    modulus(K, M), half(K, H),
    sext(M, H, U, S).

% S is the two's-complement reading of the low bits of U, for a field of
% modulus M with sign threshold H.
sext(M, H, U, S) :-
    L #= U mod M,
    Neg in 0..1,
    Neg #<==> (L #>= H),
    S #= L - Neg * M.

extend(sb, X, S) :- sext(256, 128, X, S).
extend(ub, X, S) :- S #= X mod 256.
extend(sh, X, S) :- sext(65536, 32768, X, S).
extend(uh, X, S) :- S #= X mod 65536.
extend(sw, X, S) :- sext(4294967296, 2147483648, X, S).
extend(uw, X, S) :- S #= X mod 4294967296.

load_type(l, 8, none).
load_type(sw, 4, sw).
load_type(uw, 4, uw).
load_type(sh, 2, sh).
load_type(uh, 2, uh).
load_type(sb, 1, sb).
load_type(ub, 1, ub).

load_value(ub(Why), _, _, ub(Why)).
load_value(val(U), none, _, val(U)).
load_value(val(U), T, K, val(R)) :-
    dif(T, none),
    extend(T, U, S), modulus(K, M), R #= S mod M.

%% Memory: mem(Bytes, Regions, Next, Aux)
%
% Aux is used in filc mode only: it maps an 8-aligned address to the
% capability a storep left there. An integer store leaves it alone, as
% Fil-C's aux array does.

% In plain mode an access outside every live region is undefined. In filc
% mode the access was checked against its capability already.
load_bytes(Mode, mem(B0, Rs, N, Aux), A, W, Res, mem(B, Rs, N, Aux)) :-
    must_be(integer, A),
    (   ( Mode == filc ; live(Rs, A, W) )
    ->  bytes_in(W, Mode, A, B0, B, Bytes),
        le_value(Bytes, U),
        Res = val(U)
    ;   B = B0, Res = ub(out_of_bounds(A, W))
    ).

store(plain, W, mem(B0, Rs, N, Aux), A, X, Res, mem(B, Rs, N, Aux)) :-
    width_bytes(W, Size),
    must_be(integer, A),
    (   live(Rs, A, Size)
    ->  le_bytes(Size, X, Bytes),
        bytes_out(Bytes, A, B0, B),
        Res = ok
    ;   B = B0, Res = ub(out_of_bounds(A, Size))
    ).
store(filc, W, Mem0, ptr(A, Cap), X, Res, Mem) :-
    width_bytes(W, Size),
    (   W == p -> Align = 8, X = ptr(V, VC) ; Align = 1, V = X ),
    checked(Mem0, A, Cap, Size, write, Align, Res),
    (   Res == ok
    ->  Mem0 = mem(B0, Rs, N, Aux0),
        le_bytes(Size, V, Bytes),
        bytes_out(Bytes, A, B0, B),
        (   W == p -> put_assoc(A, Aux0, VC, Aux) ; Aux = Aux0 ),
        Mem = mem(B, Rs, N, Aux)
    ;   Mem = Mem0
    ).

/* checked(+Mem, +A, +Cap, +Size, +Kind, +Align, -Res): Fil-C's access
   check. Every allocation is writable in the interpreter; readonly
   objects only come from clang-built code. */
checked(mem(_, Rs, _, _), A, Cap, Size, _, Align, Res) :-
    must_be(integer, A),
    (   Cap == none -> Res = trap(null_capability)
    ;   Cap = obj(Base), memberchk(Base-End, Rs),
        (   A >= Base, A + Size =< End
        ->  (   A mod Align =:= 0 -> Res = ok ; Res = trap(misaligned) )
        ;   Res = trap(out_of_bounds)
        )
    ).

% The access [A, A+W) lies inside one live region. A and the regions are
% integers here, so the if-then-else above is sound.
live(Rs, A, W) :-
    member(Base-End, Rs),
    A >= Base, A + W =< End, !.

% An unwritten byte is unknown in plain mode and zero in filc mode, since
% Fil-C allocations are zeroed.
bytes_in(0, _, _, B, B, []) :- !.
bytes_in(W, Mode, A, B0, B, [X|Xs]) :-
    (   get_assoc(A, B0, X) -> B1 = B0
    ;   Mode == filc -> X = 0, B1 = B0
    ;   X in 0..255, put_assoc(A, B0, X, B1)
    ),
    A1 is A + 1, W1 is W - 1,
    bytes_in(W1, Mode, A1, B1, B, Xs).

bytes_out([], _, B, B).
bytes_out([X|Xs], A, B0, B) :-
    put_assoc(A, B0, X, B1),
    A1 is A + 1,
    bytes_out(Xs, A1, B1, B).

% Little-endian.
le_value([], 0).
le_value([X|Xs], U) :- le_value(Xs, U1), U #= X + 256 * U1.

le_bytes(0, _, []) :- !.
le_bytes(W, X, [B|Bs]) :-
    B #= X mod 256,
    X1 #= X // 256,
    W1 is W - 1,
    le_bytes(W1, X1, Bs).

% Allocations are aligned, and a 16-byte gap separates them so a small
% overrun cannot land in a neighbour.
alloc(Mode, mem(B, Rs, Next, Aux), Align0, Size, Base, mem(B, [Base-End|Rs], Next1, Aux)) :-
    must_be(integer, Size),
    (   Mode == filc -> Align = 16 ; Align = Align0 ),
    Base is (Next + Align - 1) // Align * Align,
    End is Base + Size,
    Next1 is End + 16.

stack_base(4294967296).
data_base(65536).

/* initial_memory(+M, -Globals, -Mem): lay out every data definition, each
   in its own region, and fill in its bytes. */
initial_memory(module(Items), G, mem(Bytes, Rs, Stack, Aux)) :-
    empty_assoc(Aux),
    data_base(D0),
    empty_assoc(G0),
    layout(Items, D0, G0, G, [], Rs),
    empty_assoc(B0),
    foldl(fill(G), Items, B0, Bytes),
    stack_base(Stack).

layout([], _, G, G, Rs, Rs).
layout([I|Is], A0, G0, G, Rs0, Rs) :-
    (   I = data(Name, _, Align, Items)
    ->  Base is (A0 + Align - 1) // Align * Align,
        foldl(item_size, Items, 0, Size),
        End is Base + Size,
        put_assoc(Name, G0, Base, G1),
        Rs1 = [Base-End|Rs0],
        A1 is End + 16
    ;   G1 = G0, Rs1 = Rs0, A1 = A0
    ),
    layout(Is, A1, G1, G, Rs1, Rs).

item_size(zero(N), S0, S) :- S is S0 + N.
item_size(item(b, str(Cs)), S0, S) :- !, unescape(Cs, Bs), length(Bs, N), S is S0 + N.
item_size(item(W, _), S0, S) :- width_bytes(W, N), S is S0 + N.

fill(G, data(Name, _, _, Items), B0, B) :- !,
    get_assoc(Name, G, A),
    maplist(item_bytes(G), Items, Bss),
    append(Bss, Bytes),
    bytes_out(Bytes, A, B0, B).
fill(_, func(_, _, _, _, _), B, B).

item_bytes(_, zero(N), Bs) :- length(Bs, N), maplist(=(0), Bs).
item_bytes(_, item(b, str(Cs)), Bs) :- !, unescape(Cs, Bs).
item_bytes(_, item(W, c(N)), Bs) :-
    width_bytes(W, Size), Bits is Size * 8,
    U is N mod (1 << Bits),
    le_bytes(Size, U, Bs).
item_bytes(G, item(l, sym(S, Off)), Bs) :-
    get_assoc(S, G, A),
    U is A + Off,
    le_bytes(8, U, Bs).

% GNU as string escapes that QBE passes through.
unescape([], []).
unescape(['\\', C|Cs], [B|Bs]) :- !, escape(C, Cs, B, Rest), unescape(Rest, Bs).
unescape([C|Cs], [B|Bs]) :- char_code(C, B), unescape(Cs, Bs).

escape(n, Cs, 10, Cs) :- !.
escape(t, Cs, 9, Cs) :- !.
escape(r, Cs, 13, Cs) :- !.
escape('\\', Cs, 92, Cs) :- !.
escape('"', Cs, 34, Cs) :- !.
escape(D, Cs, B, Rest) :-
    octal(D, V0), octal_more(Cs, V0, 2, B, Rest).

octal_more([D|Cs], V0, N, V, Rest) :- N > 0, octal(D, X), !,
    V1 is V0 * 8 + X, N1 is N - 1, octal_more(Cs, V1, N1, V, Rest).
octal_more(Cs, V, _, V, Cs).

octal(D, V) :- char_code(D, C), C >= 0'0, C =< 0'7, V is C - 0'0.

%% Printing

outcome_text(ret(V), T) :- integer(V), !, format(atom(T), 'ret ~w', [V]).
outcome_text(ret(ptr(_, _)), 'ret pointer') :- !.
outcome_text(ret(_), 'ret unknown') :- !.
outcome_text(ret, ret).
outcome_text(hlt, hlt).
outcome_text(ub(Why), T) :- format(atom(T), 'ub ~w', [Why]).
outcome_text(trap(Why), T) :- format(atom(T), 'trap ~w', [Why]).
outcome_text(out_of_fuel, out_of_fuel).
