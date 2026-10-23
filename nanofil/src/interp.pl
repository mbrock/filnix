/*  Relational semantics of the phase-one IR.

    run(+Module, +Fn, ?Args, +Fuel, ?Outcome)
    prepare(+Module, -Prepared), run_prepared(+Prepared, +Fn, ?Args, +Fuel, ?Outcome)

    run/5 prepares the module first: its mode, initial memory, and
    indexes of its functions and blocks. Prepare once to run many times.

    Args are integers or CLP(Z) variables, one per parameter, in the range
    of the parameter's class. Outcome is one of
      ret(V)          returned V (an integer or constrained variable)
      rets([X1, X2])  returned a tuple
      ret             returned from a void function
      hlt             executed hlt
      ub(Reason)      undefined behaviour: division by zero or overflow,
                      a memory access outside every live allocation
      out_of_fuel     executed Fuel blocks without finishing

    Arithmetic and branches are CLP(Z) constraints, so the relation runs
    in every direction: Args and Outcome can both be partially unknown.
    Known values take a fast path (is/2 and if-then-else), which gives
    the same answers; only unknown values pay for constraints.
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
:- module(interp, [run/5, prepare/2, run_prepared/5, outcome_text/2]).

:- use_module(library(clpz)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(dif)).
:- use_module(ir).

run(M, Fn, Args, Fuel, Outcome) :-
    prepare(M, P),
    run_prepared(P, Fn, Args, Fuel, Outcome).

% The initial memory holds integers only, so runs can share it.
prepare(M, prep(Fns, G, Mode, Mem0)) :-
    module_mode(M, Mode),
    initial_memory(Mode, M, G, Mem0),
    M = module(Items),
    findall(Name-fn(Ret, Params, Entry, BA),
            ( member(func(Name, _, Ret, Params, Blocks), Items),
              Blocks = [blk(Entry, _, _, _)|_],
              findall(L-B, ( member(B, Blocks), B = blk(L, _, _, _) ), LBs),
              list_to_assoc(LBs, BA) ),
            NFs),
    list_to_assoc(NFs, Fns).

run_prepared(prep(Fns, G, Mode, Mem0), Fn, Args, Fuel, Outcome) :-
    get_assoc(Fn, Fns, fn(_, Params, _, _)),
    maplist(arg_in_range, Params, Args),
    call_fn(Fns, G, Mode, Fn, Args, s(Mem0, Fuel), Outcome, _).

arg_in_range(par(p, _), ptr(_, _)) :- !.
arg_in_range(par(K, _), A) :-
    modulus(K, Mod),
    Top #= Mod - 1,
    A in 0..Top.

% In plain mode a callee's allocations die when it returns; in filc mode
% every allocation is a heap object that lives on.
call_fn(Fns, G, Mode, Fn, Args, S0, Out, S) :-
    (   get_assoc(Fn, Fns, fn(Ret, Params, Entry, Blocks)) -> true
    ;   format(atom(Msg), 'cannot interpret a call to external $~w', [Fn]),
        throw(nanofil_error(Msg))
    ),
    empty_assoc(E0),
    foldl(bind_param, Params, Args, E0, Env),
    exec(c(Fns, G, Blocks, Ret, Mode), Entry, none, Env, S0, Out, S1),
    S0 = s(mem(_, Regions, _, _), _),
    S1 = s(mem(B, _, N, Aux), F),
    (   Mode == plain -> S = s(mem(B, Regions, N, Aux), F) ; S = S1 ).

bind_param(par(_, t(N)), X, E0, E) :- put_assoc(N, E0, X, E).

% Concrete fast path: when every operand is known, plain arithmetic and
% if-then-else give the same answers as the constraints, without
% propagators or choice points. Unknown operands still get constraints.
ev(R, E) :- ( ground(E) -> R is E ; R #= E ).

% test(+Goal, ?B): B is 1 if Goal holds, else 0 (reified when unknown).
reify(C, B) :-
    (   ground(C) -> ( call(C) -> B = 1 ; B = 0 )
    ;   B in 0..1, reify_(C, B)
    ).
reify_(X =:= Y, B) :- B #<==> (X #= Y).
reify_(X =\= Y, B) :- B #<==> (X #\= Y).
reify_(X < Y, B) :- B #<==> (X #< Y).
reify_(X =< Y, B) :- B #<==> (X #=< Y).
reify_(X > Y, B) :- B #<==> (X #> Y).
reify_(X >= Y, B) :- B #<==> (X #>= Y).

%% Blocks

exec(Ctx, L, Pred, Env0, s(Mem, F0), Out, S) :-
    (   F0 =:= 0 -> Out = out_of_fuel, S = s(Mem, F0)
    ;   F1 is F0 - 1,
        Ctx = c(_, _, Blocks, _, _),
        get_assoc(L, Blocks, blk(_, Phis, Insts, J)),
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
    (   integer(X) -> ( X =\= 0 -> L = L1 ; L = L2 )
    ;   X #\= 0, L = L1
    ;   X #= 0, L = L2
    ),
    exec(Ctx, L, From, Env, S0, Out, S).
jump(ret(V), Ctx, _, Env, S, ret(X), S) :-
    Ctx = c(_, _, _, K, _),
    read(K, V, Ctx, Env, X).
jump(rets(Vs), Ctx, _, Env, S, rets(Xs), S) :-
    Ctx = c(_, _, _, tuple(Ks), _),
    maplist(read_tuple(Ctx, Env), Ks, Vs, Xs).
jump(ret, _, _, _, S, ret, S).
jump(hlt, _, _, _, S, hlt, S).

read_tuple(Ctx, Env, K, V, X) :- read(K, V, Ctx, Env, X).

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
step(call(Res, t(N), Args), Ctx, Env0, S0, R) :-
    Ctx = c(M, G, _, _, Mode),
    read(p, t(N), Ctx, Env0, ptr(A, Cap)),
    maplist(read_arg(Ctx, Env0), Args, Xs),
    (   Cap = fn(F), get_assoc(F, G, ptr(A0, _)), A == A0
    ->  get_assoc(F, M, fn(Ret, Params, _, _)),
        indirect(Ret, Params, Res, Args, Xs, Ys, Conv),
        (   Conv = trap(Why) -> R = stop(trap(Why), S0)
        ;   call_fn(M, G, Mode, F, Ys, S0, Out0, S),
            convert_return(Conv, Out0, Out),
            call_result(Out, Res, Env0, S, R)
        )
    ;   Cap = ext(F)
    ->  format(atom(Msg), 'cannot interpret a call to external $~w', [F]),
        throw(nanofil_error(Msg))
    ;   R = stop(trap(not_a_function), S0)
    ).

/* indirect(+CalleeRet, +Params, +Res, +Args, +Xs, -Ys, -Conv): a call
   through a function pointer. When the classes the call site passes and
   expects give the callee's signature (w and l are the same word), it is
   a direct call. Otherwise it goes through the callee's generic entry:
   each argument and result word is 8 bytes with its lower beside it, so
   a p word read as an integer is its address and an integer read as p
   has no capability. Too few arguments, or fewer result words than the
   call site reads, fail the generic entry's size checks. Conv is same,
   conv(CallerWords, CalleeWords) or trap(Why). */
indirect(Ret, Params, Res, Args, Xs, Ys, Conv) :-
    length(Params, NP), length(Args, NA),
    res_words(Res, RWs), ret_words(Ret, CWs),
    length(RWs, NR), length(CWs, NC),
    findall(K, member(par(K, _), Params), PKs),
    findall(K, member(arg(K, _), Args), AKs),
    (   NA < NP -> Conv = trap(argument_size)
    ;   NR > NC -> Conv = trap(return_size)
    ;   length(Xs1, NP), append(Xs1, _, Xs),
        length(AKs1, NP), append(AKs1, _, AKs),
        maplist(generic_word, AKs1, PKs, Xs1, Ys),
        (   maplist(word_class, RWs, WCs), maplist(word_class, CWs, WCs) -> Conv = same
        ;   Conv = conv(RWs, CWs)
        )
    ).

res_words(void, []).
res_words(to(_, K), [K]).
res_words(tuple(Tos), Ks) :- findall(K, member(to(_, K), Tos), Ks).

ret_words(void, []) :- !.
ret_words(tuple(Ks), Ks) :- !.
ret_words(K, [K]).

word_class(p, p) :- !.
word_class(_, int).

generic_word(K, K, X, X) :- !.
generic_word(p, _, ptr(A, _), A) :- !.
generic_word(_, p, X, ptr(X, none)) :- !.
generic_word(_, _, X, X).

convert_return(same, Out, Out).
convert_return(conv(RWs, CWs), Out0, Out) :-
    (   outcome_words(Out0, Xs0)
    ->  length(RWs, N), length(Xs, N), append(Xs, _, Xs0),
        length(CWs1, N), append(CWs1, _, CWs),
        maplist(generic_word, CWs1, RWs, Xs, Ys),
        outcome_words(Out, Ys)
    ;   Out = Out0
    ).

outcome_words(ret, []).
outcome_words(ret(X), [X]).
outcome_words(rets(Xs), Xs) :- Xs = [_, _|_].

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
    ev(Y, X mod Mod),
    put_assoc(D, Env0, Y, Env).
call_result(rets(Xs), tuple(Tos), Env0, S, cont(Env, S)) :-
    foldl(bind_word, Tos, Xs, Env0, Env).
call_result(ret(_), void, Env, S, cont(Env, S)).
call_result(rets(_), void, Env, S, cont(Env, S)).
call_result(ret, void, Env, S, cont(Env, S)).
call_result(hlt, _, _, S, stop(hlt, S)).
call_result(ub(Why), _, _, S, stop(ub(Why), S)).
call_result(trap(Why), _, _, S, stop(trap(Why), S)).
call_result(out_of_fuel, _, _, S, stop(out_of_fuel, S)).

bind_word(to(t(D), p), X, Env0, Env) :- !, put_assoc(D, Env0, X, Env).
bind_word(to(t(D), K), X, Env0, Env) :-
    modulus(K, Mod), ev(Y, X mod Mod), put_assoc(D, Env0, Y, Env).

% Reading a value at class K takes its low bits(K) bits.
read(K, V, Ctx, Env, X) :- read_(V, K, Ctx, Env, X).

read_(t(N), K, _, Env, X) :-
    (   get_assoc(N, Env, X0) -> true
    ;   format(atom(M), 'read of %~w before any assignment', [N]),
        throw(nanofil_error(M))
    ),
    (   K == p -> X = X0
    ;   modulus(K, Mod),
        ev(X, X0 mod Mod)
    ).
read_(c(N), K, _, _, X) :-
    modulus(K, Mod),
    A is N mod Mod,
    (   K == p -> X = ptr(A, none) ; X = A ).
read_(glo(N), _, c(_, G, _, _, Mode), _, X) :-
    (   get_assoc(N, G, X0) -> X = X0
    ;   Mode == filc -> X = ptr(0, ext(N))
    ).

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
alu(add, p, [ptr(A, C), X], val(ptr(R, C))) :- !, modulus(l, M), ev(R, (A + X) mod M).
alu(sub, p, [ptr(A, C), X], val(ptr(R, C))) :- !, modulus(l, M), ev(R, (A - X) mod M).
alu(ptoi, _, [ptr(A, _)], val(A)).
alu(itop, _, [X], val(ptr(X, none))).

alu(add, K, [X, Y], val(R)) :- modulus(K, M), ev(R, (X + Y) mod M).
alu(sub, K, [X, Y], val(R)) :- modulus(K, M), ev(R, (X - Y) mod M).
alu(mul, K, [X, Y], val(R)) :- modulus(K, M), ev(R, (X * Y) mod M).
alu(neg, K, [X], val(R)) :- modulus(K, M), ev(R, (-X) mod M).
alu(copy, _, [X], val(X)).
alu(and, _, [X, Y], val(R)) :- ev(R, X /\ Y).
alu(or, _, [X, Y], val(R)) :- ev(R, X \/ Y).
alu(xor, _, [X, Y], val(R)) :- ev(R, xor(X, Y)).
alu(udiv, _, [X, Y], Res) :- unsigned_division(X, Y, X // Y, Res).
alu(urem, _, [X, Y], Res) :- unsigned_division(X, Y, X mod Y, Res).
alu(div, K, [X, Y], Res) :- signed_division(K, X, Y, //, Res).
alu(rem, K, [X, Y], Res) :- signed_division(K, X, Y, rem, Res).
alu(shl, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), modulus(K, M), ev(R, (X * P) mod M).
alu(shr, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), ev(R, X // P).
alu(sar, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P), signed(K, X, SX), modulus(K, M), ev(R, (SX div P) mod M).
alu(ext(T), K, [X], val(R)) :- extend(T, X, S), modulus(K, M), ev(R, S mod M).
alu(cmp(C, CK), _, [X, Y], val(B)) :- compare_(C, CK, X, Y, B).

unsigned_division(_, Y, E, Res) :-
    (   integer(Y) -> ( Y =:= 0 -> Res = ub(division_by_zero) ; ev(R, E), Res = val(R) )
    ;   Y #= 0, Res = ub(division_by_zero)
    ;   Y #\= 0, ev(R, E), Res = val(R)
    ).

% x86 idiv traps on both a zero divisor and the one quotient that
% overflows, so both are undefined here.
signed_division(K, X, Y, Fn, Res) :-
    signed(K, X, SX), signed(K, Y, SY),
    half(K, H), Min is -H,
    (   integer(SX), integer(SY)
    ->  (   SY =:= 0 -> Res = ub(division_by_zero)
        ;   SY =:= -1, SX =:= Min -> Res = ub(division_overflow)
        ;   modulus(K, M), division(Fn, SX, SY, Q), R is Q mod M, Res = val(R)
        )
    ;   SY #= 0, Res = ub(division_by_zero)
    ;   SY #= -1, SX #= Min, Res = ub(division_overflow)
    ;   SY #\= 0, #\ (SY #= -1 #/\ SX #= Min),
        modulus(K, M),
        division(Fn, SX, SY, Q),
        R #= Q mod M,
        Res = val(R)
    ).

division(//, X, Y, Q) :- ev(Q, X // Y).
division(rem, X, Y, Q) :- ev(Q, X rem Y).

% The shift count is taken modulo the class width.
shift_factor(K, Y, P) :-
    class_bits(K, Bits),
    ev(C, Y mod Bits),
    ev(P, 2 ^ C).

compare_(eq, _, X, Y, B) :- reify(X =:= Y, B).
compare_(ne, _, X, Y, B) :- reify(X =\= Y, B).
compare_(ult, _, X, Y, B) :- reify(X < Y, B).
compare_(ule, _, X, Y, B) :- reify(X =< Y, B).
compare_(ugt, _, X, Y, B) :- reify(X > Y, B).
compare_(uge, _, X, Y, B) :- reify(X >= Y, B).
compare_(slt, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), reify(SX < SY, B).
compare_(sle, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), reify(SX =< SY, B).
compare_(sgt, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), reify(SX > SY, B).
compare_(sge, K, X, Y, B) :- signed(K, X, SX), signed(K, Y, SY), reify(SX >= SY, B).

signed(K, U, S) :-
    modulus(K, M), half(K, H),
    sext(M, H, U, S).

% S is the two's-complement reading of the low bits of U, for a field of
% modulus M with sign threshold H.
sext(M, H, U, S) :- integer(U), !,
    L is U mod M,
    ( L >= H -> S is L - M ; S = L ).
sext(M, H, U, S) :-
    L #= U mod M,
    Neg in 0..1,
    Neg #<==> (L #>= H),
    S #= L - Neg * M.

extend(sb, X, S) :- sext(256, 128, X, S).
extend(ub, X, S) :- ev(S, X mod 256).
extend(sh, X, S) :- sext(65536, 32768, X, S).
extend(uh, X, S) :- ev(S, X mod 65536).
extend(sw, X, S) :- sext(4294967296, 2147483648, X, S).
extend(uw, X, S) :- ev(S, X mod 4294967296).

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
    extend(T, U, S), modulus(K, M), ev(R, S mod M).

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
   check. Cap is none, obj(Base) for a writable object, ro(Base) for
   read-only data, fn(F) for a function object (zero size, so every
   access fails the bounds check) or ext(Name) for a symbol defined
   outside the module, which the interpreter cannot follow. */
checked(mem(_, Rs, _, _), A, Cap, Size, Kind, Align, Res) :-
    must_be(integer, A),
    (   Cap == none -> Res = trap(null_capability)
    ;   Cap = fn(_) -> Res = trap(out_of_bounds)
    ;   Cap = ext(N)
    ->  format(atom(Msg), 'cannot interpret an access to external $~w', [N]),
        throw(nanofil_error(Msg))
    ;   ( Cap = obj(Base) ; Cap = ro(Base) ), memberchk(Base-End, Rs),
        (   A >= Base, A + Size =< End
        ->  (   Kind == write, Cap = ro(_) -> Res = trap(readonly)
            ;   A mod Align =:= 0 -> Res = ok
            ;   Res = trap(misaligned)
            )
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
le_value([X|Xs], U) :- le_value(Xs, U1), ev(U, X + 256 * U1).

le_bytes(0, _, []) :- !.
le_bytes(W, X, [B|Bs]) :-
    ev(B, X mod 256),
    ev(X1, X // 256),
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

/* initial_memory(+Mode, +M, -Globals, -Mem): lay out every data
   definition, each in its own region, and fill in its bytes. Globals maps
   a name to its address, or in filc mode to a pointer value: data objects
   are 16-aligned with their size rounded up to 8, as Fil-C's are, and
   each function gets an address and a fn capability. */
initial_memory(plain, module(Items), G, mem(Bytes, Rs, Stack, Aux)) :-
    empty_assoc(Aux),
    data_base(D0),
    empty_assoc(G0),
    layout(Items, D0, G0, G, [], Rs),
    empty_assoc(B0),
    foldl(fill(G), Items, B0, Bytes),
    stack_base(Stack).
initial_memory(filc, module(Items), G, mem(Bytes, Rs, Stack, Aux)) :-
    data_base(D0),
    empty_assoc(G0),
    foldl(filc_layout, Items, D0-G0-[], _-G-Rs),
    empty_assoc(B0), empty_assoc(A0),
    foldl(filc_fill(G), Items, B0-A0, Bytes-Aux),
    stack_base(Stack).

filc_layout(data(Name, Lk, _, Items), A0-G0-Rs0, A-G-[Base-End|Rs0]) :-
    Base is (A0 + 15) // 16 * 16,
    foldl(item_size, Items, 0, Size),
    End is Base + (Size + 7) // 8 * 8,
    ( Lk = ro(_) -> Cap = ro(Base) ; Cap = obj(Base) ),
    put_assoc(Name, G0, ptr(Base, Cap), G),
    A is End + 16.
filc_layout(func(Name, _, _, _, _), A0-G0-Rs, A-G-Rs) :-
    Base is (A0 + 15) // 16 * 16,
    put_assoc(Name, G0, ptr(Base, fn(Name)), G),
    A is Base + 16.

filc_fill(G, data(Name, _, _, Items), B0-A0, B-A) :- !,
    get_assoc(Name, G, ptr(Base, _)),
    foldl(filc_item(G), Items, Base-B0-A0, _-B-A).
filc_fill(_, func(_, _, _, _, _), S, S).

filc_item(G, item(p, sym(S, Off)), At-B0-A0, At1-B-A) :- !,
    (   At mod 8 =:= 0 -> true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    (   get_assoc(S, G, ptr(SA, Cap)) -> true ; SA = 0, Cap = ext(S) ),
    U is (SA + Off) mod 18446744073709551616,
    le_bytes(8, U, Bs),
    bytes_out(Bs, At, B0, B),
    put_assoc(At, A0, Cap, A),
    At1 is At + 8.
filc_item(G, I, At-B0-A, At1-B-A) :-
    item_bytes(G, I, Bs),
    bytes_out(Bs, At, B0, B),
    length(Bs, N), At1 is At + N.

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
outcome_text(rets(_), 'ret tuple') :- !.
outcome_text(ret, ret).
outcome_text(hlt, hlt).
outcome_text(ub(Why), T) :- format(atom(T), 'ub ~w', [Why]).
outcome_text(trap(Why), T) :- format(atom(T), 'trap ~w', [Why]).
outcome_text(out_of_fuel, out_of_fuel).
