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
      trap(Reason)    a Fil-C check failed (filc mode only)
      out_of_fuel     executed Fuel blocks without finishing

    Arithmetic and branches are CLP(Z) constraints, so the relation runs
    in every direction: Args and Outcome can both be partially unknown.
    Known values take a fast path (is/2 and if-then-else), which gives
    the same answers; only unknown values pay for constraints.
    Memory addresses and allocation sizes must be known when an access or
    alloc runs; otherwise the run raises an instantiation error, which is
    incomplete but never wrong.

    Memory is mem(Bytes, Regions, Next, Aux): an assoc from address to
    byte, the list of live Base-End regions, the next free stack address,
    and (filc mode) the capabilities stored in memory. A byte nobody wrote
    is a fresh variable in 0..255, so reading uninitialized memory gives
    an unknown value rather than a made-up one. In plain mode a
    function's allocations die when it returns, and addresses are never
    reused, so use after return is an out-of-bounds access.

    The run state is s(Mem, Fuel). Inside a function the interpreter
    carries ctx(Fns, Globals, Blocks, Ret, Mode): the prepared functions,
    the address of each global, the function's blocks by label, its
    return class and the module mode.
*/
:- module(interp, [run/5, prepare/2, run_prepared/5, outcome_text/2]).

:- use_module(library(clpz)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(library(dif)).
:- use_module(ir).

run(M, Fn, Args, Fuel, Outcome) :-
    prepare(M, Prepared),
    run_prepared(Prepared, Fn, Args, Fuel, Outcome).

% The initial memory holds integers only, so runs can share it.
prepare(M, prep(Fns, Globals, Mode, Mem0)) :-
    module_mode(M, Mode),
    initial_memory(Mode, M, Globals, Mem0),
    M = module(Items),
    findall(Name-fn(Ret, Params, Entry, BlockMap),
            ( member(func(Name, _, Ret, Params, Blocks), Items),
              Blocks = [blk(Entry, _, _, _)|_],
              findall(Label-Block,
                      ( member(Block, Blocks),
                        Block = blk(Label, _, _, _)
                      ),
                      LabelBlocks),
              list_to_assoc(LabelBlocks, BlockMap) ),
            NameFns),
    list_to_assoc(NameFns, Fns).

run_prepared(prep(Fns, Globals, Mode, Mem0), Fn, Args, Fuel, Outcome) :-
    get_assoc(Fn, Fns, fn(_, Params, _, _)),
    maplist(arg_in_range, Params, Args),
    call_fn(Fns, Globals, Mode, Fn, Args, s(Mem0, Fuel), Outcome, _).

arg_in_range(par(p, _), ptr(_, _)) :- !.
arg_in_range(par(K, _), A) :-
    modulus(K, Mod),
    Top #= Mod - 1,
    A in 0..Top.

% In plain mode a callee's allocations die when it returns; in filc mode
% every allocation is a heap object that lives on.
call_fn(Fns, Globals, Mode, Fn, Args, S0, Out, S) :-
    (   get_assoc(Fn, Fns, fn(Ret, Params, Entry, Blocks)) -> true
    ;   format(atom(Msg), 'cannot interpret a call to external $~w', [Fn]),
        throw(nanofil_error(Msg))
    ),
    empty_assoc(Env0),
    foldl(bind_param, Params, Args, Env0, Env),
    Ctx = ctx(Fns, Globals, Blocks, Ret, Mode),
    exec_block(Ctx, Entry, none, Env, S0, Out, S1),
    S0 = s(mem(_, Regions, _, _), _),
    S1 = s(mem(Bytes, _, Next, Aux), Fuel),
    (   Mode == plain -> S = s(mem(Bytes, Regions, Next, Aux), Fuel)
    ;   S = S1
    ).

bind_param(par(_, t(N)), X, Env0, Env) :- put_assoc(N, Env0, X, Env).

% Concrete fast path: when every operand is known, plain arithmetic and
% if-then-else give the same answers as the constraints, without
% propagators or choice points. Unknown operands still get constraints.
int_is(R, Expr) :- ( ground(Expr) -> R is Expr ; R #= Expr ).

% reify(+Test, ?B): B is 1 if Test holds, else 0 (reified when unknown).
reify(Test, B) :-
    (   ground(Test) -> ( call(Test) -> B = 1 ; B = 0 )
    ;   B in 0..1,
        reify_constraint(Test, B)
    ).

reify_constraint(X =:= Y, B) :- B #<==> (X #= Y).
reify_constraint(X =\= Y, B) :- B #<==> (X #\= Y).
reify_constraint(X < Y, B) :- B #<==> (X #< Y).
reify_constraint(X =< Y, B) :- B #<==> (X #=< Y).
reify_constraint(X > Y, B) :- B #<==> (X #> Y).
reify_constraint(X >= Y, B) :- B #<==> (X #>= Y).

%% Blocks

% exec_block(+Ctx, +Label, +Pred, +Env0, +S0, -Out, -S): run the block
% Label, entered from Pred, and everything after it. Each block costs one
% unit of fuel.
exec_block(Ctx, Label, Pred, Env0, s(Mem, Fuel0), Out, S) :-
    (   Fuel0 =:= 0 -> Out = out_of_fuel, S = s(Mem, Fuel0)
    ;   Fuel1 is Fuel0 - 1,
        Ctx = ctx(_, _, Blocks, _, _),
        get_assoc(Label, Blocks, blk(_, Phis, Insts, Jump)),
        exec_phis(Phis, Ctx, Pred, Env0, Env0, Env1),
        exec_insts(Insts, Ctx, Env1, s(Mem, Fuel1), Result),
        after_insts(Result, Jump, Ctx, Label, Out, S)
    ).

% Phis read the environment as it was on entry, then all bind at once.
exec_phis([], _, _, _, Env, Env).
exec_phis([phi(t(D), K, Pairs)|Phis], Ctx, Pred, EntryEnv, Env0, Env) :-
    memberchk(Pred-V, Pairs),
    read_value(K, V, Ctx, EntryEnv, X),
    put_assoc(D, Env0, X, Env1),
    exec_phis(Phis, Ctx, Pred, EntryEnv, Env1, Env).

after_insts(cont(Env, S0), Jump, Ctx, Label, Out, S) :-
    exec_jump(Jump, Ctx, Label, Env, S0, Out, S).
after_insts(stop(Out, S), _, _, _, Out, S).

exec_jump(jmp(L), Ctx, From, Env, S0, Out, S) :-
    exec_block(Ctx, L, From, Env, S0, Out, S).
exec_jump(jnz(V, L1, L2), Ctx, From, Env, S0, Out, S) :-
    read_value(w, V, Ctx, Env, X),
    (   integer(X) -> ( X =\= 0 -> L = L1 ; L = L2 )
    ;   X #\= 0, L = L1
    ;   X #= 0, L = L2
    ),
    exec_block(Ctx, L, From, Env, S0, Out, S).
exec_jump(ret(V), Ctx, _, Env, S, ret(X), S) :-
    Ctx = ctx(_, _, _, K, _),
    read_value(K, V, Ctx, Env, X).
exec_jump(rets(Vs), Ctx, _, Env, S, rets(Xs), S) :-
    Ctx = ctx(_, _, _, tuple(Ks), _),
    maplist(read_at(Ctx, Env), Ks, Vs, Xs).
exec_jump(ret, _, _, _, S, ret, S).
exec_jump(hlt, _, _, _, S, hlt, S).

%% Instructions

% exec_insts(+Insts, +Ctx, +Env0, +S0, -Result): Result is cont(Env, S)
% when every instruction ran, or stop(Outcome, S) when one ended the run.
exec_insts([], _, Env, S, cont(Env, S)).
exec_insts([Inst|Insts], Ctx, Env0, S0, Result) :-
    exec_inst(Inst, Ctx, Env0, S0, Result0),
    exec_insts_after(Result0, Insts, Ctx, Result).

exec_insts_after(cont(Env, S), Insts, Ctx, Result) :-
    exec_insts(Insts, Ctx, Env, S, Result).
exec_insts_after(stop(Out, S), _, _, stop(Out, S)).

exec_inst(ins(t(D), K, Op, Args), Ctx, Env0, S0, Result) :-
    Ctx = ctx(_, _, _, _, Mode),
    op_arg_classes(Op, K, Mode, ArgClasses),
    maplist(read_at(Ctx, Env0), ArgClasses, Args, Xs),
    eval_op(Op, K, Mode, Xs, S0, Res, S),
    bind_result(Res, D, Env0, S, Result).
exec_inst(store(Width, V, A), Ctx, Env, s(Mem0, Fuel), Result) :-
    Ctx = ctx(_, _, _, _, Mode),
    (   memberchk(Width, [l, p]) -> ValueClass = Width ; ValueClass = w ),
    read_value(ValueClass, V, Ctx, Env, X),
    addr_class(Mode, AddrClass),
    read_value(AddrClass, A, Ctx, Env, Addr),
    store_bytes(Mode, Width, Mem0, Addr, X, Res, Mem),
    store_result(Res, Env, s(Mem, Fuel), Result).
exec_inst(call(Res, glo(F), Args), Ctx, Env0, S0, Result) :-
    Ctx = ctx(Fns, Globals, _, _, Mode),
    maplist(read_arg(Ctx, Env0), Args, Xs),
    call_fn(Fns, Globals, Mode, F, Xs, S0, Out, S),
    call_result(Out, Res, Env0, S, Result).
exec_inst(call(Res, t(N), Args), Ctx, Env0, S0, Result) :-
    Ctx = ctx(Fns, Globals, _, _, Mode),
    read_value(p, t(N), Ctx, Env0, ptr(A, Cap)),
    maplist(read_arg(Ctx, Env0), Args, Xs),
    (   Cap = fn(F),
        get_assoc(F, Globals, ptr(FnAddr, _)),
        A == FnAddr
    ->  get_assoc(F, Fns, fn(Ret, Params, _, _)),
        indirect_call(Ret, Params, Res, Args, Xs, Ys, Conv),
        (   Conv = trap(Why) -> Result = stop(trap(Why), S0)
        ;   call_fn(Fns, Globals, Mode, F, Ys, S0, Out0, S),
            convert_return(Conv, Out0, Out),
            call_result(Out, Res, Env0, S, Result)
        )
    ;   Cap = ext(F)
    ->  format(atom(Msg), 'cannot interpret a call to external $~w', [F]),
        throw(nanofil_error(Msg))
    ;   Result = stop(trap(not_a_function), S0)
    ).

/* indirect_call(+CalleeRet, +Params, +Res, +Args, +Xs, -Ys, -Conv): a
   call through a function pointer. When the classes the call site passes
   and expects give the callee's signature (w and l are the same word), it
   is a direct call. Otherwise it goes through the callee's generic entry:
   each argument and result word is 8 bytes with its lower beside it, so
   a p word read as an integer is its address and an integer read as p
   has no capability. Too few arguments, or fewer result words than the
   call site reads, fail the generic entry's size checks. Conv is same,
   conv(CallerWords, CalleeWords) or trap(Why). */
indirect_call(Ret, Params, Res, Args, Xs, Ys, Conv) :-
    length(Params, NParams),
    length(Args, NArgs),
    result_words(Res, CallerWords),
    return_words(Ret, CalleeWords),
    length(CallerWords, NCallerWords),
    length(CalleeWords, NCalleeWords),
    findall(K, member(par(K, _), Params), ParamClasses),
    findall(K, member(arg(K, _), Args), ArgClasses),
    (   NArgs < NParams -> Conv = trap(argument_size)
    ;   NCallerWords > NCalleeWords -> Conv = trap(return_size)
    ;   length(Xs1, NParams), append(Xs1, _, Xs),
        length(ArgClasses1, NParams), append(ArgClasses1, _, ArgClasses),
        maplist(generic_word, ArgClasses1, ParamClasses, Xs1, Ys),
        (   maplist(word_class, CallerWords, WordClasses),
            maplist(word_class, CalleeWords, WordClasses)
        ->  Conv = same
        ;   Conv = conv(CallerWords, CalleeWords)
        )
    ).

% The classes of the words a call site reads and a function returns.
result_words(void, []).
result_words(to(_, K), [K]).
result_words(tuple(Tos), Ks) :- findall(K, member(to(_, K), Tos), Ks).

return_words(void, []) :- !.
return_words(tuple(Ks), Ks) :- !.
return_words(K, [K]).

word_class(p, p) :- !.
word_class(_, int).

% generic_word(+From, +To, +X, -Y): a word written at class From and
% read at class To through the generic entry.
generic_word(K, K, X, X) :- !.
generic_word(p, _, ptr(A, _), A) :- !.
generic_word(_, p, X, ptr(X, none)) :- !.
generic_word(_, _, X, X).

convert_return(same, Out, Out).
convert_return(conv(CallerWords, CalleeWords), Out0, Out) :-
    (   outcome_words(Out0, Xs0)
    ->  length(CallerWords, N),
        length(Xs, N), append(Xs, _, Xs0),
        length(CalleeWords1, N), append(CalleeWords1, _, CalleeWords),
        maplist(generic_word, CalleeWords1, CallerWords, Xs, Ys),
        outcome_words(Out, Ys)
    ;   Out = Out0
    ).

outcome_words(ret, []).
outcome_words(ret(X), [X]).
outcome_words(rets(Xs), Xs) :- Xs = [_, _|_].

read_at(Ctx, Env, K, V, X) :- read_value(K, V, Ctx, Env, X).
read_arg(Ctx, Env, arg(K, V), X) :- read_value(K, V, Ctx, Env, X).

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
    int_is(Y, X mod Mod),
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
    modulus(K, Mod),
    int_is(Y, X mod Mod),
    put_assoc(D, Env0, Y, Env).

% Reading a value at class K takes its low bits(K) bits. read_value_/5
% indexes on the value.
read_value(K, V, Ctx, Env, X) :- read_value_(V, K, Ctx, Env, X).

read_value_(t(N), K, _, Env, X) :-
    (   get_assoc(N, Env, X0) -> true
    ;   format(atom(Msg), 'read of %~w before any assignment', [N]),
        throw(nanofil_error(Msg))
    ),
    (   K == p -> X = X0
    ;   modulus(K, Mod),
        int_is(X, X0 mod Mod)
    ).
read_value_(c(N), K, _, _, X) :-
    modulus(K, Mod),
    A is N mod Mod,
    (   K == p -> X = ptr(A, none) ; X = A ).
read_value_(glo(N), _, ctx(_, Globals, _, _, Mode), _, X) :-
    (   get_assoc(N, Globals, X0) -> X = X0
    ;   Mode == filc -> X = ptr(0, ext(N))
    ).

%% Operations

% eval_op(+Op, +K, +Mode, +Args, +S0, -Res, -S): Res is val(X), ub(Why)
% or trap(Why).
eval_op(load(p), _, filc, [ptr(A, Cap)], s(Mem0, Fuel), Res, s(Mem, Fuel)) :- !,
    check_access(Mem0, A, Cap, 8, read, 8, Res0),
    (   Res0 == ok
    ->  load_bytes(filc, Mem0, A, 8, val(U), Mem),
        Mem = mem(_, _, _, Aux),
        (   get_assoc(A, Aux, C) -> true ; C = none ),
        Res = val(ptr(U, C))
    ;   Mem = Mem0, Res = Res0
    ).
eval_op(load(T), K, Mode, [A0], s(Mem0, Fuel), Res, s(Mem, Fuel)) :- !,
    load_type(T, Size, Ext),
    (   Mode == filc
    ->  A0 = ptr(A, Cap),
        check_access(Mem0, A, Cap, Size, read, 1, Res0)
    ;   A = A0, Res0 = ok
    ),
    (   Res0 == ok
    ->  load_bytes(Mode, Mem0, A, Size, Loaded, Mem),
        load_value(Loaded, Ext, K, Res)
    ;   Mem = Mem0, Res = Res0
    ).
eval_op(alloc(Align), _, Mode, [Size], s(Mem0, Fuel), val(P),
        s(Mem, Fuel)) :- !,
    alloc(Mode, Mem0, Align, Size, Base, Mem),
    (   Mode == filc -> P = ptr(Base, obj(Base)) ; P = Base ).
eval_op(Op, K, _, Xs, S, Res, S) :-
    alu(Op, K, Xs, Res).

% Pointer arithmetic keeps the capability. ptoi drops it; itop has none.
alu(add, p, [ptr(A, C), X], val(ptr(R, C))) :- !,
    modulus(l, M), int_is(R, (A + X) mod M).
alu(sub, p, [ptr(A, C), X], val(ptr(R, C))) :- !,
    modulus(l, M), int_is(R, (A - X) mod M).
alu(ptoi, _, [ptr(A, _)], val(A)).
alu(itop, _, [X], val(ptr(X, none))).

alu(add, K, [X, Y], val(R)) :- modulus(K, M), int_is(R, (X + Y) mod M).
alu(sub, K, [X, Y], val(R)) :- modulus(K, M), int_is(R, (X - Y) mod M).
alu(mul, K, [X, Y], val(R)) :- modulus(K, M), int_is(R, (X * Y) mod M).
alu(neg, K, [X], val(R)) :- modulus(K, M), int_is(R, (-X) mod M).
alu(copy, _, [X], val(X)).
alu(and, _, [X, Y], val(R)) :- int_is(R, X /\ Y).
alu(or, _, [X, Y], val(R)) :- int_is(R, X \/ Y).
alu(xor, _, [X, Y], val(R)) :- int_is(R, xor(X, Y)).
alu(udiv, _, [X, Y], Res) :- unsigned_division(X, Y, X // Y, Res).
alu(urem, _, [X, Y], Res) :- unsigned_division(X, Y, X mod Y, Res).
alu(div, K, [X, Y], Res) :- signed_division(K, X, Y, //, Res).
alu(rem, K, [X, Y], Res) :- signed_division(K, X, Y, rem, Res).
alu(shl, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P),
    modulus(K, M),
    int_is(R, (X * P) mod M).
alu(shr, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P),
    int_is(R, X // P).
alu(sar, K, [X, Y], val(R)) :-
    shift_factor(K, Y, P),
    signed(K, X, SX),
    modulus(K, M),
    int_is(R, (SX div P) mod M).
alu(ext(T), K, [X], val(R)) :-
    extend(T, X, S),
    modulus(K, M),
    int_is(R, S mod M).
alu(cmp(Cond, CK), _, [X, Y], val(B)) :- compare_cond(Cond, CK, X, Y, B).

unsigned_division(_, Y, Expr, Res) :-
    (   integer(Y)
    ->  (   Y =:= 0 -> Res = ub(division_by_zero)
        ;   int_is(R, Expr), Res = val(R)
        )
    ;   Y #= 0, Res = ub(division_by_zero)
    ;   Y #\= 0, int_is(R, Expr), Res = val(R)
    ).

% x86 idiv traps on both a zero divisor and the one quotient that
% overflows, so both are undefined here.
signed_division(K, X, Y, Fn, Res) :-
    signed(K, X, SX),
    signed(K, Y, SY),
    half(K, H),
    Min is -H,
    (   integer(SX), integer(SY)
    ->  (   SY =:= 0 -> Res = ub(division_by_zero)
        ;   SY =:= -1, SX =:= Min -> Res = ub(division_overflow)
        ;   modulus(K, M),
            division(Fn, SX, SY, Q),
            R is Q mod M,
            Res = val(R)
        )
    ;   SY #= 0, Res = ub(division_by_zero)
    ;   SY #= -1, SX #= Min, Res = ub(division_overflow)
    ;   SY #\= 0, #\ (SY #= -1 #/\ SX #= Min),
        modulus(K, M),
        division(Fn, SX, SY, Q),
        R #= Q mod M,
        Res = val(R)
    ).

division(//, X, Y, Q) :- int_is(Q, X // Y).
division(rem, X, Y, Q) :- int_is(Q, X rem Y).

% The shift count is taken modulo the class width.
shift_factor(K, Y, P) :-
    class_bits(K, Bits),
    int_is(C, Y mod Bits),
    int_is(P, 2 ^ C).

compare_cond(eq, _, X, Y, B) :- reify(X =:= Y, B).
compare_cond(ne, _, X, Y, B) :- reify(X =\= Y, B).
compare_cond(ult, _, X, Y, B) :- reify(X < Y, B).
compare_cond(ule, _, X, Y, B) :- reify(X =< Y, B).
compare_cond(ugt, _, X, Y, B) :- reify(X > Y, B).
compare_cond(uge, _, X, Y, B) :- reify(X >= Y, B).
compare_cond(slt, K, X, Y, B) :- signed_pair(K, X, Y, SX, SY), reify(SX < SY, B).
compare_cond(sle, K, X, Y, B) :- signed_pair(K, X, Y, SX, SY), reify(SX =< SY, B).
compare_cond(sgt, K, X, Y, B) :- signed_pair(K, X, Y, SX, SY), reify(SX > SY, B).
compare_cond(sge, K, X, Y, B) :- signed_pair(K, X, Y, SX, SY), reify(SX >= SY, B).

signed_pair(K, X, Y, SX, SY) :-
    signed(K, X, SX),
    signed(K, Y, SY).

signed(K, U, S) :-
    modulus(K, M),
    half(K, H),
    sign_extend(M, H, U, S).

% sign_extend(+M, +H, ?U, ?S): S is the two's-complement reading of the
% low bits of U, for a field of modulus M with sign threshold H.
sign_extend(M, H, U, S) :- integer(U), !,
    L is U mod M,
    (   L >= H -> S is L - M ; S = L ).
sign_extend(M, H, U, S) :-
    L #= U mod M,
    Neg in 0..1,
    Neg #<==> (L #>= H),
    S #= L - Neg * M.

extend(sb, X, S) :- sign_extend(256, 128, X, S).
extend(ub, X, S) :- int_is(S, X mod 256).
extend(sh, X, S) :- sign_extend(65536, 32768, X, S).
extend(uh, X, S) :- int_is(S, X mod 65536).
extend(sw, X, S) :- sign_extend(4294967296, 2147483648, X, S).
extend(uw, X, S) :- int_is(S, X mod 4294967296).

% load_type(+T, -Size, -Ext): a load of type T reads Size bytes and
% extends them with Ext.
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
    extend(T, U, S),
    modulus(K, M),
    int_is(R, S mod M).

%% Memory: mem(Bytes, Regions, Next, Aux)
%
% Aux is used in filc mode only: it maps an 8-aligned address to the
% capability a storep left there. An integer store leaves it alone, as
% Fil-C's aux array does.

% In plain mode an access outside every live region is undefined. In filc
% mode the access was checked against its capability already.
load_bytes(Mode, mem(Bytes0, Rs, Next, Aux), A, Size, Res,
           mem(Bytes, Rs, Next, Aux)) :-
    must_be(integer, A),
    (   ( Mode == filc ; in_live_region(Rs, A, Size) )
    ->  read_bytes(Size, Mode, A, Bytes0, Bytes, Read),
        le_value(Read, U),
        Res = val(U)
    ;   Bytes = Bytes0,
        Res = ub(out_of_bounds(A, Size))
    ).

store_bytes(plain, Width, mem(Bytes0, Rs, Next, Aux), A, X, Res,
            mem(Bytes, Rs, Next, Aux)) :-
    width_bytes(Width, Size),
    must_be(integer, A),
    (   in_live_region(Rs, A, Size)
    ->  le_bytes(Size, X, Written),
        write_bytes(Written, A, Bytes0, Bytes),
        Res = ok
    ;   Bytes = Bytes0,
        Res = ub(out_of_bounds(A, Size))
    ).
store_bytes(filc, Width, Mem0, ptr(A, Cap), X, Res, Mem) :-
    width_bytes(Width, Size),
    (   Width == p -> Align = 8, X = ptr(V, VCap) ; Align = 1, V = X ),
    check_access(Mem0, A, Cap, Size, write, Align, Res),
    (   Res == ok
    ->  Mem0 = mem(Bytes0, Rs, Next, Aux0),
        le_bytes(Size, V, Written),
        write_bytes(Written, A, Bytes0, Bytes),
        (   Width == p -> put_assoc(A, Aux0, VCap, Aux) ; Aux = Aux0 ),
        Mem = mem(Bytes, Rs, Next, Aux)
    ;   Mem = Mem0
    ).

/* check_access(+Mem, +A, +Cap, +Size, +Kind, +Align, -Res): Fil-C's
   access check. Cap is none, obj(Base) for a writable object, ro(Base)
   for read-only data, fn(F) for a function object (zero size, so every
   access fails the bounds check) or ext(Name) for a symbol defined
   outside the module, which the interpreter cannot follow. */
check_access(mem(_, Rs, _, _), A, Cap, Size, Kind, Align, Res) :-
    must_be(integer, A),
    (   Cap == none -> Res = trap(null_capability)
    ;   Cap = fn(_) -> Res = trap(out_of_bounds)
    ;   Cap = ext(N)
    ->  format(atom(Msg), 'cannot interpret an access to external $~w', [N]),
        throw(nanofil_error(Msg))
    ;   ( Cap = obj(Base) ; Cap = ro(Base) ),
        memberchk(Base-End, Rs),
        (   A >= Base, A + Size =< End
        ->  (   Kind == write, Cap = ro(_) -> Res = trap(readonly)
            ;   A mod Align =:= 0 -> Res = ok
            ;   Res = trap(misaligned)
            )
        ;   Res = trap(out_of_bounds)
        )
    ).

% The access [A, A+Size) lies inside one live region. A and the regions
% are integers here, so the if-then-else above is sound.
in_live_region(Rs, A, Size) :-
    member(Base-End, Rs),
    A >= Base, A + Size =< End, !.

% An unwritten byte is unknown in plain mode and zero in filc mode, since
% Fil-C allocations are zeroed.
read_bytes(0, _, _, Bytes, Bytes, []) :- !.
read_bytes(N, Mode, A, Bytes0, Bytes, [X|Xs]) :-
    (   get_assoc(A, Bytes0, X) -> Bytes1 = Bytes0
    ;   Mode == filc -> X = 0, Bytes1 = Bytes0
    ;   X in 0..255, put_assoc(A, Bytes0, X, Bytes1)
    ),
    A1 is A + 1,
    N1 is N - 1,
    read_bytes(N1, Mode, A1, Bytes1, Bytes, Xs).

write_bytes([], _, Bytes, Bytes).
write_bytes([X|Xs], A, Bytes0, Bytes) :-
    put_assoc(A, Bytes0, X, Bytes1),
    A1 is A + 1,
    write_bytes(Xs, A1, Bytes1, Bytes).

% Little-endian.
le_value([], 0).
le_value([X|Xs], U) :- le_value(Xs, U1), int_is(U, X + 256 * U1).

le_bytes(0, _, []) :- !.
le_bytes(N, X, [B|Bs]) :-
    int_is(B, X mod 256),
    int_is(X1, X // 256),
    N1 is N - 1,
    le_bytes(N1, X1, Bs).

% Allocations are aligned, and a 16-byte gap separates them so a small
% overrun cannot land in a neighbour.
alloc(Mode, mem(Bytes, Rs, Next0, Aux), Align0, Size, Base,
      mem(Bytes, [Base-End|Rs], Next, Aux)) :-
    must_be(integer, Size),
    (   Mode == filc -> Align = 16 ; Align = Align0 ),
    Base is (Next0 + Align - 1) // Align * Align,
    End is Base + Size,
    Next is End + 16.

stack_base(4294967296).
data_base(65536).

/* initial_memory(+Mode, +M, -Globals, -Mem): lay out every data
   definition, each in its own region, and fill in its bytes. Globals maps
   a name to its address, or in filc mode to a pointer value: data objects
   are 16-aligned with their size rounded up to 8, as Fil-C's are, and
   each function gets an address and a fn capability. */
initial_memory(plain, module(Items), Globals, mem(Bytes, Rs, Stack, Aux)) :-
    empty_assoc(Aux),
    data_base(DataBase),
    empty_assoc(Globals0),
    plain_layout(Items, DataBase, Globals0, Globals, [], Rs),
    empty_assoc(Bytes0),
    foldl(plain_fill(Globals), Items, Bytes0, Bytes),
    stack_base(Stack).
initial_memory(filc, module(Items), Globals, mem(Bytes, Rs, Stack, Aux)) :-
    data_base(DataBase),
    empty_assoc(Globals0),
    foldl(filc_layout, Items, DataBase-Globals0-[], _-Globals-Rs),
    empty_assoc(Bytes0),
    empty_assoc(Aux0),
    foldl(filc_fill(Globals), Items, Bytes0-Aux0, Bytes-Aux),
    stack_base(Stack).

plain_layout([], _, Globals, Globals, Rs, Rs).
plain_layout([Item|Items], A0, Globals0, Globals, Rs0, Rs) :-
    (   Item = data(Name, _, Align, DataItems)
    ->  Base is (A0 + Align - 1) // Align * Align,
        foldl(item_size, DataItems, 0, Size),
        End is Base + Size,
        put_assoc(Name, Globals0, Base, Globals1),
        Rs1 = [Base-End|Rs0],
        A1 is End + 16
    ;   Globals1 = Globals0, Rs1 = Rs0, A1 = A0
    ),
    plain_layout(Items, A1, Globals1, Globals, Rs1, Rs).

plain_fill(Globals, data(Name, _, _, Items), Bytes0, Bytes) :- !,
    get_assoc(Name, Globals, A),
    maplist(item_bytes(Globals), Items, ItemBytes),
    append(ItemBytes, DataBytes),
    write_bytes(DataBytes, A, Bytes0, Bytes).
plain_fill(_, func(_, _, _, _, _), Bytes, Bytes).

filc_layout(data(Name, Linkage, _, Items), A0-Globals0-Rs0,
            A-Globals-[Base-End|Rs0]) :-
    Base is (A0 + 15) // 16 * 16,
    foldl(item_size, Items, 0, Size),
    End is Base + (Size + 7) // 8 * 8,
    (   Linkage = ro(_) -> Cap = ro(Base) ; Cap = obj(Base) ),
    put_assoc(Name, Globals0, ptr(Base, Cap), Globals),
    A is End + 16.
filc_layout(func(Name, _, _, _, _), A0-Globals0-Rs, A-Globals-Rs) :-
    Base is (A0 + 15) // 16 * 16,
    put_assoc(Name, Globals0, ptr(Base, fn(Name)), Globals),
    A is Base + 16.

filc_fill(Globals, data(Name, _, _, Items), Bytes0-Aux0, Bytes-Aux) :- !,
    get_assoc(Name, Globals, ptr(Base, _)),
    foldl(filc_fill_item(Globals), Items, Base-Bytes0-Aux0, _-Bytes-Aux).
filc_fill(_, func(_, _, _, _, _), State, State).

filc_fill_item(Globals, item(p, sym(S, Off)), At-Bytes0-Aux0,
               At1-Bytes-Aux) :- !,
    (   At mod 8 =:= 0 -> true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    (   get_assoc(S, Globals, ptr(SymAddr, Cap)) -> true
    ;   SymAddr = 0, Cap = ext(S)
    ),
    U is (SymAddr + Off) mod 18446744073709551616,
    le_bytes(8, U, Written),
    write_bytes(Written, At, Bytes0, Bytes),
    put_assoc(At, Aux0, Cap, Aux),
    At1 is At + 8.
filc_fill_item(Globals, Item, At-Bytes0-Aux, At1-Bytes-Aux) :-
    item_bytes(Globals, Item, Written),
    write_bytes(Written, At, Bytes0, Bytes),
    length(Written, N),
    At1 is At + N.

item_size(zero(N), Size0, Size) :- Size is Size0 + N.
item_size(item(b, str(Cs)), Size0, Size) :- !,
    unescape(Cs, Bs),
    length(Bs, N),
    Size is Size0 + N.
item_size(item(W, _), Size0, Size) :-
    width_bytes(W, N),
    Size is Size0 + N.

item_bytes(_, zero(N), Bs) :- length(Bs, N), maplist(=(0), Bs).
item_bytes(_, item(b, str(Cs)), Bs) :- !, unescape(Cs, Bs).
item_bytes(_, item(W, c(N)), Bs) :-
    width_bytes(W, Size),
    Bits is Size * 8,
    U is N mod (1 << Bits),
    le_bytes(Size, U, Bs).
item_bytes(Globals, item(l, sym(S, Off)), Bs) :-
    get_assoc(S, Globals, A),
    U is A + Off,
    le_bytes(8, U, Bs).

% GNU as string escapes that QBE passes through.
unescape([], []).
unescape(['\\', C|Cs], [B|Bs]) :- !,
    escape_code(C, Cs, B, Rest),
    unescape(Rest, Bs).
unescape([C|Cs], [B|Bs]) :- char_code(C, B), unescape(Cs, Bs).

% escape_code(+C, +Cs, -Code, -Rest): the byte the escape \C... names,
% with Rest the characters after it (up to two more octal digits).
escape_code(n, Cs, 10, Cs) :- !.
escape_code(t, Cs, 9, Cs) :- !.
escape_code(r, Cs, 13, Cs) :- !.
escape_code('\\', Cs, 92, Cs) :- !.
escape_code('"', Cs, 34, Cs) :- !.
escape_code(D, Cs, B, Rest) :-
    octal_digit(D, V0),
    octal_more(Cs, V0, 2, B, Rest).

octal_more([D|Cs], V0, N, V, Rest) :- N > 0, octal_digit(D, X), !,
    V1 is V0 * 8 + X,
    N1 is N - 1,
    octal_more(Cs, V1, N1, V, Rest).
octal_more(Cs, V, _, V, Cs).

octal_digit(D, V) :- char_code(D, C), C >= 0'0, C =< 0'7, V is C - 0'0.

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
