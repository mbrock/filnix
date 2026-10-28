/*  Relational semantics of the IR (ir.pl): the outcome of running a
    function of a module, as a relation that runs in every direction,
    so that arguments and outcome can both be partially unknown.

    ## Entry points

    | Predicate | Does |
    |---|---|
    | `run(+Module, +Fn, ?(Args), +Fuel, ?(Outcome))` | prepares Module, then runs Fn |
    | `module_prepared(+Module, -Prepared)` | the module's mode, initial memory, and indexes of its functions and blocks |
    | `run_prepared(+Prepared, +Fn, ?(Args), +Fuel, ?(Outcome))` | runs Fn of a prepared module |

    Prepare once to run many times. Args are integers or CLP(Z)
    variables, one per parameter, in the range of the parameter's class
    (`ptr(Addr, Cap)` for a `p` parameter).

    ## Outcomes

    | Outcome | Means |
    |---|---|
    | `ret(V)` | returned V (an integer or constrained variable) |
    | `rets([X1, X2])` | returned a tuple |
    | `ret` | returned from a void function |
    | `unreachable` | executed `unreachable` |
    | `ub(Reason)` | undefined behaviour: `division_by_zero`, `division_overflow`, `float_conversion` (an invalid float-to-integer conversion), or in plain mode `out_of_bounds(A, Size)`, a memory access outside every live allocation |
    | `trap(Reason)` | a Fil-C check failed (filc mode only): `null_capability`, `out_of_bounds`, `misaligned`, `readonly`, `not_a_function`, `argument_size`, `return_size`, `invalid_free`, `double_free` |
    | `unchecked(Reason)` | a raw access (checked stage, ir.pl) that its capability does not allow: a check is missing or too weak, which only a broken pass produces. It is neither ub nor a trap, so it refines nothing. |
    | `out_of_fuel` | executed Fuel blocks without finishing |

    ## Unknown values

    Integer arithmetic and branches are CLP(Z) constraints, so the
    relation runs in every direction. Known values take a fast path
    (is/2 and if-then-else), which gives the same answers; only unknown
    values pay for constraints.

    Memory addresses, allocation sizes and capabilities must be known
    when an access, `alloc` or indirect call uses them; otherwise the run
    raises an instantiation error, which is incomplete but never wrong.

    Float values are concrete unsigned IEEE bits. Float arithmetic uses
    ieee.pl's integer-only SSE2 semantics, not CLP(Z) or host floats;
    unknown float inputs also raise an instantiation error.

    ## Memory

    Memory is `mem(Bytes, Regions, Next, Aux)`:

    | Part | Is |
    |---|---|
    | Bytes | an assoc from address to byte |
    | Regions | `region(Base, End, Kind, Life)` objects; Kind is stack, heap or global, Life is live or freed |
    | Next | the next allocation address; addresses are never reused |
    | Aux | in filc mode, the capabilities stored in memory |

    A byte nobody wrote is, in plain mode, a fresh variable in 0..255,
    so reading uninitialized memory gives an unknown value rather than a
    made-up one; in filc mode it is 0, since Fil-C zeroes allocations.

    In plain mode a function's allocations die when it returns, and
    addresses are never reused, so use after return is an out-of-bounds
    access. In filc mode allocations outlive their function. External
    `call(void, global(free), [arg(p, P)])` invalidates P's heap object:
    End becomes Base and Life becomes freed. A live zero-sized object
    also has End = Base, but may be freed once. Bytes and stored lowers
    stay intact; every alias consults the same region's current bounds.
    Module-defined functions take precedence over this external adapter.

    A capability's Base is stable identity, never recovered from address
    bits. All exposed capabilities for an object have the same rights
    (`obj(Base)` or `ro(Base)`); snapshot initialization is private until
    its readonly capability is published. Memory-using injected pointer
    arguments must obey these invariants and name existing objects.

    This is the deterministic explicit-free subset, not a GC simulator:
    no reclamation, concurrent or signal-handler frees, or rewriting dead
    lowers to the runtime's free singleton. Unknown external effects and
    addresses remain outside the oracle's domain. It does not justify
    check elimination or safepoint motion (docs/lifetime.md).

    ## Run state

    The run state is `s(Mem, Fuel)`; each block costs one unit of Fuel.
    Inside a function the interpreter carries
    `ctx(Fns, Globals, Blocks, Ret, Mode, Locals)`:

    | Part | Is |
    |---|---|
    | Fns | the prepared functions |
    | Globals | the address of each global |
    | Blocks | the function's blocks by label |
    | Ret | its return class |
    | Mode | the module mode |
    | Locals | this invocation's local names and fresh object identities, bound at local_alloc |

    A block is entered `from(Pred)`, Pred the label of the block that
    jumped to it, or at `entry`.

    ## Variable names

    | Name | Is |
    |---|---|
    | K | a class |
    | V | an IR value: `tmp(N)`, `const(N)` or `global(N)` |
    | X | a run-time value: an integer, a constrained variable, or in filc mode `ptr(Addr, Cap)` |
    | Env | the assoc from temporary to run-time value |
    | S | a run state |
    | Out | an outcome |
    | Res | a partial result: `val(X)`, `ok`, `ub(Why)`, `trap(Why)` or `unchecked(Why)` |

    Env0/Env and S0/S are the state before and after.
*/
:- module(interp, [run/5, module_prepared/2, run_prepared/5, outcome_text/2]).

:- use_module(library(clpz)).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(error)).
:- use_module(ir).
:- use_module(ieee).
:- use_module(cfg, [edge_label/2]).
:- use_module(provenance, [code_items/2]).

%! run(+M, +Fn, ?Args, +Fuel, ?Outcome) is nondet.
%
%  Outcome is the result of calling the function Fn of module M on Args
%  and executing at most Fuel blocks. With unknown Args each solution
%  constrains them to the inputs that take one path; see
%  run_prepared/5.

run(M, Fn, Args, Fuel, Outcome) :-
    module_prepared(M, Prepared),
    run_prepared(Prepared, Fn, Args, Fuel, Outcome).

%! module_prepared(+M, -Prepared) is det.
%
%  Prepared is M ready to run: its mode, the address of each global, its
%  initial memory, and its functions and their blocks indexed by name and
%  label. The initial memory holds integers only, so runs can share it.

module_prepared(M0, prep(Fns, Globals, Mode, Mem0)) :-
    M0 = module(All), code_items(All, Items), M = module(Items),
    module_mode(M, Mode),
    initial_memory(Mode, M, Globals, Mem0),
    findall(Name-fn(Ret, Params, Entry, BlockMap),
            ( member(func(Name, _, Ret, Params, Blocks), Items),
              Blocks = [block(Entry, _, _, _)|_],
              findall(Label-Block,
                      ( member(Block, Blocks),
                        Block = block(Label, _, _, _)
                      ),
                      LabelBlocks),
              list_to_assoc(LabelBlocks, BlockMap) ),
            NameFns),
    list_to_assoc(NameFns, Fns).

%! run_prepared(+Prepared, +Fn, ?Args, +Fuel, ?Outcome) is nondet.
%
%  Outcome is the result of calling Fn of the prepared module on Args
%  within Fuel blocks. Args is constrained to the ranges of Fn's
%  parameter classes. Where a branch or a division depends on an unknown
%  value (an argument, or a byte nobody wrote), there is one solution per
%  case, each constraining that value; comparisons are reified instead.
%  When every such value is known the outcome is unique, though the run
%  may leave a choice point, so callers use once/1. Fails when the module
%  defines no Fn. Throws nanofil_error when the run needs what the
%  interpreter does not model (a symbol the module does not define, a
%  temporary read before any assignment), and an instantiation error
%  when an address, allocation size or capability is unknown.

run_prepared(prep(Fns, Globals, Mode, Mem0), Fn, Args, Fuel, Outcome) :-
    get_assoc(Fn, Fns, fn(_, Params, _, Blocks)),
    ( assoc_to_values(Blocks, Bs), variadic_func(func(_, _, _, _, Bs))
    -> length(Params, N), length(Fixed, N), append(Fixed, _, Args)
    ; Fixed = Args ),
    maplist(arg_in_range, Params, Fixed),
    call_outcome(Fns, Globals, Mode, Fn, Args, s(Mem0, Fuel), Outcome, _).

% arg_in_range(+Param, ?X): X is a value of Param's class.
arg_in_range(param(K, _), X) :- class_arg(K, X).

% class_arg(+K, ?X): X is an argument of class K. A p argument is
% ptr(Addr, Cap), or an integer address with no pointer term (main.pl's
% canonical arguments): a defaulty case that comes from outside this
% module, so the cut stays. An unknown p argument is ptr(_, _).
class_arg(w, X) :- int_arg_in_range(w, X).
class_arg(l, X) :- int_arg_in_range(l, X).
class_arg(s, X) :- must_be(integer, X), int_arg_in_range(s, X).
class_arg(d, X) :- must_be(integer, X), int_arg_in_range(d, X).
class_arg(p, X) :-
    (   X = ptr(_, _) -> true
    ;   int_arg_in_range(p, X)
    ).

int_arg_in_range(K, X) :-
    modulus(K, Mod),
    Top #= Mod - 1,
    X in 0..Top.

% call_outcome(+Fns, +Globals, +Mode, +Fn, +Xs, +S0, -Out, -S): calling
% Fn on Xs in state S0 ends with Out in state S. In plain mode a
% callee's allocations die when it returns; in filc mode every
% allocation is a heap object that lives until explicitly freed.
call_outcome(Fns, Globals, Mode, Fn, Args, S0, Out, S) :-
    (   get_assoc(Fn, Fns, fn(Ret, Params, Entry, Blocks)) -> true
    ;   format(atom(Msg), 'cannot interpret a call to external ~w', [Fn]),
        throw(nanofil_error(Msg))
    ),
    empty_assoc(Env0),
    length(Params, NParams), length(Fixed, NParams), append(Fixed, _, Args),
    foldl(param_arg_env, Params, Fixed, Env0, Env1),
    entry_snapshot(Blocks, Args, Env1, Env, S0, SEntry),
    assoc_to_values(Blocks, Bs),
    local_objects(func(Fn, local, Ret, Params, Bs), Objects),
    findall(Name-_, member(Name-_, Objects), LocalPairs),
    list_to_assoc(LocalPairs, Locals),
    Ctx = ctx(Fns, Globals, Blocks, Ret, Mode, Locals),
    block_outcome(Ctx, Entry, entry, Env, SEntry, Out, S1),
    assoc_to_values(Locals, Bases),
    invalidate_locals(Bases, S1, S2),
    S0 = s(mem(_, Regions, _, _), _),
    returned_state(Mode, Regions, S2, S).

% Keep identities, bytes and aux, but end just this invocation's stack
% lifetimes in the latest state. A trap may precede a declaration; its
% unbound Base is not authority to select and invalidate another object.
invalidate_locals([], S, S).
invalidate_locals([Base|Bases], s(mem(Bytes, Rs0, Next, Aux), Fuel), S) :-
    ( integer(Base)
    -> select(region(Base, _, stack, live), Rs0, Rest),
       Rs = [region(Base, Base, stack, freed)|Rest]
    ; Rs = Rs0 ),
    invalidate_locals(Bases, s(mem(Bytes, Rs, Next, Aux), Fuel), S).

% returned_state(+Mode, +Regions, +S1, -S): S is the caller's state after
% a callee that ended in S1, Regions the caller's live regions.
returned_state(plain, Regions, s(mem(Bytes, _, Next, Aux), Fuel),
               s(mem(Bytes, Regions, Next, Aux), Fuel)).
returned_state(filc, _, S, S).

param_arg_env(param(_, tmp(N)), X, Env0, Env) :- put_assoc(N, Env0, X, Env).

entry_snapshot(Blocks, Args, Env0, Env, s(Mem0, Fuel), s(Mem, Fuel)) :-
    assoc_to_values(Blocks, Bs),
    ( variadic_func(func(_, _, _, _, Bs))
    -> args_snapshot(Args, Mem0, Snapshot, Mem),
       put_assoc(hidden(va_snapshot), Env0, Snapshot, Env)
    ; Env = Env0, Mem = Mem0 ).

% promote_cc_to_heap returns null for an empty argument packet. This is
% distinct from alloc(0), which creates an ordinary zero-sized object.
args_snapshot([], Mem, ptr(0, none), Mem).
args_snapshot([X|Xs], Mem0, ptr(Base, ro(Base)), Mem) :-
    length([X|Xs], N), Size is N * 8,
    alloc_base(filc, Mem0, 16, Size, Base, Mem1),
    snapshot_values([X|Xs], Base, Base, Mem1, Mem).

snapshot_values([], _, _, Mem, Mem).
snapshot_values([X|Xs], A, Base, Mem0, Mem) :-
    ( nonvar(X), X = ptr(_, _) -> W = p ; W = l ),
    % Snapshot initialization precedes publishing its readonly capability.
    store_res(filc, W, Mem0, ptr(A, obj(Base)), X, ok, Mem1),
    A1 is A + 8, snapshot_values(Xs, A1, Base, Mem1, Mem).

% int_is(?R, +Expr): R is the value of the integer expression Expr.
% Concrete fast path: when every operand is known, plain arithmetic and
% if-then-else give the same answers as the constraints, without
% propagators or choice points. Unknown operands still get constraints.
% The ground/1 test reads the instantiation, but both branches state the
% same relation, so the program stays sound for partially known Expr.
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

% block_outcome(+Ctx, +Label, +Pred, +Env0, +S0, -Out, -S): Out and S are
% the outcome and final state of running the block Label, entered from
% Pred (from(L) or entry), and everything after it. Each block costs one
% unit of fuel.
block_outcome(Ctx, Label, Pred, Env0, s(Mem, Fuel0), Out, S) :-
    (   Fuel0 =:= 0
    ->  Out = out_of_fuel,
        S = s(Mem, Fuel0)
    ;   Fuel1 is Fuel0 - 1,
        Ctx = ctx(_, _, Blocks, _, _, _),
        get_assoc(Label, Blocks, block(_, Phis, Insts, Jump)),
        phis_env(Phis, Ctx, Pred, Env0, Env0, Env1),
        insts_result(Insts, Ctx, Env1, s(Mem, Fuel1), Result),
        result_outcome(Result, Jump, Ctx, Label, Out, S)
    ).

% phis_env(+Phis, +Ctx, +Pred, +EntryEnv, +Env0, -Env): Env is Env0 with
% each phi of Phis bound to its value for the edge from Pred, read in
% EntryEnv. Phis read the environment as it was on entry, so they all
% bind at once. An entry block has no phis.
phis_env([], _, _, _, Env, Env).
phis_env([phi(tmp(D), K, Pairs)|Phis], Ctx, from(Pred), EntryEnv, Env0, Env) :-
    memberchk(Pred-V, Pairs),
    value_x(K, V, Ctx, EntryEnv, X),
    put_assoc(D, Env0, X, Env1),
    phis_env(Phis, Ctx, from(Pred), EntryEnv, Env1, Env).

% result_outcome(+Result, +Jump, +Ctx, +Label, -Out, -S): the block's
% Jump continues the run unless an instruction ended it.
result_outcome(cont(Env, S0), Jump, Ctx, Label, Out, S) :-
    jump_outcome(Jump, Ctx, Label, Env, S0, Out, S).
result_outcome(stop(Out, S), _, _, _, Out, S).

% jump_outcome(+Jump, +Ctx, +From, +Env, +S0, -Out, -S): Out is the
% outcome of Jump, ending block From, and everything after it. When the
% jnz condition is unknown, both edges are solutions, each constraining
% it; a known one takes the fast path.
% A pollcheck on the edge (poll(L)) changes nothing the interpreter
% models: explicit free calls run, but there are no asynchronous frees.
jump_outcome(goto(T), Ctx, From, Env, S0, Out, S) :-
    edge_label(T, L),
    block_outcome(Ctx, L, from(From), Env, S0, Out, S).
jump_outcome(branch(V, T1, T2), Ctx, From, Env, S0, Out, S) :-
    value_x(w, V, Ctx, Env, X),
    (   integer(X) -> ( X =\= 0 -> T = T1 ; T = T2 )
    ;   X #\= 0, T = T1
    ;   X #= 0, T = T2
    ),
    edge_label(T, L),
    block_outcome(Ctx, L, from(From), Env, S0, Out, S).
jump_outcome(ret(V), Ctx, _, Env, S, ret(X), S) :-
    Ctx = ctx(_, _, _, K, _, _),
    value_x(K, V, Ctx, Env, X).
jump_outcome(rets(Vs), Ctx, _, Env, S, rets(Xs), S) :-
    Ctx = ctx(_, _, _, tuple(Ks), _, _),
    maplist(class_value_x(Ctx, Env), Ks, Vs, Xs).
jump_outcome(ret, _, _, _, S, ret, S).
jump_outcome(unreachable, _, _, _, S, unreachable, S).

%% Instructions

% insts_result(+Insts, +Ctx, +Env0, +S0, -Result): Result is cont(Env, S)
% when every instruction ran, or stop(Outcome, S) when one ended the run.
insts_result([], _, Env, S, cont(Env, S)).
insts_result([Inst|Insts], Ctx, Env0, S0, Result) :-
    inst_result(Inst, Ctx, Env0, S0, Result0),
    rest_result(Result0, Insts, Ctx, Result).

% rest_result(+Result0, +Insts, +Ctx, -Result): Result is the result of
% the instructions Insts after one whose result is Result0.
rest_result(cont(Env, S), Insts, Ctx, Result) :-
    insts_result(Insts, Ctx, Env, S, Result).
rest_result(stop(Out, S), _, _, stop(Out, S)).

% inst_result(+Inst, +Ctx, +Env0, +S0, -Result): Result is cont(Env, S)
% after Inst, or stop(Outcome, S) when it ends the run.
inst_result(loc(_, _), _, Env, S, cont(Env, S)) :- !.
inst_result(local_alloc(Name, Size), ctx(_, _, _, _, filc, Locals), Env,
            s(Mem0, Fuel), cont(Env, s(Mem, Fuel))) :-
    ( get_assoc(Name, Locals, Base), var(Base) -> true
    ; throw(nanofil_error('duplicate or undeclared local allocation')) ),
    alloc_base(local, Mem0, 16, Size, Base, Mem).
inst_result(local_load(tmp(D), K, T, Name, Off), Ctx, Env, S0, Result) :-
    local_pointer(Ctx, Name, Off, P),
    load_op_res(T, K, filc, [P], S0, Res, S),
    res_result(Res, D, Env, S, Result).
inst_result(local_store(W, V, Name, Off), Ctx, Env, s(Mem0, Fuel), Result) :-
    local_pointer(Ctx, Name, Off, P),
    width_value_class(W, K), value_x(K, V, Ctx, Env, X),
    store_res(filc, W, Mem0, P, X, Res, Mem),
    store_res_result(Res, Env, s(Mem, Fuel), Result).
inst_result(let(tmp(D), a, check_local(Name, Off, Size, Rights, Align), []),
            Ctx, Env, s(Mem, Fuel), Result) :- !,
    local_pointer(Ctx, Name, Off, ptr(A, Cap)),
    access_res(Mem, A, Cap, Size, Rights, Align, Check),
    checked_res(Check, ptr(A, Cap), Res),
    res_result(Res, D, Env, s(Mem, Fuel), Result).
inst_result(flight(tmp(D), Op, Args, Lower), Ctx, Env0, S, Result) :-
    maplist(flight_arg_x(Ctx, Env0), Args, Xs),
    alu(Op, l, Xs, val(A)),
    flight_cap(Lower, Ctx, Env0, Cap),
    res_result(val(ptr(A, Cap)), D, Env0, S, Result).
inst_result(let(tmp(D), p, va_args, [const(Off)]), _, Env0, S, Result) :- !,
    get_assoc(hidden(va_snapshot), Env0, ptr(A, Cap)),
    B is (A + Off) mod 18446744073709551616,
    res_result(val(ptr(B, Cap)), D, Env0, S, Result).
inst_result(let(tmp(D), f, check_function, [V]), Ctx, Env0, S, Result) :- !,
    value_x(p, V, Ctx, Env0, P),
    function_check_res(P, Ctx, Check),
    checked_res(Check, P, Res),
    res_result(Res, D, Env0, S, Result).
inst_result(let(tmp(D), K, Op, Args), Ctx, Env0, S0, Result) :-
    Ctx = ctx(_, _, _, _, Mode, _),
    op_arg_classes(Op, K, Mode, ArgClasses),
    maplist(class_value_x(Ctx, Env0), ArgClasses, Args, Xs),
    op_res(Op, K, Mode, Xs, S0, Res, S),
    res_result(Res, D, Env0, S, Result).
inst_result(store(Width, V, A), Ctx, Env, s(Mem0, Fuel), Result) :-
    Ctx = ctx(_, _, _, _, Mode, _),
    width_value_class(Width, ValueClass),
    value_x(ValueClass, V, Ctx, Env, X),
    addr_class(Mode, AddrClass),
    value_x(AddrClass, A, Ctx, Env, Addr),
    store_res(Mode, Width, Mem0, Addr, X, Res, Mem),
    store_res_result(Res, Env, s(Mem, Fuel), Result).
% One thread and no atomic boxes: an atomic pointer store is a pointer
% store, and a fence does nothing observable.
inst_result(atomic_store(p, V, A), Ctx, Env, S, Result) :- !,
    inst_result(store(p, V, A), Ctx, Env, S, Result).
inst_result(fence, _, Env, S, cont(Env, S)) :- !.
inst_result(raw_store(Width, Off, V, A), Ctx, Env, s(Mem0, Fuel), Result) :-
    width_value_class(Width, ValueClass),
    value_x(ValueClass, V, Ctx, Env, X),
    value_x(a, A, Ctx, Env, ptr(B, Cap)),
    raw_address(B, Off, Addr),
    store_res(filc, Width, Mem0, ptr(Addr, Cap), X, Res0, Mem),
    raw_res(Res0, Res),
    store_res_result(Res, Env, s(Mem, Fuel), Result).
inst_result(raw_store_pointer(Off, V, A, Effects), Ctx, Env,
            s(Mem0, Fuel), Result) :-
    value_x(p, V, Ctx, Env, X),
    value_x(a, A, Ctx, Env, ptr(B, Cap)),
    raw_address(B, Off, Addr),
    access_res(Mem0, Addr, Cap, 8, write, 8, Check),
    pointer_store_effects_res(Check, Effects, Addr, X, Mem0, Res, Mem),
    store_res_result(Res, Env, s(Mem, Fuel), Result).
inst_result(call(Res, global(F), Args), Ctx, Env0, S0, Result) :-
    Ctx = ctx(Fns, Globals, _, _, Mode, _),
    maplist(arg_x(Ctx, Env0), Args, Xs),
    (   get_assoc(F, Fns, _)
    ->  call_outcome(Fns, Globals, Mode, F, Xs, S0, Out, S)
    ;   external_call_outcome(Mode, Globals, F, Res, Args, Xs, S0, Out, S)
    ),
    call_outcome_result(Out, Res, Env0, S, Result).
inst_result(call(Res, tmp(N), Args), Ctx, Env0, S0, Result) :-
    value_x(p, tmp(N), Ctx, Env0, ptr(A, Cap)),
    maplist(arg_x(Ctx, Env0), Args, Xs),
    function_check_res(ptr(A, Cap), Ctx, Check),
    checked_call_result(Check, Cap, Res, Args, Xs, Ctx, Env0, S0, Result).
inst_result(raw_call(Res, Callee, Args), Ctx, Env0, S0, Result) :-
    value_x(f, Callee, Ctx, Env0, ptr(A, Cap)),
    maplist(arg_x(Ctx, Env0), Args, Xs),
    function_check_res(ptr(A, Cap), Ctx, Check0),
    raw_res(Check0, Check),
    checked_call_result(Check, Cap, Res, Args, Xs, Ctx, Env0, S0, Result).

local_pointer(ctx(_, _, _, _, filc, Locals), Name, Off, ptr(A, obj(Base))) :-
    ( get_assoc(Name, Locals, Base), integer(Base) -> true
    ; throw(nanofil_error('local access before allocation')) ),
    A is Base + Off.

% Only libc free's ordinary signature is modeled. Resolution comes first:
% an in-module function is handled above; an in-module data symbol is not
% a function. Other signatures and external calls are explicit gaps, not
% silently failed relations or guessed libc effects.
external_call_outcome(filc, Globals, free, Res, Args, Xs,
                      s(Mem0, Fuel), Out, s(Mem, Fuel)) :- !,
    (   get_assoc(free, Globals, _)
    ->  Out = trap(not_a_function), Mem = Mem0
    ;   Res == void, Args = [arg(p, _)], Xs = [P]
    ->  free_res(P, Mem0, Freed, Mem), free_outcome(Freed, Out)
    ;   throw(nanofil_error('interpreter supports only void free(p)'))
    ).
external_call_outcome(_, _, F, _, _, _, _, _, _) :-
    format(atom(Msg), 'cannot interpret a call to external ~w', [F]),
    throw(nanofil_error(Msg)).

free_outcome(ok, ret).
free_outcome(trap(Why), trap(Why)).

% width_value_class(+Width, -K): a store of Width reads its value at K.
width_value_class(b, w).
width_value_class(h, w).
width_value_class(w, w).
width_value_class(l, l).
width_value_class(p, p).
width_value_class(s, s).
width_value_class(d, d).
width_value_class(x, x).

% function_check_res(+P, +Ctx, -Res): P designates a function only when
% it carries that function's capability at its exact callable address.
% An unknown address is not proof; an external symbol's kind is unknown
% to the interpreter, which must not guess that it names a function.
function_check_res(ptr(A, Cap), ctx(_, Globals, _, _, _, _), Res) :-
    must_be(callable, Cap),
    cap_function_res(Cap, A, Globals, Res).

cap_function_res(fn(F), A, Globals, Res) :-
    (   get_assoc(F, Globals, ptr(FnAddr, _)),
        A == FnAddr
    ->  Res = ok
    ;   Res = trap(not_a_function)
    ).
cap_function_res(ext(F), _, _, _) :-
    format(atom(Msg), 'cannot interpret a call to external ~w', [F]),
    throw(nanofil_error(Msg)).
cap_function_res(none, _, _, trap(not_a_function)).
cap_function_res(obj(_), _, _, trap(not_a_function)).
cap_function_res(ro(_), _, _, trap(not_a_function)).

% A target check authorizes the call, not its signature. Only a failed
% target check becomes unchecked in raw_call; ABI and callee traps keep
% their meaning. The conversions below are shared with unchecked call.
checked_call_result(ok, fn(F), Res, Args, Xs, Ctx, Env0, S0, Result) :-
    Ctx = ctx(Fns, Globals, _, _, Mode, _),
    get_assoc(F, Fns, fn(Ret, Params, _, Bs)),
    indirect_call_conv(Ret, Params, Res, Args, Xs, Fixed, Conv),
    assoc_to_values(Bs, Blocks),
    ( variadic_func(func(_, _, _, _, Blocks)), Conv \= trap(_)
    -> length(Params, NP), length(Prefix, NP), append(Prefix, Extra, Xs),
       append(Fixed, Extra, Ys)
    ; Ys = Fixed ),
    conv_call_result(Conv, Fns, Globals, Mode, F, Ys, Res, Env0, S0, Result).
checked_call_result(trap(Why), _, _, _, _, _, _, S, stop(trap(Why), S)).
checked_call_result(unchecked(Why), _, _, _, _, _, _, S, stop(unchecked(Why), S)).

% conv_call_result(+Conv, +Fns, +Globals, +Mode, +F, +Ys, +Res, +Env0,
% +S0, -Result): the result of an indirect call to F on Ys, with the
% call's conversion Conv.
conv_call_result(trap(Why), _, _, _, _, _, _, _, S0, stop(trap(Why), S0)).
conv_call_result(same, Fns, Globals, Mode, F, Ys, Res, Env0, S0, Result) :-
    call_outcome(Fns, Globals, Mode, F, Ys, S0, Out, S),
    call_outcome_result(Out, Res, Env0, S, Result).
conv_call_result(conv(CallerWords, CalleeWords), Fns, Globals, Mode, F, Ys,
                 Res, Env0, S0, Result) :-
    call_outcome(Fns, Globals, Mode, F, Ys, S0, Out0, S),
    converted_outcome(CallerWords, CalleeWords, Out0, Out),
    call_outcome_result(Out, Res, Env0, S, Result).

/* indirect_call_conv(+CalleeRet, +Params, +Res, +Args, +Xs, -Ys, -Conv):
   a call through a function pointer. When the classes the call site
   passes and expects give the callee's signature (w and l are the same
   word), it is a direct call. Otherwise it goes through the callee's
   generic entry: each argument and result word is 8 bytes with its lower
   beside it, so a p word read as an integer is its address and an
   integer read as p has no capability. Too few arguments, or fewer
   result words than the call site reads, fail the generic entry's size
   checks. Conv is same, conv(CallerWords, CalleeWords) or trap(Why). */
indirect_call_conv(Ret, Params, Res, Args, Xs, Ys, Conv) :-
    length(Params, NParams),
    length(Args, NArgs),
    result_words(Res, CallerWords),
    return_words(Ret, CalleeWords),
    length(CallerWords, NCallerWords),
    length(CalleeWords, NCalleeWords),
    findall(K, member(param(K, _), Params), ParamClasses),
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

% result_words(+Res, -Ks) and return_words(+Ret, -Ks): the classes of
% the words a call site reads and a function returns.
result_words(void, []).
result_words(result(_, K), [K]).
result_words(tuple(Tos), Ks) :- findall(K, member(result(_, K), Tos), Ks).

return_words(void, []).
return_words(tuple(Ks), Ks).
return_words(w, [w]).
return_words(l, [l]).
return_words(p, [p]).
return_words(s, [s]).
return_words(d, [d]).

% word_class(?K, ?Class): Class is p for p, and int for w and l, which
% are the same word.
word_class(w, int).
word_class(l, int).
word_class(p, p).
word_class(s, s).
word_class(d, d).

% generic_word(+From, +To, +X, -Y): Y is the word X written at class From
% and read at class To through the generic entry.
generic_word(w, To, X, Y) :- int_word_as(To, X, Y).
generic_word(l, To, X, Y) :- int_word_as(To, X, Y).
generic_word(p, To, X, Y) :- pointer_word_as(To, X, Y).
generic_word(s, To, X, Y) :- int_word_as(To, X, Y).
generic_word(d, To, X, Y) :- int_word_as(To, X, Y).

int_word_as(w, X, X).
int_word_as(l, X, X).
int_word_as(p, X, ptr(X, none)).
int_word_as(s, X, Y) :- word_at_class(s, X, Y).
int_word_as(d, X, Y) :- word_at_class(d, X, Y).

% A p word read as an integer is its address. An integer held at p (see
% class_arg/2) is its own address: the defaulty case keeps the
% if-then-else.
pointer_word_as(w, X, A) :- pointer_address(X, A).
pointer_word_as(l, X, A) :- pointer_address(X, A).
pointer_word_as(p, X, X).
pointer_word_as(s, X, Y) :- pointer_address(X, A), word_at_class(s, A, Y).
pointer_word_as(d, X, Y) :- pointer_address(X, A), word_at_class(d, A, Y).

pointer_address(X, A) :- ( X = ptr(A0, _) -> A = A0 ; A = X ).

% converted_outcome(+CallerWords, +CalleeWords, +Out0, -Out): Out is the
% callee's outcome Out0 as a call site that reads CallerWords reads it.
% An outcome that does not return passes unchanged.
converted_outcome(CallerWords, CalleeWords, Out0, Out) :-
    (   outcome_words(Out0, Xs0)
    ->  length(CallerWords, N),
        length(Xs, N), append(Xs, _, Xs0),
        length(CalleeWords1, N), append(CalleeWords1, _, CalleeWords),
        maplist(generic_word, CalleeWords1, CallerWords, Xs, Ys),
        outcome_words(Out, Ys)
    ;   Out = Out0
    ).

% outcome_words(?Out, ?Xs): the returning outcome Out returns the words
% Xs. Fails for an outcome that does not return.
outcome_words(ret, []).
outcome_words(ret(X), [X]).
outcome_words(rets(Xs), Xs) :- Xs = [_, _|_].

class_value_x(Ctx, Env, K, V, X) :- value_x(K, V, Ctx, Env, X).
arg_x(Ctx, Env, arg(K, V), X) :- value_x(K, V, Ctx, Env, X).

% res_result/5, store_res_result/4 and call_outcome_result/5 relate an
% operation's Res, or a callee's outcome, to the instruction's Result.
res_result(val(X), D, Env0, S, cont(Env, S)) :- put_assoc(D, Env0, X, Env).
res_result(ub(Why), _, _, S, stop(ub(Why), S)).
res_result(trap(Why), _, _, S, stop(trap(Why), S)).
res_result(unchecked(Why), _, _, S, stop(unchecked(Why), S)).

store_res_result(ok, Env, S, cont(Env, S)).
store_res_result(ub(Why), _, S, stop(ub(Why), S)).
store_res_result(trap(Why), _, S, stop(trap(Why), S)).
store_res_result(unchecked(Why), _, S, stop(unchecked(Why), S)).

call_outcome_result(ret(X), Res, Env0, S, cont(Env, S)) :-
    ret_env(Res, X, Env0, Env).
call_outcome_result(rets(Xs), Res, Env0, S, cont(Env, S)) :-
    rets_env(Res, Xs, Env0, Env).
call_outcome_result(ret, void, Env, S, cont(Env, S)).
call_outcome_result(unreachable, _, _, S, stop(unreachable, S)).
call_outcome_result(ub(Why), _, _, S, stop(ub(Why), S)).
call_outcome_result(trap(Why), _, _, S, stop(trap(Why), S)).
call_outcome_result(unchecked(Why), _, _, S, stop(unchecked(Why), S)).
call_outcome_result(out_of_fuel, _, _, S, stop(out_of_fuel, S)).

% ret_env(+Res, +X, +Env0, -Env) and rets_env(+Res, +Xs, +Env0, -Env):
% Env is Env0 with the returned word X, or words Xs, bound as the call
% site's Res reads them.
ret_env(result(T, K), X, Env0, Env) :- to_word_env(result(T, K), X, Env0, Env).
ret_env(void, _, Env, Env).

rets_env(tuple(Tos), Xs, Env0, Env) :- foldl(to_word_env, Tos, Xs, Env0, Env).
rets_env(void, _, Env, Env).

to_word_env(result(tmp(D), K), X0, Env0, Env) :-
    word_at_class(K, X0, X),
    put_assoc(D, Env0, X, Env).

% word_at_class(+K, ?X0, ?X): X is the word X0 taken at class K, its low
% bits(K) bits; a p word is itself.
word_at_class(w, X0, X) :- modulus(w, Mod), int_is(X, X0 mod Mod).
word_at_class(l, X0, X) :- modulus(l, Mod), int_is(X, X0 mod Mod).
word_at_class(p, X, X).
word_at_class(a, X, X).
word_at_class(f, X, X).
word_at_class(s, X0, X) :- must_be(integer, X0), X is X0 mod 4294967296.
word_at_class(d, X0, X) :- must_be(integer, X0), X is X0 mod 18446744073709551616.
word_at_class(x, X0, X) :- must_be(integer, X0), X is X0 mod (1 << 80).

% value_x(+K, +V, +Ctx, +Env, -X): X is the IR value V read at class K,
% which takes its low bits(K) bits. value_x_/5 indexes on the value. A
% symbol the module does not define is ptr(0, ext(Name)) in filc mode;
% in plain mode (which the validator rejects) the read fails.
value_x(K, V, Ctx, Env, X) :- value_x_(V, K, Ctx, Env, X).

value_x_(tmp(N), K, _, Env, X) :-
    (   get_assoc(N, Env, X0) -> true
    ;   format(atom(Msg), 'read of tmp(~w) before any assignment', [N]),
        throw(nanofil_error(Msg))
    ),
    word_at_class(K, X0, X).
value_x_(const(N), K, _, _, X) :-
    modulus(K, Mod),
    A is N mod Mod,
    constant_at_class(K, A, X).
value_x_(global(N), _, ctx(_, Globals, _, _, Mode, _), _, X) :-
    (   get_assoc(N, Globals, X0) -> X = X0
    ;   undefined_symbol(Mode, N, X)
    ).

% constant_at_class(+K, +A, -X): X is the constant A at class K; at p it
% is a pointer with no capability.
constant_at_class(w, A, A).
constant_at_class(l, A, A).
constant_at_class(p, A, ptr(A, none)).
constant_at_class(s, A, A).
constant_at_class(d, A, A).
constant_at_class(x, A, A).

undefined_symbol(filc, N, ptr(0, ext(N))).

% Flight's two components are read independently from the old
% environment. Projecting an address takes its low 64 bits; projecting
% a lower copies capability identity without inspecting it or its address.
flight_arg_x(Ctx, Env, address(P), X) :- !,
    value_x(p, P, Ctx, Env, ptr(A, _)),
    word_at_class(l, A, X).
flight_arg_x(Ctx, Env, V, X) :- value_x(l, V, Ctx, Env, X).

flight_cap(none, _, _, none).
flight_cap(lower(P), Ctx, Env, Cap) :- value_x(p, P, Ctx, Env, ptr(_, Cap)).

%% Operations

% op_res(+Op, +K, +Mode, +Args, +S0, -Res, -S): Res is val(X), ub(Why)
% or trap(Why). Op is an IR term (ir.pl).
% Commit before integer dispatch: float bits must never get CLP(Z)
% arithmetic, even if a caller asks for a different result on backtracking.
op_res(cmp(C, CK), _, _, [A, B], S, val(R), S) :-
    memberchk(CK, [s, d, x]), !, ieee_compare(CK, C, A, B, R).
op_res(Op, K, _, Xs, S, val(R), S) :-
    memberchk(K, [s, d, x]), memberchk(Op, [add, sub, mul, div, neg, copy]), !,
    float_arithmetic(Op, K, Xs, R).
op_res(Op, K, Mode, Xs, S0, Res, S) :-
    op_kind(Op, Kind),
    kind_res(Kind, Op, K, Mode, Xs, S0, Res, S).

% kind_res(+Kind, +Op, +K, +Mode, +Args, +S0, -Res, -S): as op_res/7, for
% Op of Kind. Loads and allocs use the memory; the rest is arithmetic.
kind_res(setjmp, _, _, _, _, _, _, _) :-
    throw(nanofil_error('interpreter does not support setjmp/nonlocal returns')).
kind_res(load, load(T), K, Mode, Args, S0, Res, S) :-
    load_op_res(T, K, Mode, Args, S0, Res, S).
kind_res(atomic_load, atomic_load(p), K, Mode, Args, S0, Res, S) :-
    load_op_res(p, K, Mode, Args, S0, Res, S).
kind_res(check, check(Lo, Hi, Rights, Align), a, filc, [ptr(A, Cap)],
         s(Mem, Fuel), Res, s(Mem, Fuel)) :-
    raw_address(A, Lo, B),
    Size is Hi - Lo,
    access_res(Mem, B, Cap, Size, Rights, Align, Res0),
    checked_res(Res0, ptr(A, Cap), Res).
kind_res(ld, raw_load(T, Off), K, filc, [ptr(A, Cap)], S0, Res, S) :-
    raw_address(A, Off, B),
    load_op_res(T, K, filc, [ptr(B, Cap)], S0, Res0, S),
    raw_res(Res0, Res).
kind_res(ld_pointer, raw_load_pointer(Off, Effects), p, filc, [ptr(A, Cap)],
         s(Mem0, Fuel), Res, s(Mem, Fuel)) :-
    raw_address(A, Off, B),
    access_res(Mem0, B, Cap, 8, read, 8, Check),
    pointer_load_effects_res(Check, Effects, B, Mem0, Res, Mem).
kind_res(alloc, alloc(Align), _, Mode, [Size], s(Mem0, Fuel), val(P),
         s(Mem, Fuel)) :-
    alloc_base(Mode, Mem0, Align, Size, Base, Mem),
    alloc_pointer(Mode, Base, P).
kind_res(va_arg, _, K, filc, [P], S0, Res, S) :-
    pointer_load_res(filc, [P], S0, Cursor, S1),
    va_cursor_res(Cursor, K, P, S1, Res, S).
kind_res(additive, Op, K, _, Xs, S, Res, S) :- additive_res(K, Op, Xs, Res).
kind_res(alu, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(shift, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(neg, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(copy, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(ptoi, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(itop, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(cmp, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(ext, Op, K, _, Xs, S, Res, S) :- alu(Op, K, Xs, Res).
kind_res(float_convert, ext(s), K, _, [X], S, val(R), S) :-
    ieee_convert(s, K, X, R).
kind_res(float_convert, ext(d), x, _, [X], S, val(R), S) :-
    ieee_convert(d, x, X, R).
kind_res(float_convert, truncd, s, _, [X], S, val(R), S) :-
    ieee_convert(d, s, X, R).
kind_res(float_convert, truncx, K, _, [X], S, val(R), S) :-
    ieee_convert(x, K, X, R).
kind_res(float_to_int, Op, K, _, [X], S, Res, S) :-
    float_integer(Op, K, X, Res).
kind_res(int_to_float, Op, K, _, [X], S, val(R), S) :-
    must_be(integer, X), integer_source(Op, X, N), ieee_from_int(K, N, R).
kind_res(cast, _, _, _, [X], S, val(X), S) :- must_be(integer, X).

float_arithmetic(copy, _, [X], X) :- must_be(integer, X).
float_arithmetic(neg, K, [X], R) :- ieee_neg(K, X, R).
float_arithmetic(Op, K, [X, Y], R) :- ieee_binary(K, Op, X, Y, R).

integer_source(swtof, X, N) :- signed(w, X, N).
integer_source(uwtof, X, X).
integer_source(sltof, X, N) :- signed(l, X, N).
integer_source(ultof, X, X).

float_integer(Op, K, X, Res) :-
    float_source(Op, From, Sign),
    modulus(K, M),
    ( Sign == signed -> Min is -(M // 2), Max is M // 2 - 1
    ; Min = 0, Max is M - 1 ),
    ( ieee_to_int(From, X, N), N >= Min, N =< Max
    -> R is N mod M, Res = val(R)
    ; Res = ub(float_conversion) ).

float_source(stosi, s, signed). float_source(stoui, s, unsigned).
float_source(dtosi, d, signed). float_source(dtoui, d, unsigned).
float_source(xtosi, x, signed). float_source(xtoui, x, unsigned).

% A va_arg of class K takes Step bytes at an Align-aligned cursor, as
% filc_get_next_ptr_bytes_for_va_arg does: a long double's cell is 16
% bytes at 16, of which it reads its 10.
va_cell(x, 16, 16) :- !.
va_cell(K, Size, 8) :- width_bytes(K, Size).

va_cursor_res(trap(Why), _, _, S, trap(Why), S).
va_cursor_res(val(ptr(A, Cap)), K, P, s(Mem0, Fuel), Res, S) :-
    va_cell(K, Step, Align), width_bytes(K, Size),
    Aligned is (A + Align - 1) // Align * Align,
    access_res(Mem0, Aligned, Cap, Step, read, 8, Check),
    va_checked_res(Check, K, P, Aligned, Size-Step, s(Mem0, Fuel), Res, S).

va_checked_res(trap(Why), _, _, _, _, S, trap(Why), S).
va_checked_res(ok, K, P, A, Size-Step, s(Mem0, Fuel), Res, s(Mem, Fuel)) :-
    Next is A + Step,
    store_res(filc, l, Mem0, P, Next, Store, Mem1),
    ( Store = trap(Why) -> Res = trap(Why), Mem = Mem1
    ; K == p -> pointer_access_load(ok, Mem1, A, Res, Mem)
    ; load_res(filc, Mem1, A, Size, Res, Mem) ).

% checked_res(+Res0, +P, -Res): a check whose access_res/7 is Res0
% yields P, proven, or traps.
checked_res(ok, P, val(P)).
checked_res(trap(Why), _, trap(Why)).

% raw_res(+Res0, -Res): a raw access is the access its check covers,
% made again without trapping: what would have trapped is unchecked.
raw_res(val(X), val(X)).
raw_res(ok, ok).
raw_res(ub(Why), ub(Why)).
raw_res(trap(Why), unchecked(Why)).

% raw_address(+A, +Off, -B): B is the address A plus the constant Off.
raw_address(A, Off, B) :- B is (A + Off) mod 18446744073709551616.

alloc_pointer(plain, Base, Base).
alloc_pointer(filc, Base, ptr(Base, obj(Base))).

% load_op_res(+T, +K, +Mode, +Args, +S0, -Res, -S): Res is the result of
% a load of type T at class K. A load reads Size bytes and extends them
% as T names; load(l) takes them as they are.
load_op_res(p, _, Mode, Args, S0, Res, S) :-
    pointer_load_res(Mode, Args, S0, Res, S).
load_op_res(l, _, Mode, Args, S0, Res, S) :-
    int_load_res(Mode, 8, Args, S0, Res, S).
load_op_res(s, _, Mode, Args, S0, Res, S) :-
    int_load_res(Mode, 4, Args, S0, Res, S).
load_op_res(d, _, Mode, Args, S0, Res, S) :-
    int_load_res(Mode, 8, Args, S0, Res, S).
load_op_res(x, _, Mode, Args, S0, Res, S) :-
    int_load_res(Mode, 10, Args, S0, Res, S).
load_op_res(sw, K, Mode, Args, S0, Res, S) :-
    ext_load_res(sw, 4, K, Mode, Args, S0, Res, S).
load_op_res(uw, K, Mode, Args, S0, Res, S) :-
    ext_load_res(uw, 4, K, Mode, Args, S0, Res, S).
load_op_res(sh, K, Mode, Args, S0, Res, S) :-
    ext_load_res(sh, 2, K, Mode, Args, S0, Res, S).
load_op_res(uh, K, Mode, Args, S0, Res, S) :-
    ext_load_res(uh, 2, K, Mode, Args, S0, Res, S).
load_op_res(sb, K, Mode, Args, S0, Res, S) :-
    ext_load_res(sb, 1, K, Mode, Args, S0, Res, S).
load_op_res(ub, K, Mode, Args, S0, Res, S) :-
    ext_load_res(ub, 1, K, Mode, Args, S0, Res, S).

% load(p) exists in filc mode only. It reads the word and the capability
% the last store(p, ...) left there, none if there was none.
pointer_load_res(filc, [ptr(A, Cap)], s(Mem0, Fuel), Res, s(Mem, Fuel)) :-
    access_res(Mem0, A, Cap, 8, read, 8, Res0),
    pointer_access_load(Res0, Mem0, A, Res, Mem).

pointer_access_load(ok, Mem0, A, val(ptr(U, C)), Mem) :-
    load_res(filc, Mem0, A, 8, val(U), Mem),
    Mem = mem(_, _, _, Aux),
    (   get_assoc(A, Aux, C) -> true ; C = none ).
pointer_access_load(trap(Why), Mem, _, trap(Why), Mem).

% Execute the supplied pointer-access protocol. Its local state keeps
% the aux word separate from the resolved lower and primary address;
% only the completed load publishes a pointer. Aux contains abstract
% capability identities, not native boxes, so resolution is identity.
pointer_load_effects_res(ok, Effects, A, Mem0, val(P), Mem) :-
    foldl(pointer_load_effect(A), Effects,
          loaded(none, ptr(0, none), Mem0), loaded(_, P, Mem)).
pointer_load_effects_res(trap(Why), _, _, Mem, unchecked(Why), Mem).

pointer_load_effect(A, aux_read, loaded(_, ptr(U, _), Mem),
                    loaded(C, ptr(U, C), Mem)) :-
    Mem = mem(_, _, _, Aux),
    ( get_assoc(A, Aux, C) -> true ; C = none ).
pointer_load_effect(_, lower_resolve, loaded(C, ptr(U, _), Mem),
                    loaded(C, ptr(U, C), Mem)).
% Fil-C's helper reads the address and the lower (or the box's pair) as
% one unit; with one thread that is aux_read then address_read.
pointer_load_effect(A, atomic_read, L0, L) :-
    pointer_load_effect(A, aux_read, L0, L1),
    pointer_load_effect(A, address_read, L1, L).
pointer_load_effect(A, address_read, loaded(C, ptr(_, Lower), Mem0),
                    loaded(C, ptr(U, Lower), Mem)) :-
    load_res(filc, Mem0, A, 8, val(U), Mem).

% The interpreter has no GC, aux allocation or asynchronous frees.
% Ensure/barrier/reload are therefore abstract identities, not a claim
% that native helpers cannot exit or fail. The observable writes still
% execute in list order: lower first, then primary bytes, without another
% bounds check after ensure-aux. Regions and Next are carried opaquely.
pointer_store_effects_res(ok, Effects, A, P, Mem0, ok, Mem) :-
    foldl(pointer_store_effect(A, P), Effects, Mem0, Mem).
pointer_store_effects_res(trap(Why), _, _, _, Mem, unchecked(Why), Mem).

pointer_store_effect(_, _, aux_ensure, Mem, Mem).
pointer_store_effect(_, _, lower_barrier, Mem, Mem).
pointer_store_effect(_, _, rooted_reload, Mem, Mem).
pointer_store_effect(A, P, atomic_write, Mem0, Mem) :-
    pointer_store_effect(A, P, lower_write, Mem0, Mem1),
    pointer_store_effect(A, P, address_write, Mem1, Mem).
pointer_store_effect(A, ptr(_, C), lower_write,
                     mem(Bytes, Rs, Next, Aux0), mem(Bytes, Rs, Next, Aux)) :-
    stored_aux(cap(C), A, Aux0, Aux).
pointer_store_effect(A, ptr(U, _), address_write,
                     mem(Bytes0, Rs, Next, Aux), mem(Bytes, Rs, Next, Aux)) :-
    le_bytes(8, U, Written),
    written_bytes(Written, A, Bytes0, Bytes).

ext_load_res(T, Size, K, Mode, Args, S0, Res, S) :-
    int_load_res(Mode, Size, Args, S0, Res0, S),
    extended_res(Res0, T, K, Res).

% extended_res(+Res0, +T, +K, -Res): Res is the loaded Res0 extended as
% T names and taken at class K.
extended_res(val(U), T, K, val(R)) :-
    extension(T, U, S),
    modulus(K, M),
    int_is(R, S mod M).
extended_res(ub(Why), _, _, ub(Why)).
extended_res(trap(Why), _, _, trap(Why)).

% int_load_res(+Mode, +Size, +Args, +S0, -Res, -S): Res is val(U), U the
% Size bytes at the address in Args, or why there is none.
int_load_res(Mode, Size, [A0], s(Mem0, Fuel), Res, s(Mem, Fuel)) :-
    address_access(Mode, A0, Mem0, Size, A, Res0),
    int_access_load(Res0, Mode, Mem0, A, Size, Res, Mem).

% address_access(+Mode, +A0, +Mem, +Size, -A, -Res): A is the address
% of the access value A0 and Res is ok when a Size-byte read there may
% go ahead. Fil-C checks the capability; plain mode checks the region
% when it reads.
address_access(plain, A, _, _, A, ok).
address_access(filc, ptr(A, Cap), Mem, Size, A, Res) :-
    access_res(Mem, A, Cap, Size, read, 1, Res).

int_access_load(ok, Mode, Mem0, A, Size, Res, Mem) :-
    load_res(Mode, Mem0, A, Size, Res, Mem).
int_access_load(trap(Why), _, Mem, _, _, trap(Why), Mem).

% additive_res(+K, +Op, +Xs, -Res): Res is the result of add or sub (Op)
% of class K on Xs. Pointer arithmetic keeps the capability.
additive_res(p, Op, [ptr(A, C), X], val(ptr(R, C))) :-
    modulus(l, M),
    pointer_offset(Op, A, X, M, R).
additive_res(w, Op, Xs, Res) :- alu(Op, w, Xs, Res).
additive_res(l, Op, Xs, Res) :- alu(Op, l, Xs, Res).

% pointer_offset(+Op, +A, +X, +M, -R): R is the address A plus (add) or
% minus (sub) X, modulo M.
pointer_offset(add, A, X, M, R) :- int_is(R, (A + X) mod M).
pointer_offset(sub, A, X, M, R) :- int_is(R, (A - X) mod M).

% alu(+Op, +K, +Xs, -Res): Res is the result of the arithmetic Op of
% class K on Xs; add and sub are integer here (additive_res/4). ptoi
% drops the capability; itop has none.
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
    extension(T, X, S),
    modulus(K, M),
    int_is(R, S mod M).
alu(cmp(Cond, CK), _, [X, Y], val(B)) :- cond_bit(Cond, CK, X, Y, B).

% unsigned_division(+X, +Y, +Expr, -Res): Res is val of Expr, or ub when
% the divisor Y is zero. An unknown Y gives both cases as solutions; a
% known one takes the fast path.
unsigned_division(_, Y, Expr, Res) :-
    (   integer(Y)
    ->  (   Y =:= 0 -> Res = ub(division_by_zero)
        ;   int_is(R, Expr), Res = val(R)
        )
    ;   Y #= 0, Res = ub(division_by_zero)
    ;   Y #\= 0, int_is(R, Expr), Res = val(R)
    ).

% x86 idiv traps on both a zero divisor and the one quotient that
% overflows, so both are undefined here. Known operands take the fast
% path; otherwise the three cases are disjoint constraints.
signed_division(K, X, Y, Fn, Res) :-
    signed(K, X, SX),
    signed(K, Y, SY),
    half_modulus(K, H),
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

% cond_bit(+Cond, +K, ?X, ?Y, ?B): B is 1 when X Cond Y holds at class
% K, else 0.
cond_bit(eq, _, X, Y, B) :- reify(X =:= Y, B).
cond_bit(ne, _, X, Y, B) :- reify(X =\= Y, B).
cond_bit(ult, _, X, Y, B) :- reify(X < Y, B).
cond_bit(ule, _, X, Y, B) :- reify(X =< Y, B).
cond_bit(ugt, _, X, Y, B) :- reify(X > Y, B).
cond_bit(uge, _, X, Y, B) :- reify(X >= Y, B).
cond_bit(slt, K, X, Y, B) :-
    signed_pair(K, X, Y, SX, SY),
    reify(SX < SY, B).
cond_bit(sle, K, X, Y, B) :-
    signed_pair(K, X, Y, SX, SY),
    reify(SX =< SY, B).
cond_bit(sgt, K, X, Y, B) :-
    signed_pair(K, X, Y, SX, SY),
    reify(SX > SY, B).
cond_bit(sge, K, X, Y, B) :-
    signed_pair(K, X, Y, SX, SY),
    reify(SX >= SY, B).

signed_pair(K, X, Y, SX, SY) :-
    signed(K, X, SX),
    signed(K, Y, SY).

% signed(+K, ?U, ?S): S is the two's-complement reading of U at class K.
signed(K, U, S) :-
    modulus(K, M),
    half_modulus(K, H),
    sign_extension(M, H, U, S).

% sign_extension(+M, +H, ?U, ?S): S is the two's-complement reading of
% the low bits of U, for a field of modulus M with sign threshold H. The
% first clause is the fast path for a known U; the cut commits to it, and
% the second clause states the same relation with constraints.
sign_extension(M, H, U, S) :-
    integer(U),
    !,
    L is U mod M,
    (   L >= H -> S is L - M ; S = L ).
sign_extension(M, H, U, S) :-
    L #= U mod M,
    Neg in 0..1,
    Neg #<==> (L #>= H),
    S #= L - Neg * M.

% extension(+T, ?X, ?S): S is the low bits of X that T names, sign- or
% zero-extended.
extension(sb, X, S) :- sign_extension(256, 128, X, S).
extension(ub, X, S) :- int_is(S, X mod 256).
extension(sh, X, S) :- sign_extension(65536, 32768, X, S).
extension(uh, X, S) :- int_is(S, X mod 65536).
extension(sw, X, S) :- sign_extension(4294967296, 2147483648, X, S).
extension(uw, X, S) :- int_is(S, X mod 4294967296).

%% Memory: mem(Bytes, Regions, Next, Aux)
%
% Each region(Base, End, Kind, Life) is shared by every capability with
% that Base. Only free changes a Fil-C object's bounds, monotonically
% to empty. Freed regions remain so zero-sized live objects and double
% frees are distinguishable. No reclamation or address reuse is modeled.
%
% Aux is used in filc mode only: it maps an 8-aligned address to the
% capability a store(p, ...) left there. An integer store leaves it alone, as
% Fil-C's aux array does.

% free_res(+P, +Mem0, -Res, -Mem): the pinned runtime's free_with_checks,
% object_for_deallocate and free_impl, for objects this interpreter owns.
% ext(_) has a placeholder address, not a known zero; it stays unsupported.
% Public run/5 also accepts integer p arguments: these have no capability.
free_res(A, Mem0, Res, Mem) :-
    integer(A), !,
    cap_free_res(none, A, Mem0, Res, Mem).
free_res(ptr(A, Cap), Mem0, Res, Mem) :-
    must_be(integer, A), must_be(callable, Cap),
    cap_free_res(Cap, A, Mem0, Res, Mem).

cap_free_res(ext(N), _, _, _, _) :-
    format(atom(Msg), 'cannot interpret free of external ~w', [N]),
    throw(nanofil_error(Msg)).
cap_free_res(none, A, Mem, Res, Mem) :-
    ( A =:= 0 -> Res = ok ; Res = trap(invalid_free) ).
cap_free_res(fn(_), A, Mem, Res, Mem) :-
    ( A =:= 0 -> Res = ok ; Res = trap(invalid_free) ).
cap_free_res(obj(Base), A, Mem0, Res, Mem) :-
    object_free_res(Base, A, Mem0, Res, Mem).
cap_free_res(ro(Base), A, Mem0, Res, Mem) :-
    object_free_res(Base, A, Mem0, Res, Mem).

% Null is a no-op even with an object's lower. Otherwise kind/address
% validation precedes the FREE test, as object_for_deallocate precedes
% free_impl. READONLY alone does not prevent deallocation of a heap object.
object_free_res(Base, A, mem(Bytes, Rs0, Next, Aux), Res,
                mem(Bytes, Rs, Next, Aux)) :-
    (   A =:= 0 -> Res = ok, Rs = Rs0
    ;   object_region(Base, Rs0, region(Base, End, Kind, Life)),
        (   Kind \== heap -> Res = trap(invalid_free), Rs = Rs0
        ;   A =\= Base -> Res = trap(invalid_free), Rs = Rs0
        ;   Life == freed -> Res = trap(double_free), Rs = Rs0
        ;   select(region(Base, End, Kind, Life), Rs0, Rest),
            Rs = [region(Base, Base, heap, freed)|Rest], Res = ok
        )
    ).

% object_region(+Base, +Rs, -Region): capabilities refer to registered
% identities. An injected unknown base is outside the interpreter domain,
% not authority for the live object that happens to contain its address.
object_region(Base, Rs, Region) :-
    must_be(integer, Base),
    (   memberchk(region(Base, End, Kind, Life), Rs)
    ->  Region = region(Base, End, Kind, Life)
    ;   throw(nanofil_error('capability names an unregistered object'))
    ).

% load_res(+Mode, +Mem0, +A, +Size, -Res, -Mem): Res is val(U), U the
% little-endian value of the Size bytes at A, or ub(...). In plain mode
% an access outside every live region is undefined. In filc mode the
% access was checked against its capability already. Mem is Mem0 with
% any unwritten byte read now made a fresh variable (plain mode).
load_res(Mode, mem(Bytes0, Rs, Next, Aux), A, Size, Res,
         mem(Bytes, Rs, Next, Aux)) :-
    must_be(integer, A),
    (   ( Mode == filc ; in_live_region(Rs, A, Size) )
    ->  length(Read, Size),
        bytes_at(Read, Mode, A, Bytes0, Bytes),
        le_value(Read, U),
        Res = val(U)
    ;   Bytes = Bytes0,
        Res = ub(out_of_bounds(A, Size))
    ).

% store_res(+Mode, +Width, +Mem0, +Addr, +X, -Res, -Mem): Mem is Mem0
% with X written at Addr as Width, when Res is ok.
store_res(plain, Width, mem(Bytes0, Rs, Next, Aux), A, X, Res,
          mem(Bytes, Rs, Next, Aux)) :-
    width_bytes(Width, Size),
    must_be(integer, A),
    (   in_live_region(Rs, A, Size)
    ->  le_bytes(Size, X, Written),
        written_bytes(Written, A, Bytes0, Bytes),
        Res = ok
    ;   Bytes = Bytes0,
        Res = ub(out_of_bounds(A, Size))
    ).
store_res(filc, Width, Mem0, ptr(A, Cap), X, Res, Mem) :-
    width_bytes(Width, Size),
    width_word(Width, X, V, Align, Stored),
    access_res(Mem0, A, Cap, Size, write, Align, Res),
    access_store(Res, Mem0, A, Size, V, Stored, Mem).

% width_word(+Width, ?X, ?V, -Align, -Stored): a Fil-C store of Width
% writes the integer V of the value X, needs alignment Align, and Stored
% is cap(C) for the capability C of a store(p, ...), or none.
width_word(b, V, V, 1, none).
width_word(h, V, V, 1, none).
width_word(w, V, V, 1, none).
width_word(l, V, V, 1, none).
width_word(s, V, V, 1, none).
width_word(d, V, V, 1, none).
width_word(x, V, V, 8, none).
width_word(p, ptr(V, C), V, 8, cap(C)).

% access_store(+Res, +Mem0, +A, +Size, +V, +Stored, -Mem): Mem is Mem0
% after a checked store with result Res.
access_store(ok, mem(Bytes0, Rs, Next, Aux0), A, Size, V, Stored,
             mem(Bytes, Rs, Next, Aux)) :-
    le_bytes(Size, V, Written),
    written_bytes(Written, A, Bytes0, Bytes),
    stored_aux(Stored, A, Aux0, Aux).
access_store(trap(_), Mem, _, _, _, _, Mem).

stored_aux(none, _, Aux, Aux).
stored_aux(cap(C), A, Aux0, Aux) :- put_assoc(A, Aux0, C, Aux).

/* access_res(+Mem, +A, +Cap, +Size, +Kind, +Align, -Res): Fil-C's access
   check, Res ok or trap(Why). Cap is none, obj(Base) for a writable
   object, ro(Base) for read-only data, fn(F) for a function object
   (zero size, so every access fails the bounds check) or ext(Name) for
   a symbol defined outside the module, which the interpreter cannot
   follow. Cap must be known: an unknown capability (an unknown p
   argument) raises an instantiation error, as an unknown address does.
   An unregistered Base is outside the interpreter's domain. */
access_res(mem(_, Rs, _, _), A, Cap, Size, Kind, Align, Res) :-
    must_be(integer, A),
    must_be(callable, Cap),
    cap_access_res(Cap, Rs, A, Size, Kind, Align, Res).

cap_access_res(none, _, _, _, _, _, trap(null_capability)).
cap_access_res(fn(_), _, _, _, _, _, trap(out_of_bounds)).
cap_access_res(ext(N), _, _, _, _, _, _) :-
    format(atom(Msg), 'cannot interpret an access to external ~w', [N]),
    throw(nanofil_error(Msg)).
cap_access_res(obj(Base), Rs, A, Size, _, Align, Res) :-
    object_region(Base, Rs, region(Base, End, _, _)),
    (   A >= Base, A + Size =< End
    ->  aligned_res(A, Align, Res)
    ;   Res = trap(out_of_bounds)
    ).
cap_access_res(ro(Base), Rs, A, Size, Kind, Align, Res) :-
    object_region(Base, Rs, region(Base, End, _, _)),
    (   A >= Base, A + Size =< End
    ->  readonly_access_res(Kind, A, Align, Res)
    ;   Res = trap(out_of_bounds)
    ).

readonly_access_res(read, A, Align, Res) :- aligned_res(A, Align, Res).
readonly_access_res(write, _, _, trap(readonly)).

aligned_res(A, Align, Res) :-
    (   A mod Align =:= 0 -> Res = ok ; Res = trap(misaligned) ).

% in_live_region(+Rs, +A, +Size): the access [A, A+Size) lies inside one
% live region. A and the regions are integers here, so the if-then-else
% in the callers is sound. The cut commits to the first such region.
in_live_region(Rs, A, Size) :-
    member(region(Base, End, _, live), Rs),
    A >= Base,
    A + Size =< End,
    !.

% bytes_at(?Xs, +Mode, +A, +Bytes0, -Bytes): Xs are the bytes at A,
% A+1, ... in Bytes0; Bytes is Bytes0 with each unwritten byte among
% them bound. An unwritten byte is unknown in plain mode and zero in filc
% mode, since Fil-C allocations are zeroed.
bytes_at([], _, _, Bytes, Bytes).
bytes_at([X|Xs], Mode, A, Bytes0, Bytes) :-
    (   get_assoc(A, Bytes0, X) -> Bytes1 = Bytes0
    ;   unwritten_byte(Mode, A, X, Bytes0, Bytes1)
    ),
    A1 is A + 1,
    bytes_at(Xs, Mode, A1, Bytes1, Bytes).

unwritten_byte(filc, _, 0, Bytes, Bytes).
unwritten_byte(plain, A, X, Bytes0, Bytes) :-
    X in 0..255,
    put_assoc(A, Bytes0, X, Bytes).

% written_bytes(+Xs, +A, +Bytes0, -Bytes): Bytes is Bytes0 with the bytes
% Xs at A, A+1, ...
written_bytes([], _, Bytes, Bytes).
written_bytes([X|Xs], A, Bytes0, Bytes) :-
    put_assoc(A, Bytes0, X, Bytes1),
    A1 is A + 1,
    written_bytes(Xs, A1, Bytes1, Bytes).

% le_value(+Bytes, ?U) and le_bytes(+N, ?X, -Bytes): U is the
% little-endian value of Bytes; Bytes are the N low bytes of X.
le_value([], 0).
le_value([X|Xs], U) :- le_value(Xs, U1), int_is(U, X + 256 * U1).

le_bytes(N, X, Bs) :-
    length(Bs, N),
    low_bytes(Bs, X).

% low_bytes(?Bs, ?X): Bs are the length(Bs) low bytes of X.
low_bytes([], _).
low_bytes([B|Bs], X) :-
    int_is(B, X mod 256),
    int_is(X1, X // 256),
    low_bytes(Bs, X1).

% alloc_base(+Mode, +Mem0, +Align, +Size, -Base, -Mem): Base is a new
% region of Size bytes in Mem. Allocations are aligned (Fil-C's to 16),
% with Fil-C bounds rounded to 16 as prepare_allocate_object does (zero
% stays zero). A 16-byte gap separates distinct, never-reused identities.
alloc_base(Mode, mem(Bytes, Rs, Next0, Aux), Align0, Size, Base,
           mem(Bytes, [region(Base, End, Kind, live)|Rs], Next, Aux)) :-
    must_be(integer, Size),
    alloc_align(Mode, Align0, Align),
    alloc_extent(Mode, Size, Extent, Kind),
    Base is (Next0 + Align - 1) // Align * Align,
    End is Base + Extent,
    allocation_stride(Mode, Size, Extent, Stride),
    Next is Base + Stride + 16.

alloc_extent(plain, Size, Size, stack).
alloc_extent(filc, Size, Extent, heap) :- Extent is (Size + 15) // 16 * 16.
alloc_extent(local, Size, Size, stack).

allocation_stride(plain, _, Extent, Extent).
allocation_stride(filc, _, Extent, Extent).
allocation_stride(local, Size, _, Stride) :- Stride is (Size + 15) // 16 * 16.

alloc_align(plain, Align, Align).
alloc_align(filc, _, 16).
alloc_align(local, _, 16).

stack_base(4294967296).
data_base(65536).

/* initial_memory(+Mode, +M, -Globals, -Mem): Mem holds every data
   definition, each in its own region, with its bytes. Globals maps a
   name to its address, or in filc mode to a pointer value: data objects
   are 16-aligned with their size rounded up to 8, as Fil-C's are, and
   each function gets an address and a fn capability. */
initial_memory(plain, module(Items), Globals, mem(Bytes, Rs, Stack, Aux)) :-
    empty_assoc(Aux),
    data_base(DataBase),
    empty_assoc(Globals0),
    foldl(plain_layout, Items, DataBase-Globals0-[], _-Globals-Rs),
    empty_assoc(Bytes0),
    foldl(plain_contents(Globals), Items, Bytes0, Bytes),
    stack_base(Stack).
initial_memory(filc, module(Items), Globals, mem(Bytes, Rs, Stack, Aux)) :-
    data_base(DataBase),
    empty_assoc(Globals0),
    foldl(filc_layout, Items, DataBase-Globals0-[], _-Globals-Rs),
    empty_assoc(Bytes0),
    empty_assoc(Aux0),
    foldl(filc_contents(Globals), Items, Bytes0-Aux0, Bytes-Aux),
    stack_base(Stack).

% plain_layout(+Item, +A0-Globals0-Rs0, -A-Globals-Rs): Globals and Rs
% add to Globals0 and Rs0 the address and region of Item placed at the
% next address from A0 that its alignment allows; a function takes no
% space.
plain_layout(data(Name, _, Align, DataItems), A0-Globals0-Rs0,
             A-Globals-[region(Base, End, global, live)|Rs0]) :-
    Base is (A0 + Align - 1) // Align * Align,
    foldl(item_size, DataItems, 0, Size),
    End is Base + Size,
    put_assoc(Name, Globals0, Base, Globals),
    A is End + 16.
plain_layout(func(_, _, _, _, _), State, State).

% plain_contents(+Globals, +Item, +Bytes0, -Bytes), filc_contents/4:
% Bytes (and in filc mode Aux) add the bytes (and capabilities) of Item.
plain_contents(Globals, data(Name, _, _, Items), Bytes0, Bytes) :-
    get_assoc(Name, Globals, A),
    maplist(item_bytes(Globals), Items, ItemBytes),
    append(ItemBytes, DataBytes),
    written_bytes(DataBytes, A, Bytes0, Bytes).
plain_contents(_, func(_, _, _, _, _), Bytes, Bytes).

% filc_layout(+Item, +A0-Globals0-Rs0, -A-Globals-Rs): place Item at
% the next 16-aligned address from A0.
filc_layout(data(Name, Linkage, _, Items), A0-Globals0-Rs0,
            A-Globals-[region(Base, End, global, live)|Rs0]) :-
    Base is (A0 + 15) // 16 * 16,
    foldl(item_size, Items, 0, Size),
    End is Base + (Size + 7) // 8 * 8,
    data_cap(Linkage, Base, Cap),
    put_assoc(Name, Globals0, ptr(Base, Cap), Globals),
    A is End + 16.
filc_layout(func(Name, _, _, _, _), A0-Globals0-Rs, A-Globals-Rs) :-
    Base is (A0 + 15) // 16 * 16,
    put_assoc(Name, Globals0, ptr(Base, fn(Name)), Globals),
    A is Base + 16.

% data_cap(+Linkage, +Base, -Cap): the capability of data at Base.
data_cap(export, Base, obj(Base)).
data_cap(local, Base, obj(Base)).
data_cap(ro(_), Base, ro(Base)).
data_cap(tls(_), Base, obj(Base)).      % one thread: one instance
data_cap(init(_, _), Base, ro(Base)).   % a table entry, never run here

filc_contents(Globals, data(Name, _, _, Items), Bytes0-Aux0, Bytes-Aux) :-
    get_assoc(Name, Globals, ptr(Base, _)),
    foldl(filc_item_contents(Globals), Items, Base-Bytes0-Aux0, _-Bytes-Aux).
filc_contents(_, func(_, _, _, _, _), State, State).

% filc_item_contents(+Globals, +Item, +At0-Bytes0-Aux0, -At-Bytes-Aux):
% Item written at At0; At is the address after it. Data items are IR
% terms (ir.pl); the cut commits to the pointer item before the clause
% for every other item.
filc_item_contents(Globals, item(p, sym(S, Off)), At-Bytes0-Aux0,
                   At1-Bytes-Aux) :- !,
    (   At mod 8 =:= 0 -> true
    ;   throw(nanofil_error('pointer data item is not 8-aligned'))
    ),
    (   get_assoc(S, Globals, ptr(SymAddr, Cap)) -> true
    ;   SymAddr = 0, Cap = ext(S)
    ),
    U is (SymAddr + Off) mod 18446744073709551616,
    le_bytes(8, U, Written),
    written_bytes(Written, At, Bytes0, Bytes),
    put_assoc(At, Aux0, Cap, Aux),
    At1 is At + 8.
filc_item_contents(Globals, Item, At-Bytes0-Aux, At1-Bytes-Aux) :-
    item_bytes(Globals, Item, Written),
    written_bytes(Written, At, Bytes0, Bytes),
    length(Written, N),
    At1 is At + N.

% item_size(+Item, +Size0, -Size): Size is Size0 plus Item's size. The
% cut commits to a string before the clause for any other item of width
% b (a constant).
item_size(zero(N), Size0, Size) :- Size is Size0 + N.
item_size(item(b, str(Cs)), Size0, Size) :- !,
    length(Cs, N),
    Size is Size0 + N.
item_size(item(W, _), Size0, Size) :-
    width_bytes(W, N),
    Size is Size0 + N.

% item_bytes(+Globals, +Item, -Bs): Bs are the bytes of the data Item,
% one per character of a string. The cut commits to a string, as in
% item_size/3.
item_bytes(_, zero(N), Bs) :- length(Bs, N), maplist(=(0), Bs).
item_bytes(_, item(b, str(Cs)), Bs) :- !, maplist(char_code, Cs, Bs).
item_bytes(_, item(W, const(N)), Bs) :-
    width_bytes(W, Size),
    Bits is Size * 8,
    U is N mod (1 << Bits),
    le_bytes(Size, U, Bs).
item_bytes(Globals, item(l, sym(S, Off)), Bs) :-
    get_assoc(S, Globals, A),
    U is A + Off,
    le_bytes(8, U, Bs).

%% Printing

%! outcome_text(+Outcome, -Text) is det.
%
%  Text is the atom that prints Outcome: its integer return value, or
%  just the kind of a pointer, unknown or tuple result. A returned value
%  is an integer, an unknown (a variable, possibly constrained) or
%  ptr(Addr, Cap): a defaulty term, so ret_text/2 tests it.

outcome_text(ret(V), T) :- ret_text(V, T).
outcome_text(rets(_), 'ret tuple').
outcome_text(ret, ret).
outcome_text(unreachable, unreachable).
outcome_text(ub(Why), T) :- format(atom(T), 'ub ~w', [Why]).
outcome_text(trap(Why), T) :- format(atom(T), 'trap ~w', [Why]).
outcome_text(unchecked(Why), T) :- format(atom(T), 'unchecked ~w', [Why]).
outcome_text(out_of_fuel, out_of_fuel).

ret_text(V, T) :-
    (   integer(V) -> format(atom(T), 'ret ~w', [V])
    ;   var(V) -> T = 'ret unknown'
    ;   V = ptr(_, _) -> T = 'ret pointer'
    ;   T = 'ret unknown'
    ).
