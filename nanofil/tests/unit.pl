/*  Interpreter, validator and printer tests that native differential
    testing cannot cover: outcomes with no native counterpart, backend
    regressions, and queries that run the semantics backwards.

    Run from nanofil/src:  ../bin/nanofil --script ../tests/unit.pl
    Expected values are derived by hand in the comments, not from the
    interpreter.

    Each test(Name) clause is one test; it passes if its body succeeds
    once without raising. Modules are written as their items, the IR
    terms of ir.pl.
*/
:- use_module('../src/ir').
:- use_module('../src/ieee').
:- use_module('../src/ir_text').
:- use_module('../src/interp').
:- use_module('../src/cfg').
:- use_module('../src/escape').
:- use_module('../src/alias').
:- use_module('../src/promote').
:- use_module('../src/copy').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module('../src/check_reuse').
:- use_module('../src/c_lex').
:- use_module('../src/c_parse').
:- use_module('../src/c_lower').
:- use_module('../src/c_types').
:- use_module('../src/asm').
:- use_module('../src/filc_amd64').
:- use_module('abi').
:- use_module('local_storage').
:- use_module('registers').
:- use_module('cache_check').
:- use_module('regs_check').
:- use_module(library(assoc)).
:- use_module(library(pio)).
:- use_module(library(clpz)).
:- use_module(library(lists)).
:- use_module(library(charsio)).
:- use_module(library(format)).
:- use_module(library(dcgs)).

:- dynamic(test/1).
:- discontiguous(test/1).
:- initialization(main).

% Run every test in file order, report, and exit 0 if all passed.
main :-
    findall(Test, clause(test(Test), _), Tests),
    foldl(run_test, Tests, 0, Failed),
    length(Tests, N),
    (   Failed =:= 0
    ->  format("nanofil unit: ~w tests ok~n", [N]),
        halt(0)
    ;   format("nanofil unit: ~w of ~w failed~n", [Failed, N]),
        halt(1)
    ).

% run_test(+Test, +Failed0, -Failed): run Test, printing why it failed;
% Failed counts it on top of Failed0 if it did.
run_test(Test, Failed0, Failed) :-
    (   catch(once(test(Test)),
              Error,
              ( format("~w: raised ~q~n", [Test, Error]),
                fail
              ))
    ->  Failed = Failed0
    ;   format("FAILED ~w~n", [Test]),
        Failed is Failed0 + 1
    ).

% ir_module(+Items, -Module): Module is the valid module of Items.
ir_module(Items, M) :-
    M = module(Items),
    valid_module(M).

% file_module(+File, -Module): Module is the valid module in IR File.
file_module(F, M) :-
    read_ir_file(F, M, _),
    valid_module(M).

% reads_back(+Module): the printed text of Module reads back as Module,
% clause by clause.
reads_back(module(Items)) :-
    phrase(module_text(module(Items)), Cs),
    clause_texts(Cs, Ts),
    maplist(clause_term, Ts, Items2),
    Items2 == Items.

% clause_texts(+Cs, -Ts): Ts are the clauses of text Cs, each up to and
% including its full stop. The printer ends every clause with ".\n"
% and escapes newlines inside quotes, so nothing else does.
clause_texts([], []).
clause_texts(Cs, [T|Ts]) :-
    append(T0, ['.', '\n'|Rest], Cs), !,
    append(T0, ['.'], T),
    clause_texts(Rest, Ts).

clause_term(T, X) :- read_term_from_chars(T, X, []).

test(abi_products) :- abi_products.
test(local_storage_selection) :- local_selection.
test(scalar_cache) :- scalar_cache.
test(cache_checker) :- cache_checker.
test(regs_checker) :- regs_checker.
test(local_storage_semantics) :- local_semantics.
test(local_storage_lifetime) :- local_lifetime.
test(local_storage_validation) :- local_validation.

% module_fn_args_outcome(+Module, +Fn, +Args, ?Outcome): Outcome is the first
% outcome of Fn(Args) on Module with fuel for 1000 blocks.
module_fn_args_outcome(M, Fn, Args, Out) :-
    once(run(M, Fn, Args, 1000, Out)).

% rejected_with(+Items, +Fragment): validating the module of Items throws
% a nanofil_error whose message contains the characters Fragment.
rejected_with(Items, Fragment) :-
    catch(( ir_module(Items, _),
            fail
          ),
          nanofil_error(Msg),
          true),
    atom_chars(Msg, Cs),
    append(_, Rest, Cs),
    append(Fragment, _, Rest),
    !.

%% Backend regressions (tests/backend), cases qbe 1.2 / c081897 got wrong

% storew of an l value stores its low word.
% memory 11 22 88 99 aa bb 77 88, loaduh at 5 = 0x77bb
test(storew_of_l_stores_low_word) :-
    file_module('../tests/backend/storew-l.ir', M),
    module_fn_args_outcome(M, f,
                           [9833440827789222417, 18441921395520346504],
                           ret(30651)).

% jnz after a shift by zero tests the shifted value, not stale flags.
% -128 >> 0 = -128, nonzero
test(jnz_after_shift_by_zero) :-
    file_module('../tests/backend/jnz-shift-flags.ir', M),
    module_fn_args_outcome(M, f, [0], ret(1)),
    module_fn_args_outcome(M, f, [1], ret(1)).

% jnz tests only the low 32 bits of its operand.
% 2^32 has zero low 32 bits
test(jnz_tests_low_32_bits) :-
    file_module('../tests/backend/jnz-long-flags.ir', M),
    module_fn_args_outcome(M, f, [4294967296, 0], ret(0)).

%% Outcomes with no native counterpart

% Division by zero and INT_MIN / -1 are undefined; other division
% truncates toward zero.
test(division_by_zero_and_overflow) :-
    ir_module([
        func(f, export, w, [param(w, tmp(a)), param(w, tmp(b))], [
            block(s, [], [
                let(tmp(q), w, div, [tmp(a), tmp(b)])
            ], ret(tmp(q)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [5, 0], ub(division_by_zero)),
    module_fn_args_outcome(M, f, [2147483648, 4294967295],
                           ub(division_overflow)),
    % -7 / 2 truncates to -3
    module_fn_args_outcome(M, f, [4294967289, 2], ret(4294967293)).

% A 4-byte store at offset 1 of a 4-byte allocation is out of bounds.
test(store_past_allocation) :-
    ir_module([
        func(f, export, void, [], [
            block(s, [], [
                let(tmp(p), l, alloc(4), [const(4)]),
                let(tmp(q), l, add, [tmp(p), const(1)]),
                store(w, const(0), tmp(q))
            ], ret)
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% An allocation dies with its function: loading through a returned
% pointer to it is out of bounds.
test(use_after_return) :-
    ir_module([
        func(leak, local, l, [], [
            block(s, [], [
                let(tmp(p), l, alloc(8), [const(8)]),
                store(l, const(1), tmp(p))
            ], ret(tmp(p)))
        ]),
        func(f, export, l, [], [
            block(s, [], [
                call(result(tmp(p), l), global(leak), []),
                let(tmp(v), l, load(l), [tmp(p)])
            ], ret(tmp(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 8))).

% A 4-byte load at offset 2 of a 4-byte data definition is out of
% bounds.
test(data_overrun) :-
    ir_module([
        data(d, local, 8, [item(w, const(1))]),
        func(f, export, w, [], [
            block(s, [], [
                let(tmp(p), l, add, [global(d), const(2)]),
                let(tmp(v), w, load(sw), [tmp(p)])
            ], ret(tmp(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% Two of the four bytes are unwritten: the result is unknown, but the
% written low half is still known.
test(uninitialized_bytes_are_unknown) :-
    ir_module([
        func(f, export, w, [], [
            block(s, [], [
                let(tmp(p), l, alloc(4), [const(4)]),
                store(h, const(4660), tmp(p)),
                let(tmp(v), w, load(sw), [tmp(p)])
            ], ret(tmp(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ret(V)),
    var(V),
    V mod 65536 #= 4660.

% unreachable is its own outcome.
test(unreachable) :-
    ir_module([
        func(f, export, void, [], [
            block(s, [], [], unreachable)
        ])
    ], M),
    module_fn_args_outcome(M, f, [], unreachable).

% An infinite loop ends as out_of_fuel.
test(out_of_fuel) :-
    ir_module([
        func(f, export, void, [], [
            block(s, [], [], goto(l)),
            block(l, [], [], goto(l))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], out_of_fuel).

%% Running backwards

% 3x + 1 = 7 (mod 2^32) has the unique solution x = 2.
test(backwards_find_input) :-
    ir_module([
        func(f, export, w, [param(w, tmp(x))], [
            block(s, [], [
                let(tmp(y), w, mul, [tmp(x), const(3)]),
                let(tmp(z), w, add, [tmp(y), const(1)])
            ], ret(tmp(z)))
        ])
    ], M),
    run(M, f, [X], 10, ret(7)),
    once(labeling([], [X])),
    X =:= 2.

% Which input reaches unreachable? Only x = 12345, found by propagation alone.
test(backwards_reach_hlt) :-
    ir_module([
        func(f, export, w, [param(w, tmp(x))], [
            block(s, [], [
                let(tmp(c), w, cmp(eq, w), [tmp(x), const(12345)])
            ], branch(tmp(c), bad, ok)),
            block(bad, [], [], unreachable),
            block(ok, [], [], ret(const(0)))
        ])
    ], M),
    run(M, f, [X], 10, unreachable),
    X == 12345.

% Signed division by 2 is not an arithmetic shift: they differ at -1
% (-1 / 2 = 0, -1 >> 1 = -1).
test(backwards_counterexample) :-
    ir_module([
        func(d, export, w, [param(w, tmp(x))], [
            block(s, [], [
                let(tmp(y), w, div, [tmp(x), const(2)])
            ], ret(tmp(y)))
        ]),
        func(s, export, w, [param(w, tmp(x))], [
            block(s, [], [
                let(tmp(y), w, sar, [tmp(x), const(1)])
            ], ret(tmp(y)))
        ])
    ], M),
    run(M, d, [X], 10, ret(A)),
    run(M, s, [X], 10, ret(B)),
    A #\= B,
    % Bound the search so an implementation where they agree fails fast
    % instead of enumerating 2^32 inputs.
    X in 0..255 \/ 4294967040..4294967295,
    once(labeling([down], [X])),
    X =:= 4294967295,
    A =:= 0,
    B =:= 4294967295.

%% Validator and parser diagnostics

% A w temporary cannot be read as l.
test(rejects_w_temp_as_l) :-
    rejected_with([
        func(f, export, l, [param(w, tmp(a))], [
            block(s, [], [
                let(tmp(b), l, add, [tmp(a), const(1)])
            ], ret(tmp(b)))
        ])
    ],
                  "tmp(a) has class w but is used as l").
% The entry block cannot be a jump target.
test(rejects_jump_to_entry) :-
    rejected_with([
        func(f, export, void, [], [
            block(s, [], [], goto(s))
        ])
    ],
                  "jump to the entry block").
% A phi needs an argument for every predecessor.
test(rejects_missing_phi_argument) :-
    rejected_with([
        func(f, export, w, [param(w, tmp(a))], [
            block(s, [], [], branch(tmp(a), x, y)),
            block(x, [], [], goto(y)),
            block(y, [
                phi(tmp(v), w, [x-const(1)])
            ], [], ret(tmp(v)))
        ])
    ],
                  "predecessors are").
% Unsupported instructions are refused with their line.
test(rejects_unknown_instruction) :-
    rejected_with([
        func(f, export, w, [param(w, tmp(a))], [
            block(s, [], [
                let(tmp(b), w, sqrt, [tmp(a)])
            ], ret(tmp(b)))
        ])
    ],
                  "unknown instruction sqrt").

% Literals just above a halfway binary32 value must not be rounded
% through binary64. Hex and decimal must reach the same rounding boundary.
test(float_literal_rounding) :-
    ieee_parse(s, "1.000000059604644775390625", 1065353216),
    ieee_parse(s, "1.000000059604644775390626", 1065353217),
    ieee_parse(s, "0x1.000001p0", 1065353216),
    ieee_parse(s, "0x1.000003p0", 1065353218),
    ieee_parse(d, "0x1p-1074", 1),
    ieee_parse(d, "0x1p-1075", 0),
    ieee_parse(d, "-0.0", 9223372036854775808).

% Float bit patterns, the widest integers in the IR, read back exactly.
test(float_bits_read_back) :-
    forall(member(K-Bits, [s-0, s-1, s-8388607, s-8388608,
                           s-1065353217, s-2139095039, s-2147483648,
                           s-2139095040, s-4290847557,
                           d-1, d-4503599627370496,
                           d-9218868437227405311, d-9223372036854775808,
                           d-18444492273895866373]),
           ( M = module([func(f, export, K, [],
                              [block(start, [], [], ret(const(Bits)))])]),
             valid_module(M), reads_back(M) )).

test(float_arithmetic_ieee) :-
    ieee_binary(s, add, 1065353216, 864026624, 1065353216),
    ieee_binary(s, add, 1065353217, 864026624, 1065353218),
    ieee_binary(s, div, 0, 0, 4290772992),
    ieee_binary(d, sub, 9221120237041090561, 18444492273895866370,
                9221120237041090561),
    ieee_binary(s, mul, 1, 1056964608, 0),
    ieee_binary(s, mul, 3, 1056964608, 2),
    ieee_binary(s, add, 2147483648, 2147483648, 2147483648),
    ieee_binary(s, add, 2147483648, 0, 0).

test(float_validator) :-
    forall(member(Op, [rem, urem, udiv, and, or, xor, sar, shr, shl]),
           ( M = module([func(f, local, s, [],
                              [block(start, [], [let(tmp(x), s, Op, [const(0), const(0)])],
                                   ret(tmp(x)))])]),
             catch((valid_module(M), fail), nanofil_error(_), true) )),
    rejected_with([
        func(f, local, w, [param(s, tmp(x))], [
            block(start, [], [
                let(tmp(y), w, copy, [tmp(x)])
            ], ret(tmp(y)))
        ])
    ],
                  "has class s but is used as w"),
    rejected_with([
        func(f, local, w, [param(s, tmp(x))], [
            block(start, [], [
                let(tmp(y), w, cmp(sle, s), [tmp(x), tmp(x)])
            ], ret(tmp(y)))
        ])
    ],
                  "unknown instruction cmp(sle,s)").

% Native conversion instructions return an indefinite integer for invalid
% input; the C-like IR must report UB instead, not silently accept it.
test(float_conversion_ub) :-
    file_module('../tests/float/edges.ir', M),
    forall(member(Fn-Bits, [si_w-2143289345, si_w-2139095040,
                            si_w-1325400064, si_w-3472883713,
                            ui_w-1333788672, ui_w-3212836864,
                            si_l-1593835520, si_l-3741319169,
                            ui_l-1602224128, ui_l-3212836864,
                            di_w-9221120237041090561,
                            di_w-4746794007248502784,
                            di_w-13970166044107472896,
                            du_w-4751297606875873280,
                            du_w-13830554455654793216,
                            di_l-4890909195324358656,
                            di_l-14114281232179134465,
                            du_l-4895412794951729152,
                            du_l-13830554455654793216]),
           module_fn_args_outcome(M, Fn, [Bits], ub(float_conversion))).

test(float_unknown_is_incomplete) :-
    ir_module([
        func(f, local, d, [param(d, tmp(x))], [
            block(start, [], [
                let(tmp(y), d, add, [tmp(x), const(4607182418800017408)])
            ], ret(tmp(y)))
        ])
    ], M),
    catch((run(M, f, [_], 10, _), fail), error(instantiation_error, _), true),
    % A symbolic integer cannot be cast into a symbolic float either.
    file_module('../tests/float/edges.ir', Edges),
    catch((run(Edges, adds, [_, 0], 10, _), fail),
          error(instantiation_error, _), true).

% The same concrete bits go through byte memory in Fil-C mode, without
% acquiring a capability or invoking integer extension on loads.
test(float_filc_memory) :-
    ir_module([
        func(f, local, l, [], [
            block(start, [], [
                let(tmp(p), p, alloc(8), [const(16)]),
                let(tmp(q), p, add, [tmp(p), const(8)]),
                store(s, const(2147483648), tmp(p)),
                store(d, const(18444492273895866370), tmp(q)),
                let(tmp(s), s, load(s), [tmp(p)]),
                let(tmp(d), d, load(d), [tmp(q)]),
                let(tmp(w), w, cast, [tmp(s)]),
                let(tmp(l), l, cast, [tmp(d)]),
                let(tmp(v), l, ext(uw), [tmp(w)]),
                let(tmp(r), l, xor, [tmp(l), tmp(v)])
            ], ret(tmp(r)))
        ])
    ], M),
    Expected is xor(18444492273895866370, 2147483648),
    module_fn_args_outcome(M, f, [], ret(Expected)).

%% Class p

% A p temporary cannot be read as l without ptoi.
test(rejects_p_as_l) :-
    rejected_with([
        func(f, export, l, [param(p, tmp(a))], [
            block(s, [], [
                let(tmp(b), l, add, [tmp(a), const(1)])
            ], ret(tmp(b)))
        ])
    ],
                  "tmp(a) has class p but is used as l (use ptoi)").
% In a Fil-C module (one using p), an l temporary cannot be used as an
% address without itop.
test(rejects_l_as_p) :-
    rejected_with([
        func(f, export, w, [param(l, tmp(a))], [
            block(s, [], [
                let(tmp(v), w, load(sw), [tmp(a)])
            ], ret(tmp(v)))
        ]),
        func(g, export, p, [], [
            block(s, [], [
                let(tmp(q), p, alloc(8), [const(8)])
            ], ret(tmp(q)))
        ])
    ],
                  "tmp(a) has class l but is used as p (use itop)").
% Pointers cannot be multiplied.
test(rejects_pointer_multiply) :-
    rejected_with([
        func(f, export, p, [param(p, tmp(a))], [
            block(s, [], [
                let(tmp(b), p, mul, [tmp(a), const(2)])
            ], ret(tmp(b)))
        ])
    ],
                  "instruction mul cannot have class p").
% Fil-C data holds a symbol's address as p, not l.
test(rejects_l_symbol_in_filc_data) :-
    rejected_with([
        data(d, local, 8, [item(l, sym(d, 0))]),
        func(f, export, p, [], [
            block(s, [], [
                let(tmp(q), p, alloc(8), [const(8)])
            ], ret(tmp(q)))
        ])
    ],
                  "is item(p, sym(d, _))").
% Fil-C code materializes a symbol with copy before using it.
test(rejects_symbol_operand_in_filc) :-
    rejected_with([
        data(d, local, 8, [item(w, const(1))]),
        func(f, export, w, [], [
            block(s, [], [
                let(tmp(q), p, add, [global(d), const(4)]),
                let(tmp(v), w, load(sw), [tmp(q)])
            ], ret(tmp(v)))
        ])
    ],
                  "only copy at p reads global(d)").

% Which offsets can a 1-byte read of a 16-byte allocation take without
% trapping? Exactly 0..15.
test(in_bounds_offsets) :-
    ir_module([
        func(f, export, w, [param(l, tmp(i))], [
            block(s, [], [
                let(tmp(p), p, alloc(8), [const(16)]),
                let(tmp(q), p, add, [tmp(p), tmp(i)]),
                let(tmp(v), w, load(ub), [tmp(q)])
            ], ret(tmp(v)))
        ])
    ], M),
    findall(I,
            ( between(0, 40, I),
              once(run(M, f, [I], 10, ret(_)))
            ),
            Is),
    numlist(0, 15, Expected),
    Is == Expected.

% Lifetime cases also run natively in basic.ir. Expected bounds are the
% runtime's 16-byte rounding, not the size the C caller requested.
test(free_lifetime_outcomes) :-
    file_module('../tests/filc/basic.ir', M),
    pizlonate_module(M, Checked), valid_module(Checked),
    forall(member(case(F, Args, Out), [
        case(free_alias, [0], ret(73)),
        case(free_alias, [1], trap(out_of_bounds)),
        case(freed_pointer_value, [], ret(8)),
        case(free_offset, [16, 0, 0], ret(1)),
        case(free_offset, [16, 1, 0], trap(invalid_free)),
        case(free_offset, [16, 16, 0], trap(invalid_free)),
        case(free_offset, [16, 0, 1], trap(double_free)),
        case(free_offset, [0, 0, 0], ret(1)),
        case(free_offset, [0, 0, 1], trap(double_free)),
        case(heap_bounds, [0, 0], trap(out_of_bounds)),
        case(heap_bounds, [1, 15], ret(0)),
        case(heap_bounds, [1, 16], trap(out_of_bounds)),
        case(heap_bounds, [17, 31], ret(0)),
        case(heap_bounds, [17, 32], trap(out_of_bounds)),
        case(free_forged, [0], ret(31)),
        case(free_forged, [1], trap(invalid_free))
    ]), (once(run(M, F, Args, 20, Out)),
         once(run(Checked, F, Args, 20, Out)))).

% A check cannot survive free. Deliberately run the invalid checked
% program too: the interpreter must expose the stale proof as unchecked,
% including pointer accesses, rather than silently read retained bytes.
test(free_invalidates_checks) :-
    Alloc = let(tmp(p), p, alloc(16), [const(16)]),
    Free = call(void, global(free), [arg(p, tmp(p))]),
    forall(member(Rights-Access, [
        read-let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
        read-let(tmp(x), p, raw_load_pointer(0,
            [aux_read, lower_resolve, address_read]), [tmp(q)]),
        write-raw_store(l, 0, const(9), tmp(q)),
        write-raw_store_pointer(0, tmp(p), tmp(q),
            [aux_ensure, lower_barrier, rooted_reload, lower_write, address_write])
    ]), (
        Check = let(tmp(q), a, check(0, 8, Rights, 8), [tmp(p)]),
        Fresh = module([func(f, local, w, [], [
            block(s, [], [Alloc, Free, Check, Access], ret(const(1)))])]),
        valid_module(Fresh),
        once(run(Fresh, f, [], 10, trap(out_of_bounds))),
        Stale = module([func(f, local, w, [], [
            block(s, [], [Alloc, Check, Free, Access], ret(const(1)))])]),
        catch((valid_module(Stale), fail), nanofil_error(_), true),
        once(run(Stale, f, [], 10, unchecked(out_of_bounds)))
    )).

% Neither changing a pointer's address bits nor allocating a new object
% revives its dead lower. An integer overwrite must retain that lower.
test(free_does_not_launder_stored_capability) :-
    ir_module([func(f, local, l, [], [block(s, [], [
        let(tmp(p), p, alloc(16), [const(16)]),
        let(tmp(box), p, alloc(16), [const(16)]),
        store(p, tmp(p), tmp(box)),
        call(void, global(free), [arg(p, tmp(p))]),
        let(tmp(new), p, alloc(16), [const(16)]),
        store(l, const(87), tmp(new)),
        let(tmp(a), l, ptoi, [tmp(new)]),
        store(l, tmp(a), tmp(box)),
        let(tmp(back), p, load(p), [tmp(box)]),
        let(tmp(x), l, load(l), [tmp(back)])
    ], ret(tmp(x)))])], M),
    once(run(M, f, [], 10, trap(out_of_bounds))),
    pizlonate_module(M, C), valid_module(C),
    once(run(C, f, [], 10, trap(out_of_bounds))).

% Readonly is permission, not allocation origin: heap snapshots may be
% freed, but static objects and function objects cannot be freed.
test(free_object_kinds) :-
    forall(member(Obj, [data(obj, local, 8, [zero(16)]),
                       data(obj, ro(local), 8, [zero(16)]),
                       func(obj, local, void, [], [block(s, [], [], ret)])]), (
        ir_module([Obj, func(f, local, void, [], [block(s, [], [
            let(tmp(p), p, copy, [global(obj)]),
            call(void, global(free), [arg(p, tmp(p))])], ret)])], M),
        once(run(M, f, [], 10, trap(invalid_free)))
    )),
    ir_module([func(f, local, void, [], [block(s, [], [
        let(tmp(p), p, va_args, [const(0)]),
        call(void, global(free), [arg(p, tmp(p))]),
        call(void, global(free), [arg(p, tmp(p))])], ret)])], Snapshot),
    once(run(Snapshot, f, [], 10, ret)),
    once(run(Snapshot, f, [23], 10, trap(double_free))).

% A module function called free remains an ordinary function, even with
% a different signature. A data symbol with that name is not libc free.
test(free_symbol_resolution) :-
    ir_module([
        func(free, local, void, [param(p, tmp(p))], [block(s, [], [
            store(w, const(59), tmp(p))], ret)]),
        func(f, local, w, [], [block(s, [], [
            let(tmp(p), p, alloc(16), [const(16)]),
            call(void, global(free), [arg(p, tmp(p))]),
            let(tmp(x), w, load(sw), [tmp(p)])], ret(tmp(x)))])
    ], Ordinary),
    once(run(Ordinary, f, [], 10, ret(59))),
    ir_module([
        func(free, local, w, [param(w, tmp(x))], [block(s, [], [], ret(tmp(x)))]),
        func(f, local, w, [], [block(s, [], [
            let(tmp(p), p, alloc(16), [const(16)]),
            call(result(tmp(x), w), global(free), [arg(w, const(43))])
        ], ret(tmp(x)))])
    ], Defined),
    once(run(Defined, f, [], 10, ret(43))),
    ir_module([
        data(free, local, 8, [zero(16)]),
        func(f, local, void, [], [block(s, [], [
            call(void, global(free), [arg(p, const(0))])], ret)])
    ], Data),
    once(run(Data, f, [], 10, trap(not_a_function))).

% Unsupported external signatures/objects are incompleteness errors,
% never failure, invented external effects, or a null no-op for ext(_).
test(free_external_boundary) :-
    ir_module([func(f, local, void, [param(p, tmp(p))], [block(s, [], [
        call(void, global(free), [arg(p, tmp(p))])], ret)])], Numeric),
    once(run(Numeric, f, [0], 10, ret)),
    once(run(Numeric, f, [1], 10, trap(invalid_free))),
    forall(member(Call, [call(void, global(free), []),
                         call(void, global(free), [arg(l, const(0))]),
                         call(result(tmp(x), w), global(free), [arg(p, const(0))]),
                         call(void, global(free), [arg(p, const(0)), arg(w, const(1))]),
                         call(void, global(malloc), [arg(l, const(16))])]), (
        ir_module([func(f, local, void, [], [block(s, [], [
            let(tmp(p), p, alloc(16), [const(16)]), Call], ret)])], M),
        catch((run(M, f, [], 10, _), fail), nanofil_error(_), true)
    )),
    ir_module([func(f, local, void, [], [block(s, [], [
        let(tmp(p), p, copy, [global(unknown)]),
        call(void, global(free), [arg(p, tmp(p))])], ret)])], Ext),
    catch((run(Ext, f, [], 10, _), fail), nanofil_error(_), true).

%% Printing

% Printing a module and reading the text gives the same module back.
test(print_round_trip) :-
    forall(member(F, ['../tests/fixtures/arith.ir',
                      '../tests/fixtures/memory.ir',
                      '../tests/filc/globals.ir']),
           ( file_module(F, M), reads_back(M) )),
    % Lowered C has quoted labels ('L6'), temps ('pr.1') and symbols.
    c_file_module('../tests/c/basic.c', C),
    reads_back(C).

% A str/1 data item holds its bytes, one per character: \001 is four
% bytes, not one, and the backends escape quote, backslash and
% unprintable bytes only when they print the .ascii directive.
test(data_string_is_bytes) :-
    ir_module([
        data(d, local, 1, [item(b, str(['\\', '0', '0', '1'])),
                           item(b, const(7))]),
        func(f, export, w, [param(l, tmp(i))], [
            block(s, [], [
                let(tmp(p), l, add, [global(d), tmp(i)]),
                let(tmp(v), w, load(ub), [tmp(p)])
            ], ret(tmp(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [1], ret(48)),
    module_fn_args_outcome(M, f, [4], ret(7)),
    char_code(One, 1), char_code(High, 200),
    asm:line_chars(ascii(['"', '\\', '\n', '\t', a, One, High]), Cs),
    append(Text, ['\n'], Cs),
    Text == "\t.ascii \"\\\"\\\\\\n\\ta\\001\\310\"".

%% Middle end (M5)

% s -> a; a -> b | c; b, c -> d; d -> a | e. The loop a..d makes a its
% own frontier; b and c join at d. x lives from s to the exit, y around
% the loop (read in b and as d's phi argument on the edge from c), z
% only on the edge b -> d, and w is defined by d's phi.
loop_cfg_text([
    func(f, export, w, [param(w, tmp(p))], [
        block(s, [], [
            let(tmp(x), w, copy, [tmp(p)]),
            let(tmp(y), w, copy, [const(1)])
        ], goto(a)),
        block(a, [], [], branch(tmp(x), b, c)),
        block(b, [], [
            let(tmp(z), w, add, [tmp(y), const(1)])
        ], goto(d)),
        block(c, [], [], goto(d)),
        block(d, [
            phi(tmp(w), w, [b-tmp(z), c-tmp(y)])
        ], [], branch(tmp(w), a, e)),
        block(e, [], [], ret(tmp(x)))
    ])
]).

% The reverse postorder, immediate dominators and dominance frontiers
% of loop_cfg_text/1.
test(dominators_and_frontiers) :-
    loop_cfg_text(T),
    ir_module(T, module([func(_, _, _, _, Bs)])),
    func_cfg(Bs, Cfg),
    Cfg = cfg(s, Rpo, _, _),
    msort(Rpo, [a, b, c, d, e, s]),
    cfg_idoms(Cfg, Idom),
    assoc_to_list(Idom, [a-s, b-a, c-a, d-a, e-d]),
    cfg_frontiers(Cfg, Idom, DF),
    assoc_to_list(DF, [a-[a], b-[d], c-[d], d-[a], e-[], s-[]]).

% The temporaries live into and out of each block of loop_cfg_text/1.
test(temp_liveness) :-
    loop_cfg_text(T),
    ir_module(T, module([func(_, _, _, _, Bs)])),
    temp_liveness(Bs, In, Out),
    assoc_to_list(In, [a-[x, y], b-[x, y], c-[x, y], d-[x, y], e-[x],
                       s-[p]]),
    get_assoc(b, Out, [x, y, z]),
    get_assoc(c, Out, [x, y]),
    get_assoc(d, Out, [x, y]).

% Nested loops, two latches sharing a header, and a self-loop. The dead
% predecessor must not enter the body. u/v form an irreducible cycle with
% separate entries, so neither is a natural-loop header. Layout is shuffled.
test(natural_loop_membership) :-
    Bs = [block(s, [], [], goto(outer)),
          block(latch_b, [], [], goto(outer)),
          block(inner, [], [], branch(tmp(n), spin, latch_a)),
          block(spin, [], [], goto(inner)),
          block(outer, [], [], branch(tmp(n), inner, self)),
          block(latch_a, [], [], branch(tmp(n), outer, latch_b)),
          block(dead, [], [], goto(inner)),
          block(self, [], [], branch(tmp(n), self, choice)),
          block(choice, [], [], branch(tmp(n), u, v)),
          block(u, [], [], branch(tmp(n), v, done)),
          block(v, [], [], branch(tmp(n), u, done)),
          block(done, [], [], ret)],
    func_cfg(Bs, Cfg),
    cfg_idoms(Cfg, Idom),
    natural_loops(Cfg, Idom, Loops),
    assoc_to_list(Loops,
                  [inner-loop([spin], [inner, spin]),
                   outer-loop([latch_a, latch_b],
                              [inner, latch_a, latch_b, outer, spin]),
                   self-loop([self], [self])]).

% These are address expressions, not disjointness claims. Wrapping and
% signed subtraction must give the same modular offset. Loads, casts,
% variable offsets and phis get their own opaque bases, not an alloc's.
test(alias_base_offsets) :-
    F = func(f, export, p, [param(p, tmp(p)), param(l, tmp(n)), param(w, tmp(c))],
             [block(s, [],
                  [let(tmp(a), p, alloc(8), [const(32)]),
                   let(tmp(a4), p, add, [tmp(a), const(4)]),
                   let(tmp(wrap), p, add, [tmp(a4), const(18446744073709551615)]),
                   let(tmp(back), p, sub, [tmp(wrap), const(-1)]),
                   let(tmp(q), p, copy, [tmp(p)]),
                   let(tmp(q9), p, add, [tmp(q), const(9)]),
                   let(tmp(g), p, copy, [global(global)]),
                   let(tmp(raw), l, ptoi, [tmp(a)]),
                   let(tmp(cast), p, itop, [tmp(raw)]),
                   let(tmp(loaded), p, load(p), [tmp(a)]),
                   let(tmp(loaded3), p, add, [tmp(loaded), const(3)]),
                   call(result(tmp(called), p), global(external), []),
                   let(tmp(vary), p, add, [tmp(a), tmp(n)]),
                   let(tmp(narrow), w, copy, [tmp(n)]),
                   let(tmp(wide), l, ext(uw), [tmp(narrow)]),
                   let(tmp(nplus), l, sub, [tmp(n), const(18446744073709551615)]),
                   let(tmp(nwrap), l, add, [const(18446744073709551616), tmp(n)])],
                  branch(tmp(c), left, right)),
              block(left, [], [], goto(join)),
              block(right, [], [], goto(join)),
              block(join, [phi(tmp(merged), p, [left-tmp(a), right-tmp(q)])],
                  [let(tmp(result), p, add, [tmp(merged), const(5)])],
                  ret(tmp(result)))]),
    once(valid_module(module([data(global, local, 8, [item(l, const(7))]),
                              F]))),
    alias_facts(F, Facts),
    forall(member(T-A, [a-addr(p, alloc(a), 0),
                        back-addr(p, alloc(a), 4),
                        wrap-addr(p, alloc(a), 3),
                        q9-addr(p, param(p), 9),
                        g-addr(p, symbol(global), 0),
                        raw-addr(l, value(raw), 0),
                        cast-addr(p, value(cast), 0),
                        loaded3-addr(p, value(loaded), 3),
                        called-addr(p, value(called), 0),
                        vary-addr(p, value(vary), 0),
                        wide-addr(l, value(wide), 0),
                        nplus-addr(l, param(n), 1),
                        nwrap-addr(l, param(n), 0),
                        result-addr(p, value(merged), 5)]),
           get_assoc(T, Facts, A)),
    \+ get_assoc(narrow, Facts, _),
    file_module('../tests/fixtures/copy.ir', Copies),
    func_named(Copies, redefined, Bad),
    alias_facts(Bad, Empty),
    assoc_to_list(Empty, []).

% Each alloc used one way that makes it escape, and one that does not.
test(escape_classes) :-
    ir_module([
        func(f, export, w, [param(l, tmp(n))], [
            block(s, [], [
                let(tmp(a), p, alloc(4), [const(8)]),
                let(tmp(b), p, add, [tmp(a), const(4)]),
                store(w, const(1), tmp(a)),
                store(w, const(2), tmp(b)),
                let(tmp(v), w, load(sw), [tmp(b)]),
                let(tmp(e), p, alloc(8), [const(8)]),
                call(void, global(g), [arg(p, tmp(e))]),
                let(tmp(f), p, alloc(8), [const(8)]),
                let(tmp(i), l, ptoi, [tmp(f)]),
                let(tmp(h), p, alloc(8), [const(8)]),
                let(tmp(q), p, add, [tmp(h), tmp(n)]),
                let(tmp(m), p, alloc(8), [const(8)]),
                let(tmp(z), p, alloc(8), [const(8)]),
                store(p, tmp(m), tmp(z))
            ], ret(tmp(v)))
        ])
    ], M),
    M = module([F]),
    alloc_classes(F, Cs),
    Cs == [a-local(const(8), [acc(0, w), acc(4, w)]),
           e-escapes(call),
           f-escapes(ptoi),
           h-escapes(add),
           m-escapes(stored),
           z-local(const(8), [acc(0, p)])].

% Fil-C allocations are zero: a read before any write gives 0, and a
% pointer read before any write has no capability, so using it traps.
test(promote_reads_zero_in_filc) :-
    ir_module([
        func(f, export, w, [], [
            block(s, [], [
                let(tmp(s), p, alloc(4), [const(4)]),
                let(tmp(v), w, load(sw), [tmp(s)])
            ], ret(tmp(v)))
        ]),
        func(g, export, w, [], [
            block(s, [], [
                let(tmp(s), p, alloc(8), [const(8)]),
                let(tmp(q), p, load(p), [tmp(s)]),
                let(tmp(v), w, load(sw), [tmp(q)])
            ], ret(tmp(v)))
        ])
    ], M0),
    optimize(o1, M0, M),
    once(valid_module(M)),
    alloc_count(M, 0),
    module_fn_args_outcome(M0, f, [], ret(0)),
    module_fn_args_outcome(M, f, [], ret(0)),
    module_fn_args_outcome(M0, g, [], trap(null_capability)),
    module_fn_args_outcome(M, g, [], trap(null_capability)).

% Which allocs promote must remove, and which it must keep, on the
% fixture and on tests/c/basic.c (only arr's array and ptrs's array have
% their address passed or stored). A promote that did nothing would still
% pass every differential test; this does not.
test(promote_removes_allocs) :-
    file_module('../tests/fixtures/promote.ir', M0),
    alloc_count(M0, 12),
    optimize(o1, M0, M),
    once(valid_module(M)),
    alloc_count(M, 4),
    func_named(M, kept, K),
    alloc_count(module([K]), 4),
    c_file_module('../tests/c/basic.c', C0),
    alloc_count(C0, 23),
    optimize(o1, C0, C),
    once(valid_module(C)),
    findall(Fn,
            ( C = module(Is),
              member(func(Fn, _, _, _, Bs), Is),
              member(block(_, _, Ins, _), Bs),
              member(let(_, _, alloc(_), _), Ins)
            ),
            Kept),
    Kept == [arr, ptrs].

% Each selectable pass must do its own work. The first allocation can
% promote; the second has overlapping stores and must stay as memory.
% Little-endian 0x1234 with its low byte replaced by 0x56 is 4694;
% adding the first slot's 7 gives 4701, with any subset of the passes.
test(selectable_optimization_passes) :-
    ir_module([func(f, export, w, [], [block(s, [], [
        loc('passes.c', 1),
        let(tmp(slot), p, alloc(4), [const(4)]),
        let(tmp(v), w, copy, [const(7)]),
        store(w, tmp(v), tmp(slot)),
        let(tmp(x), w, load(sw), [tmp(slot)]),
        let(tmp(bytes), p, alloc(8), [const(8)]),
        store(h, const(4660), tmp(bytes)),
        store(b, const(86), tmp(bytes)),
        let(tmp(y), w, load(uw), [tmp(bytes)]),
        let(tmp(z), w, add, [tmp(x), tmp(y)])
    ], ret(tmp(z)))])], M0),
    forall(member(Passes, [[], [promote], [copy], [local_storage],
                          [promote, copy], [promote, local_storage],
                          [copy, local_storage],
                          [promote, copy, local_storage]]),
           ( optimize(passes(Passes), M0, M), valid_module(M),
             module_fn_args_outcome(M, f, [], ret(4701)),
             ( memberchk(local_storage, Passes) -> Allocs = 0
             ; memberchk(promote, Passes) -> Allocs = 1
             ; Allocs = 2 ),
             alloc_count(M, Allocs),
             findall(Name, sub_term(local_alloc(Name, _), M), Locals),
             ( memberchk(local_storage, Passes)
             -> ( memberchk(promote, Passes) -> Locals == [bytes]
                ; Locals == [slot, bytes] )
             ; Locals == [] ),
             ( memberchk(copy, Passes)
             -> \+ sub_term(let(_, _, copy, _), M)
             ;  sub_term(let(_, _, copy, _), M) ),
             ( Passes == [] -> M == M0
             ; \+ sub_term(loc(_, _), M) )
           )),
    optimization_passes(o1, All),
    optimize(o1, M0, Full), optimize(passes(All), M0, Full),
    foldl(optimize_pass, All, M0, Full),
    pizlonate_module(M0, Checked),
    optimize(passes(All), Checked, Unchanged), Unchanged == Checked,
    optimize_pass(local_storage, M0, Local),
    optimize(passes(All), Local, StillLocal), StillLocal == Local,
    \+ optimize_pass(unknown, Checked, _),
    \+ optimize_pass(unknown, Local, _),
    forall(member(Bad, [[copy, promote], [local_storage, copy],
                        [copy, copy], [unknown]]),
           \+ optimization_passes(passes(Bad), _)).

% The optimizer must actually remove aliases, not just preserve results.
% Keep the narrowing copy, global materialization and non-SSA function.
test(copy_eliminates_aliases) :-
    file_module('../tests/fixtures/copy.ir', M0),
    optimize(o1, M0, M),
    once(valid_module(M)),
    forall(member(Name, [chain, swap, constants]),
           ( func_named(M, Name, func(_, _, _, _, Bs)),
             \+ ( member(block(_, _, Is, _), Bs),
                  member(let(_, _, copy, _), Is)
                )
           )),
    func_named(M, narrow, func(_, _, _, _, [block(_, _, Narrow, _)])),
    findall(K, member(let(_, K, copy, _), Narrow), [w]),
    func_named(M, global, func(_, _, _, _, [block(_, _, Global, _)])),
    memberchk(let(_, l, copy, [global(cell)]), Global),
    func_named(M0, redefined, Redefined),
    func_named(M, redefined, Redefined).

% Removing phis is part of the optimization contract, not merely producing
% equivalent output. Keep narrowing, genuine loop recurrences and dead
% definitions; remove chains regardless of block/name order.
test(copy_eliminates_trivial_phis) :-
    file_module('../tests/fixtures/copy.ir', M0),
    copy_module(M0, M),
    once(valid_module(M)),
    forall(member(Name-Names, [invariant-[i],
                               phi_constants-[],
                               phi_narrow-[w],
                               phi_dead_edges-[different, self],
                               swap-[a, b, i]]),
           ( func_phi_names(M, Name, Names),
             func_named(M, Name, F),
             F = func(_, _, _, _, Bs),
             func_cfg(Bs, Cfg),
             cfg_idoms(Cfg, Idom),
             strict_ssa(F, Cfg, Idom)
           )),
    ir_module([
        func(f, export, w, [param(w, tmp(n))], [
            block(s, [], [], goto(loop)),
            block(loop, [
                phi(tmp(p), p, [s-const(0), loop-tmp(p)])
            ], [], branch(tmp(n), loop, done)),
            block(done, [], [], ret(const(7)))
        ])
    ], Literal),
    copy_module(Literal, LiteralKept),
    Literal == LiteralKept,
    module_mode(LiteralKept, filc).

% func_phi_names(+Module, +Fn, -Names): Names is the ordset of the
% temporaries the phis of function Fn define.
func_phi_names(M, Name, Names) :-
    func_named(M, Name, func(_, _, _, _, Bs)),
    findall(T,
            ( member(block(_, Ps, _, _), Bs),
              member(phi(tmp(T), _, _), Ps)
            ),
            Ts),
    sort(Ts, Names).

% A use must be dominated by a definition: one later in the same block
% is not, and neither is one in only one arm of a diamond. A second
% definition in a dominating block is enough (memory.ir's twice).
test(definitions_dominate_uses) :-
    Later = func(f, export, l, [param(l, tmp(x))], [
        block(s, [], [
            let(tmp(a), l, copy, [tmp(b)]),
            let(tmp(b), l, add, [tmp(x), const(1)])
        ], ret(tmp(a)))
    ]),
    catch(( valid_module(module([Later])), fail ), nanofil_error(M1), true),
    M1 == 'in f: tmp(b) is used in block s, which no definition dominates',
    Arm = func(g, export, w, [param(w, tmp(x))], [
        block(s, [], [let(tmp(y), w, copy, [const(0)])], branch(tmp(x), l, r)),
        block(l, [], [let(tmp(y), w, copy, [const(1)]), let(tmp(z), w, copy, [const(2)])],
            goto(j)),
        block(r, [], [], goto(j)),
        block(j, [], [], ret(tmp(z)))
    ]),
    catch(( valid_module(module([Arm])), fail ), nanofil_error(M2), true),
    M2 == 'in g: tmp(z) is used in block j, which no definition dominates',
    Arm = func(G, E, R, Ps, [S, L, Rt, block(j, [], [], ret(tmp(z)))]),
    valid_module(module([func(G, E, R, Ps, [S, L, Rt, block(j, [], [], ret(tmp(y)))])])).

% copy leaves a literal pointer copy, which keeps the module Fil-C,
% unchanged.
test(copy_keeps_literal_pointer_copy) :-
    ir_module([
        func(f, export, w, [], [
            block(s, [], [
                let(tmp(p), p, copy, [const(0)])
            ], ret(const(7)))
        ])
    ], Literal),
    copy_module(Literal, Kept),
    Literal == Kept,
    module_mode(Kept, filc).

% The native GC test must exercise eliminated aliases, not merely run
% unchanged pointer code under an optimizer that does nothing.
test(copy_removes_gc_aliases) :-
    file_module('../tests/filc/gc.ir', M0),
    M0 = module(Items0),
    member(func(_, _, _, _, Bs0), Items0),
    member(block(_, _, Is0, _), Bs0),
    member(let(_, p, copy, _), Is0),
    !,
    optimize(o1, M0, M),
    once(valid_module(M)),
    M = module(Items),
    % local_roots deliberately retains null literals to overwrite roots;
    % the list functions exercise eliminated pointer aliases.
    \+ ( member(func(Name, _, _, _, Bs), Items), memberchk(Name, [build, sum]),
         member(block(_, _, Is, _), Bs),
         member(let(_, p, copy, _), Is)
       ),
    func_phi_names(M, sum, [j, left, p, right, s]).

% Unlike promote, copy moves no allocations. Compare whole pointer values,
% including object identity: equal offsets in different objects are not equal.
test(copy_preserves_pointer_identity) :-
    ir_module([
        func(f, export, p, [param(w, tmp(which))], [
            block(s, [], [
                let(tmp(a), p, alloc(8), [const(8)]),
                let(tmp(b), p, alloc(8), [const(8)]),
                let(tmp(x), p, copy, [tmp(a)]),
                let(tmp(y), p, copy, [tmp(b)])
            ], branch(tmp(which), left, right)),
            block(left, [], [], goto(join)),
            block(right, [], [], goto(join)),
            block(join, [
                phi(tmp(p), p, [left-tmp(x), right-tmp(y)])
            ], [
                let(tmp(q), p, copy, [tmp(p)])
            ], ret(tmp(q)))
        ]),
        func(raw, export, p, [], [
            block(s, [], [
                let(tmp(a), p, alloc(8), [const(8)]),
                let(tmp(p), p, copy, [tmp(a)]),
                let(tmp(i), l, ptoi, [tmp(p)]),
                let(tmp(raw), p, itop, [tmp(i)]),
                let(tmp(q), p, copy, [tmp(raw)])
            ], ret(tmp(q)))
        ])
    ], M0),
    copy_module(M0, M),
    once(valid_module(M)),
    module_mode(M0, Mode),
    module_mode(M, Mode),
    forall(member(Which, [0, 1]),
           ( module_fn_args_outcome(M0, f, [Which], Before),
             module_fn_args_outcome(M, f, [Which], After),
             Before == After
           )),
    module_fn_args_outcome(M0, f, [0], B),
    module_fn_args_outcome(M0, f, [1], A),
    B \== A,
    module_fn_args_outcome(M0, raw, [], Raw0),
    module_fn_args_outcome(M, raw, [], Raw),
    Raw0 == Raw,
    Raw = ret(ptr(_, none)),
    file_module('../tests/filc/copy.ir', P0),
    copy_module(P0, P),
    once(valid_module(P)),
    func_phi_names(P, pointer_invariant, [i]),
    forall(member(N, [0, 1, 5]),
           ( module_fn_args_outcome(P0, pointer_invariant, [N], Before),
             module_fn_args_outcome(P, pointer_invariant, [N], After),
             Before == After
           )).

% Bounded symbolic queries share the same input variables across both runs.
% The domains include branch choices, loop counts and the 32-bit sign edge;
% labeling makes absence of a counterexample decisive within those domains.
test(symbolic_optimized_returns) :-
    file_module('../tests/fixtures/promote.ir', P0),
    optimize(o1, P0, P),
    \+ ( X in 0..15,
         Y in 0..3,
         returns_differ(P0, P, diamond, [X, Y], 20)
       ),
    \+ ( N in 0..6,
         returns_differ(P0, P, loop, [N], 20)
       ),
    file_module('../tests/fixtures/copy.ir', C0),
    optimize(o1, C0, C),
    \+ ( X in 0..15,
         returns_differ(C0, C, chain, [X], 20)
       ),
    \+ ( N in 0..7,
         returns_differ(C0, C, swap, [N], 20)
       ),
    \+ ( X in 0..15,
         N in 0..5,
         returns_differ(C0, C, invariant, [X, N], 20)
       ),
    \+ ( X in 0..1,
         returns_differ(C0, C, phi_constants, [X], 20)
       ),
    \+ ( X in 4294967296..4294967311,
         W in 0..1,
         returns_differ(C0, C, phi_narrow, [X, W], 20)
       ),
    \+ ( X in 0..15,
         returns_differ(C0, C, phi_dead_edges, [X], 20)
       ),
    \+ ( X in 4294967296..4294967311 \/ 6442450936..6442450952,
         returns_differ(C0, C, narrow, [X], 20)
       ),
    \+ ( X in 0..15,
         returns_differ(C0, C, effects, [X], 20)
       ).

% A wrong l->w copy elimination followed by extuw loses truncation. The
% symbolic query must find the first value above 2^32, not bless the pass.
test(symbolic_finds_narrowing_error) :-
    ir_module([
        func(f, export, l, [param(l, tmp(x))], [
            block(s, [], [
                let(tmp(w), w, copy, [tmp(x)]),
                let(tmp(r), l, ext(uw), [tmp(w)])
            ], ret(tmp(r)))
        ])
    ], Before),
    ir_module([
        func(f, export, l, [param(l, tmp(x))], [
            block(s, [], [], ret(tmp(x)))
        ])
    ], Wrong),
    X in 4294967296..4294967311,
    once(returns_differ(Before, Wrong, f, [X], 10)),
    X =:= 4294967296.

% returns_differ(+Module0, +Module, +Fn, ?Args, +Fuel) is nondet: $Fn
% returns different values on Module0 and Module for Args, labelled.
% Throws if either run does not return.
returns_differ(M0, M, Fn, Args, Fuel) :-
    run(M0, Fn, Args, Fuel, Out0),
    run(M, Fn, Args, Fuel, Out),
    (   Out0 = ret(A),
        Out = ret(B)
    ->  A #\= B,
        labeling([], Args)
    ;   throw(expected_symbolic_returns(Fn, Out0, Out))
    ).

% Translation validation's comparison: undefined behaviour and unknown
% bytes allow any outcome they could produce, nothing else differs.
test(refines) :-
    refines(ub(division_by_zero), ret(7)),
    V in 0..255,
    refines(ret(V), ret(0)),
    \+ refines(ret(V), ret(256)),
    \+ refines(ret(5), ret(6)),
    \+ refines(ret(5), trap(out_of_bounds)),
    refines(ret(ptr(4112, obj(4096))), ret(ptr(8208, obj(8192)))),
    \+ refines(ret(ptr(4112, obj(4096))), ret(ptr(8200, obj(8192)))).

% An indirect call whose site reads w from a callee returning p goes
% through the generic entry and reads the pointer's address as an
% integer. (word_class/2 once matched p with int here, called the
% words the same, and the run died on a type error.)
test(indirect_call_reads_pointer_result_as_int) :-
    ir_module([
        func(k, local, p, [], [
            block(s, [], [
                let(tmp(p), p, alloc(8), [const(16)])
            ], ret(tmp(p)))
        ]),
        func(m, export, w, [], [
            block(s, [], [
                let(tmp(f), p, copy, [global(k)]),
                call(result(tmp(r), w), tmp(f), [])
            ], ret(tmp(r)))
        ])
    ], M),
    module_fn_args_outcome(M, m, [], Out),
    Out = ret(V),
    integer(V).

test(variadic_slot_stays_in_memory) :-
    ir_module([
        func(f, export, l, [param(p, tmp(args))], [
            block(s, [], [
                let(tmp(slot), p, alloc(8), [const(24)]),
                store(p, tmp(args), tmp(slot)),
                let(tmp(x), l, va_arg, [tmp(slot)])
            ], ret(tmp(x)))
        ])
    ], M0),
    optimize(o1, M0, M), valid_module(M),
    M = module([F]), F = func(_, _, _, _, [block(_, _, Is, _)]),
    member(let(Slot, p, alloc(8), [const(24)]), Is),
    member(let(_, l, va_arg, [Slot]), Is),
    alloc_classes(F, Classes), memberchk(slot-escapes(va_arg), Classes),
    reads_back(M).

test(variadic_invalid_ir) :-
    rejected_with([
        func(f, local, w, [], [
            block(s, [], [
                let(tmp(x), w, va_arg, [const(0)])
            ], ret(tmp(x)))
        ])
    ], "va_arg"),
    rejected_with([
        func(f, local, p, [], [
            block(s, [], [
                let(tmp(x), p, va_args, [const(-1)])
            ], ret(tmp(x)))
        ])
    ], "non-negative"),
    rejected_with([
        func(f, local, p, [param(l, tmp(n))], [
            block(s, [], [
                let(tmp(x), p, va_args, [tmp(n)])
            ], ret(tmp(x)))
        ])
    ], "constant").

test(setjmp_contract) :-
    file_module('../tests/filc/setjmp.ir', M),
    reads_back(M),
    module_mode(M, filc),
    promote_module(M, M), copy_module(M, M),
    ir_module([
        func(f, local, w, [param(p, tmp(buf))], [
            block(s, [], [
                let(tmp(slot), p, alloc(8), [const(8)]),
                store(w, const(3), tmp(slot)),
                let(tmp(copy), w, copy, [const(9)]),
                let(tmp(x), w, setjmp('_setjmp'), [tmp(buf), const(0)]),
                let(tmp(v), w, load(sw), [tmp(slot)]),
                let(tmp(out), w, add, [tmp(v), tmp(copy)])
            ], ret(tmp(out)))
        ])
    ], Kept),
    Kept = module([F]),
    promote_func(filc, F, F), promotable(filc, F, []),
    promote_module(Kept, Kept), copy_module(Kept, Kept),
    ir_module([
        func(f, local, w, [], [
            block(s, [], [
                let(tmp(x), w, setjmp(sigsetjmp), [const(0), const(1)])
            ], ret(tmp(x)))
        ])
    ], Null),
    module_mode(Null, filc),
    catch(run(Null, f, [], 100, _), nanofil_error(Msg), true),
    Msg == 'interpreter does not support setjmp/nonlocal returns',
    rejected_with([
        func(f, local, w, [], [
            block(s, [], [
                let(tmp(x), w, setjmp(setjmp), [const(0), const(1)])
            ], ret(tmp(x)))
        ])
    ], "zero SaveMask"),
    rejected_with([
        func(f, local, w, [], [
            block(s, [], [
                let(tmp(x), w, setjmp('_setjmp'), [const(0), const(1)])
            ], ret(tmp(x)))
        ])
    ], "zero SaveMask"),
    rejected_with([
        func(f, local, p, [], [
            block(s, [], [
                let(tmp(x), p, setjmp(setjmp), [const(0), const(0)])
            ], ret(tmp(x)))
        ])
    ], "class p").

% The C binding and typed origins survive every selected pass, without
% changing executable IR, outcomes or assembly. sum's loop-carried s
% gets a generated phi, distinct from its narrow machine-class meaning.
test(source_locations) :-
    c_file_module('../tests/c/locations.c', M),
    M = module(Items),
    memberchk(context(fib, Rs), Items),
    member(binding(B, n, int, at(_, 2)), Rs),
    member(value(_, named(B, value), _), Rs),
    member(origin(_, at(_, 3), typed(val, int, _), _), Rs),
    without_locs(M, Bare),
    forall(member(Option, [o0, passes([promote]), passes([promote, copy]), o1]),
           ( optimize(Option, M, O), valid_module(O),
             optimize(Option, Bare, OBare), without_locs(O, OBare),
             run(O, sum, [10], 10000, ret(88)),
             pizlonate_module(O, Checked), valid_module(Checked),
             without_locs(Checked, CPlain),
             filc_module_asm(Checked, Asm), filc_module_asm(CPlain, Asm),
             Checked = module(CItems), memberchk(context(fib, CRs), CItems),
             member(site(inst(_, _), [_|_]), CRs)
           )),
    optimize(passes([promote]), M, module(PItems)),
    memberchk(context(sum, PRs), PItems),
    member(binding(S, s, long, at(_, 7)), PRs),
    member(value(Phi, named(S, value), [OId]), PRs),
    member(origin(OId, none, generated(promote, slot(S, 0, l)), _), PRs),
    member(site(phi(Phi), [OId]), PRs).

% Shadowing is binding identity, not spelling. Eliminating a's load
% must not rename its surviving parameter n; the inner n becomes 7.
test(source_binding_aliases) :-
    c_tokens("int f(int n) { int a=n; { int n=7; a+=n; } return a; }
              int g(int n) { return n; }", 'bindings.c', Ts),
    c_parse(Ts, C), c_module(C, M), valid_module(M),
    M = module(Is), memberchk(context(f, Rs), Is),
    findall(B, member(binding(B, n, int, _), Rs), [Outer, Inner]),
    Outer \== Inner,
    memberchk(binding(A, a, int, _), Rs),
    member(value(Param, named(Outer, value), [0]), Rs),
    optimize(o1, M, O), valid_module(O), reads_back(O),
    O = module(OIs), memberchk(context(f, ORs), OIs),
    member(alias(_, tmp(Param), named(A, value), _), ORs),
    member(alias(_, const(7), named(Inner, value), _), ORs),
    member(value(Param, named(Outer, value), [0]), ORs),
    run(O, f, [5], 100, ret(12)), run(O, g, [19], 100, ret(19)),
    forall(member(Goal, [promote_module, copy_module, local_storage:local_storage_module]),
           ( call(Goal, M, Direct), valid_module(Direct),
             Direct = module(DIs), memberchk(context(f, _), DIs) )).

% A switch of 64 cases reaches each case, and the default, within 20
% blocks: a binary search takes about 10, a compare chain up to 66.
% Case values are scrambled and include negatives (docs/perf.md).
test(switch_dispatch_is_logarithmic) :-
    findall(N-V, ( between(0, 63, N), V is (N * 37) mod 64 * 3 - 90 ), NVs),
    findall(Case, ( member(N-V, NVs),
                    format(atom(Case), " case ~d: return ~d;", [V, N]) ), Cases),
    atomic_list_concat(['int f(int x) { switch (x) {'|Cases], Head),
    atom_concat(Head, ' default: return -1; } }', Source),
    atom_chars(Source, Cs),
    c_tokens(Cs, 'switch.c', Ts), c_parse(Ts, C), c_module(C, M), valid_module(M),
    forall(member(N-V, NVs),
           ( W is V mod 4294967296, once(run(M, f, [W], 20, ret(N))) )),
    once(run(M, f, [1], 20, ret(4294967295))).

% Legacy location instructions become sidecars. A generated check and
% its access share the old access's location; metadata cannot excuse a
% loc or real instruction inserted between the proof and its use.
test(context_boundaries) :-
    F = func(f, export, w, [param(p, tmp(p))], [block(s, [], [
        loc('legacy.c', 17), let(tmp(x), w, load(sw), [tmp(p)])
    ], ret(tmp(x)))]),
    M = module([F]), valid_module(M),
    pizlonate_module(M, Checked), valid_module(Checked), reads_back(Checked),
    Checked = module([CF, context(f, Rs)]),
    memberchk(site(inst(s, 0), [AccessOrigin]), Rs),
    memberchk(site(inst(s, 1), [AccessOrigin]), Rs),
    memberchk(origin(AccessOrigin, at('legacy.c', 17), _, _), Rs),
    member(value(Q, none, [CheckOrigin]), Rs),
    memberchk(origin(CheckOrigin, none, generated(pizlonate, check), [AccessOrigin]), Rs),
    CF = func(f, export, w, Ps, [block(s, [], [Check, Access], J)]),
    Check = let(tmp(Q), a, _, _),
    forall(member(Between, [loc('legacy.c', 17), let(tmp(extra), w, copy, [const(0)])]),
           catch((valid_module(module([func(f, export, w, Ps,
                     [block(s, [], [Check, Between, Access], J)]), context(f, [])])), fail),
                 nanofil_error(_), true)),
    \+ valid_module(module([CF, context(missing, [])])),
    \+ valid_module(module([CF, context(f, [site(inst(s, 2), [])])])),
    \+ valid_module(module([CF, context(f, [value(x, none, [missing])])])),
    \+ valid_module(module([CF, context(f, [
        alias(chk0, const(1), none, []), alias(chk0, const(1), none, [])])])),
    valid_module(module([CF, context(f, [])])),
    module_mode(Checked, filc), module_stage(Checked, checked),
    % Existing sites count loc instructions too. Normalizing must move
    % the rich load attachment from 1 to 0 and merge, not duplicate, sites.
    Mixed = module([F, context(f, [
        origin(rich, at('legacy.c', 18), typed(val, int, load), []),
        site(inst(s, 1), [rich]), site(jump(s), [rich])])]),
    valid_module(Mixed), promote_module(Mixed, Normal), valid_module(Normal),
    Normal = module([_, context(f, NRs)]),
    memberchk(origin(Legacy, at('legacy.c', 17), statement(legacy), []), NRs),
    sort([rich, Legacy], Both),
    memberchk(site(inst(s, 0), Both), NRs), memberchk(site(jump(s), Both), NRs),
    \+ member(site(inst(s, 1), _), NRs),
    pizlonate_module(Mixed, Expanded), valid_module(Expanded),
    Expanded = module([_, context(f, ERs)]),
    memberchk(site(inst(s, 0), Both), ERs), memberchk(site(inst(s, 1), Both), ERs).

% A deleted executable name can be reused for a proof; its old constant
% alias must not describe the new definition. Occupied origin names are
% independent of executable freshness and cannot affect emitted code.
test(context_historical_names) :-
    M = module([func(f, local, w, [param(p, tmp(p))], [block(s, [], [
        let(tmp(chk0), w, copy, [const(1)]),
        let(tmp(x), w, load(sw), [tmp(p)])
    ], ret(tmp(x)))]), context(f, [
        origin(old, at('history.c', 2), statement(decl), []),
        origin(access, at('history.c', 3), typed(val, int, load), []),
        origin(pizlonate(chk0), none, generated(test, occupied), []),
        value(chk0, none, [old]), value(x, none, [access]),
        site(inst(s, 0), [old]), site(inst(s, 1), [access])])]),
    valid_module(M), copy_module(M, Copied), valid_module(Copied),
    Copied = module([_, context(f, CRs)]),
    memberchk(site(inst(s, 0), [access]), CRs),
    \+ member(site(inst(s, 1), _), CRs),
    pizlonate_module(Copied, Checked), valid_module(Checked), reads_back(Checked),
    Checked = module([func(f, _, _, _, [block(s, [], [
        let(tmp(chk0), a, _, _), let(tmp(x), w, raw_load(sw, 0), [tmp(chk0)])
    ], _)]), context(f, Rs)]),
    member(history(_, chk0, none, [old], replaced(const(1))), Rs),
    \+ member(alias(chk0, _, _, _), Rs),
    memberchk(value(chk0, none, [Proof]), Rs), Proof \== pizlonate(chk0),
    memberchk(origin(Proof, none, generated(pizlonate, check), [access]), Rs),
    without_locs(M, Bare), copy_module(Bare, BCopy), pizlonate_module(BCopy, BChecked),
    without_locs(Checked, BChecked),
    filc_module_asm(Checked, Asm), filc_module_asm(BChecked, Asm),
    % The alias TARGET can also be retired: local objects and proofs
    % inhabit different executable namespaces, despite sharing chk0.
    Local = module([func(g, local, w, [], [block(s, [], [
        let(tmp(chk0), p, alloc(4), [const(4)]),
        let(tmp(q), p, copy, [tmp(chk0)]),
        store(w, const(257), tmp(q)), store(b, const(2), tmp(q)),
        let(tmp(x), w, load(sw), [tmp(q)])
    ], ret(tmp(x)))]), context(g, [
        origin(o, none, statement(decl), []),
        value(chk0, none, [o]), value(q, none, [o]),
        history(earlier, previous, none, [o], replaced(tmp(chk0))),
        origin(earlier, none, generated(test, previous), [])])]),
    valid_module(Local), optimize(o1, Local, LOpt), valid_module(LOpt),
    pizlonate_module(LOpt, LChecked), valid_module(LChecked), reads_back(LChecked),
    LChecked = module([_, context(g, LRs)]),
    memberchk(alias(q, historical(Retired), none, [o]), LRs),
    memberchk(history(Retired, chk0, none, [o], none), LRs),
    memberchk(history(earlier, previous, none, [o], replaced(historical(Retired))), LRs),
    Historical = module([func(g, local, w, [], [block(s, [], [], ret(const(0)))]), context(g, LRs)]),
    copy_module(Historical, HCopy), valid_module(HCopy),
    HCopy = module([_, context(g, HRs)]), memberchk(alias(q, historical(Retired), none, [o]), HRs),
    without_locs(Local, LBare), optimize(o1, LBare, LBOpt), pizlonate_module(LBOpt, LBChecked),
    without_locs(LChecked, LBChecked),
    filc_module_asm(LChecked, LAsm), filc_module_asm(LBChecked, LAsm),
    run(LChecked, g, [], 100, ret(258)),
    LChecked = module([F|_]),
    \+ valid_module(module([F, context(g, [alias(q, historical(missing), none, [])])])).

% Completed array bounds are part of the binding type; a struct's
% first field shares its address, but is not a value of the whole struct.
test(context_binding_types) :-
    c_tokens("char g[] = \"abc\";
              struct S { int x, y; };
              int f(void) { char s[] = \"hi\"; struct S a = {1, 2};
                return a.x + s[0] + g[0]; }", 'types.c', Ts),
    c_parse(Ts, C), c_module(C, M), valid_module(M),
    M = module(Is), memberchk(context(f, Rs), Is),
    member(binding(_, s, array(char, 3), _), Rs),
    member(binding(global(g), g, array(char, 4), _), Rs),
    member(binding(A, a, struct(_), _), Rs),
    \+ member(value(_, named(A, value), _), Rs),
    optimize(o1, M, O), valid_module(O), run(O, f, [], 100, ret(202)).

% Pizlonation states the checks that load and store imply in filc mode,
% so the checked module has the same outcomes, traps included; deleting
% a check turns that trap into unchecked (not ub, not a trap), and the
% validator rejects the mutant. The object is [b, b+16): at offset 12 the
% w store and load fit and return 7; at offset 14 the store reaches b+18.
test(pizlonate_states_every_check) :-
    ir_module([
        func(f, export, w, [param(l, tmp(i))], [
            block(s, [], [
                let(tmp(b), p, alloc(8), [const(16)]),
                let(tmp(a), p, add, [tmp(b), tmp(i)]),
                store(w, const(7), tmp(a)),
                let(tmp(x), w, load(sw), [tmp(a)])
            ], ret(tmp(x)))
        ])
    ], M),
    pizlonate_module(M, C),
    valid_module(C),
    C = module([func(f, E, R, Ps, [block(s, [], Is, J)])]),
    Is = [Alloc, Add, let(tmp(Q), a, check(0, 4, write, 1), [tmp(a)]),
          raw_store(w, 0, const(7), tmp(Q)),
          let(tmp(Q2), a, check(0, 4, read, 1), [tmp(a)]),
          let(tmp(x), w, raw_load(sw, 0), [tmp(Q2)])],
    Q \== Q2,
    once(run(M, f, [12], 10, ret(7))),
    once(run(C, f, [12], 10, ret(7))),
    once(run(M, f, [14], 10, trap(out_of_bounds))),
    once(run(C, f, [14], 10, trap(out_of_bounds))),
    [_, _, _, _|Rest] = Is,
    Mutant = module([func(f, E, R, Ps,
                          [block(s, [], [Alloc, Add, raw_store(w, 0, const(7), tmp(a))|Rest],
                               J)])]),
    once(run(Mutant, f, [12], 10, ret(7))),
    once(run(Mutant, f, [14], 10, unchecked(out_of_bounds))),
    catch(( valid_module(Mutant), fail ), nanofil_error(Msg), true),
    Msg == 'in f: tmp(a) has class p but is used as a'.

% Pointer memory states the aux/barrier order, without new operand
% lifetimes. chk0 tests freshness; direct checked input is a normal form.
test(pizlonate_states_pointer_effects) :-
    Load = [aux_read, lower_resolve, address_read],
    Store = [aux_ensure, lower_barrier, rooted_reload, lower_write, address_write],
    ir_module([func(f, local, p, [], [block(s, [], [
        let(tmp(chk0), p, alloc(8), [const(16)]),
        store(p, const(7), tmp(chk0)),
        let(tmp(x), p, load(p), [tmp(chk0)])
    ], ret(tmp(x)))])], M),
    pizlonate_module(M, C), valid_module(C), reads_back(C),
    C = module([func(f, local, p, [], [block(s, [], [
        let(tmp(chk0), p, alloc(8), [const(16)]),
        let(tmp(chk1), a, check(0, 8, write, 8), [tmp(chk0)]),
        raw_store_pointer(0, const(7), tmp(chk1), Store),
        let(tmp(chk2), a, check(0, 8, read, 8), [tmp(chk0)]),
        let(tmp(x), p, raw_load_pointer(0, Load), [tmp(chk2)])
    ], ret(tmp(x)))])]),
    pizlonate_module(C, C1), C1 == C,
    optimize(o1, C, C2), C2 == C,
    once(run(C, f, [], 10, ret(ptr(7, none)))),
    inst_uses(raw_store_pointer(0, tmp(v), tmp(q), Store), [q, v]),
    forall(bad_pointer_effects(Load, Bad),
        rejected_pointer_access(read,
            let(tmp(x), p, raw_load_pointer(0, Bad), [tmp(q)]))),
    forall(bad_pointer_effects(Store, Bad),
        rejected_pointer_access(write, raw_store_pointer(0, const(7), tmp(q), Bad))),
    rejected_pointer_access(read, let(tmp(x), p, raw_load(p, 0), [tmp(q)])),
    rejected_pointer_access(write, raw_store(p, 0, const(7), tmp(q))),
    rejected_pointer_access(write, raw_store_pointer(0, tmp(q), tmp(q), Store)).

% Every obligation matters, as does its order; malformed protocols are
% rejected at the public checked-IR boundary, not repaired by emission.
bad_pointer_effects(Es, Bad) :-
    append(Before, [_|After], Es), append(Before, After, Bad).
bad_pointer_effects(Es, Bad) :-
    append(Before, [E|After], Es), append(Before, [E,E|After], Bad).
bad_pointer_effects(Es, Bad) :-
    append(Before, [A,B|After], Es), append(Before, [B,A|After], Bad).
bad_pointer_effects(Es, [unknown|Es]).

rejected_pointer_access(Rights, Access) :-
    \+ catch(valid_module(module([func(f, local, void, [param(p, tmp(a))], [
        block(s, [], [let(tmp(q), a, check(0, 8, Rights, 8), [tmp(a)]),
            Access], ret)])])), nanofil_error(_), fail).

% Replacing a pointer must replace both halves. Scalar stores instead
% retain the old lower. The two objects are disjoint and hold different
% values, so missing either write or the aux read cannot pass by chance.
test(pointer_memory_effects_execute) :-
    Prefix = [let(tmp(box), p, alloc(8), [const(16)]),
              let(tmp(a), p, alloc(8), [const(16)]),
              let(tmp(b), p, alloc(8), [const(16)]),
              store(l, const(41), tmp(a)), store(l, const(73), tmp(b))],
    forall(member(case(Is, K, Out), [
        case([store(p, tmp(a), tmp(box)), store(p, tmp(b), tmp(box)),
              let(tmp(p), p, load(p), [tmp(box)]),
              let(tmp(r), l, load(l), [tmp(p)])], l, ret(73)),
        case([store(p, tmp(a), tmp(box)), let(tmp(bits), l, ptoi, [tmp(b)]),
              store(l, tmp(bits), tmp(box)),
              let(tmp(p), p, load(p), [tmp(box)]),
              let(tmp(r), l, load(l), [tmp(p)])], l, trap(out_of_bounds)),
        case([store(l, const(19), tmp(box)),
              let(tmp(r), p, load(p), [tmp(box)])], p, ret(ptr(19, none))),
        case([store(p, tmp(a), tmp(box)), store(p, const(0), tmp(box)),
              let(tmp(r), p, load(p), [tmp(box)])], p, ret(ptr(0, none))),
        case([store(p, tmp(a), tmp(box)), store(p, const(19), tmp(box)),
              let(tmp(r), p, load(p), [tmp(box)])], p, ret(ptr(19, none))),
        % The source slot and result may be the same logical temporary.
        case([store(p, tmp(b), tmp(box)),
              let(tmp(box), p, load(p), [tmp(box)]),
              let(tmp(r), l, load(l), [tmp(box)])], l, ret(73)),
        case([store(p, tmp(box), tmp(box)),
              let(tmp(p), p, load(p), [tmp(box)]),
              let(tmp(r), l, sub, [const(9), const(2)]),
              store(l, tmp(r), tmp(p))], l, ret(7))
    ]), (
        append(Prefix, Is, All),
        ir_module([func(f, local, K, [], [block(s, [], All, ret(tmp(r)))])], M),
        pizlonate_module(M, C), valid_module(C),
        once(run(M, f, [], 10, Out)), once(run(C, f, [], 10, Out))
    )).

% Address arithmetic and lower propagation are separate decisions. The
% address wraps at 64 bits, while every kind of capability is preserved;
% an integer round trip keeps the address but discards the capability.
test(pizlonate_states_flight_components) :-
    ir_module([
        func(shift, local, p, [param(p, tmp(p)), param(l, tmp(n))], [
            block(s, [], [
                let(tmp(a), p, add, [tmp(p), tmp(n)]),
                let(tmp(b), p, sub, [tmp(a), const(2)]),
                let(tmp(r), p, copy, [tmp(b)])
            ], ret(tmp(r)))
        ]),
        func(forge, local, p, [param(p, tmp(p))], [
            block(s, [], [
                let(tmp(i), l, ptoi, [tmp(p)]),
                let(tmp(r), p, itop, [tmp(i)])
            ], ret(tmp(r)))
        ])
    ], M),
    pizlonate_module(M, C), valid_module(C), reads_back(C),
    pizlonate_module(C, C1), C1 == C,
    optimize(o1, C, C2), C2 == C,
    C = module([
        func(shift, local, p, _, [block(s, [], [
            flight(tmp(a), add, [address(tmp(p)), tmp(n)], lower(tmp(p))),
            flight(tmp(b), sub, [address(tmp(a)), const(2)], lower(tmp(a))),
            flight(tmp(r), copy, [address(tmp(b))], lower(tmp(b)))
        ], ret(tmp(r)))]),
        func(forge, local, p, _, [block(s, [], [
            let(tmp(i), l, ptoi, [tmp(p)]),
            flight(tmp(r), copy, [tmp(i)], none)
        ], ret(tmp(r)))])
    ]),
    forall(member(Cap, [none, obj(4096), ro(8192), fn(shift), ext(other)]),
           ( once(run(M, shift, [ptr(18446744073709551614, Cap), 5], 10,
                      ret(ptr(1, Cap)))),
             once(run(C, shift, [ptr(18446744073709551614, Cap), 5], 10,
                      ret(ptr(1, Cap)))),
             once(run(C, forge, [ptr(37, Cap)], 10, ret(ptr(37, none)))) )),
    once(run(C, shift, [ptr(18446744073709551614, obj(4096)), N], 10,
             ret(ptr(1, obj(4096))))),
    once(labeling([], [N])), N == 5.

% The lower donor need not supply the address: capabilities cannot be
% forged from integer bits, but may be paired with any computed address.
% Both projections are real uses, including in dominance and liveness.
test(flight_components_are_independent) :-
    F = func(f, local, p, [param(p, tmp(a)), param(p, tmp(b))], [
        block(s, [], [
            flight(tmp(r), sub, [address(tmp(a)), address(tmp(b))], lower(tmp(b)))
        ], ret(tmp(r)))
    ]),
    ir_module([F], M), reads_back(M),
    once(run(M, f, [ptr(31, obj(4096)), ptr(9, ro(8192))], 10,
             ret(ptr(22, ro(8192))))),
    inst_uses(flight(tmp(r), sub, [address(tmp(a)), address(tmp(b))], lower(tmp(c))),
              [a, b, c]),
    % Restoring an already held capability to capability-free address
    % bits succeeds; borrowing a disjoint object's lower still traps.
    forall(member(Source-Expected, [bits-ret(29), a-trap(out_of_bounds)]),
        ( ir_module([
            data(left, local, 8, [item(l, const(17))]),
            data(right, local, 8, [item(l, const(29))]),
            func(read, local, l, [], [block(s, [], [
                let(tmp(a), p, copy, [global(left)]),
                let(tmp(b), p, copy, [global(right)]),
                flight(tmp(bits), copy, [address(tmp(b))], none),
                flight(tmp(r), copy, [address(tmp(Source))], lower(tmp(b))),
                let(tmp(q), a, check(0, 8, read, 1), [tmp(r)]),
                let(tmp(v), l, raw_load(l, 0), [tmp(q)])
            ], ret(tmp(v)))])
          ], Access),
          once(run(Access, read, [], 10, Expected)) )),
    forall(member(Inst, [
        flight(tmp(r), copy, [const(1)], lower(const(7))),
        flight(tmp(r), copy, [address(const(1))], none)
    ]),
        ( ir_module([func(g, local, p, [], [block(s, [], [Inst], ret(tmp(r)))])], G),
          once(run(G, g, [], 10, ret(ptr(1, none)))) )),
    forall(member(Bad, [
        flight(tmp(r), mul, [const(2), const(3)], none),
        flight(tmp(r), add, [const(2)], none),
        flight(tmp(r), copy, [tmp(a)], lower(tmp(b))),
        flight(tmp(r), copy, [address(tmp(i))], none),
        flight(tmp(r), copy, [const(0)], lower(tmp(i))),
        flight(tmp(r), copy, [const(0)], const(4096)),
        flight(tmp(r), copy, [address(global(g))], none),
        flight(tmp(r), copy, [const(0)], lower(global(g))),
        flight(tmp(r), copy, [address(address(tmp(a)))], none)
    ]),
        \+ catch(valid_module(module([func(bad, local, p,
            [param(p, tmp(a)), param(p, tmp(b)), param(l, tmp(i))],
            [block(s, [], [Bad], ret(tmp(r)))])])), nanofil_error(_), fail)),
    forall(member(Inst, [
        flight(tmp(r), copy, [address(tmp(late))], none),
        flight(tmp(r), add, [const(0), address(tmp(late))], none),
        flight(tmp(r), copy, [const(0)], lower(tmp(late)))
    ]), rejected_with([func(late, local, p, [], [block(s, [], [
            Inst, flight(tmp(late), copy, [const(0)], none)
        ], ret(tmp(r)))])], "dominate")),
    % Even an unreachable flight selects the checked contract for the
    % entire module, including otherwise untouched functions.
    Witness = func(witness, local, void, [], [block(s, [], [], ret),
        block(dead, [], [flight(tmp(dead), copy, [const(0)], none)], ret)]),
    forall(member(Implicit, [
        let(tmp(r), p, add, [tmp(p), const(3)]),
        let(tmp(r), p, sub, [tmp(p), const(3)]),
        let(tmp(r), p, copy, [tmp(p)]),
        let(tmp(r), p, copy, [const(7)]),
        let(tmp(r), p, itop, [const(7)])
    ]), rejected_with([Witness, func(old, local, p, [param(p, tmp(p))],
        [block(s, [], [Implicit], ret(tmp(r)))])], "implicit pointer operation")).

% A function proof is not a memory proof. It certifies the exact
% function address, not just its capability. Removing it exposes a pass
% error; a trap from the callee or its ABI still belongs to the program.
test(pizlonate_states_function_checks) :-
    ir_module([
        func(subtract, local, l, [param(l, tmp(x)), param(l, tmp(y))], [
            block(s, [], [let(tmp(r), l, sub, [tmp(x), tmp(y)])], ret(tmp(r)))
        ]),
        func(f, export, l, [param(l, tmp(off))], [
            block(s, [], [
                let(tmp(chk0), p, copy, [global(subtract)]),
                let(tmp(p), p, add, [tmp(chk0), tmp(off)]),
                call(result(tmp(r), l), tmp(p), [arg(l, const(42)), arg(l, const(7))])
            ], ret(tmp(r)))
        ])
    ], M),
    pizlonate_module(M, C), valid_module(C), reads_back(C),
    pizlonate_module(C, C1), C1 == C,
    C = module([Sub, func(f, E, R, Ps, [block(s, [], Is, J)])]),
    Is = [Copy, Add, let(tmp(Q), f, check_function, [tmp(p)]),
          raw_call(Res, tmp(Q), Args)],
    Q \== chk0,
    forall(member(Input-Expected, [0-ret(35), 1-trap(not_a_function),
                                   8-trap(not_a_function)]),
           ( once(run(M, f, [Input], 10, Expected)),
             once(run(C, f, [Input], 10, Expected)) )),
    Mutant = module([Sub, func(f, E, R, Ps,
        [block(s, [], [Copy, Add, raw_call(Res, tmp(p), Args)], J)])]),
    once(run(Mutant, f, [0], 10, ret(35))),
    once(run(Mutant, f, [1], 10, unchecked(not_a_function))),
    catch(( valid_module(Mutant), fail ), nanofil_error(_), true),
    file_module('../tests/filc/globals.ir', G),
    pizlonate_module(G, GC), valid_module(GC),
    once(run(GC, toofew, [], 10, trap(argument_size))),
    once(run(GC, trapcall, [], 10, trap(readonly))),
    % A nested bad target must not be mistaken for a missing outer check.
    Nested = func(nested, local, w, [], [block(s, [], [
        let(tmp(p), p, copy, [global(nullfn)]),
        call(result(tmp(r), w), tmp(p), [])], ret(tmp(r)))]),
    G = module(GItems), pizlonate_module(module([Nested|GItems]), GN),
    valid_module(GN), once(run(GN, nested, [], 10, trap(not_a_function))),
    % Target identity alone says nothing about the number of result words.
    Returns = func(returns, local, tuple([l, l]), [], [block(s, [], [
        let(tmp(p), p, copy, [global(three)]),
        call(tuple([result(tmp(x), l), result(tmp(y), l)]), tmp(p),
             [arg(w, const(7))])], rets([tmp(x), tmp(y)]))]),
    pizlonate_module(module([Returns|GItems]), GR), valid_module(GR),
    once(run(GR, returns, [], 10, trap(return_size))),
    % No ordinary p temporary: this is still checked Fil-C IR.
    Null = module([func(null, local, void, [], [block(s, [], [
        let(tmp(q), f, check_function, [const(0)]),
        raw_call(void, tmp(q), [])], ret)])]),
    valid_module(Null), once(run(Null, null, [], 10, trap(not_a_function))),
    Ext = module([func(ext, local, void, [], [block(s, [], [
        let(tmp(p), p, copy, [global(external)]),
        let(tmp(q), f, check_function, [tmp(p)]),
        raw_call(void, tmp(q), [])], ret)])]),
    valid_module(Ext),
    catch(( run(Ext, ext, [], 10, _), fail ), nanofil_error(External), true),
    External == 'cannot interpret a call to external external'.

% Checked IR states which check covers an access, and nothing else may
% come between them; every loop polls.
test(checked_ir_rules) :-
    Weak = func(f, export, l, [param(p, tmp(a))], [
        block(s, [], [
            let(tmp(q), a, check(0, 4, read, 1), [tmp(a)]),
            let(tmp(x), l, raw_load(l, 0), [tmp(q)])
        ], ret(tmp(x)))
    ]),
    catch(( valid_module(module([Weak])), fail ), nanofil_error(M1), true),
    M1 == 'in f: check tmp(q) is not followed by an access it covers',
    Apart = func(f, export, l, [param(p, tmp(a))], [
        block(s, [], [
            let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
            call(void, global(g), []),
            let(tmp(x), l, raw_load(l, 0), [tmp(q)])
        ], ret(tmp(x)))
    ]),
    catch(( valid_module(module([Apart])), fail ), nanofil_error(M2), true),
    M2 == 'in f: check tmp(q) is not followed by an access it covers',
    Loop = func(f, export, w, [param(p, tmp(a))], [
        block(s, [], [], goto(h)),
        block(h, [], [
            let(tmp(q), a, check(0, 4, write, 1), [tmp(a)]),
            raw_store(w, 0, const(0), tmp(q))
        ], goto(h))
    ]),
    catch(( valid_module(module([Loop])), fail ), nanofil_error(M3), true),
    M3 == 'in f: a cycle without a poll edge in checked IR',
    Loop = func(F, E, R, Ps, [S, block(h, [], Is, goto(h))]),
    valid_module(module([func(F, E, R, Ps, [S, block(h, [], Is, goto(poll(h)))])])).

% Check reuse (docs/m7.md). A heap proof covers later scalar accesses
% in its block until an instruction that could free the object or reach
% a safepoint, or a redefinition of the proof or its pointer; never in
% another block, never more range or rights than its check, never a
% pointer access. reuse_fn(+Insts, -M): f(a, b) with body Insts.
reuse_fn(Insts, module([func(f, local, w, [param(p, tmp(a)), param(p, tmp(b))],
                             [block(s, [], Insts, ret(const(0)))])])).

reuse_l_fn(Insts, module([func(f, local, l, [], [block(s, [], Insts, ret(tmp(x)))])])).

% reuse_fail_jumps(+M, -N): M's assembly jumps to a check failure block
% after N lower tests, one per heap access check.
reuse_fail_jumps(M, N) :-
    filc_module_asm(M, Lines),
    findall(F, ( member(ins(jz, none, [sym(F)]), Lines),
                 atom_concat(_, Suffix, F), atom_concat('..fail.', _, Suffix) ), Fs),
    length(Fs, N).

reuse_rejected(M) :-
    catch(( valid_module(M), fail ), nanofil_error(Msg), true),
    Msg == 'in f: a raw access at tmp(q) that no live check covers'.

test(reuse_validation) :-
    pointer_memory_effects(load, LoadEs), pointer_memory_effects(store, StoreEs),
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]),
    S = raw_store(l, 0, const(1), tmp(q)),
    L = let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
    % Accepted: a write proof covers a later 4- and 8-byte read across
    % arithmetic, another object's check and scalar store, and a pointer
    % load; a write between two reads may reuse a write proof.
    forall(member(Insts, [
        [C, S, L],
        [C, S, let(tmp(n), l, add, [const(1), const(2)]),
         let(tmp(r), a, check(0, 8, write, 1), [tmp(b)]),
         raw_store(l, 0, tmp(n), tmp(r)),
         flight(tmp(c), add, [address(tmp(b)), const(8)], lower(tmp(b))),
         let(tmp(y), w, raw_load(sw, 0), [tmp(q)]),
         let(tmp(r2), a, check(0, 8, read, 8), [tmp(b)]),
         let(tmp(z), p, raw_load_pointer(0, LoadEs), [tmp(r2)]),
         L, raw_store(w, 0, const(2), tmp(q))]
    ]), ( reuse_fn(Insts, M), valid_module(M) )),
    % Rejected: whatever may free, exit or relabel comes between.
    forall(member(Between, [
        [call(void, global(g), [])],
        [call(void, global(free), [arg(p, tmp(b))])],
        [let(tmp(n), p, alloc(8), [const(8)])],
        [let(tmp(n), p, copy, [global(g)])],
        [let(tmp(r), a, check(0, 8, write, 8), [tmp(b)]),
         raw_store_pointer(0, tmp(b), tmp(r), StoreEs)],
        [let(tmp(r), f, check_function, [tmp(b)]), raw_call(void, tmp(r), [])],
        [flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b)))],
        [let(tmp(q), a, check(0, 4, write, 1), [tmp(b)]),
         raw_store(w, 0, const(3), tmp(q))]
    ]), ( append([[C, S], Between, [L]], Insts), reuse_fn(Insts, M),
          reuse_rejected(M) )),
    % Rejected: too little range, a read proof for a write, a pointer
    % access at a live proof.
    forall(member(Insts, [
        [let(tmp(q), a, check(0, 4, write, 1), [tmp(a)]),
         raw_store(w, 0, const(1), tmp(q)), L],
        [let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]), L, S],
        [let(tmp(q), a, check(0, 8, write, 8), [tmp(a)]), S,
         let(tmp(z), p, raw_load_pointer(0, LoadEs), [tmp(q)])]
    ]), ( reuse_fn(Insts, M), reuse_rejected(M) )),
    % A check on one arm does not dominate the join at all.
    catch(( valid_module(module([func(f, local, w, [param(p, tmp(a)), param(w, tmp(c))], [
                block(s, [], [], branch(tmp(c), t, u)),
                block(t, [], [C, S], goto(u)),
                block(u, [], [L], ret(const(0)))])])), fail ),
          nanofil_error(_), true).

% Across edges (docs/m7.md): evidence flows along plain edges and is
% intersected at joins; a poll edge, an edge from a later block, a free
% on one path or a phi redefining the pointer ends it.
% reuse_cfg(+Blocks, -M): f(a, b, c) with Blocks.
reuse_cfg(Blocks, module([func(f, local, w,
    [param(p, tmp(a)), param(p, tmp(b)), param(w, tmp(c))], Blocks)])).

test(reuse_edges) :-
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]),
    S = raw_store(l, 0, const(1), tmp(q)),
    L = let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
    Free = call(void, global(free), [arg(p, tmp(a))]),
    R = ret(const(0)),
    forall(member(Bs, [
        [block(s, [], [C, S], goto(t)), block(t, [], [L], R)],
        [block(s, [], [C, S], branch(tmp(c), t, u)), block(t, [], [], goto(j)),
         block(u, [], [], goto(j)), block(j, [], [L], R)]
    ]), ( reuse_cfg(Bs, M), valid_module(M) )),
    forall(member(Bs, [
        % a poll edge, even forward
        [block(s, [], [C, S], goto(poll(t))), block(t, [], [L], R)],
        % one arm of the same branch polls
        [block(s, [], [C, S], branch(tmp(c), poll(j), j)), block(j, [], [L], R)],
        % free on one path
        [block(s, [], [C, S], branch(tmp(c), t, j)), block(t, [], [Free], goto(j)),
         block(j, [], [L], R)],
        % the same, from a block after the join in block order
        [block(s, [], [C, S], branch(tmp(c), j, t)), block(j, [], [L], R),
         block(t, [], [Free], goto(j))],
        % branch-only: q proves 8 bytes only on t's path, 4 on u's
        [block(s, [], [let(tmp(q), a, check(0, 4, write, 1), [tmp(a)]),
                       raw_store(w, 0, const(1), tmp(q))], branch(tmp(c), t, j)),
         block(t, [], [C, S], goto(j)), block(j, [], [L], R)],
        % a phi redefines the checked pointer
        [block(s, [], [C, S], branch(tmp(c), t, j)), block(t, [], [], goto(j)),
         block(j, [phi(tmp(a), p, [s-tmp(b), t-tmp(b)])], [L], R)],
        % loop-carried: the previous iteration freed a
        [block(s, [], [C, S], goto(h)),
         block(h, [], [L, Free], goto(poll(h)))]
    ]), ( reuse_cfg(Bs, M), reuse_rejected(M) )),
    % The pass deletes the join's check only when every path checked p,
    % keeps it after a free on one path or around a loop, and all three
    % keep the reference outcomes.
    Alloc = let(tmp(p), p, alloc(8), [const(8)]),
    St = store(l, const(5), tmp(p)), Ld = let(tmp(y), l, load(l), [tmp(p)]),
    PFree = call(void, global(free), [arg(p, tmp(p))]),
    forall(member(Bs-Checks-Outs, [
        [block(s, [], [Alloc, St], branch(tmp(c), t, u)),
         block(t, [], [], goto(j)), block(u, [], [], goto(j)),
         block(j, [], [Ld], ret(tmp(y)))]-1-[ret(5), ret(5)],
        [block(s, [], [Alloc, St], branch(tmp(c), t, j)),
         block(t, [], [PFree], goto(j)),
         block(j, [], [Ld], ret(tmp(y)))]-2-[trap(out_of_bounds), ret(5)],
        [block(s, [], [Alloc, St], goto(h)),
         block(h, [phi(tmp(i), l, [s-const(0), h-tmp(i1)])],
               [Ld, let(tmp(i1), l, add, [tmp(i), const(1)]),
                let(tmp(d), w, cmp(slt, l), [tmp(i1), const(3)])],
               branch(tmp(d), h, e)),
         block(e, [], [], ret(tmp(y)))]-2-[ret(5), ret(5)]
    ]), (
        M = module([func(g, local, l, [param(w, tmp(c))], Bs)]),
        valid_module(M), pizlonate_module(M, Ck), reuse_checks(Ck, Re),
        reuse_refines(Ck, Re), valid_module(Re),
        reuse_fail_jumps(Re, Checks),
        Outs = [O1, O0],
        forall(member(X, [M, Ck, Re]),
               ( once(run(X, g, [1], 20, O1)), once(run(X, g, [0], 20, O0)) ))
    )),
    Rc = let(tmp(r), a, check(0, 8, read, 1), [tmp(a)]),
    Lr = let(tmp(x), l, raw_load(l, 0), [tmp(r)]),
    % Emission reuses across an edge only a proof and pointer each
    % defined once; a second definition of a, even unreachable, refuses.
    reuse_cfg([block(s, [], [C, S], goto(t)), block(t, [], [L], R)], One),
    reuse_fail_jumps(One, 1),
    reuse_cfg([block(s, [], [C, S], goto(t)), block(t, [], [L], R),
               block(u, [], [flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b)))], R)],
              Two),
    valid_module(Two),
    catch(( filc_module_asm(Two, _), fail ), nanofil_error(_), true),
    % Nor when the proof's name has two definitions: here t's reuse is
    % of v's check of a, and reloading u's pointer b would be wrong.
    reuse_cfg([block(s, [], [], goto(v)),
               block(u, [], [let(tmp(q), a, check(0, 8, write, 1), [tmp(b)]),
                             raw_store(l, 0, const(2), tmp(q))], R),
               block(v, [], [C, S], goto(t)), block(t, [], [L], R)], TwoQ),
    valid_module(TwoQ),
    catch(( filc_module_asm(TwoQ, _), fail ), nanofil_error(_), true),
    % Nor does the pass carry a proof over a poll edge.
    reuse_cfg([block(s, [], [C, S], goto(poll(t))), block(t, [], [Rc, Lr], R)], Polled),
    valid_module(Polled), reuse_checks(Polled, Polled1), Polled1 == Polled,
    % So the pass rewires across an edge only under the same condition.
    reuse_cfg([block(s, [], [C, S], goto(t)), block(t, [], [Rc, Lr], R),
               block(u, [], [flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b)))], R)],
              TwoChecked),
    valid_module(TwoChecked), reuse_checks(TwoChecked, TwoChecked1), TwoChecked1 == TwoChecked,
    % A deleted proof must have had no reader in another block.
    Zr = let(tmp(z), l, raw_load(l, 0), [tmp(r)]),
    reuse_cfg([block(s, [], [C, S], goto(t)), block(t, [], [Rc, Lr], goto(u)),
               block(u, [], [Zr], R)], Before),
    valid_module(Before),
    reuse_cfg([block(s, [], [C, S], goto(t)), block(t, [], [L], goto(u)),
               block(u, [], [Zr], R)], After),
    \+ reuse_refines(Before, After),
    reuse_checks(Before, Before1), Before1 == Before.

% The interpreter re-checks every raw access against the object as it
% is now: stale evidence after free is unchecked where the reference
% traps. A proof of the wrong object is safe, so only reuse_refines/2
% rejects that rewiring: 10 * 1 + 2 = 12 becomes 11.
test(reuse_semantics) :-
    Alloc = let(tmp(p), p, alloc(8), [const(8)]),
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(p)]),
    S = raw_store(l, 0, const(5), tmp(q)),
    Free = call(void, global(free), [arg(p, tmp(p))]),
    R = let(tmp(r), a, check(0, 8, read, 1), [tmp(p)]),
    reuse_l_fn([Alloc, C, S, Free, R, let(tmp(x), l, raw_load(l, 0), [tmp(r)])], Fresh),
    valid_module(Fresh), once(run(Fresh, f, [], 10, trap(out_of_bounds))),
    reuse_l_fn([Alloc, C, S, Free, let(tmp(x), l, raw_load(l, 0), [tmp(q)])], Stale),
    \+ catch(valid_module(Stale), nanofil_error(_), fail),
    once(run(Stale, f, [], 10, unchecked(out_of_bounds))),
    Two = [let(tmp(a), p, alloc(8), [const(8)]), let(tmp(b), p, alloc(8), [const(8)]),
           let(tmp(qa), a, check(0, 8, write, 1), [tmp(a)]), raw_store(l, 0, const(1), tmp(qa)),
           let(tmp(qb), a, check(0, 8, write, 1), [tmp(b)]), raw_store(l, 0, const(2), tmp(qb)),
           let(tmp(u), l, raw_load(l, 0), [tmp(qa)])],
    Tail = [let(tmp(t), l, mul, [tmp(u), const(10)]), let(tmp(x), l, add, [tmp(t), tmp(v)])],
    append([Two, [let(tmp(rb), a, check(0, 8, read, 1), [tmp(b)]),
                  let(tmp(v), l, raw_load(l, 0), [tmp(rb)])], Tail], RefInsts),
    reuse_l_fn(RefInsts, Ref), valid_module(Ref), once(run(Ref, f, [], 10, ret(12))),
    reuse_checks(Ref, Reused), reuse_refines(Ref, Reused), valid_module(Reused),
    once(run(Reused, f, [], 10, ret(12))),
    append([Two, [let(tmp(v), l, raw_load(l, 0), [tmp(qa)])], Tail], WrongInsts),
    reuse_l_fn(WrongInsts, Wrong), valid_module(Wrong), once(run(Wrong, f, [], 10, ret(11))),
    \+ reuse_refines(Ref, Wrong).

% The pass deletes exactly the covered checks of pizlonated IR, and on
% hand-written checked IR compares with the deleted check itself, not
% its access, and forgets a proof whose name is redefined.
test(reuse_pass) :-
    ir_module([func(f, local, l, [param(w, tmp(v))], [block(s, [], [
        let(tmp(p), p, alloc(4), [const(8)]),
        store(w, tmp(v), tmp(p)),
        let(tmp(x), w, load(sw), [tmp(p)]),
        let(tmp(y), l, load(l), [tmp(p)]),
        call(void, global(free), [arg(p, tmp(p))]),
        let(tmp(z), w, load(sw), [tmp(p)])
    ], ret(tmp(y)))])], M),
    pizlonate_module(M, C), reuse_checks(C, R),
    reuse_refines(C, R), valid_module(R),
    R = module([func(f, local, l, _, [block(s, [], [_,
        let(tmp(Q), a, check(0, 4, write, 1), [tmp(p)]), raw_store(w, 0, tmp(v), tmp(Q)),
        let(tmp(x), w, raw_load(sw, 0), [tmp(Q)]),
        let(tmp(Q2), a, check(0, 8, read, 1), [tmp(p)]),
        let(tmp(y), l, raw_load(l, 0), [tmp(Q2)]),
        _, let(tmp(Q3), a, check(0, 4, read, 1), [tmp(p)]), _], _)])|_]),
    Q \== Q2, Q2 \== Q3,
    forall(member(Mod, [M, C, R]), once(run(Mod, f, [7], 10, trap(out_of_bounds)))),
    % A read proof does not subsume a hand-written wider write check
    % before a read: the readonly trap stays.
    Ro = module([data(msg, ro(local), 1, [item(b, str("h"))]),
        func(g, local, w, [], [block(s, [], [
            let(tmp(p), p, copy, [global(msg)]),
            let(tmp(q), a, check(0, 1, read, 1), [tmp(p)]),
            let(tmp(x), w, raw_load(ub, 0), [tmp(q)]),
            let(tmp(r), a, check(0, 1, write, 1), [tmp(p)]),
            let(tmp(y), w, raw_load(ub, 0), [tmp(r)])
        ], ret(tmp(y)))])]),
    valid_module(Ro), reuse_checks(Ro, Ro1), Ro1 == Ro,
    once(run(Ro, g, [], 10, trap(readonly))),
    % q proves a, then b: r's check of a must stay, and reading b
    % instead would return 2, not 1.
    Re = module([func(h, local, l, [], [block(s, [], [
            let(tmp(a), p, alloc(8), [const(8)]),
            let(tmp(b), p, alloc(8), [const(8)]),
            let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]),
            raw_store(l, 0, const(1), tmp(q)),
            let(tmp(q), a, check(0, 8, write, 1), [tmp(b)]),
            raw_store(l, 0, const(2), tmp(q)),
            let(tmp(r), a, check(0, 8, read, 1), [tmp(a)]),
            let(tmp(x), l, raw_load(l, 0), [tmp(r)])
        ], ret(tmp(x)))])]),
    valid_module(Re), reuse_checks(Re, Re1), Re1 == Re,
    once(run(Re, h, [], 10, ret(1))),
    % A deleted check's proof must have no other reader: here x reads
    % q's proof of b after it, so deleting that check and pointing only y
    % at r would leave x reading q's proof of a, 1 instead of 2.
    Two = [let(tmp(a), p, alloc(8), [const(8)]), let(tmp(b), p, alloc(8), [const(8)]),
           let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]), raw_store(l, 0, const(1), tmp(q)),
           let(tmp(r), a, check(0, 8, write, 1), [tmp(b)]), raw_store(l, 0, const(2), tmp(r))],
    Last = [let(tmp(x), l, raw_load(l, 0), [tmp(q)])],
    append([Two, [let(tmp(q), a, check(0, 8, read, 1), [tmp(b)]),
                  let(tmp(y), l, raw_load(l, 0), [tmp(q)])], Last], ReadIs),
    append([Two, [let(tmp(y), l, raw_load(l, 0), [tmp(r)])], Last], WrongIs),
    Rd = module([func(k, local, l, [], [block(s, [], ReadIs, ret(tmp(x)))])]),
    Wr = module([func(k, local, l, [], [block(s, [], WrongIs, ret(tmp(x)))])]),
    valid_module(Rd), once(run(Rd, k, [], 10, ret(2))),
    valid_module(Wr), once(run(Wr, k, [], 10, ret(1))),
    \+ reuse_refines(Rd, Wr), reuse_checks(Rd, Rd1), Rd1 == Rd.

% Emission reads a reused access at the checked pointer without a
% check, and refuses one whose pointer was redefined since its check,
% which only the validator would otherwise catch.
test(reuse_emission) :-
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]),
    S = raw_store(l, 0, const(1), tmp(q)),
    L = let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
    reuse_fn([C, S, L], Reused), valid_module(Reused),
    reuse_fail_jumps(Reused, 1),
    reuse_fn([C, S, let(tmp(r), a, check(0, 8, read, 1), [tmp(a)]),
              let(tmp(x), l, raw_load(l, 0), [tmp(r)])], Ref),
    reuse_fail_jumps(Ref, 2),
    reuse_fn([C, S, flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b))), L], Moved),
    catch(( filc_module_asm(Moved, _), fail ), nanofil_error(_), true),
    % Also when the fused first access itself redefines the pointer.
    pointer_memory_effects(load, Es),
    reuse_fn([let(tmp(q), a, check(0, 8, write, 8), [tmp(a)]),
              let(tmp(a), p, raw_load_pointer(0, Es), [tmp(q)]), L], Loaded),
    catch(( filc_module_asm(Loaded, _), fail ), nanofil_error(_), true).

% The IR can describe wider proofs than subq's signed immediate. Native
% compilation must refuse them, never emit an immediate that changes size.
test(native_check_range) :-
    forall(member(Size, [8, 2147483647, 2147483648, 4294967296]),
        ( M = module([func(f, export, l, [param(p, tmp(p))], [
              block(s, [], [
                  let(tmp(q), a, check(0, Size, read, 1), [tmp(p)]),
                  let(tmp(r), l, raw_load(l, 0), [tmp(q)])
              ], ret(tmp(r)))])]),
          valid_module(M),
          ( Size =< 2147483647 -> filc_module_asm(M, _)
          ; catch((filc_module_asm(M, _), fail), nanofil_error(_), true)
          ) )).

% Only the immediately preceding function check authorizes a raw call.
% Neither a memory proof nor a proof carried across an effect qualifies.
test(checked_call_rules) :-
    Check = let(tmp(q), f, check_function, [tmp(p)]),
    Call = raw_call(void, tmp(q), []),
    Prefix = flight(tmp(p), copy, [const(0)], none),
    valid_module(module([func(f, local, void, [], [
        block(s, [], [Prefix, Check, Call], ret)])])),
    forall(member(Insts, [
        [Prefix, Check, call(void, global(g), []), Call],
        [Prefix, Check, Call, Call],
        [Prefix, let(tmp(q), a, check(0, 8, read, 8), [tmp(p)]), Call],
        [Prefix, Check, raw_call(void, tmp(p), [])],
        [Prefix, Check, Call, call(void, tmp(p), [])],
        [Prefix, Check, raw_call(void, tmp(q), [arg(f, tmp(q))])],
        [Prefix, Check, raw_call(result(tmp(r), f), tmp(q), [])],
        [Prefix, Check, raw_call(tuple([result(tmp(r), l), result(tmp(t), f)]), tmp(q), [])],
        [Prefix, Check, raw_call(void, const(0), [])],
        [Prefix, Check, raw_call(result(tmp(r), a), tmp(q), [])],
        [Prefix, Check, raw_call(tuple([result(tmp(r), a), result(tmp(t), l)]), tmp(q), [])],
        [Prefix, Check, raw_call(void, tmp(q), [arg(a, const(0))])],
        [Prefix, Check, Call, let(tmp(r), w, copy, [tmp(q)])],
        [Prefix, Check, Call, let(tmp(r), l, copy, [tmp(q)])],
        [Prefix, Check, Call, flight(tmp(r), copy, [address(tmp(q))], none)],
        [Prefix, Check, Call, flight(tmp(r), copy, [const(0)], lower(tmp(q)))],
        [Prefix, Check, Call, store(l, tmp(q), tmp(p))],
        [Prefix, Check, Call, let(tmp(r), f, copy, [tmp(q)])],
        [Prefix, Check],
        [Prefix, Check, raw_call(void, tmp(other), [])]
    ]), catch(( valid_module(module([func(f, local, void, [], [
                    block(s, [], Insts, ret)])])), fail ), nanofil_error(_), true)),
    catch(( valid_module(module([func(f, local, void, [param(f, tmp(q))], [
                block(s, [], [Call], ret)])])), fail ), nanofil_error(_), true).

% A host atom built at run time is an atom of arity 0 only. Unpatched
% Trealla unified it with any same-name compound, so a field named label
% entered a label/2 clause (patches/trealla-runtime-atom-arity-unify.patch).
test(runtime_atom_is_not_a_compound) :-
    atom_chars(A, "foo"), \+ A = foo(_),
    atom_concat(fo, o, C), \+ C = foo(_, _, _),
    atom_codes(B, [0'f, 0'o, 0'o]), \+ B = foo(_),
    \+ foo = foo(_),
    atom_chars(L, "label"),
    findall(K, label_shape(L, K), [atom]),
    A == foo, B == foo, C == foo.

label_shape(label(_, _), compound).
label_shape(label, atom).

% c_file_module(+File, -Module): Module is the valid module of the C
% in File, lexed without preprocessing.
c_file_module(F, M) :-
    phrase_from_file(seq(Cs), F),
    c_tokens(Cs, F, Ts),
    c_parse(Ts, Items),
    c_module(Items, M),
    valid_module(M).

%% Documentation examples (docs/dterm.md)

% Every example in a module's doc/3 holds: example(Goal) succeeds,
% example(Goal, Check) succeeds with Check true, fails(Goal) fails.
% Goals run in the module that documents them.
test(doc_examples) :-
    findall(M-E, doc_example(M, E), Es),
    Es = [_|_],
    findall(M-E, ( member(M-E, Es), \+ doc_example_holds(M, E) ), Bad),
    forall(member(M-E, Bad), format("  ~w: ~q does not hold~n", [M, E])),
    Bad == [].

doc_example(M, E) :-
    documented_module(M),
    M:doc(_, _, Props),
    member(E, Props),
    doc_example_form(E).

documented_module(c_types).

doc_example_form(example(_)).
doc_example_form(example(_, _)).
doc_example_form(fails(_)).

doc_example_holds(M, example(G)) :- once(M:G).
doc_example_holds(M, example(G, C)) :- once(( M:G, C )).
doc_example_holds(M, fails(G)) :- \+ M:G.
