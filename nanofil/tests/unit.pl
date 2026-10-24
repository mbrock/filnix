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
:- use_module('../src/c_lex').
:- use_module('../src/c_parse').
:- use_module('../src/c_lower').
:- use_module('../src/c_types').
:- use_module('../src/asm').
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
        func(f, export, w, [par(w, t(a)), par(w, t(b))], [
            blk(s, [], [
                ins(t(q), w, div, [t(a), t(b)])
            ], ret(t(q)))
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
            blk(s, [], [
                ins(t(p), l, alloc(4), [c(4)]),
                ins(t(q), l, add, [t(p), c(1)]),
                store(w, c(0), t(q))
            ], ret)
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% An allocation dies with its function: loading through a returned
% pointer to it is out of bounds.
test(use_after_return) :-
    ir_module([
        func(leak, local, l, [], [
            blk(s, [], [
                ins(t(p), l, alloc(8), [c(8)]),
                store(l, c(1), t(p))
            ], ret(t(p)))
        ]),
        func(f, export, l, [], [
            blk(s, [], [
                call(to(t(p), l), glo(leak), []),
                ins(t(v), l, load(l), [t(p)])
            ], ret(t(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 8))).

% A 4-byte load at offset 2 of a 4-byte data definition is out of
% bounds.
test(data_overrun) :-
    ir_module([
        data(d, local, 8, [item(w, c(1))]),
        func(f, export, w, [], [
            blk(s, [], [
                ins(t(p), l, add, [glo(d), c(2)]),
                ins(t(v), w, load(sw), [t(p)])
            ], ret(t(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% Two of the four bytes are unwritten: the result is unknown, but the
% written low half is still known.
test(uninitialized_bytes_are_unknown) :-
    ir_module([
        func(f, export, w, [], [
            blk(s, [], [
                ins(t(p), l, alloc(4), [c(4)]),
                store(h, c(4660), t(p)),
                ins(t(v), w, load(sw), [t(p)])
            ], ret(t(v)))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], ret(V)),
    var(V),
    V mod 65536 #= 4660.

% hlt is its own outcome.
test(hlt) :-
    ir_module([
        func(f, export, void, [], [
            blk(s, [], [], hlt)
        ])
    ], M),
    module_fn_args_outcome(M, f, [], hlt).

% An infinite loop ends as out_of_fuel.
test(out_of_fuel) :-
    ir_module([
        func(f, export, void, [], [
            blk(s, [], [], jmp(l)),
            blk(l, [], [], jmp(l))
        ])
    ], M),
    module_fn_args_outcome(M, f, [], out_of_fuel).

%% Running backwards

% 3x + 1 = 7 (mod 2^32) has the unique solution x = 2.
test(backwards_find_input) :-
    ir_module([
        func(f, export, w, [par(w, t(x))], [
            blk(s, [], [
                ins(t(y), w, mul, [t(x), c(3)]),
                ins(t(z), w, add, [t(y), c(1)])
            ], ret(t(z)))
        ])
    ], M),
    run(M, f, [X], 10, ret(7)),
    once(labeling([], [X])),
    X =:= 2.

% Which input reaches hlt? Only x = 12345, found by propagation alone.
test(backwards_reach_hlt) :-
    ir_module([
        func(f, export, w, [par(w, t(x))], [
            blk(s, [], [
                ins(t(c), w, cmp(eq, w), [t(x), c(12345)])
            ], jnz(t(c), bad, ok)),
            blk(bad, [], [], hlt),
            blk(ok, [], [], ret(c(0)))
        ])
    ], M),
    run(M, f, [X], 10, hlt),
    X == 12345.

% Signed division by 2 is not an arithmetic shift: they differ at -1
% (-1 / 2 = 0, -1 >> 1 = -1).
test(backwards_counterexample) :-
    ir_module([
        func(d, export, w, [par(w, t(x))], [
            blk(s, [], [
                ins(t(y), w, div, [t(x), c(2)])
            ], ret(t(y)))
        ]),
        func(s, export, w, [par(w, t(x))], [
            blk(s, [], [
                ins(t(y), w, sar, [t(x), c(1)])
            ], ret(t(y)))
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
        func(f, export, l, [par(w, t(a))], [
            blk(s, [], [
                ins(t(b), l, add, [t(a), c(1)])
            ], ret(t(b)))
        ])
    ],
                  "t(a) has class w but is used as l").
% The entry block cannot be a jump target.
test(rejects_jump_to_entry) :-
    rejected_with([
        func(f, export, void, [], [
            blk(s, [], [], jmp(s))
        ])
    ],
                  "jump to the entry block").
% A phi needs an argument for every predecessor.
test(rejects_missing_phi_argument) :-
    rejected_with([
        func(f, export, w, [par(w, t(a))], [
            blk(s, [], [], jnz(t(a), x, y)),
            blk(x, [], [], jmp(y)),
            blk(y, [
                phi(t(v), w, [x-c(1)])
            ], [], ret(t(v)))
        ])
    ],
                  "predecessors are").
% Unsupported instructions are refused with their line.
test(rejects_unknown_instruction) :-
    rejected_with([
        func(f, export, w, [par(w, t(a))], [
            blk(s, [], [
                ins(t(b), w, sqrt, [t(a)])
            ], ret(t(b)))
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
                              [blk(start, [], [], ret(c(Bits)))])]),
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
                              [blk(start, [], [ins(t(x), s, Op, [c(0), c(0)])],
                                   ret(t(x)))])]),
             catch((valid_module(M), fail), nanofil_error(_), true) )),
    rejected_with([
        func(f, local, w, [par(s, t(x))], [
            blk(start, [], [
                ins(t(y), w, copy, [t(x)])
            ], ret(t(y)))
        ])
    ],
                  "has class s but is used as w"),
    rejected_with([
        func(f, local, w, [par(s, t(x))], [
            blk(start, [], [
                ins(t(y), w, cmp(sle, s), [t(x), t(x)])
            ], ret(t(y)))
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
        func(f, local, d, [par(d, t(x))], [
            blk(start, [], [
                ins(t(y), d, add, [t(x), c(4607182418800017408)])
            ], ret(t(y)))
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
            blk(start, [], [
                ins(t(p), p, alloc(8), [c(16)]),
                ins(t(q), p, add, [t(p), c(8)]),
                store(s, c(2147483648), t(p)),
                store(d, c(18444492273895866370), t(q)),
                ins(t(s), s, load(s), [t(p)]),
                ins(t(d), d, load(d), [t(q)]),
                ins(t(w), w, cast, [t(s)]),
                ins(t(l), l, cast, [t(d)]),
                ins(t(v), l, ext(uw), [t(w)]),
                ins(t(r), l, xor, [t(l), t(v)])
            ], ret(t(r)))
        ])
    ], M),
    Expected is xor(18444492273895866370, 2147483648),
    module_fn_args_outcome(M, f, [], ret(Expected)).

%% Class p

% A p temporary cannot be read as l without ptoi.
test(rejects_p_as_l) :-
    rejected_with([
        func(f, export, l, [par(p, t(a))], [
            blk(s, [], [
                ins(t(b), l, add, [t(a), c(1)])
            ], ret(t(b)))
        ])
    ],
                  "t(a) has class p but is used as l (use ptoi)").
% In a Fil-C module (one using p), an l temporary cannot be used as an
% address without itop.
test(rejects_l_as_p) :-
    rejected_with([
        func(f, export, w, [par(l, t(a))], [
            blk(s, [], [
                ins(t(v), w, load(sw), [t(a)])
            ], ret(t(v)))
        ]),
        func(g, export, p, [], [
            blk(s, [], [
                ins(t(q), p, alloc(8), [c(8)])
            ], ret(t(q)))
        ])
    ],
                  "t(a) has class l but is used as p (use itop)").
% Pointers cannot be multiplied.
test(rejects_pointer_multiply) :-
    rejected_with([
        func(f, export, p, [par(p, t(a))], [
            blk(s, [], [
                ins(t(b), p, mul, [t(a), c(2)])
            ], ret(t(b)))
        ])
    ],
                  "instruction mul cannot have class p").
% Fil-C data holds a symbol's address as p, not l.
test(rejects_l_symbol_in_filc_data) :-
    rejected_with([
        data(d, local, 8, [item(l, sym(d, 0))]),
        func(f, export, p, [], [
            blk(s, [], [
                ins(t(q), p, alloc(8), [c(8)])
            ], ret(t(q)))
        ])
    ],
                  "is item(p, sym(d, _))").
% Fil-C code materializes a symbol with copy before using it.
test(rejects_symbol_operand_in_filc) :-
    rejected_with([
        data(d, local, 8, [item(w, c(1))]),
        func(f, export, w, [], [
            blk(s, [], [
                ins(t(q), p, add, [glo(d), c(4)]),
                ins(t(v), w, load(sw), [t(q)])
            ], ret(t(v)))
        ])
    ],
                  "only copy at p reads glo(d)").

% Which offsets can a 1-byte read of a 16-byte allocation take without
% trapping? Exactly 0..15.
test(in_bounds_offsets) :-
    ir_module([
        func(f, export, w, [par(l, t(i))], [
            blk(s, [], [
                ins(t(p), p, alloc(8), [c(16)]),
                ins(t(q), p, add, [t(p), t(i)]),
                ins(t(v), w, load(ub), [t(q)])
            ], ret(t(v)))
        ])
    ], M),
    findall(I,
            ( between(0, 40, I),
              once(run(M, f, [I], 10, ret(_)))
            ),
            Is),
    numlist(0, 15, Expected),
    Is == Expected.

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
                           item(b, c(7))]),
        func(f, export, w, [par(l, t(i))], [
            blk(s, [], [
                ins(t(p), l, add, [glo(d), t(i)]),
                ins(t(v), w, load(ub), [t(p)])
            ], ret(t(v)))
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
    func(f, export, w, [par(w, t(p))], [
        blk(s, [], [
            ins(t(x), w, copy, [t(p)]),
            ins(t(y), w, copy, [c(1)])
        ], jmp(a)),
        blk(a, [], [], jnz(t(x), b, c)),
        blk(b, [], [
            ins(t(z), w, add, [t(y), c(1)])
        ], jmp(d)),
        blk(c, [], [], jmp(d)),
        blk(d, [
            phi(t(w), w, [b-t(z), c-t(y)])
        ], [], jnz(t(w), a, e)),
        blk(e, [], [], ret(t(x)))
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
    Bs = [blk(s, [], [], jmp(outer)),
          blk(latch_b, [], [], jmp(outer)),
          blk(inner, [], [], jnz(t(n), spin, latch_a)),
          blk(spin, [], [], jmp(inner)),
          blk(outer, [], [], jnz(t(n), inner, self)),
          blk(latch_a, [], [], jnz(t(n), outer, latch_b)),
          blk(dead, [], [], jmp(inner)),
          blk(self, [], [], jnz(t(n), self, choice)),
          blk(choice, [], [], jnz(t(n), u, v)),
          blk(u, [], [], jnz(t(n), v, done)),
          blk(v, [], [], jnz(t(n), u, done)),
          blk(done, [], [], ret)],
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
    F = func(f, export, p, [par(p, t(p)), par(l, t(n)), par(w, t(c))],
             [blk(s, [],
                  [ins(t(a), p, alloc(8), [c(32)]),
                   ins(t(a4), p, add, [t(a), c(4)]),
                   ins(t(wrap), p, add, [t(a4), c(18446744073709551615)]),
                   ins(t(back), p, sub, [t(wrap), c(-1)]),
                   ins(t(q), p, copy, [t(p)]),
                   ins(t(q9), p, add, [t(q), c(9)]),
                   ins(t(g), p, copy, [glo(global)]),
                   ins(t(raw), l, ptoi, [t(a)]),
                   ins(t(cast), p, itop, [t(raw)]),
                   ins(t(loaded), p, load(p), [t(a)]),
                   ins(t(loaded3), p, add, [t(loaded), c(3)]),
                   call(to(t(called), p), glo(external), []),
                   ins(t(vary), p, add, [t(a), t(n)]),
                   ins(t(narrow), w, copy, [t(n)]),
                   ins(t(wide), l, ext(uw), [t(narrow)]),
                   ins(t(nplus), l, sub, [t(n), c(18446744073709551615)]),
                   ins(t(nwrap), l, add, [c(18446744073709551616), t(n)])],
                  jnz(t(c), left, right)),
              blk(left, [], [], jmp(join)),
              blk(right, [], [], jmp(join)),
              blk(join, [phi(t(merged), p, [left-t(a), right-t(q)])],
                  [ins(t(result), p, add, [t(merged), c(5)])],
                  ret(t(result)))]),
    once(valid_module(module([data(global, local, 8, [item(l, c(7))]),
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
        func(f, export, w, [par(l, t(n))], [
            blk(s, [], [
                ins(t(a), p, alloc(4), [c(8)]),
                ins(t(b), p, add, [t(a), c(4)]),
                store(w, c(1), t(a)),
                store(w, c(2), t(b)),
                ins(t(v), w, load(sw), [t(b)]),
                ins(t(e), p, alloc(8), [c(8)]),
                call(void, glo(g), [arg(p, t(e))]),
                ins(t(f), p, alloc(8), [c(8)]),
                ins(t(i), l, ptoi, [t(f)]),
                ins(t(h), p, alloc(8), [c(8)]),
                ins(t(q), p, add, [t(h), t(n)]),
                ins(t(m), p, alloc(8), [c(8)]),
                ins(t(z), p, alloc(8), [c(8)]),
                store(p, t(m), t(z))
            ], ret(t(v)))
        ])
    ], M),
    M = module([F]),
    alloc_classes(F, Cs),
    Cs == [a-local(c(8), [acc(0, w), acc(4, w)]),
           e-escapes(call),
           f-escapes(ptoi),
           h-escapes(add),
           m-escapes(stored),
           z-local(c(8), [acc(0, p)])].

% Fil-C allocations are zero: a read before any write gives 0, and a
% pointer read before any write has no capability, so using it traps.
test(promote_reads_zero_in_filc) :-
    ir_module([
        func(f, export, w, [], [
            blk(s, [], [
                ins(t(s), p, alloc(4), [c(4)]),
                ins(t(v), w, load(sw), [t(s)])
            ], ret(t(v)))
        ]),
        func(g, export, w, [], [
            blk(s, [], [
                ins(t(s), p, alloc(8), [c(8)]),
                ins(t(q), p, load(p), [t(s)]),
                ins(t(v), w, load(sw), [t(q)])
            ], ret(t(v)))
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
              member(blk(_, _, Ins, _), Bs),
              member(ins(_, _, alloc(_), _), Ins)
            ),
            Kept),
    Kept == [arr, ptrs].

% The optimizer must actually remove aliases, not just preserve results.
% Keep the narrowing copy, global materialization and non-SSA function.
test(copy_eliminates_aliases) :-
    file_module('../tests/fixtures/copy.ir', M0),
    optimize(o1, M0, M),
    once(valid_module(M)),
    forall(member(Name, [chain, swap, constants]),
           ( func_named(M, Name, func(_, _, _, _, Bs)),
             \+ ( member(blk(_, _, Is, _), Bs),
                  member(ins(_, _, copy, _), Is)
                )
           )),
    func_named(M, narrow, func(_, _, _, _, [blk(_, _, Narrow, _)])),
    findall(K, member(ins(_, K, copy, _), Narrow), [w]),
    func_named(M, global, func(_, _, _, _, [blk(_, _, Global, _)])),
    memberchk(ins(_, l, copy, [glo(cell)]), Global),
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
        func(f, export, w, [par(w, t(n))], [
            blk(s, [], [], jmp(loop)),
            blk(loop, [
                phi(t(p), p, [s-c(0), loop-t(p)])
            ], [], jnz(t(n), loop, done)),
            blk(done, [], [], ret(c(7)))
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
            ( member(blk(_, Ps, _, _), Bs),
              member(phi(t(T), _, _), Ps)
            ),
            Ts),
    sort(Ts, Names).

% copy leaves a non-SSA function (a use before its definition) and a
% literal pointer copy, which keeps the module Fil-C, unchanged.
test(copy_keeps_unguarded_definitions) :-
    ir_module([
        func(f, export, l, [par(l, t(x))], [
            blk(s, [], [
                ins(t(a), l, copy, [t(b)]),
                ins(t(b), l, add, [t(x), c(1)])
            ], ret(t(a)))
        ])
    ], NonSSA),
    copy_module(NonSSA, Unchanged),
    NonSSA == Unchanged,
    ir_module([
        func(f, export, w, [], [
            blk(s, [], [
                ins(t(p), p, copy, [c(0)])
            ], ret(c(7)))
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
    member(blk(_, _, Is0, _), Bs0),
    member(ins(_, p, copy, _), Is0),
    !,
    optimize(o1, M0, M),
    once(valid_module(M)),
    M = module(Items),
    \+ ( member(func(_, _, _, _, Bs), Items),
         member(blk(_, _, Is, _), Bs),
         member(ins(_, p, copy, _), Is)
       ),
    func_phi_names(M, sum, [j, left, p, right, s]).

% Unlike promote, copy moves no allocations. Compare whole pointer values,
% including object identity: equal offsets in different objects are not equal.
test(copy_preserves_pointer_identity) :-
    ir_module([
        func(f, export, p, [par(w, t(which))], [
            blk(s, [], [
                ins(t(a), p, alloc(8), [c(8)]),
                ins(t(b), p, alloc(8), [c(8)]),
                ins(t(x), p, copy, [t(a)]),
                ins(t(y), p, copy, [t(b)])
            ], jnz(t(which), left, right)),
            blk(left, [], [], jmp(join)),
            blk(right, [], [], jmp(join)),
            blk(join, [
                phi(t(p), p, [left-t(x), right-t(y)])
            ], [
                ins(t(q), p, copy, [t(p)])
            ], ret(t(q)))
        ]),
        func(raw, export, p, [], [
            blk(s, [], [
                ins(t(a), p, alloc(8), [c(8)]),
                ins(t(p), p, copy, [t(a)]),
                ins(t(i), l, ptoi, [t(p)]),
                ins(t(raw), p, itop, [t(i)]),
                ins(t(q), p, copy, [t(raw)])
            ], ret(t(q)))
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
        func(f, export, l, [par(l, t(x))], [
            blk(s, [], [
                ins(t(w), w, copy, [t(x)]),
                ins(t(r), l, ext(uw), [t(w)])
            ], ret(t(r)))
        ])
    ], Before),
    ir_module([
        func(f, export, l, [par(l, t(x))], [
            blk(s, [], [], ret(t(x)))
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
            blk(s, [], [
                ins(t(p), p, alloc(8), [c(16)])
            ], ret(t(p)))
        ]),
        func(m, export, w, [], [
            blk(s, [], [
                ins(t(f), p, copy, [glo(k)]),
                call(to(t(r), w), t(f), [])
            ], ret(t(r)))
        ])
    ], M),
    module_fn_args_outcome(M, m, [], Out),
    Out = ret(V),
    integer(V).

test(variadic_slot_stays_in_memory) :-
    ir_module([
        func(f, export, l, [par(p, t(args))], [
            blk(s, [], [
                ins(t(slot), p, alloc(8), [c(24)]),
                store(p, t(args), t(slot)),
                ins(t(x), l, va_arg, [t(slot)])
            ], ret(t(x)))
        ])
    ], M0),
    optimize(o1, M0, M), valid_module(M),
    M = module([F]), F = func(_, _, _, _, [blk(_, _, Is, _)]),
    member(ins(Slot, p, alloc(8), [c(24)]), Is),
    member(ins(_, l, va_arg, [Slot]), Is),
    alloc_classes(F, Classes), memberchk(slot-escapes(va_arg), Classes),
    reads_back(M).

test(variadic_invalid_ir) :-
    rejected_with([
        func(f, local, w, [], [
            blk(s, [], [
                ins(t(x), w, va_arg, [c(0)])
            ], ret(t(x)))
        ])
    ], "va_arg"),
    rejected_with([
        func(f, local, p, [], [
            blk(s, [], [
                ins(t(x), p, va_args, [c(-1)])
            ], ret(t(x)))
        ])
    ], "non-negative"),
    rejected_with([
        func(f, local, p, [par(l, t(n))], [
            blk(s, [], [
                ins(t(x), p, va_args, [t(n)])
            ], ret(t(x)))
        ])
    ], "constant").

test(setjmp_contract) :-
    file_module('../tests/filc/setjmp.ir', M),
    reads_back(M),
    module_mode(M, filc),
    promote_module(M, M), copy_module(M, M),
    ir_module([
        func(f, local, w, [par(p, t(buf))], [
            blk(s, [], [
                ins(t(slot), p, alloc(8), [c(8)]),
                store(w, c(3), t(slot)),
                ins(t(copy), w, copy, [c(9)]),
                ins(t(x), w, setjmp('_setjmp'), [t(buf), c(0)]),
                ins(t(v), w, load(sw), [t(slot)]),
                ins(t(out), w, add, [t(v), t(copy)])
            ], ret(t(out)))
        ])
    ], Kept),
    Kept = module([F]),
    promote_func(filc, F, F), promotable(filc, F, []),
    promote_module(Kept, Kept), copy_module(Kept, Kept),
    ir_module([
        func(f, local, w, [], [
            blk(s, [], [
                ins(t(x), w, setjmp(sigsetjmp), [c(0), c(1)])
            ], ret(t(x)))
        ])
    ], Null),
    module_mode(Null, filc),
    catch(run(Null, f, [], 100, _), nanofil_error(Msg), true),
    Msg == 'interpreter does not support setjmp/nonlocal returns',
    rejected_with([
        func(f, local, w, [], [
            blk(s, [], [
                ins(t(x), w, setjmp(setjmp), [c(0), c(1)])
            ], ret(t(x)))
        ])
    ], "zero SaveMask"),
    rejected_with([
        func(f, local, w, [], [
            blk(s, [], [
                ins(t(x), w, setjmp('_setjmp'), [c(0), c(1)])
            ], ret(t(x)))
        ])
    ], "zero SaveMask"),
    rejected_with([
        func(f, local, p, [], [
            blk(s, [], [
                ins(t(x), p, setjmp(setjmp), [c(0), c(0)])
            ], ret(t(x)))
        ])
    ], "class p").

% Lowered C says where its code comes from: every block of tests/c/
% locations.c begins with a loc/2, each statement's code follows its own
% line, and a loop's condition and step are at the loop's line. By hand:
% fib's entry is line 2 then the return, line 3, whose ?: arms and join
% are line 3 too; sum's entry is line 6, its declaration 7 and the for
% 8; the condition is 8, the body 9, the step 8 and the return 10. The
% middle end and the backends do not see them.
test(source_locations) :-
    c_file_module('../tests/c/locations.c', M),
    M = module(Items),
    findall(Fn-Lines,
            ( member(func(Fn, _, _, _, Bs), Items),
              findall(Ls, ( member(blk(_, _, Is, _), Bs),
                            findall(L, member(loc(_, L), Is), Ls) ),
                      Lines) ),
            FnLines),
    FnLines == [fib-[[2, 3], [3], [3], [3]],
                sum-[[6, 7, 8], [8], [9], [8], [10]]],
    optimize(o1, M, O), without_locs(O, O1), O1 == O.

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
