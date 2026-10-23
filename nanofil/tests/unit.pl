/*  Interpreter, validator and printer tests that native differential
    testing cannot cover: outcomes qbe has no counterpart for, inputs qbe
    miscompiles, and queries that run the semantics backwards.

    Run from nanofil/src:  tpl -q ../tests/unit.pl
    Expected values are derived by hand in the comments, not from the
    interpreter.
*/
:- use_module('../src/ir').
:- use_module('../src/qbe_parse').
:- use_module('../src/qbe_print').
:- use_module('../src/interp').
:- use_module(library(clpz)).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(dcgs)).

:- dynamic(test/1).
:- initialization(main).

main :-
    findall(T, clause(test(T), _), Ts),
    foldl(run_test, Ts, 0, Failed),
    length(Ts, N),
    (   Failed =:= 0
    ->  format("nanofil unit: ~w tests ok~n", [N]), halt(0)
    ;   format("nanofil unit: ~w of ~w failed~n", [Failed, N]), halt(1)
    ).

run_test(T, F0, F) :-
    (   catch(once(test(T)), E, (format("~w: raised ~q~n", [T, E]), fail))
    ->  F = F0
    ;   format("FAILED ~w~n", [T]), F is F0 + 1
    ).

mod(Text, M) :- parse_qbe_chars(Text, M), valid_module(M).
mod_file(F, M) :- parse_qbe_file(F, M), valid_module(M).

outcome(M, Fn, Args, Out) :- once(run(M, Fn, Args, 1000, Out)).

rejects(Text, Fragment) :-
    catch(( mod(Text, _), fail ), nanofil_error(Msg), true),
    atom_chars(Msg, Cs),
    append(_, Rest, Cs), append(Fragment, _, Rest), !.

%% Spec answers where qbe 1.2 / c081897 are wrong (tests/qbe-bugs)

% memory 11 22 88 99 aa bb 77 88, loaduh at 5 = 0x77bb
test(storew_of_l_stores_low_word) :-
    mod_file('../tests/qbe-bugs/storew-l.ssa', M),
    outcome(M, f, [9833440827789222417, 18441921395520346504], ret(30651)).

% -128 >> 0 = -128, nonzero
test(jnz_after_shift_by_zero) :-
    mod_file('../tests/qbe-bugs/jnz-shift-flags.ssa', M),
    outcome(M, f, [0], ret(1)),
    outcome(M, f, [1], ret(1)).

% 2^32 has zero low 32 bits
test(jnz_tests_low_32_bits) :-
    mod_file('../tests/qbe-bugs/jnz-long-flags.ssa', M),
    outcome(M, f, [4294967296, 0], ret(0)).

%% Outcomes with no native counterpart

test(division_by_zero_and_overflow) :-
    mod("export function w $f(w %a, w %b) {\n@s\n\t%q =w div %a, %b\n\tret %q\n}\n", M),
    outcome(M, f, [5, 0], ub(division_by_zero)),
    outcome(M, f, [2147483648, 4294967295], ub(division_overflow)),
    % -7 / 2 truncates to -3
    outcome(M, f, [4294967289, 2], ret(4294967293)).

test(store_past_allocation) :-
    mod("export function $f() {\n@s\n\t%p =l alloc4 4\n\t%q =l add %p, 1\n\tstorew 0, %q\n\tret\n}\n", M),
    outcome(M, f, [], ub(out_of_bounds(_, 4))).

test(use_after_return) :-
    mod("function l $leak() {\n@s\n\t%p =l alloc8 8\n\tstorel 1, %p\n\tret %p\n}\nexport function l $f() {\n@s\n\t%p =l call $leak()\n\t%v =l loadl %p\n\tret %v\n}\n", M),
    outcome(M, f, [], ub(out_of_bounds(_, 8))).

test(data_overrun) :-
    mod("data $d = { w 1 }\nexport function w $f() {\n@s\n\t%p =l add $d, 2\n\t%v =w loadw %p\n\tret %v\n}\n", M),
    outcome(M, f, [], ub(out_of_bounds(_, 4))).

% Two of the four bytes are unwritten: the result is unknown, but the
% written low half is still known.
test(uninitialized_bytes_are_unknown) :-
    mod("export function w $f() {\n@s\n\t%p =l alloc4 4\n\tstoreh 4660, %p\n\t%v =w loadw %p\n\tret %v\n}\n", M),
    outcome(M, f, [], ret(V)),
    var(V),
    V mod 65536 #= 4660.

test(hlt) :-
    mod("export function $f() {\n@s\n\thlt\n}\n", M),
    outcome(M, f, [], hlt).

test(out_of_fuel) :-
    mod("export function $f() {\n@s\n\tjmp @l\n@l\n\tjmp @l\n}\n", M),
    outcome(M, f, [], out_of_fuel).

%% Running backwards

% 3x + 1 = 7 (mod 2^32) has the unique solution x = 2.
test(backwards_find_input) :-
    mod("export function w $f(w %x) {\n@s\n\t%y =w mul %x, 3\n\t%z =w add %y, 1\n\tret %z\n}\n", M),
    run(M, f, [X], 10, ret(7)),
    once(labeling([], [X])),
    X =:= 2.

% Which input reaches hlt? Only x = 12345, found by propagation alone.
test(backwards_reach_hlt) :-
    mod("export function w $f(w %x) {\n@s\n\t%c =w ceqw %x, 12345\n\tjnz %c, @bad, @ok\n@bad\n\thlt\n@ok\n\tret 0\n}\n", M),
    run(M, f, [X], 10, hlt),
    X == 12345.

% Signed division by 2 is not an arithmetic shift: they differ at -1
% (-1 / 2 = 0, -1 >> 1 = -1).
test(backwards_counterexample) :-
    mod("export function w $d(w %x) {\n@s\n\t%y =w div %x, 2\n\tret %y\n}\nexport function w $s(w %x) {\n@s\n\t%y =w sar %x, 1\n\tret %y\n}\n", M),
    run(M, d, [X], 10, ret(A)),
    run(M, s, [X], 10, ret(B)),
    A #\= B,
    % Bound the search so an implementation where they agree fails fast
    % instead of enumerating 2^32 inputs.
    X in 0..255 \/ 4294967040..4294967295,
    once(labeling([down], [X])),
    X =:= 4294967295, A =:= 0, B =:= 4294967295.

%% Validator and parser diagnostics

test(rejects_w_temp_as_l) :-
    rejects("export function l $f(w %a) {\n@s\n\t%b =l add %a, 1\n\tret %b\n}\n",
            "%a has class w but is used as l").
test(rejects_jump_to_entry) :-
    rejects("export function $f() {\n@s\n\tjmp @s\n}\n", "jump to the entry block").
test(rejects_missing_phi_argument) :-
    rejects("export function w $f(w %a) {\n@s\n\tjnz %a, @x, @y\n@x\n\tjmp @y\n@y\n\t%v =w phi @x 1\n\tret %v\n}\n",
            "predecessors are").
test(rejects_floats_with_line) :-
    rejects("export function d $f() {\n@s\n\tret\n}\n", "line 1: only w and l").
test(rejects_unknown_instruction) :-
    rejects("export function w $f(w %a) {\n@s\n\t%b =w swtof %a\n\tret %b\n}\n",
            "line 3: unsupported instruction swtof").

%% Printing

test(print_round_trip) :-
    forall(member(F, ['../tests/fixtures/arith.ssa', '../tests/fixtures/memory.ssa']),
           ( mod_file(F, M),
             phrase(module_chars(M), Cs),
             mod(Cs, M2),
             M2 == M )).
