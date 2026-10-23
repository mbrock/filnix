/*  Interpreter, validator and printer tests that native differential
    testing cannot cover: outcomes qbe has no counterpart for, inputs qbe
    miscompiles, and queries that run the semantics backwards.

    Run from nanofil/src:  ../bin/nanofil --script ../tests/unit.pl
    Expected values are derived by hand in the comments, not from the
    interpreter.

    Each test(Name) clause is one test; it passes if its body succeeds
    once without raising. QBE sources are string literals split at their
    newlines with the ISO continuation escape (a backslash ending the
    line), so the next source line starts in column 0 of the file and
    the string is unchanged.
*/
:- use_module('../src/ir').
:- use_module('../src/qbe_parse').
:- use_module('../src/qbe_print').
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
:- use_module(library(assoc)).
:- use_module(library(pio)).
:- use_module(library(clpz)).
:- use_module(library(lists)).
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

% text_module(+Text, -Module): Module is the valid module of QBE Text.
text_module(Text, M) :-
    parse_qbe_chars(Text, M),
    valid_module(M).

% file_module(+File, -Module): Module is the valid module in QBE File.
file_module(F, M) :-
    parse_qbe_file(F, M),
    valid_module(M).

% first_outcome(+Module, +Fn, +Args, ?Outcome): Outcome is the first
% outcome of $Fn(Args) on Module with fuel for 1000 blocks.
first_outcome(M, Fn, Args, Out) :-
    once(run(M, Fn, Args, 1000, Out)).

% rejected_with(+Text, +Fragment): parsing or validating QBE Text throws
% a nanofil_error whose message contains the characters Fragment.
rejected_with(Text, Fragment) :-
    catch(( text_module(Text, _),
            fail
          ),
          nanofil_error(Msg),
          true),
    atom_chars(Msg, Cs),
    append(_, Rest, Cs),
    append(Fragment, _, Rest),
    !.

%% Spec answers where qbe 1.2 / c081897 are wrong (tests/qbe-bugs)

% storew of an l value stores its low word.
% memory 11 22 88 99 aa bb 77 88, loaduh at 5 = 0x77bb
test(storew_of_l_stores_low_word) :-
    file_module('../tests/qbe-bugs/storew-l.ssa', M),
    first_outcome(M, f, [9833440827789222417, 18441921395520346504],
                  ret(30651)).

% jnz after a shift by zero tests the shifted value, not stale flags.
% -128 >> 0 = -128, nonzero
test(jnz_after_shift_by_zero) :-
    file_module('../tests/qbe-bugs/jnz-shift-flags.ssa', M),
    first_outcome(M, f, [0], ret(1)),
    first_outcome(M, f, [1], ret(1)).

% jnz tests only the low 32 bits of its operand.
% 2^32 has zero low 32 bits
test(jnz_tests_low_32_bits) :-
    file_module('../tests/qbe-bugs/jnz-long-flags.ssa', M),
    first_outcome(M, f, [4294967296, 0], ret(0)).

%% Outcomes with no native counterpart

% Division by zero and INT_MIN / -1 are undefined; other division
% truncates toward zero.
test(division_by_zero_and_overflow) :-
    text_module("export function w $f(w %a, w %b) {\n\
@s\n\
\t%q =w div %a, %b\n\
\tret %q\n\
}\n", M),
    first_outcome(M, f, [5, 0], ub(division_by_zero)),
    first_outcome(M, f, [2147483648, 4294967295], ub(division_overflow)),
    % -7 / 2 truncates to -3
    first_outcome(M, f, [4294967289, 2], ret(4294967293)).

% A 4-byte store at offset 1 of a 4-byte allocation is out of bounds.
test(store_past_allocation) :-
    text_module("export function $f() {\n\
@s\n\
\t%p =l alloc4 4\n\
\t%q =l add %p, 1\n\
\tstorew 0, %q\n\
\tret\n\
}\n", M),
    first_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% An allocation dies with its function: loading through a returned
% pointer to it is out of bounds.
test(use_after_return) :-
    text_module("function l $leak() {\n\
@s\n\
\t%p =l alloc8 8\n\
\tstorel 1, %p\n\
\tret %p\n\
}\n\
export function l $f() {\n\
@s\n\
\t%p =l call $leak()\n\
\t%v =l loadl %p\n\
\tret %v\n\
}\n", M),
    first_outcome(M, f, [], ub(out_of_bounds(_, 8))).

% A 4-byte load at offset 2 of a 4-byte data definition is out of
% bounds.
test(data_overrun) :-
    text_module("data $d = { w 1 }\n\
export function w $f() {\n\
@s\n\
\t%p =l add $d, 2\n\
\t%v =w loadw %p\n\
\tret %v\n\
}\n", M),
    first_outcome(M, f, [], ub(out_of_bounds(_, 4))).

% Two of the four bytes are unwritten: the result is unknown, but the
% written low half is still known.
test(uninitialized_bytes_are_unknown) :-
    text_module("export function w $f() {\n\
@s\n\
\t%p =l alloc4 4\n\
\tstoreh 4660, %p\n\
\t%v =w loadw %p\n\
\tret %v\n\
}\n", M),
    first_outcome(M, f, [], ret(V)),
    var(V),
    V mod 65536 #= 4660.

% hlt is its own outcome.
test(hlt) :-
    text_module("export function $f() {\n\
@s\n\
\thlt\n\
}\n", M),
    first_outcome(M, f, [], hlt).

% An infinite loop ends as out_of_fuel.
test(out_of_fuel) :-
    text_module("export function $f() {\n\
@s\n\
\tjmp @l\n\
@l\n\
\tjmp @l\n\
}\n", M),
    first_outcome(M, f, [], out_of_fuel).

%% Running backwards

% 3x + 1 = 7 (mod 2^32) has the unique solution x = 2.
test(backwards_find_input) :-
    text_module("export function w $f(w %x) {\n\
@s\n\
\t%y =w mul %x, 3\n\
\t%z =w add %y, 1\n\
\tret %z\n\
}\n", M),
    run(M, f, [X], 10, ret(7)),
    once(labeling([], [X])),
    X =:= 2.

% Which input reaches hlt? Only x = 12345, found by propagation alone.
test(backwards_reach_hlt) :-
    text_module("export function w $f(w %x) {\n\
@s\n\
\t%c =w ceqw %x, 12345\n\
\tjnz %c, @bad, @ok\n\
@bad\n\
\thlt\n\
@ok\n\
\tret 0\n\
}\n", M),
    run(M, f, [X], 10, hlt),
    X == 12345.

% Signed division by 2 is not an arithmetic shift: they differ at -1
% (-1 / 2 = 0, -1 >> 1 = -1).
test(backwards_counterexample) :-
    text_module("export function w $d(w %x) {\n\
@s\n\
\t%y =w div %x, 2\n\
\tret %y\n\
}\n\
export function w $s(w %x) {\n\
@s\n\
\t%y =w sar %x, 1\n\
\tret %y\n\
}\n", M),
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
    rejected_with("export function l $f(w %a) {\n\
@s\n\
\t%b =l add %a, 1\n\
\tret %b\n\
}\n",
                  "%a has class w but is used as l").
% The entry block cannot be a jump target.
test(rejects_jump_to_entry) :-
    rejected_with("export function $f() {\n\
@s\n\
\tjmp @s\n\
}\n",
                  "jump to the entry block").
% A phi needs an argument for every predecessor.
test(rejects_missing_phi_argument) :-
    rejected_with("export function w $f(w %a) {\n\
@s\n\
\tjnz %a, @x, @y\n\
@x\n\
\tjmp @y\n\
@y\n\
\t%v =w phi @x 1\n\
\tret %v\n\
}\n",
                  "predecessors are").
% Float classes are refused with the line they appear on.
test(rejects_floats_with_line) :-
    rejected_with("export function d $f() {\n\
@s\n\
\tret\n\
}\n",
                  "line 1: only w, l and p").
% Unsupported instructions are refused with their line.
test(rejects_unknown_instruction) :-
    rejected_with("export function w $f(w %a) {\n\
@s\n\
\t%b =w swtof %a\n\
\tret %b\n\
}\n",
                  "line 3: unsupported instruction swtof").

%% Class p

% A p temporary cannot be read as l without ptoi.
test(rejects_p_as_l) :-
    rejected_with("export function l $f(p %a) {\n\
@s\n\
\t%b =l add %a, 1\n\
\tret %b\n\
}\n",
                  "%a has class p but is used as l (use ptoi)").
% In a Fil-C module (one using p), an l temporary cannot be used as an
% address without itop.
test(rejects_l_as_p) :-
    rejected_with("export function w $f(l %a) {\n\
@s\n\
\t%v =w loadw %a\n\
\tret %v\n\
}\n\
export function p $g() {\n\
@s\n\
\t%q =p alloc8 8\n\
\tret %q\n\
}\n",
                  "%a has class l but is used as p (use itop)").
% Pointers cannot be multiplied.
test(rejects_pointer_multiply) :-
    rejected_with("export function p $f(p %a) {\n\
@s\n\
\t%b =p mul %a, 2\n\
\tret %b\n\
}\n",
                  "instruction mul cannot have class p").
% Fil-C data holds a symbol's address as p, not l.
test(rejects_l_symbol_in_filc_data) :-
    rejected_with("data $d = { l $d }\n\
export function p $f() {\n\
@s\n\
\t%q =p alloc8 8\n\
\tret %q\n\
}\n",
                  "use p $d for a pointer").
% Fil-C code materializes a symbol with copy before using it.
test(rejects_symbol_operand_in_filc) :-
    rejected_with("data $d = { w 1 }\n\
export function w $f() {\n\
@s\n\
\t%q =p add $d, 4\n\
\t%v =w loadw %q\n\
\tret %v\n\
}\n",
                  "use %t =p copy $d").

% Which offsets can a 1-byte read of a 16-byte allocation take without
% trapping? Exactly 0..15.
test(in_bounds_offsets) :-
    text_module("export function w $f(l %i) {\n\
@s\n\
\t%p =p alloc8 16\n\
\t%q =p add %p, %i\n\
\t%v =w loadub %q\n\
\tret %v\n\
}\n", M),
    findall(I,
            ( between(0, 40, I),
              once(run(M, f, [I], 10, ret(_)))
            ),
            Is),
    numlist(0, 15, Expected),
    Is == Expected.

%% Printing

% Printing a module and parsing the text gives the same module back.
test(print_round_trip) :-
    forall(member(F, ['../tests/fixtures/arith.ssa',
                      '../tests/fixtures/memory.ssa']),
           ( file_module(F, M),
             phrase(module_chars(M), Cs),
             text_module(Cs, M2),
             M2 == M
           )).

%% Middle end (M5)

% s -> a; a -> b | c; b, c -> d; d -> a | e. The loop a..d makes a its
% own frontier; b and c join at d. x lives from s to the exit, y around
% the loop (read in b and as d's phi argument on the edge from c), z
% only on the edge b -> d, and w is defined by d's phi.
loop_cfg_text("export function w $f(w %p) {\n\
@s\n\
\t%x =w copy %p\n\
\t%y =w copy 1\n\
\tjmp @a\n\
@a\n\
\tjnz %x, @b, @c\n\
@b\n\
\t%z =w add %y, 1\n\
\tjmp @d\n\
@c\n\
\tjmp @d\n\
@d\n\
\t%w =w phi @b %z, @c %y\n\
\tjnz %w, @a, @e\n\
@e\n\
\tret %x\n\
}\n").

% The reverse postorder, immediate dominators and dominance frontiers
% of loop_cfg_text/1.
test(dominators_and_frontiers) :-
    loop_cfg_text(T),
    text_module(T, module([func(_, _, _, _, Bs)])),
    func_cfg(Bs, Cfg),
    Cfg = cfg(s, Rpo, _, _),
    msort(Rpo, [a, b, c, d, e, s]),
    dominators(Cfg, Idom),
    assoc_to_list(Idom, [a-s, b-a, c-a, d-a, e-d]),
    frontiers(Cfg, Idom, DF),
    assoc_to_list(DF, [a-[a], b-[d], c-[d], d-[a], e-[], s-[]]).

% The temporaries live into and out of each block of loop_cfg_text/1.
test(temp_liveness) :-
    loop_cfg_text(T),
    text_module(T, module([func(_, _, _, _, Bs)])),
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
    dominators(Cfg, Idom),
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
    file_module('../tests/fixtures/copy.ssa', Copies),
    func_named(Copies, redefined, Bad),
    alias_facts(Bad, Empty),
    assoc_to_list(Empty, []).

% Each alloc used one way that makes it escape, and one that does not.
test(escape_classes) :-
    text_module("export function w $f(l %n) {\n\
@s\n\
\t%a =p alloc4 8\n\
\t%b =p add %a, 4\n\
\tstorew 1, %a\n\
\tstorew 2, %b\n\
\t%v =w loadsw %b\n\
\t%e =p alloc8 8\n\
\tcall $g(p %e)\n\
\t%f =p alloc8 8\n\
\t%i =l ptoi %f\n\
\t%h =p alloc8 8\n\
\t%q =p add %h, %n\n\
\t%m =p alloc8 8\n\
\t%z =p alloc8 8\n\
\tstorep %m, %z\n\
\tret %v\n\
}\n", M),
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
    text_module("export function w $f() {\n\
@s\n\
\t%s =p alloc4 4\n\
\t%v =w loadsw %s\n\
\tret %v\n\
}\n\
export function w $g() {\n\
@s\n\
\t%s =p alloc8 8\n\
\t%q =p loadp %s\n\
\t%v =w loadsw %q\n\
\tret %v\n\
}\n", M0),
    optimize(o1, M0, M),
    once(valid_module(M)),
    alloc_count(M, 0),
    first_outcome(M0, f, [], ret(0)),
    first_outcome(M, f, [], ret(0)),
    first_outcome(M0, g, [], trap(null_capability)),
    first_outcome(M, g, [], trap(null_capability)).

% Which allocs promote must remove, and which it must keep, on the
% fixture and on tests/c/basic.c (only arr's array and ptrs's array have
% their address passed or stored). A promote that did nothing would still
% pass every differential test; this does not.
test(promote_removes_allocs) :-
    file_module('../tests/fixtures/promote.ssa', M0),
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
    file_module('../tests/fixtures/copy.ssa', M0),
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
    file_module('../tests/fixtures/copy.ssa', M0),
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
             dominators(Cfg, Idom),
             strict_ssa(F, Cfg, Idom)
           )),
    text_module("export function w $f(w %n) {\n\
@s\n\
\tjmp @loop\n\
@loop\n\
\t%p =p phi @s 0, @loop %p\n\
\tjnz %n, @loop, @done\n\
@done\n\
\tret 7\n\
}\n", Literal),
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
    text_module("export function l $f(l %x) {\n\
@s\n\
\t%a =l copy %b\n\
\t%b =l add %x, 1\n\
\tret %a\n\
}\n", NonSSA),
    copy_module(NonSSA, Unchanged),
    NonSSA == Unchanged,
    text_module("export function w $f() {\n\
@s\n\
\t%p =p copy 0\n\
\tret 7\n\
}\n", Literal),
    copy_module(Literal, Kept),
    Literal == Kept,
    module_mode(Kept, filc).

% The native GC test must exercise eliminated aliases, not merely run
% unchanged pointer code under an optimizer that does nothing.
test(copy_removes_gc_aliases) :-
    file_module('../tests/filc/gc.ssa', M0),
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
    text_module("export function p $f(w %which) {\n\
@s\n\
\t%a =p alloc8 8\n\
\t%b =p alloc8 8\n\
\t%x =p copy %a\n\
\t%y =p copy %b\n\
\tjnz %which, @left, @right\n\
@left\n\
\tjmp @join\n\
@right\n\
\tjmp @join\n\
@join\n\
\t%p =p phi @left %x, @right %y\n\
\t%q =p copy %p\n\
\tret %q\n\
}\n\
export function p $raw() {\n\
@s\n\
\t%a =p alloc8 8\n\
\t%p =p copy %a\n\
\t%i =l ptoi %p\n\
\t%raw =p itop %i\n\
\t%q =p copy %raw\n\
\tret %q\n\
}\n", M0),
    copy_module(M0, M),
    once(valid_module(M)),
    module_mode(M0, Mode),
    module_mode(M, Mode),
    forall(member(Which, [0, 1]),
           ( first_outcome(M0, f, [Which], Before),
             first_outcome(M, f, [Which], After),
             Before == After
           )),
    first_outcome(M0, f, [0], B),
    first_outcome(M0, f, [1], A),
    B \== A,
    first_outcome(M0, raw, [], Raw0),
    first_outcome(M, raw, [], Raw),
    Raw0 == Raw,
    Raw = ret(ptr(_, none)),
    file_module('../tests/filc/copy.ssa', P0),
    copy_module(P0, P),
    once(valid_module(P)),
    func_phi_names(P, pointer_invariant, [i]),
    forall(member(N, [0, 1, 5]),
           ( first_outcome(P0, pointer_invariant, [N], Before),
             first_outcome(P, pointer_invariant, [N], After),
             Before == After
           )).

% Bounded symbolic queries share the same input variables across both runs.
% The domains include branch choices, loop counts and the 32-bit sign edge;
% labeling makes absence of a counterexample decisive within those domains.
test(symbolic_optimized_returns) :-
    file_module('../tests/fixtures/promote.ssa', P0),
    optimize(o1, P0, P),
    \+ ( X in 0..15,
         Y in 0..3,
         returns_differ(P0, P, diamond, [X, Y], 20)
       ),
    \+ ( N in 0..6,
         returns_differ(P0, P, loop, [N], 20)
       ),
    file_module('../tests/fixtures/copy.ssa', C0),
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
    text_module("export function l $f(l %x) {\n\
@s\n\
\t%w =w copy %x\n\
\t%r =l extuw %w\n\
\tret %r\n\
}\n", Before),
    text_module("export function l $f(l %x) {\n\
@s\n\
\tret %x\n\
}\n", Wrong),
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

% c_file_module(+File, -Module): Module is the valid module of the C
% in File, lexed without preprocessing.
c_file_module(F, M) :-
    phrase_from_file(seq(Cs), F),
    c_tokens(Cs, F, Ts),
    c_parse(Ts, Items),
    c_module(Items, M),
    valid_module(M).
