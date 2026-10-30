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
test(regs_checker) :- regs_checker.
test(operands_checker) :- operands_checker.
% A function that indexes a local array still gets register homes: the
% local's address is a constant-offset lea after its range check
% (docs/perf.md item 3c), not an indexed frame operand, which 3a's
% preflight rejects. LZ4HC_InsertAndGetWiderMatch had none.
test(local_array_registers) :-
    c_tokens("int f(int n) { union { unsigned u; unsigned char c[4]; } one = { 1 };
              int s = 0;
              for (int i = 0; i < n; i++) s += one.c[0] + i;
              return s; }", 'local.c', Ts),
    c_parse(Ts, C), c_module(C, M), optimize(o1, M, O), pizlonate_module(O, P),
    forall(member(R, [temps]),
           ( filc_module_asm(P, emit(R, selected), Lines, Reports),
             memberchk(function(f, allocated(N, _)), Reports), N > 0,
             \+ ( member(ins(_,_,Os), Lines), member(mem(_,rbp,_), Os) ) )).
% Item 7a: -O puts the inline filter, with the destination's masked
% header test, in front of a small constant memcpy and keeps the call
% behind it; call mode, 17 bytes and a module that defines memcpy keep
% only the call.
test(small_copy_filter) :-
    Decl = "typedef unsigned long size_t; void *memcpy(void *, const void *, size_t);",
    Mask = 0x0786ffffffffffff,
    copy_lines(Decl, "long f(char *d, char *s, long n) { long t = 0;
                        for (long i = 0; i < n; i++) { memcpy(d + i, s, 8); t += d[i]; }
                        return t; }", inline, Lines-Reports),
    % The region checker accepts the filter in an allocated function.
    memberchk(function(f, allocated(A, _)), Reports), A > 0,
    memberchk(ins(movabs,q,[imm(Mask),reg(rdx)]), Lines),
    memberchk(ins(mov,q,[mem(0,rsi),reg(rdx)]), Lines),
    memberchk(ins(call,none,[sym(_)]), Lines),
    copy_lines(Decl, "void f(char *d, char *s) { memcpy(d, s, 8); }", call, Called-_),
    \+ memberchk(ins(movabs,q,[imm(Mask),reg(rdx)]), Called),
    copy_lines(Decl, "void f(char *d, char *s) { memcpy(d, s, 17); }", inline, Long-_),
    \+ memberchk(ins(movabs,q,[imm(Mask),reg(rdx)]), Long),
    copy_lines(Decl, "void f(char *d, char *s) { memcpy(d, s, 8); }
                      void *memcpy(void *d, const void *s, size_t n) { return d; }",
               inline, Defined-_),
    \+ memberchk(ins(movabs,q,[imm(Mask),reg(rdx)]), Defined).
% Own pools (temps, the allocating layout) keep s and d temporaries out
% of the scalar slots, so every scalar home is w/l and can take a
% register; shared pools (the reference layout) mix them in this function.
test(split_float_pools) :-
    c_tokens("int f(double x, int n) { int a = (int)(x * 3.0);
              double y = x + 1.0; int b = a * n;
              int c = (int)(y * 2.0); return b + c; }", 'pools.c', Ts),
    c_parse(Ts, C), c_module(C, M), optimize(o1, M, O), pizlonate_module(O, P),
    P = module(Items), memberchk(F, Items), F = func(f,_,_,_,_),
    pool_homes(shared, P, F, Shared),
    once(( member(home(_, Ks), Shared), memberchk(d, Ks), memberchk(w, Ks) )),
    pool_homes(own, P, F, Own), Own = [_|_],
    forall(member(home(_, Ks), Own), forall(member(K, Ks), memberchk(K, [w,l]))).
% Own pools give each w/l temporary its own home, where shared pools
% reuse slots of disjoint temporaries; own(Groups) pools a group again.
test(own_scalar_homes) :-
    own_homes("int f(int x, int n) { int a = x * 3; int b = a + n;
               int c = b * x; return c - n; }", Shared, Own, Again),
    length(Shared, NS), length(Own, NO), NO > NS,
    findall(K, member(home(_, [K]), Own), Ks), length(Ks, NO),
    length(Again, NS).
% Temps mode lowers a function with many temporaries twice, the second
% time sharing slots among temporaries the first allocation gave the
% same register, so its frame is far smaller than a home per temporary
% needs (432 bytes here) and no larger than the reference's (176) with the
% five callee-save slots, rounded to 16 (docs/perf.md 3d): recursion keeps
% its depth.
test(temps_frame) :-
    c_tokens("long g(long n, long a, long b) {
                if (n == 0) return a ^ b;
                long c = a * 3 + b, d = b * 5 - a, e = (c ^ d) + n, h = c * d - e;
                long i = (h >> 3) + (e << 2), j = i ^ (c + d), k = j * 7 + h, l = k - (i ^ e);
                long m = (l + c) * (d - e), o = m ^ (k + j), p = o + (l >> 1), q = p * (m & 15);
                long r = g(n - 1, q ^ c, p + d);
                return r + (a ^ e) + (b ^ h) + (i ^ j) + (k ^ l) + (m ^ o) + (p ^ q) + c + d; }",
             'frame.c', Ts),
    c_parse(Ts, C), c_module(C, M), optimize(o1, M, O), pizlonate_module(O, P),
    findall(R-F, ( member(R, [stack, temps]),
                   filc_module_asm(P, emit(R, selected), Lines, _),
                   once(( append(_, [ins(sub,q,[imm(F),reg(rsp)])|_], Lines) )) ), [stack-FS, temps-FT]),
    P = module(Items), memberchk(G, Items), G = func(g,_,_,_,_), module_symbols(P, Symbols),
    filc_amd64:lower_item(own, Symbols, G, abi_function(_,_,_,_,OwnFrame,_,_,_,_,_)),
    filc_amd64:layout(OwnFrame, _, _, FO),
    FT < FO, FT =< FS + 48.
% Phis of different blocks share shadow slots by class and position in
% the allocating layouts (docs/perf.md item 9): swaps' two loops have
% 1 + 4 integer and 2 + 0 pointer phis, so 4 + 2 shadows, not 7. The
% reference layout keeps one per phi; so do a phi destination defined in
% two blocks (twice's t) and a setjmp function. Each frame's roots are
% the origin's count, zeroed at entry, at distinct offsets.
test(shared_shadows) :-
    file_module('../tests/filc/shadows.ir', M0), pizlonate_module(M0, P),
    P = module(Items), memberchk(func(swaps,L,R,Ps,Bs), Items),
    shadow_frame(own, P, func(swaps,L,R,Ps,Bs), Shared),
    Shared = frame(SKs, [_,_]),
    msort(SKs, [shadow_slot(int,0), shadow_slot(int,1), shadow_slot(int,2),
                shadow_slot(int,3), shadow_slot(p,0), shadow_slot(p,1)]),
    shadow_frame(shared, P, func(swaps,L,R,Ps,Bs), frame(RKs, [_,_])),
    length(RKs, 7), forall(member(K, RKs), K = shadow(_)),
    memberchk(func(twice,L2,R2,Ps2,Bs2), Items),
    shadow_frame(own, P, func(twice,L2,R2,Ps2,Bs2), frame(TKs, _)),
    memberchk(shadow(t), TKs), \+ memberchk(shadow(x), TKs),
    file_module('../tests/filc/setjmp.ir', J0), pizlonate_module(J0, J),
    J = module(JItems),
    once(( member(F, JItems), F = func(_,_,_,_,JBs),
           member(block(_,[_|_],_,_), JBs) )),
    shadow_frame(own, J, F, frame(JKs, _)), JKs = [_|_],
    forall(member(K, JKs), K = shadow(_)).
test(local_storage_semantics) :- local_semantics.

test(local_storage_lifetime) :- local_lifetime.
test(local_storage_validation) :- local_validation.

% shadow_frame(+Pools, +Module, +Func, -frame(Keys, Roots)): the shadow
% keys and shadow roots of Func's frame lowered with Pools, after
% checking that the frame's roots are as many as its origins count and
% its entry zeroes, each at an offset of its own.
shadow_frame(Pools, Module, Func, frame(Keys, ShadowRoots)) :-
    module_symbols(Module, Symbols),
    filc_amd64:lower_item(Pools, Symbols, Func, Product),
    Product = abi_function(_,_,_,_,Frame,Entry,_,_,_,Origins),
    Frame = frame(Plain, Roots, _),
    length(Roots, NR), memberchk(zero_roots(NR), Entry),
    forall(member(origin(_,_,N,_,_), Origins), N =:= NR),
    filc_amd64:layout(Frame, Slots, _, _),
    findall(Off, ( member(Root, Roots), get_assoc(Root, Slots, Off) ), Offs),
    sort(Offs, Distinct), length(Distinct, NR),
    findall(K, ( member(K, Plain), ( K = shadow(_) ; K = shadow_slot(_,_) ) ), Keys),
    findall(Root, ( member(Root, Roots),
                    ( Root = lower(shadow(_)) ; Root = lower(shadow_slot(_,_)) ) ),
            ShadowRoots).

% pool_homes(+Pools, +Module, +Func, -Homes): the scalar homes, with
% their temporaries' classes, of Func lowered with Pools.
pool_homes(Pools, Module, Func, Homes) :-
    module_symbols(Module, Symbols),
    filc_amd64:lower_item(Pools, Symbols, Func, Product),
    Product = abi_function(_,_,_,_,Frame,_,_,_,_,_), Frame = frame(_,_,Aliases),
    filc_amd64:layout(Frame, Slots, _, _),
    filc_amd64:scalar_homes(Func, Aliases, Slots, Homes).

% own_homes(+Src, -Shared, -Own, -Again): the scalar homes of the one
% function in Src lowered with shared pools, with own pools, and with own
% pools that put every w/l temporary in one group.
own_homes(Src, Shared, Own, Again) :-
    c_tokens(Src, 'own.c', Ts),
    c_parse(Ts, C), c_module(C, M), optimize(o1, M, O), pizlonate_module(O, P),
    P = module(Items), member(F, Items), F = func(_,_,_,_,_), !,
    pool_homes(shared, P, F, Shared), pool_homes(own, P, F, Own),
    F = func(_,_,_,Ps,Bs),
    findall(N, ( member(param(K, tmp(N)), Ps) ; member(block(_,Phis,Is,_), Bs),
                 ( member(phi(tmp(N),K,_), Phis) ; member(let(tmp(N),K,_,_), Is) ) ), Ns0),
    sort(Ns0, Ns), findall(N-frame, member(N, Ns), Groups),
    pool_homes(own(Groups), P, F, Again).

% copy_lines(+Decl, +Src, +Copies, -Lines-Reports): the -O Fil-C lines
% and reports of the C text Decl followed by Src, with small copies
% Copies (call or inline).
copy_lines(Decl, Src, Copies, Lines-Reports) :-
    append(Decl, Src, Text),
    c_tokens(Text, 'copy.c', Ts), c_parse(Ts, C), c_module(C, M),
    optimize(o1, M, O), pizlonate_module(O, P),
    filc_module_asm(P, emit(temps, selected, Copies), Lines, Reports).

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

test(alias_validator) :-
    F = func(f, export, w, [], [block(start, [], [], ret(const(1)))]),
    D = data(d, export, 4, [item(w, const(5))]),
    Caller = func(c, export, w, [], [block(start, [], [call(result(tmp(r), w), global(a), [])], ret(tmp(r)))]),
    valid_module(module([F, D, alias(a, export, f), alias(b, weak, d)])),
    forall(member(Items, [[F, alias(a, export, missing)],      % target undefined
                          [F, data(w, extern(weak), 1, []), alias(a, export, w)],
                          [F, alias(f, export, f)],            % name already defined
                          [F, alias(a, local, f)],             % linkage
                          [D, Caller, alias(a, export, d)]]),  % a call names a data alias
           catch((valid_module(module(Items)), fail), nanofil_error(_), true)).

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

% Alignment above 16 (docs/abi-findings.md): in Fil-C mode an alloc and
% a data object are as aligned as they ask, 16 at least, up to 4096,
% each placed after a 1-byte object that leaves the next address
% unaligned; 8192 is refused.
test(over_aligned_alloc_and_data) :-
    forall(member(A, [16, 32, 4096]),
           ( Mask is A - 1,
             ir_module([
                 data(pad, local, 1, [item(b, const(1))]),
                 data(g, local, A, [item(b, const(1))]),
                 func(f, export, l, [], [
                     block(s, [], [
                         let(tmp(c), p, alloc(4), [const(1)]),
                         let(tmp(p), p, alloc(A), [const(8)]),
                         let(tmp(g), p, copy, [global(g)]),
                         let(tmp(i), l, ptoi, [tmp(p)]),
                         let(tmp(j), l, ptoi, [tmp(g)]),
                         let(tmp(k), l, or, [tmp(i), tmp(j)]),
                         let(tmp(r), l, and, [tmp(k), const(Mask)])
                     ], ret(tmp(r)))
                 ])
             ], M),
             module_fn_args_outcome(M, f, [], ret(0)) )).
test(rejects_alignment_above_4096) :-
    rejected_with([data(g, local, 8192, [item(b, const(1))])],
                  "unsupported data alignment 8192"),
    rejected_with([
        func(f, export, p, [], [
            block(s, [], [let(tmp(p), p, alloc(8192), [const(8)])], ret(tmp(p)))
        ])
    ], "alloc(8192)").

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

% A union read through a narrower member (lz4's LZ4_isLittleEndian,
% perf.md): a word stored once and read as bytes or halves at each
% offset promotes, and each read is the little-endian bytes the store
% wrote: 0x81828384 is 0x84 0x83 0x82 0x81 in memory, so the unsigned
% bytes are 132, 131, 130, 129, the signed top byte -127, the unsigned
% halves 0x8384 = 33668 and 0x8182 = 33154, the signed high half
% -32382 (a w result is reported mod 2^32: 4294967169 and 4294934914). A half stored and read as bytes promotes too (0x1234: 52, 18).
% The other order, bytes stored and the word read, must stay memory:
% bytes 1, 2, 3, 4 read as a word are 0x04030201 = 67305985.
test(promote_punned_reads) :-
    Word = 2172814212,
    Reads = [ub-0-132, ub-1-131, ub-2-130, ub-3-129, sb-3-4294967169,
             uh-0-33668, uh-2-33154, sh-2-4294934914],
    findall(func(Fn, export, w, [], [block(s, [], [
                let(tmp(a), p, alloc(4), [const(4)]),
                store(w, const(Word), tmp(a)),
                let(tmp(q), p, add, [tmp(a), const(Off)]),
                let(tmp(v), w, load(T), [tmp(q)])
            ], ret(tmp(v)))]),
            ( nth0(I, Reads, T-Off-_), atom_concat(r, I, Fn) ), Fs),
    ir_module([func(half, export, w, [], [block(s, [], [
                   let(tmp(a), p, alloc(4), [const(2)]),
                   store(h, const(4660), tmp(a)),
                   let(tmp(x), w, load(ub), [tmp(a)]),
                   let(tmp(q), p, add, [tmp(a), const(1)]),
                   let(tmp(y), w, load(ub), [tmp(q)]),
                   let(tmp(z), w, mul, [tmp(x), const(256)]),
                   let(tmp(v), w, add, [tmp(z), tmp(y)])
               ], ret(tmp(v)))]),
               func(bytes, export, w, [], [block(s, [], [
                   let(tmp(a), p, alloc(4), [const(4)]),
                   store(b, const(1), tmp(a)),
                   let(tmp(q1), p, add, [tmp(a), const(1)]),
                   store(b, const(2), tmp(q1)),
                   let(tmp(q2), p, add, [tmp(a), const(2)]),
                   store(b, const(3), tmp(q2)),
                   let(tmp(q3), p, add, [tmp(a), const(3)]),
                   store(b, const(4), tmp(q3)),
                   let(tmp(v), w, load(uw), [tmp(a)])
               ], ret(tmp(v)))])|Fs], M0),
    optimize(passes([promote]), M0, M), once(valid_module(M)),
    forall(nth0(I, Reads, _-_-V),
           ( atom_concat(r, I, Fn),
             module_fn_args_outcome(M0, Fn, [], ret(V)),
             module_fn_args_outcome(M, Fn, [], ret(V)),
             func_named(M, Fn, F), alloc_count(module([F]), 0) )),
    module_fn_args_outcome(M0, half, [], ret(13330)),
    module_fn_args_outcome(M, half, [], ret(13330)),
    func_named(M, half, H), alloc_count(module([H]), 0),
    module_fn_args_outcome(M0, bytes, [], ret(67305985)),
    module_fn_args_outcome(M, bytes, [], ret(67305985)),
    func_named(M, bytes, B), alloc_count(module([B]), 1),
    % Only h and w slots are punned: a pointer's bytes are no value of a
    % w slot, and an l slot would need l shifts. Both stay memory.
    ir_module([func(pb, export, w, [], [block(s, [], [
                   let(tmp(a), p, alloc(8), [const(8)]),
                   let(tmp(g), p, alloc(8), [const(8)]),
                   store(p, tmp(g), tmp(a)),
                   let(tmp(v), w, load(ub), [tmp(a)])
               ], ret(tmp(v)))]),
               func(lb, export, w, [], [block(s, [], [
                   let(tmp(a), p, alloc(8), [const(8)]),
                   store(l, const(4294967296), tmp(a)),
                   let(tmp(q), p, add, [tmp(a), const(4)]),
                   let(tmp(v), w, load(ub), [tmp(q)])
               ], ret(tmp(v)))])], P0),
    optimize(passes([promote]), P0, P), once(valid_module(P)),
    module_fn_args_outcome(P, lb, [], ret(1)),
    func_named(P, lb, LB), alloc_count(module([LB]), 1),
    func_named(P, pb, PB), alloc_count(module([PB]), 2).

% An alloc outside the entry block (an inlined callee's local, perf.md
% item 4) is a fresh zeroed object at each execution. Promoted, each
% execution must read 0 before its first store: x is 0 three times, so
% 3 * (0 + 5) = 15; a value surviving the loop would give 0+5+5+... A
% pointer stored on the first pass must not survive to the second,
% which traps on it as null, also when the object is too small to
% promote (a 4-byte object written as a pointer stays memory, fresh per
% pass: the review's reproduction of a store reset keeping capabilities).
% An address merged in a phi escapes and stays a heap object per pass,
% so the two passes see different objects (ret 2; one shared object,
% as hoisting made it, gives 1).
test(promote_nonentry_allocs) :-
    Loop = [block(s, [], [], goto(h)),
            block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                      phi(tmp(t), w, [s-const(0), b-tmp(t1)])],
                  [let(tmp(c), w, cmp(slt, w), [tmp(i), const(3)])],
                  branch(tmp(c), b, e))],
    append(Loop, [
        block(b, [], [
            let(tmp(a), p, alloc(4), [const(4)]),
            let(tmp(x), w, load(sw), [tmp(a)]),
            let(tmp(x5), w, add, [tmp(x), const(5)]),
            store(w, tmp(x5), tmp(a)),
            let(tmp(y), w, load(sw), [tmp(a)]),
            let(tmp(xy), w, add, [tmp(x), tmp(y)]),
            let(tmp(t1), w, add, [tmp(t), tmp(xy)]),
            let(tmp(i1), w, add, [tmp(i), const(1)])
        ], goto(h)),
        block(e, [], [], ret(tmp(t)))], ZeroBs),
    Ptr = fun(Size, [block(s, [], [let(tmp(g), p, alloc(8), [const(8)])], goto(h)),
           block(h, [phi(tmp(i), w, [s-const(0), next-tmp(i1)])],
                 [let(tmp(c), w, cmp(slt, w), [tmp(i), const(2)])],
                 branch(tmp(c), b, e)),
           block(b, [], [
               let(tmp(a), p, alloc(8), [const(Size)]),
               let(tmp(q), p, load(p), [tmp(a)]),
               let(tmp(z), w, cmp(eq, w), [tmp(i), const(1)])
           ], branch(tmp(z), use, first)),
           block(first, [], [store(p, tmp(g), tmp(a))], goto(next)),
           block(use, [], [let(tmp(v), w, load(sw), [tmp(q)])], goto(next)),
           block(next, [], [let(tmp(i1), w, add, [tmp(i), const(1)])], goto(h)),
           block(e, [], [], ret(const(7)))]),
    copy_term(Ptr, fun(4, SmallBs)), Ptr = fun(16, PtrBs),
    Esc = [block(s, [], [], goto(h)),
           block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                     phi(tmp(prev), p, [s-const(0), b-tmp(a)]),
                     phi(tmp(t), w, [s-const(0), b-tmp(t1)])],
                 [let(tmp(c), w, cmp(slt, w), [tmp(i), const(2)])],
                 branch(tmp(c), b, e)),
           block(b, [], [
               let(tmp(a), p, alloc(4), [const(4)]),
               store(w, tmp(i), tmp(a)),
               let(tmp(av), l, ptoi, [tmp(a)]),
               let(tmp(pv), l, ptoi, [tmp(prev)]),
               let(tmp(d), w, cmp(ne, l), [tmp(av), tmp(pv)]),
               let(tmp(t1), w, add, [tmp(t), tmp(d)]),
               let(tmp(i1), w, add, [tmp(i), const(1)])
           ], goto(h)),
           block(e, [], [], ret(tmp(t)))],
    ir_module([func(zero, export, w, [], ZeroBs), func(ptr, export, w, [], PtrBs),
               func(small, export, w, [], SmallBs), func(esc, export, w, [], Esc)], M0),
    optimize(passes([promote]), M0, M), once(valid_module(M)),
    forall(member(F-Want, [zero-ret(15), ptr-trap(null_capability),
                           small-trap(null_capability), esc-ret(2)]),
           ( module_fn_args_outcome(M0, F, [], Want),
             module_fn_args_outcome(M, F, [], Want) )),
    % zero's and ptr's loop allocs promote; small's and esc's stay.
    forall(member(F-N, [zero-0, ptr-1, small-2, esc-1]),
           ( func_named(M, F, Fn), alloc_count(module([Fn]), N) )).

% --inline=small (src/inline.pl, docs/perf.md item 4): eligible calls
% inline, every exclusion keeps its call, both sides of each cap, and
% every run keeps its outcome under passes([inline]) and o1(small).
test(inline_small) :-
    Add1 = func(add1, local, w, [param(w, tmp(x))],
                [block(s, [], [let(tmp(y), w, add, [tmp(x), const(1)])], ret(tmp(y)))]),
    Sum3 = func(sum3, export, w, [], [
        block(s, [], [], goto(h)),
        block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                  phi(tmp(t), w, [s-const(0), b-tmp(t1)])],
              [let(tmp(c), w, cmp(slt, w), [tmp(i), const(3)])], branch(tmp(c), b, e)),
        block(b, [], [call(result(tmp(r), w), global(add1), [arg(w, tmp(i))]),
                      let(tmp(t1), w, add, [tmp(t), tmp(r)]),
                      let(tmp(i1), w, add, [tmp(i), const(1)])], goto(h)),
        block(e, [], [], ret(tmp(t)))]),
    % A fresh zero per call, in a loop.
    Cell = func(cell, local, w, [param(w, tmp(v))], [
        block(s, [], [let(tmp(a), p, alloc(4), [const(4)]),
                      let(tmp(x), w, load(sw), [tmp(a)]),
                      store(w, tmp(v), tmp(a)),
                      let(tmp(y), w, load(sw), [tmp(a)]),
                      let(tmp(z), w, add, [tmp(x), tmp(y)])], ret(tmp(z)))]),
    Cells = func(cells, export, w, [], [
        block(s, [], [], goto(h)),
        block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                  phi(tmp(t), w, [s-const(0), b-tmp(t1)])],
              [let(tmp(c), w, cmp(slt, w), [tmp(i), const(3)])], branch(tmp(c), b, e)),
        block(b, [], [let(tmp(v), w, add, [tmp(i), const(5)]),
                      call(result(tmp(r), w), global(cell), [arg(w, tmp(v))]),
                      let(tmp(t1), w, add, [tmp(t), tmp(r)]),
                      let(tmp(i1), w, add, [tmp(i), const(1)])], goto(h)),
        block(e, [], [], ret(tmp(t)))]),
    % A returned local, through a phi and ptoi in a loop: a heap object
    % per call, as before.
    Addr = func(addr, local, p, [], [
        block(s, [], [let(tmp(a), p, alloc(4), [const(4)]),
                      store(w, const(1), tmp(a))], ret(tmp(a)))]),
    Addrs = func(addrs, export, w, [], [
        block(s, [], [], goto(h)),
        block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                  phi(tmp(prev), p, [s-const(0), b-tmp(a)]),
                  phi(tmp(t), w, [s-const(0), b-tmp(t1)])],
              [let(tmp(c), w, cmp(slt, w), [tmp(i), const(2)])], branch(tmp(c), b, e)),
        block(b, [], [call(result(tmp(a), p), global(addr), []),
                      let(tmp(av), l, ptoi, [tmp(a)]),
                      let(tmp(pv), l, ptoi, [tmp(prev)]),
                      let(tmp(d), w, cmp(ne, l), [tmp(av), tmp(pv)]),
                      let(tmp(t1), w, add, [tmp(t), tmp(d)]),
                      let(tmp(i1), w, add, [tmp(i), const(1)])], goto(h)),
        block(e, [], [], ret(tmp(t)))]),
    % Depth 2: twice calls add1, so it inlines in the second round.
    Twice = func(twice, local, w, [param(w, tmp(x))], [
        block(s, [], [call(result(tmp(a), w), global(add1), [arg(w, tmp(x))]),
                      call(result(tmp(b), w), global(add1), [arg(w, tmp(a))])], ret(tmp(b)))]),
    % The caller already holds names with the second round's first
    % prefix, one of which twice's renamed body would redefine.
    Deep = func(deep, export, w, [param(w, tmp(n))], [
        block(s, [], [let(tmp('i2_1.x'), w, add, [tmp(n), const(10)]),
                      let(tmp('i2_1.a'), w, add, [tmp(n), const(100)]),
                      call(result(tmp(r), w), global(twice), [arg(w, tmp('i2_1.x'))]),
                      let(tmp(z), w, add, [tmp(r), tmp('i2_1.a')])], ret(tmp(z)))]),
    % A callee label that the join block's label must avoid.
    Jn = func(jn, local, w, [param(w, tmp(x))], [
        block(s, [], [], branch(tmp(x), join, z)),
        block(join, [], [], ret(const(1))),
        block(z, [], [], ret(const(2)))]),
    Jns = func(jns, export, w, [param(w, tmp(n))], [
        block(s, [], [call(result(tmp(r), w), global(jn), [arg(w, tmp(n))])], ret(tmp(r)))]),
    % Exclusions: each keeps its call.
    Rec = func(rec, local, w, [param(w, tmp(n))], [
        block(s, [], [], branch(tmp(n), d, z)),
        block(d, [], [let(tmp(m), w, sub, [tmp(n), const(1)]),
                      call(result(tmp(r), w), global(rec), [arg(w, tmp(m))])], ret(tmp(r))),
        block(z, [], [], ret(const(4)))]),
    Va = func(va, local, w, [param(w, tmp(x))], [
        block(s, [], [let(tmp(ap), p, va_args, [const(0)])], ret(tmp(x)))]),
    Ext = func(ext, export, w, [param(w, tmp(x))], [block(s, [], [], ret(tmp(x)))]),
    Big = func(big, local, w, [], [
        block(s, [], [let(tmp(a), p, alloc(4), [const(300)]),
                      let(tmp(x), w, load(sw), [tmp(a)])], ret(tmp(x)))]),
    Dyn = func(dyn, local, w, [param(l, tmp(k))], [
        block(s, [], [let(tmp(a), p, alloc(4), [tmp(k)]),
                      store(w, const(3), tmp(a)),
                      let(tmp(x), w, load(sw), [tmp(a)])], ret(tmp(x)))]),
    Sj = func(sj, local, w, [param(p, tmp(buf))], [
        block(s, [], [let(tmp(x), w, setjmp('_setjmp'), [tmp(buf), const(0)])], ret(tmp(x)))]),
    Noret = func(noret, local, w, [], [block(s, [], [], goto(l)), block(l, [], [], goto(l))]),
    Users = func(users, export, w, [param(w, tmp(n)), param(p, tmp(buf))], [
        block(s, [], [call(result(tmp(r1), w), global(rec), [arg(w, tmp(n))]),
                      call(result(tmp(r2), w), global(va), [arg(w, tmp(n))]),
                      call(result(tmp(r3), w), global(ext), [arg(w, tmp(n))]),
                      call(result(tmp(r5), w), global(big), []),
                      call(result(tmp(r6), w), global(dyn), [arg(l, const(4))])],
              branch(tmp(n), more, out)),
        block(more, [], [call(result(tmp(r7), w), global(sj), [arg(p, tmp(buf))]),
                         call(result(tmp(r8), w), global(noret), [])], goto(out)),
        block(out, [], [let(tmp(a), w, add, [tmp(r1), tmp(r3)]),
                        let(tmp(c), w, add, [tmp(a), tmp(r6)])], ret(tmp(c)))]),
    % A setjmp caller and a recursive caller keep their calls.
    SjCaller = func(sjc, export, w, [param(p, tmp(buf))], [
        block(s, [], [let(tmp(x), w, setjmp('_setjmp'), [tmp(buf), const(0)]),
                      call(result(tmp(r), w), global(add1), [arg(w, tmp(x))])], ret(tmp(r)))]),
    RecCaller = func(rc, export, w, [param(w, tmp(n))], [
        block(s, [], [call(result(tmp(a), w), global(add1), [arg(w, tmp(n))])],
              branch(tmp(n), d, z)),
        block(d, [], [let(tmp(m), w, sub, [tmp(n), const(1)]),
                      call(result(tmp(r), w), global(rc), [arg(w, tmp(m))]),
                      let(tmp(q), w, add, [tmp(r), tmp(a)])], ret(tmp(q))),
        block(z, [], [], ret(tmp(a)))]),
    % Callee cap: 120 inlines, 121 does not. Caller cap: 2000 inlines,
    % 2001 does not. Growth: a 301 caller takes 150 more, a 100 callee
    % but not then a 51 one.
    chain_func(c120, local, 119, F120), chain_func(c121, local, 120, F121),
    chain_func(c100, local, 99, F100), chain_func(c51, local, 50, F51),
    caller_func(k2000, 1998, [c120], K2000), caller_func(k2001, 1999, [c120], K2001),
    caller_func(k300, 298, [c100, c51], K300),
    caller_func(kc, 0, [c121, c120], KC),
    Items = [Add1, Sum3, Cell, Cells, Addr, Addrs, Twice, Deep, Jn, Jns, Rec, Va, Ext,
             Big, Dyn, Sj, Noret, Users, SjCaller, RecCaller,
             F120, F121, F100, F51, K2000, K2001, K300, KC],
    ir_module(Items, M0),
    optimize(passes([inline]), M0, MI), once(valid_module(MI)), reads_back(MI),
    optimize(o1(small), M0, M), once(valid_module(M)),
    forall(member(Caller-Callee, [sum3-add1, cells-cell, addrs-addr, deep-twice,
                                  deep-add1, jns-jn, k2000-c120, kc-c120]),
           \+ calls_in(MI, Caller, Callee)),
    forall(member(Caller-Callee-N, [users-rec-1, users-va-1, users-ext-1,
                                    users-big-1, users-dyn-1, users-sj-1, users-noret-1,
                                    sjc-add1-1, rc-add1-1, k2001-c120-1, kc-c121-1,
                                    k300-c100-0, k300-c51-1]),
           ( findall(x, call_in(MI, Caller, Callee), Xs), length(Xs, N) )),
    % No callee of users is eligible, so it is unchanged.
    func_named(M0, users, Users), func_named(MI, users, Users),
    forall(member(F-Args-Want, [sum3-[]-ret(6), cells-[]-ret(18), addrs-[]-ret(2),
                                deep-[5]-ret(122), jns-[0]-ret(2), jns-[3]-ret(1), users-[0, 0]-ret(7), rc-[2]-ret(6),
                                k2000-[1]-ret(_), kc-[1]-ret(_)]),
           ( module_fn_args_outcome(M0, F, Args, Want),
             module_fn_args_outcome(MI, F, Args, Want),
             module_fn_args_outcome(M, F, Args, Want) )),
    func_named(M, cells, CellsF), alloc_count(module([CellsF]), 0),
    func_named(M, addrs, AddrsF), alloc_count(module([AddrsF]), 1).

calls_in(M, Caller, Callee) :- once(call_in(M, Caller, Callee)).
call_in(M, Caller, Callee) :-
    func_named(M, Caller, func(_, _, _, _, Bs)),
    member(block(_, _, Is, _), Bs), member(call(_, global(Callee), _), Is).

% chain_func(+Name, +Linkage, +N, -F): F takes x and returns it plus N,
% with N adds and a ret: N + 1 instructions and jumps.
chain_func(Name, L, N, func(Name, L, w, [param(w, tmp(x0))], [block(s, [], Is, ret(Last))])) :-
    chain_adds(0, N, Is, Last).
chain_adds(K, N, [], tmp(X)) :- K >= N, !, format(atom(X), 'x~w', [K]).
chain_adds(K, N, [let(tmp(Y), w, add, [tmp(X), const(1)])|Is], Last) :-
    format(atom(X), 'x~w', [K]), K1 is K + 1, format(atom(Y), 'x~w', [K1]),
    chain_adds(K1, N, Is, Last).

% caller_func(+Name, +N, +Callees, -F): F does N adds, then calls each
% of Callees in turn and returns the last result: N + |Callees| + 1.
caller_func(Name, N, Callees, func(Name, export, w, [param(w, tmp(x0))],
                                   [block(s, [], Is, ret(Last))])) :-
    chain_adds(0, N, Adds, V0),
    foldl(callee_call, Callees, Calls, 0-V0, _-Last),
    append(Adds, Calls, Is).
callee_call(G, call(result(tmp(R), w), global(G), [arg(w, V)]), K0-V, K-tmp(R)) :-
    K is K0 + 1, format(atom(R), 'r~w', [K]).

% Source contexts follow an inlined call: the calling block's sites
% before the call stay, the call's origins go to the parameter copies,
% later sites and the jump move to the join, shifted, and the callee's
% records are renamed with inl(Round, N, Id) identities.
test(inline_contexts) :-
    O = origin(_, at('t.c', 1), statement(expr), []),
    Callee = func(add1, local, w, [param(w, tmp(x))],
                  [block(s, [], [let(tmp(y), w, add, [tmp(x), const(1)])], ret(tmp(y)))]),
    Caller = func(f, export, w, [param(w, tmp(n))], [
        block(s, [], [let(tmp(a), w, add, [tmp(n), const(2)]),
                      call(result(tmp(r), w), global(add1), [arg(w, tmp(a))]),
                      let(tmp(b), w, add, [tmp(r), const(3)]),
                      call(result(tmp(r2), w), global(add1), [arg(w, tmp(b))]),
                      let(tmp(c), w, add, [tmp(r2), const(4)])], ret(tmp(c)))]),
    maplist(origin_named(O), [o1, o2, o3, o4, o5, o6], Os),
    origin_named(O, c1, C1), origin_named(O, c2, C2),
    ir_module([Callee, context(add1, [C1, C2, site(inst(s, 0), [c1]), site(jump(s), [c2])]),
               Caller, context(f, [site(inst(s, 0), [o1]), site(inst(s, 1), [o2]),
                                   site(inst(s, 2), [o3]), site(inst(s, 3), [o4]),
                                   site(inst(s, 4), [o5]), site(jump(s), [o6])|Os])],
              M0),
    optimize(passes([inline]), M0, module(Items)),
    once(valid_module(module(Items))),
    memberchk(context(f, Rs), Items),
    findall(S-Ids, member(site(S, Ids), Rs), Sites),
    msort(Sites, Got),
    msort([inst(s, 0)-[o1], inst(s, 1)-[o2],
           inst('i1_1.s', 0)-[inl(1, 1, c1)], jump('i1_1.s')-[inl(1, 1, c2)],
           inst('i1_1.join', 0)-[o3], inst('i1_1.join', 1)-[o4],
           inst('i1_2.s', 0)-[inl(1, 2, c1)], jump('i1_2.s')-[inl(1, 2, c2)],
           inst('i1_2.join', 0)-[o5], jump('i1_2.join')-[o6]], Want),
    Got == Want,
    memberchk(origin(inl(1, 2, c1), at('t.c', 1), statement(expr), []), Rs).

origin_named(origin(_, L, D, Ps), Id, origin(Id, L, D, Ps)).

% The cheap middle end (src/simplify.pl, docs/perf.md item 8). Each
% function keeps its outcome on inputs where a plausible wrong rewrite
% differs, and the rewrite it targets happened. Expected values are
% worked by hand: fold's w sum wraps (2^32 - 1 + 2 = 1) where the l sum
% does not; -1 <s 0 holds where -1 <u 0 does not; 8x at w loses bit 29.
test(simplify) :-
    Fold = func(fold, export, l, [], [block(s, [], [
        let(tmp(a), w, add, [const(4294967295), const(2)]),
        let(tmp(b), l, add, [const(4294967295), const(2)]),
        let(tmp(e), l, ext(uw), [tmp(a)]),
        let(tmp(r), l, add, [tmp(b), tmp(e)])], ret(tmp(r)))]),
    Div0 = func(div0, export, w, [param(w, tmp(x))], [block(s, [], [
        let(tmp(q), w, udiv, [const(5), const(0)]),
        let(tmp(z), w, add, [tmp(q), tmp(x)])], ret(tmp(z)))]),
    Bools = func(bools, export, w, [param(w, tmp(a)), param(w, tmp(b))], [
        block(s, [], [let(tmp(c), w, cmp(slt, w), [tmp(a), tmp(b)]),
                      let(tmp(n), w, cmp(eq, w), [tmp(c), const(0)]),
                      let(tmp(e), l, ext(sw), [tmp(n)]),
                      let(tmp(z), w, cmp(ne, l), [tmp(e), const(0)])], branch(tmp(z), t, f)),
        block(t, [], [], ret(const(1))),
        block(f, [], [], ret(const(2)))]),
    Notb = func(notb, export, w, [param(w, tmp(a))], [
        block(s, [], [let(tmp(c), w, and, [tmp(a), const(1)]),
                      let(tmp(n), w, cmp(eq, w), [tmp(c), const(0)])], branch(tmp(n), t, f)),
        block(t, [], [], ret(const(10))),
        block(f, [], [], ret(const(20)))]),
    Constbr = func(constbr, export, w, [param(w, tmp(x))], [
        block(s, [], [let(tmp(k), w, cmp(eq, l), [const(8), const(8)])], branch(tmp(k), a, b)),
        block(a, [], [let(tmp(y), w, add, [tmp(x), const(1)])], goto(j)),
        block(b, [], [let(tmp(y2), w, add, [tmp(x), const(2)])], goto(j)),
        block(j, [phi(tmp(r), w, [a-tmp(y), b-tmp(y2)])], [], ret(tmp(r)))]),
    Gvn = func(gvn, export, w, [param(w, tmp(c)), param(w, tmp(x))], [
        block(s, [], [let(tmp(t1), w, add, [tmp(x), const(3)])], branch(tmp(c), a, b)),
        block(a, [], [let(tmp(u), w, mul, [tmp(x), tmp(x)]),
                      let(tmp(t2), w, add, [const(3), tmp(x)]),
                      let(tmp(u2), w, add, [tmp(u), tmp(t2)])], goto(j)),
        block(b, [], [let(tmp(v), w, mul, [tmp(x), tmp(x)])], goto(j)),
        block(j, [phi(tmp(r), w, [a-tmp(u2), b-tmp(v)])],
              [let(tmp(w2), w, mul, [tmp(x), tmp(x)]),
               let(tmp(r2), w, add, [tmp(r), tmp(w2)]),
               let(tmp(r3), w, add, [tmp(r2), tmp(t1)])], ret(tmp(r3)))]),
    Bypass = func(bypass, export, w, [param(w, tmp(c)), param(w, tmp(x))], [
        block(s, [], [], branch(tmp(c), a, b)),
        block(a, [], [let(tmp(ya), w, add, [tmp(x), const(1)])], goto(e)),
        block(b, [], [let(tmp(yb), w, add, [tmp(x), const(2)])], goto(e)),
        block(e, [phi(tmp(q), w, [a-tmp(ya), b-tmp(yb)])], [], goto(t)),
        block(t, [phi(tmp(r), w, [e-tmp(q), l-tmp(r2)])],
              [let(tmp(k), w, cmp(ult, w), [tmp(r), const(30)])], branch(tmp(k), l, done)),
        block(l, [], [let(tmp(r2), w, add, [tmp(r), const(10)])], goto(t)),
        block(done, [], [], ret(tmp(r)))]),
    Strength = func(strength, export, w, [param(w, tmp(x))], [block(s, [], [
        let(tmp(m), w, mul, [tmp(x), const(8)]),
        let(tmp(u), w, udiv, [tmp(x), const(16)]),
        let(tmp(v), w, urem, [tmp(x), const(16)]),
        let(tmp(s1), w, add, [tmp(m), tmp(u)]),
        let(tmp(s2), w, add, [tmp(s1), tmp(v)])], ret(tmp(s2)))]),
    Dead = func(deadload, export, w, [param(l, tmp(x))], [block(s, [], [
        let(tmp(p), p, itop, [tmp(x)]),
        let(tmp(v), w, load(sw), [tmp(p)]),
        let(tmp(d), w, add, [tmp(v), const(1)]),
        let(tmp(q), l, udiv, [tmp(x), tmp(x)])], ret(const(0)))]),
    Narrow = func(narrow, export, w, [param(w, tmp(x))], [block(s, [], [
        let(tmp(a), p, alloc(4), [const(4)]),
        store(h, tmp(x), tmp(a)),
        let(tmp(v), w, load(uh), [tmp(a)]),
        let(tmp(e), w, ext(uh), [tmp(v)]),
        let(tmp(f), w, ext(sh), [tmp(v)]),
        let(tmp(g), w, add, [tmp(e), tmp(f)])], ret(tmp(g)))]),
    ir_module([Fold, Div0, Bools, Notb, Constbr, Gvn, Bypass, Strength, Dead, Narrow], M0),
    optimize(passes([simplify]), M0, M), once(valid_module(M)),
    Runs = [fold-[]-ret(4294967298), div0-[1]-ub(division_by_zero),
            bools-[4294967295, 0]-ret(2), bools-[0, 4294967295]-ret(1),
            bools-[5, 5]-ret(1), notb-[2]-ret(10), notb-[3]-ret(20),
            constbr-[4294967295]-ret(0),
            gvn-[1, 2]-ret(18), gvn-[0, 2]-ret(13),
            bypass-[1, 5]-ret(36), bypass-[0, 5]-ret(37),
            strength-[4294967295]-ret(268435462), strength-[536870912]-ret(33554432),
            deadload-[0]-trap(null_capability),
            narrow-[65535]-ret(65534), narrow-[4294934528]-ret(0)],
    forall(member(Fn-Args-Out, Runs),
           ( module_fn_args_outcome(M0, Fn, Args, Out0), Out0 == Out,
             module_fn_args_outcome(M, Fn, Args, Out1), Out1 == Out )),
    M = module(Items),
    forall(member(F, Items),
           ( F = func(_, _, _, _, Bs), func_cfg(Bs, Cfg), cfg_idoms(Cfg, Idom),
             strict_ssa(F, Cfg, Idom) )),
    func_named(M, fold, func(_, _, _, _, [block(s, [], [], ret(const(4294967298)))])),
    func_named(M, div0, func(_, _, _, _, [block(s, [], [let(tmp(q), w, udiv, [const(5), const(0)]), _], _)])),
    % bools: one comparison, its negation, decides the branch.
    func_named(M, bools, func(_, _, _, _, [block(s, [], [let(tmp(N), w, cmp(sge, w), [tmp(a), tmp(b)])],
                                                  branch(tmp(N), t, f))|_])),
    func_named(M, notb, func(_, _, _, _, [block(s, [], [let(tmp(Cn), w, and, _)], branch(tmp(Cn), f, t))|_])),
    func_named(M, constbr, func(_, _, _, _, [block(s, [], [let(_, w, add, [tmp(x), const(1)])], ret(_))])),
    % gvn: t2 reuses t1 (a dominating add, operands swapped); w2 stays,
    % since neither mul dominates j.
    func_named(M, gvn, func(_, _, _, _, GB)),
    findall(x, ( member(block(_, _, Is, _), GB), member(let(_, _, add, [_, const(3)]), Is) ), [x]),
    findall(x, ( member(block(_, _, Is, _), GB), member(let(_, _, mul, _), Is) ), [x, x, x]),
    func_named(M, bypass, func(_, _, _, _, BB)), \+ memberchk(block(e, _, _, _), BB),
    func_named(M, strength, func(_, _, _, _, [block(s, [], SI, _)])),
    findall(Op, member(let(_, _, Op, _), SI), [shl, shr, and, add, add]),
    func_named(M, deadload, func(_, _, _, _, [block(s, [], DI, _)])),
    findall(Op, member(let(_, _, Op, _), DI), [itop, load(sw), udiv]),
    func_named(M, narrow, func(_, _, _, _, [block(s, [], NI, _)])),
    findall(Op, member(let(_, _, Op, _), NI), [alloc(4), load(uh), ext(sh), add]).

% Simplify's source contexts: a removed instruction's site goes, and an
% appended block's sites move into its predecessor at its offset.
test(simplify_contexts) :-
    O = origin(_, at('t.c', 1), statement(expr), []),
    F = func(f, export, w, [param(w, tmp(n))], [
        block(s, [], [let(tmp(d), w, mul, [tmp(n), tmp(n)]),
                      let(tmp(a), w, add, [tmp(n), const(2)])], goto(t)),
        block(t, [], [let(tmp(b), w, mul, [tmp(a), tmp(n)])], ret(tmp(b)))]),
    maplist(origin_named(O), [o0, o1, o2, o3, o4], Os),
    ir_module([F, context(f, [site(inst(s, 0), [o0]), site(inst(s, 1), [o1]),
                              site(jump(s), [o2]), site(inst(t, 0), [o3]),
                              site(jump(t), [o4])|Os])], M0),
    optimize(passes([simplify]), M0, module(Items)),
    once(valid_module(module(Items))),
    memberchk(func(f, _, _, _, [block(s, [], [let(tmp(a), _, _, _), let(tmp(b), _, _, _)], ret(tmp(b)))]), Items),
    memberchk(context(f, Rs), Items),
    findall(S-Ids, member(site(S, Ids), Rs), Sites),
    msort(Sites, Got),
    msort([inst(s, 0)-[o1], inst(s, 1)-[o3], jump(s)-[o4]], Want),
    Got == Want,
    % A block that has absorbed its successor is absorbed in turn by a
    % block after it: the holder's jump site is the last block's (the
    % review's case: a stale entry left two jump sites, one for b2).
    G = func(g, export, w, [param(w, tmp(c)), param(w, tmp(n))], [
        block(s, [], [], branch(tmp(c), b1, x)),
        block(b2, [], [let(tmp(y), w, mul, [tmp(n), tmp(n)])], goto(b3)),
        block(b1, [], [let(tmp(z), w, mul, [tmp(n), tmp(c)])], goto(b2)),
        block(b3, [], [let(tmp(u), w, add, [tmp(y), tmp(z)])], ret(tmp(u))),
        block(x, [], [], ret(const(0)))]),
    maplist(origin_named(O), [p0, p1, p2, p3, p4, p5], Ps),
    ir_module([G, context(g, [site(jump(b2), [p0]), site(jump(b1), [p1]),
                              site(jump(b3), [p2]), site(inst(b2, 0), [p3]),
                              site(inst(b1, 0), [p4]), site(inst(b3, 0), [p5])|Ps])], G0),
    optimize(passes([simplify]), G0, module(GItems)),
    once(valid_module(module(GItems))),
    memberchk(func(g, _, _, _, [_, block(b1, [], [let(tmp(z), _, _, _), let(tmp(y), _, _, _),
                                                 let(tmp(u), _, _, _)], ret(tmp(u))), _]), GItems),
    memberchk(context(g, GRs), GItems),
    findall(S-Ids, member(site(S, Ids), GRs), GSites),
    msort(GSites, GGot),
    msort([inst(b1, 0)-[p4], inst(b1, 1)-[p3], inst(b1, 2)-[p5], jump(b1)-[p2]], GWant),
    GGot == GWant.

% Which allocs promote must remove, and which it must keep, on the
% fixture and on tests/c/basic.c (only arr's array and ptrs's array have
% their address passed or stored). A promote that did nothing would still
% pass every differential test; this does not.
test(promote_removes_allocs) :-
    file_module('../tests/fixtures/promote.ir', M0),
    alloc_count(M0, 12),
    optimize(o1, M0, M),
    once(valid_module(M)),
    alloc_count(M, 3),
    func_named(M, kept, K),
    alloc_count(module([K]), 3),
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
    reuse_checks(Before, Before1), Before1 == Before,
    % The pass leaves no choicepoint, even at a poll edge: one per
    % function kept every function's terms alive, and SQLite's -O
    % --checks=reuse compile overflowed the 1 GB stack.
    reuse_cfg([block(s, [], [C, S], goto(h)), block(h, [], [L], goto(poll(h)))], Loop),
    call_cleanup(reuse_checks(Loop, _), Det = true), Det == true.

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

% Round 3 (docs/m7.md): a check of a constant-offset flight from the
% same root, with the same lower donor, reuses the root's proof at the
% shifted offset. Fields hold distinct values, so a wrong distance or
% root shows as a value; refines rejects both rewirings independently.
test(reuse_related) :-
    Obj = [let(tmp(p), p, alloc(16), [const(16)]),
           let(tmp(q), a, check(0, 16, write, 1), [tmp(p)]),
           raw_store(l, 0, const(5), tmp(q)), raw_store(l, 8, const(7), tmp(q))],
    F8 = flight(tmp(f), add, [address(tmp(p)), const(8)], lower(tmp(p))),
    Read = [let(tmp(c), a, check(0, 8, read, 1), [tmp(f)]),
            let(tmp(x), l, raw_load(l, 0), [tmp(c)])],
    append([Obj, [F8], Read], RefIs), reuse_l_fn(RefIs, Ref),
    valid_module(Ref), once(run(Ref, f, [], 10, ret(7))),
    reuse_checks(Ref, R), reuse_refines(Ref, R), valid_module(R),
    once(run(R, f, [], 10, ret(7))),
    R = module([func(f, _, _, _, [block(s, [], RIs, _)])|_]),
    append(_, [F8, let(tmp(x), l, raw_load(l, 8), [tmp(q)])], RIs),
    % It emits as a reload of p plus 8, with one check.
    once(( filc_module_asm(R, emit(temps, selected), Lines, _),
           memberchk(ins(add, q, [imm(8), reg(rax)]), Lines) )),
    reuse_fail_jumps(R, 1),
    % The same flight read at the wrong distance (offset 0) is valid and
    % reads 5; only refines tells.
    append([Obj, [F8], [let(tmp(x), l, raw_load(l, 0), [tmp(q)])]], DistIs),
    reuse_l_fn(DistIs, Dist), valid_module(Dist), once(run(Dist, f, [], 10, ret(5))),
    \+ reuse_refines(Ref, Dist),
    % A rewiring to another root's proof at the right offset reads o's 9.
    O = [let(tmp(o), p, alloc(16), [const(16)]),
         let(tmp(r), a, check(0, 16, write, 1), [tmp(o)]),
         raw_store(l, 8, const(9), tmp(r))],
    append([Obj, O, [F8], Read], Ref2Is), reuse_l_fn(Ref2Is, Ref2),
    append([Obj, O, [F8], [let(tmp(x), l, raw_load(l, 8), [tmp(r)])]], RootIs),
    reuse_l_fn(RootIs, Root), valid_module(Root), once(run(Root, f, [], 10, ret(9))),
    \+ reuse_refines(Ref2, Root),
    % Kept: another lower donor, another root, a shifted range outside
    % the proof, a read proof before a store, and a free in between.
    forall(member(Is, [
        % (o first: an alloc after p's proof would end it anyway.)
        [ O, Obj, [flight(tmp(f), add, [address(tmp(p)), const(8)], lower(tmp(o)))], Read ],
        [ [let(tmp(o), p, alloc(16), [const(16)])], Obj,
          [flight(tmp(f), add, [address(tmp(o)), const(8)], lower(tmp(o)))], Read ],
        [ [let(tmp(p), p, alloc(16), [const(16)]),
           let(tmp(q), a, check(0, 8, write, 1), [tmp(p)]),
           raw_store(l, 0, const(5), tmp(q))], [F8], Read ],
        [ [let(tmp(p), p, alloc(16), [const(16)]),
           let(tmp(q), a, check(0, 16, read, 1), [tmp(p)]),
           let(tmp(x0), l, raw_load(l, 0), [tmp(q)])], [F8],
          [let(tmp(c), a, check(0, 8, write, 1), [tmp(f)]),
           raw_store(l, 0, const(3), tmp(c)), let(tmp(x), l, add, [tmp(x0), const(0)])] ],
        [ Obj, [F8, call(void, global(free), [arg(p, tmp(p))])], Read ]]),
        ( append(Is, Flat), reuse_l_fn(Flat, M), valid_module(M),
          reuse_checks(M, M1), M1 == M )),
    % The validator still bounds a rewired access by its proof's range.
    append([Obj, [F8], [let(tmp(x), l, raw_load(l, 16), [tmp(q)])]], OutIs),
    reuse_l_fn(OutIs, Out), reuse_rejected(Out),
    % A negative distance, from hand-written checked IR (pizlonation's
    % checks have Lo = 0): f's proof of [-8, 8), the only one, covers
    % p's [0, 8).
    Neg = [let(tmp(p), p, alloc(16), [const(16)]), F8,
           let(tmp(n), a, check(-8, 8, write, 1), [tmp(f)]),
           raw_store(l, -8, const(5), tmp(n)),
           let(tmp(c), a, check(0, 8, read, 1), [tmp(p)]),
           let(tmp(x), l, raw_load(l, 0), [tmp(c)])],
    reuse_l_fn(Neg, NegM), valid_module(NegM),
    reuse_checks(NegM, NegR), reuse_refines(NegM, NegR), valid_module(NegR),
    NegR = module([func(f, _, _, _, [block(s, [], NIs, _)])|_]),
    last(NIs, let(tmp(x), l, raw_load(l, -8), [tmp(n)])),
    once(run(NegR, f, [], 10, ret(5))),
    % Self-referential and two-cycle flights in an unreachable block:
    % the pass terminates and keeps their checks.
    forall(member(Cyc, [
        [flight(tmp(u), add, [address(tmp(u)), const(8)], lower(tmp(u)))],
        [flight(tmp(u), add, [address(tmp(v)), const(8)], lower(tmp(v))),
         flight(tmp(v), add, [address(tmp(u)), const(8)], lower(tmp(u)))]]),
        ( append(Cyc, [let(tmp(k1), a, check(0, 8, read, 1), [tmp(u)]),
                       let(tmp(z1), l, raw_load(l, 0), [tmp(k1)]),
                       flight(tmp(w), add, [address(tmp(u)), const(8)], lower(tmp(u))),
                       let(tmp(k2), a, check(0, 8, read, 1), [tmp(w)]),
                       let(tmp(z2), l, raw_load(l, 0), [tmp(k2)])], Dead),
          C = module([func(f, local, l, [], [block(s, [], [], ret(const(0))),
                                             block(d, [], Dead, ret(tmp(z2)))])]),
          valid_module(C), reuse_checks(C, C1), reuse_refines(C, C1) )).

% Renewal (docs/m7.md, round 4): a heap check dominated by a check of
% the same pointer that covers its bounds and alignment tests only that
% the object is not freed (and for a write not read-only), across calls
% and polls. renew_fn(+Blocks, -M): f(a, b, c) with Blocks.
renew_fn(Blocks, module([func(f, local, l,
    [param(p, tmp(a)), param(p, tmp(b)), param(w, tmp(c))], Blocks)])).

renew_rejected(M) :-
    catch(( valid_module(M), fail ), nanofil_error(Msg), true),
    once(sub_atom(Msg, _, _, _, renew)).

test(renew_validation) :-
    C = let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
    L = let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
    Rn = let(tmp(r), a, renew(0, 8, write, 1), [tmp(q), tmp(a)]),
    W = raw_store(l, 0, const(2), tmp(r)),
    Call = call(void, global(free), [arg(p, tmp(b))]),
    R = ret(const(0)),
    % Accepted: after a call, and across a poll edge (a back edge too).
    forall(member(Bs, [
        [block(s, [], [C, L, Call, Rn, W], R)],
        [block(s, [], [C, L], goto(poll(t))), block(t, [], [Call, Rn, W], R)],
        [block(s, [], [C, L], goto(h)),
         block(h, [], [Call, Rn, W], branch(tmp(c), poll(h), e)), block(e, [], [], R)]
    ]), ( renew_fn(Bs, M), valid_module(M) )),
    % An irreducible loop {a, d, b}, entered at a and at b: d, which
    % only a enters, may renew a's check; b, which s also enters, not.
    Irr = [block(s, [], [], branch(tmp(c), a, b)),
           block(a, [], [C, L], goto(d)),
           block(d, [], [Call, Rn, W], goto(b)),
           block(b, [], [], branch(tmp(c), poll(a), e)),
           block(e, [], [], R)],
    renew_fn(Irr, IrrM), valid_module(IrrM),
    renew_fn([block(s, [], [], branch(tmp(c), a, b)),
              block(a, [], [C, L], goto(b)),
              block(b, [], [Call, Rn, W], branch(tmp(c), poll(a), e)),
              block(e, [], [], R)], IrrBad),
    catch(( valid_module(IrrBad), fail ), nanofil_error(_), true),
    % Rejected: Q1 does not dominate (one arm checks), a second definition
    % of P1 (a phi) or of Q1, a setjmp, too little range, a weaker
    % alignment, a renew not followed by its access, an empty range, Q1
    % later in the block.
    renew_fn([block(s, [], [], branch(tmp(c), t, u)), block(t, [], [C, L], goto(j)),
              block(u, [], [], goto(j)), block(j, [], [Rn, W], R)], NoDom),
    catch(( valid_module(NoDom), fail ), nanofil_error(_), true),
    renew_fn([block(s, [], [], branch(tmp(c), t, j)), block(t, [], [], goto(j)),
              block(j, [phi(tmp(a), p, [s-tmp(a), t-tmp(b)])], [C, L, Call, Rn, W], R)], TwoP),
    renew_rejected(TwoP),
    renew_fn([block(s, [], [C, L, Call, Rn, W], R),
              block(u, [], [C, L], R)], TwoQ),
    renew_rejected(TwoQ),
    renew_fn([block(s, [], [C, L,
                  let(tmp(j), w, setjmp('_setjmp'), [tmp(b), const(0)]),
                  Rn, W], R)], Sj),
    renew_rejected(Sj),
    renew_fn([block(s, [], [C, L, Call, let(tmp(r), a, renew(0, 16, write, 1), [tmp(q), tmp(a)]),
                            raw_store(l, 0, const(2), tmp(r))], R)], Wide),
    renew_rejected(Wide),
    renew_fn([block(s, [], [C, L, Call, let(tmp(r), a, renew(0, 8, read, 8), [tmp(q), tmp(a)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(r)])], R)], Aligned),
    renew_rejected(Aligned),
    renew_fn([block(s, [], [C, L, Call, Rn, Call, W], R)], Apart),
    renew_rejected(Apart),
    renew_fn([block(s, [], [C, L, Call, let(tmp(r), a, renew(4, 4, read, 1), [tmp(q), tmp(a)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(r)])], R)], Empty),
    renew_rejected(Empty),
    % Q1 later in the same block.
    renew_fn([block(s, [], [Call, Rn, W, C, L], R)], Later),
    catch(( valid_module(Later), fail ), nanofil_error(_), true),
    % Q1 starts later than the renew, or at an offset its alignment
    % does not reach.
    renew_fn([block(s, [], [let(tmp(q), a, check(4, 12, read, 1), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 4), [tmp(q)]), Call,
                            let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), tmp(a)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(r)])], R)], Below),
    renew_rejected(Below),
    renew_fn([block(s, [], [let(tmp(q), a, check(0, 16, read, 8), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 0), [tmp(q)]), Call,
                            let(tmp(r), a, renew(4, 12, read, 8), [tmp(q), tmp(a)]),
                            let(tmp(y), l, raw_load(l, 4), [tmp(r)])], R)], Shifted),
    renew_rejected(Shifted),
    % A renew of a renew's proof is not a check's.
    renew_fn([block(s, [], [C, L, Call, Rn, W, Call,
                            let(tmp(r2), a, renew(0, 8, write, 1), [tmp(r), tmp(a)]),
                            raw_store(l, 0, const(3), tmp(r2))], R)], Chain),
    renew_rejected(Chain),
    % P must hold P1's address and capability (same_pointer/3): another
    % pointer, a different offset or lower donor are refused; another
    % flight to the same address from the same base is accepted.
    Fa0 = flight(tmp(a0), copy, [address(tmp(a))], lower(tmp(a))),
    F4 = flight(tmp(a4), add, [address(tmp(a)), const(4)], lower(tmp(a))),
    F4b = flight(tmp(a4b), add, [address(tmp(a)), const(4)], lower(tmp(a))),
    F4x = flight(tmp(a4x), add, [address(tmp(a)), const(4)], lower(tmp(b))),
    F4n = flight(tmp(a4n), sub, [address(tmp(a)), const(-4)], lower(tmp(a))),
    Rp = [P0, M1]>>( renew_fn([block(s, [], [F4, F4b, F4x, F4n, Fa0,
                           let(tmp(q), a, check(0, 8, read, 1), [tmp(a4)]),
                           let(tmp(x), l, raw_load(l, 0), [tmp(q)]), Call], R)], M0),
                         M0 = module([func(Fn, Lk, Rt, Ps, [block(Lb, Ph, Is0, J)])]),
                         append(Is0, [let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), P0]),
                                      let(tmp(y), l, raw_load(l, 0), [tmp(r)])], Is1),
                         M1 = module([func(Fn, Lk, Rt, Ps, [block(Lb, Ph, Is1, J)])]) ),
    forall(member(P0, [tmp(a4), tmp(a4b), tmp(a4n)]),
           ( call(Rp, P0, Mok), valid_module(Mok) )),
    forall(member(P0, [tmp(a), tmp(a0), tmp(b), tmp(a4x)]),
           ( call(Rp, P0, Mno), renew_rejected(Mno) )),
    % The emitter's access reads P, not P1, so P1 need not stay live,
    % and the validator's fact after it is keyed by P.
    call(Rp, tmp(a4b), Mp), Mp = module([func(_, _, _, Pp, BsP)]),
    filc_amd64:fused_blocks(f, Pp, BsP, [block(_, _, IsF, _)], _),
    memberchk(fused(renew(_, _, _, _), let(_, _, _, [PF])), IsF), PF == tmp(a4b),
    BsP = [block(_, _, IsP, _)],
    ir:stage_sources(Pp, BsP, SrcP), ir:evidence_none(Ev0),
    ir:checked_insts(IsP, f-SrcP, filc, Ev0, ev(FsP, _, _)),
    memberchk(live(r, PL, _, _, _, _), FsP), PL == tmp(a4b),
    % The emitter refuses the first two as well, rather than reloading
    % a pointer that may not be the one Q1 checked.
    forall(member(Bad, [TwoP, TwoQ]),
           catch(( filc_module_asm(Bad, _), fail ), nanofil_error(_), true)).

% The interpreter runs a renew's whole access test: a free in between
% traps out_of_bounds and a write to a read-only object traps readonly,
% as the replaced check does; a span that was never true is unchecked.
test(renew_semantics) :-
    Alloc = let(tmp(p), p, alloc(8), [const(8)]),
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(p)]),
    S = raw_store(l, 0, const(5), tmp(q)),
    Free = call(void, global(free), [arg(p, tmp(p))]),
    Ld = [let(tmp(x), l, raw_load(l, 0), [tmp(r)])],
    reuse_l_fn([Alloc, C, S, Free, let(tmp(r), a, check(0, 8, read, 1), [tmp(p)])|Ld], Ref),
    reuse_l_fn([Alloc, C, S, Free, let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), tmp(p)])|Ld], Ren),
    valid_module(Ref), valid_module(Ren),
    once(run(Ref, f, [], 10, trap(out_of_bounds))),
    once(run(Ren, f, [], 10, trap(out_of_bounds))),
    reuse_l_fn([Alloc, C, S, let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), tmp(p)])|Ld], Live),
    valid_module(Live), once(run(Live, f, [], 10, ret(5))),
    Ro = module([data(msg, ro(local), 1, [item(b, str("h"))]),
        func(g, local, w, [], [block(s, [], [
            let(tmp(p), p, copy, [global(msg)]),
            let(tmp(q), a, check(0, 1, read, 1), [tmp(p)]),
            let(tmp(x), w, raw_load(ub, 0), [tmp(q)]),
            let(tmp(r), a, renew(0, 1, write, 1), [tmp(q), tmp(p)]),
            raw_store(b, 0, const(1), tmp(r))
        ], ret(tmp(x)))])]),
    valid_module(Ro), once(run(Ro, g, [], 10, trap(readonly))),
    % Forged: more range than the object has, or an alignment the
    % address lacks. The validator rejects both; run anyway, unchecked.
    reuse_l_fn([Alloc, C, S, let(tmp(r), a, renew(0, 64, read, 1), [tmp(q), tmp(p)]),
                let(tmp(x), l, raw_load(l, 0), [tmp(r)])], Wide),
    renew_rejected(Wide), once(run(Wide, f, [], 10, unchecked(span))),
    reuse_l_fn([Alloc, flight(tmp(o), add, [address(tmp(p)), const(1)], lower(tmp(p))),
                let(tmp(q), a, check(0, 4, write, 1), [tmp(o)]),
                raw_store(w, 0, const(5), tmp(q)),
                let(tmp(r), a, renew(0, 4, read, 4), [tmp(q), tmp(o)]),
                let(tmp(y), w, raw_load(sw, 0), [tmp(r)]),
                let(tmp(x), l, ext(sw), [tmp(y)])], Mis),
    renew_rejected(Mis), once(run(Mis, f, [], 10, unchecked(span))),
    % Forged: P is another object's pointer, live and in bounds, which
    % the validator refuses; run anyway, unchecked(alias).
    reuse_l_fn([Alloc, C, S, let(tmp(p2), p, alloc(8), [const(8)]),
                let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), tmp(p2)])|Ld], Other),
    renew_rejected(Other), once(run(Other, f, [], 10, O)), O == unchecked(alias).

% The pass renews a loop's checks after a call when the check before the
% loop dominates and covers them, keeps those it does not cover, and all
% modules agree; renew_refines/2 accepts it and refuses a renew of
% another object's proof. Native: fewer full checks, a flag test each.
test(renew_pass) :-
    ir_module([func(f, local, l, [param(w, tmp(k))], [
        block(s, [], [
            let(tmp(p), p, alloc(8), [const(16)]),
            store(l, const(1), tmp(p)),
            let(tmp(v0), l, load(l), [tmp(p)])
        ], goto(h)),
        block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                  phi(tmp(t), l, [s-tmp(v0), b-tmp(t1)])], [
            let(tmp(m), w, cmp(slt, w), [tmp(i), tmp(k)])
        ], branch(tmp(m), b, e)),
        block(b, [], [
            let(tmp(o), p, alloc(8), [const(16)]),
            call(void, global(free), [arg(p, tmp(o))]),
            let(tmp(v), l, load(l), [tmp(p)]),
            let(tmp(t1), l, add, [tmp(t), tmp(v)]),
            store(l, tmp(t1), tmp(p)),
            let(tmp(p8), p, add, [tmp(p), const(8)]),
            let(tmp(u), l, load(l), [tmp(p8)]),
            let(tmp(t2), l, add, [tmp(t1), tmp(u)]),
            store(l, tmp(t2), tmp(p8)),
            let(tmp(i1), w, add, [tmp(i), const(1)])
        ], goto(h)),
        block(e, [], [], ret(tmp(t)))])], M),
    pizlonate_module(M, C0), reuse_checks(C0, C1), renew_checks(C1, C2),
    renew_refines(C1, C2), valid_module(C2),
    C2 = module([func(f, _, _, _, Bs)|_]), memberchk(block(b, _, Is, _), Bs),
    findall(Op, member(let(_, a, Op, _), Is), Ops),
    % p's load and store are renewed after the call (a read never covers
    % a write, so the store gets its own); p+8 was never checked before
    % the loop: its load's check stays, and its store renews that.
    Ops = [renew(0, 8, read, 1), renew(0, 8, write, 1), check(0, 8, read, 1),
           renew(0, 8, write, 1)],
    % *p doubles each iteration: 1, 2, 4, 8.
    forall(member(Mod, [M, C0, C2]),
           ( once(run(Mod, f, [3], 100, ret(R))), R == 8 )),
    reuse_fail_jumps(C1, N1), reuse_fail_jumps(C2, N2), N2 < N1,
    filc_module_asm(C2, Lines), memberchk(ins(test, b, [imm(6), mem(-2, rcx)]), Lines),
    % Wrong object: the renew reads o's proof.
    renew_fn([block(s, [], [let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
                            let(tmp(qb), a, check(0, 8, read, 1), [tmp(b)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(qb)]),
                            let(tmp(r), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(z), l, raw_load(l, 0), [tmp(r)])], ret(tmp(z)))], Two),
    valid_module(Two), renew_checks(Two, Two1), renew_refines(Two, Two1),
    Two1 = module([func(_, _, _, _, [block(_, _, [_, _, _, _, let(_, a, renew(_, _, _, _), [tmp(q), _]), _], _)])]),
    renew_fn([block(s, [], [let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
                            let(tmp(qb), a, check(0, 8, read, 1), [tmp(b)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(qb)]),
                            let(tmp(r), a, renew(0, 8, read, 1), [tmp(qb), tmp(a)]),
                            let(tmp(z), l, raw_load(l, 0), [tmp(r)])], ret(tmp(z)))], Wrong),
    renew_rejected(Wrong), \+ renew_refines(Two, Wrong),
    % Wrong distance: a check of a+8 renewed from a's proof. The
    % validator refuses it (a+8 is not a's address), and so does
    % renew_refines.
    F8 = flight(tmp(a8), add, [address(tmp(a)), const(8)], lower(tmp(a))),
    Q16 = [let(tmp(q), a, check(0, 16, read, 1), [tmp(a)]),
           let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
           call(void, global(free), [arg(p, tmp(b))]), F8],
    append(Q16, [let(tmp(k), a, check(0, 8, read, 1), [tmp(a8)]),
                 let(tmp(y), l, raw_load(l, 0), [tmp(k)])], DIs),
    renew_fn([block(s, [], DIs, ret(tmp(y)))], Dist),
    append(Q16, [let(tmp(k), a, renew(0, 8, read, 1), [tmp(q), tmp(a8)]),
                 let(tmp(y), l, raw_load(l, 0), [tmp(k)])], DwIs),
    renew_fn([block(s, [], DwIs, ret(tmp(y)))], DistWrong),
    valid_module(Dist), renew_rejected(DistWrong), \+ renew_refines(Dist, DistWrong),
    renew_checks(Dist, Dist1), Dist1 == Dist,
    % A chain of +1 flights N links long against a+N: the pass renews only
    % what the validator's bounded walk accepts (65 links is beyond it).
    Chain = [N, Mc]>>( numlist(1, N, Ks),
        findall(flight(tmp(Pk), add, [address(tmp(Pj)), const(1)], lower(tmp(Pj))),
                ( member(K, Ks), atom_concat(p, K, Pk), J is K - 1,
                  ( J =:= 0 -> Pj = a ; atom_concat(p, J, Pj) ) ), Fs),
        atom_concat(p, N, PN),
        append([[flight(tmp(far), add, [address(tmp(a)), const(N)], lower(tmp(a))),
                 let(tmp(q), a, check(0, 8, read, 1), [tmp(far)]),
                 let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
                 call(void, global(free), [arg(p, tmp(b))])], Fs,
                [let(tmp(k), a, check(0, 8, read, 1), [tmp(PN)]),
                 let(tmp(y), l, raw_load(l, 0), [tmp(k)])]], CIs),
        renew_fn([block(s, [], CIs, ret(tmp(y)))], Mc) ),
    forall(member(N-Renewed, [10-true, 65-false]),
           ( call(Chain, N, Mc), valid_module(Mc), renew_checks(Mc, Mc1),
             renew_refines(Mc, Mc1), valid_module(Mc1),
             ( Mc1 == Mc -> Renewed == false ; Renewed == true ) )),
    % The pass's facts end at a redefinition of their pointer.
    renew_fn([block(s, [], [let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
                            flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b))),
                            let(tmp(k), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(y), l, raw_load(l, 0), [tmp(k)])], ret(tmp(y)))], Redef),
    valid_module(Redef), reuse_checks(Redef, Redef1), Redef1 == Redef,
    % The emitter refuses a renew whose source pointer has two
    % definitions, even unvalidated.
    renew_fn([block(s, [], [let(tmp(q), a, check(0, 8, read, 1), [tmp(a)]),
                            let(tmp(x), l, raw_load(l, 0), [tmp(q)])], goto(t)),
              block(t, [], [let(tmp(r), a, renew(0, 8, read, 1), [tmp(q), tmp(a)]),
                            let(tmp(z), l, raw_load(l, 0), [tmp(r)])], ret(tmp(z))),
              block(u, [], [flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b)))], goto(t))],
             TwoDefs),
    catch(( filc_module_asm(TwoDefs, _), fail ), nanofil_error(_), true).

% Range guards (docs/m7.md, round 5, slice A): a span test before a
% loop proves the bounds of every access through one base at offsets in
% a constant interval, and each check becomes renew_if, which tests only
% the free and read-only flags and alignment when the guard passed.
% guard_fn(+Pre, +Body, -M): f(a, b, c) with Pre in s, then Body in a
% loop h that calls free(b) and polls.
guard_fn(Pre, Body, M) :-
    append(Body, [call(void, global(free), [arg(p, tmp(b))])], Body1),
    renew_fn([block(s, [], Pre, goto(h)),
              block(h, [], Body1, branch(tmp(c), poll(h), e)),
              block(e, [], [], ret(const(0)))], M).

guard_rejected(M) :-
    catch(( valid_module(M), fail ), nanofil_error(Msg), true),
    once(sub_atom(Msg, _, _, _, renew_if)).

% guard_access(+P, +Lo, +Hi, +G, -Insts): a guarded read of [Lo, Hi) at P.
guard_access(P, Lo, Hi, G, [let(tmp(q), a, renew_if(Lo, Hi, read, 1), [P, tmp(G)]),
                            let(tmp(x), w, raw_load(ub, Lo), [tmp(q)])]).

test(guard_validation) :-
    Ok = [Pre, Body]>>( guard_fn(Pre, Body, M), valid_module(M) ),
    No = [Pre, Body]>>( guard_fn(Pre, Body, M), guard_rejected(M) ),
    G16 = let(tmp(g), w, span_test(0, 16), [tmp(a)]),
    F8 = flight(tmp(a8), add, [address(tmp(a)), const(8)], lower(tmp(a))),
    guard_access(tmp(a8), 0, 8, g, A8),
    % A constant offset: [8, 16) lies in [0, 16), and not in [0, 15) or
    % [9, 16) (one byte short at either end).
    call(Ok, [G16, F8], A8),
    call(No, [let(tmp(g), w, span_test(0, 15), [tmp(a)]), F8], A8),
    call(No, [let(tmp(g), w, span_test(9, 16), [tmp(a)]), F8], A8),
    % A byte index: [0, 256) fits a 256-byte table, and not 255; a
    % signed byte reaches [-128, 128), not [0, 256).
    Nub = [let(tmp(n), w, ext(ub), [tmp(c)]), let(tmp(nl), l, ext(uw), [tmp(n)]),
           flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))],
    guard_access(tmp(an), 0, 1, g, An),
    append(Nub, An, NubBody),
    call(Ok, [let(tmp(g), w, span_test(0, 256), [tmp(a)])], NubBody),
    call(No, [let(tmp(g), w, span_test(0, 255), [tmp(a)])], NubBody),
    Nsb = [let(tmp(n), w, ext(sb), [tmp(c)]), let(tmp(nl), l, ext(sw), [tmp(n)]),
           flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(-128, 128), [tmp(a)])], Nsb),
    call(No, [let(tmp(g), w, span_test(0, 256), [tmp(a)])], Nsb),
    % A sub flight negates its term: a - n lies in [-255, 0].
    Nsub = [let(tmp(n), w, ext(ub), [tmp(c)]), let(tmp(nl), l, ext(uw), [tmp(n)]),
            flight(tmp(an), sub, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(-255, 1), [tmp(a)])], Nsub),
    call(No, [let(tmp(g), w, span_test(0, 256), [tmp(a)])], Nsub),
    % Masks and scales: (c & 63) << 2 lies in [0, 252]; c % 10 in [0, 9].
    Nmask = [let(tmp(n), w, and, [tmp(c), const(63)]), let(tmp(n4), w, shl, [tmp(n), const(2)]),
             let(tmp(nl), l, ext(sw), [tmp(n4)]),
             flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(0, 253), [tmp(a)])], Nmask),
    call(No, [let(tmp(g), w, span_test(0, 252), [tmp(a)])], Nmask),
    Nrem = [let(tmp(n), w, urem, [tmp(c), const(10)]), let(tmp(nl), l, ext(uw), [tmp(n)]),
            flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(0, 10), [tmp(a)])], Nrem),
    call(No, [let(tmp(g), w, span_test(0, 9), [tmp(a)])], Nrem),
    % ext(uw) only of a w value known non-negative: a signed byte widened
    % unsigned is near 2^32, not in [-128, 128).
    Nuw = [let(tmp(n), w, ext(sb), [tmp(c)]), let(tmp(nl), l, ext(uw), [tmp(n)]),
           flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(No, [let(tmp(g), w, span_test(-128, 128), [tmp(a)])], Nuw),
    % A negative factor swaps the ends: -c lies in [-255, 0], not [0, 8).
    Nneg = [let(tmp(n0), w, ext(ub), [tmp(c)]), let(tmp(n), w, mul, [tmp(n0), const(-1)]),
            let(tmp(nl), l, ext(sw), [tmp(n)]),
            flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(-255, 1), [tmp(a)])], Nneg),
    call(No, [let(tmp(g), w, span_test(0, 8), [tmp(a)])], Nneg),
    % A w constant is signed: 0xFFFFFFFF sign-extended is -1, not 2^32-1.
    Ncst = [let(tmp(nl), l, ext(sw), [const(4294967295)]),
            flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An],
    call(Ok, [let(tmp(g), w, span_test(-1, 0), [tmp(a)])], Ncst),
    call(No, [let(tmp(g), w, span_test(4294967295, 4294967303), [tmp(a)])], Ncst),
    % A shift by the width is no interval, even where 1 << 64 and two
    % steps of -2^63 would sum to 0.
    Nshl = [let(tmp(nl), l, shl, [const(1), const(64)]),
            flight(tmp(a1), add, [address(tmp(a)), tmp(nl)], lower(tmp(a))),
            flight(tmp(a2), add, [address(tmp(a1)), const(9223372036854775808)], lower(tmp(a1))),
            flight(tmp(an), add, [address(tmp(a2)), const(9223372036854775808)], lower(tmp(a2)))|An],
    call(No, [let(tmp(g), w, span_test(0, 1), [tmp(a)])], Nshl),
    % w arithmetic that may wrap, or masks that do not bound a signed w
    % value: rejected whatever the span.
    Big = let(tmp(g), w, span_test(-9223372036854775807, 9223372036854775807), [tmp(a)]),
    forall(member(Def, [ [let(tmp(n0), w, ext(ub), [tmp(c)]),
                          let(tmp(n), w, add, [tmp(n0), const(2147483647)])],
                         [let(tmp(n), w, and, [tmp(c), const(2147483648)])],
                         [let(tmp(n), w, urem, [tmp(c), const(3000000000)])],
                         [let(tmp(n0), w, ext(ub), [tmp(c)]), let(tmp(n), w, shl, [tmp(n0), const(32)])],
                         [let(tmp(n0), w, ext(ub), [tmp(c)]), let(tmp(n), w, mul, [tmp(n0), const(16777216)])] ]),
           ( append(Def, [let(tmp(nl), l, ext(sw), [tmp(n)]),
                          flight(tmp(an), add, [address(tmp(a)), tmp(nl)], lower(tmp(a)))|An], B),
             call(No, [Big], B) )),
    % Another root, another lower donor, a guard that is not a span
    % test, an offset name defined twice, a setjmp, no access after it.
    guard_access(tmp(b), 0, 1, g, Ab), call(No, [G16], Ab),
    Fx = flight(tmp(ax), add, [address(tmp(a)), const(0)], lower(tmp(b))),
    guard_access(tmp(ax), 0, 1, g, Ax), call(No, [G16, Fx], Ax),
    guard_access(tmp(a), 0, 1, g, A0),
    call(Ok, [G16], A0),
    call(No, [let(tmp(g), w, copy, [const(1)])], A0),
    guard_fn([let(tmp(g), w, span_test(0, 256), [tmp(a)])], NubBody, Two0),
    Two0 = module([func(F, Lk, Rt, Ps, Bs0)]),
    append(Bs0, [block(u, [], [let(tmp(n), w, ext(ub), [tmp(c)])], goto(h))], Bs1),
    guard_rejected(module([func(F, Lk, Rt, Ps, Bs1)])),
    call(No, [G16, let(tmp(j), w, setjmp('_setjmp'), [tmp(b), const(0)])], A0),
    % The base defined twice (an unreachable copy redefines a).
    guard_fn([G16], A0, TwoA0), TwoA0 = module([func(F, Lk, Rt, Ps, BsA)]),
    append(BsA, [block(v, [], [flight(tmp(a), copy, [address(tmp(b))], lower(tmp(b)))], goto(h))], BsA1),
    guard_rejected(module([func(F, Lk, Rt, Ps, BsA1)])),
    guard_fn([G16], [let(tmp(q), a, renew_if(0, 1, read, 1), [tmp(a), tmp(g)])], Apart),
    guard_rejected(Apart),
    % A guard that does not dominate the loop: one arm defines it.
    renew_fn([block(s, [], [], branch(tmp(c), t, h)), block(t, [], [G16], goto(h)),
              block(h, [], A0, ret(const(0)))], NoDom),
    catch(( valid_module(NoDom), fail ), nanofil_error(_), true).

% The interpreter: a span test is 1 exactly when the object contains
% the span; renew_if with G = 0 is its check, and with G = 1 traps
% out_of_bounds after a free, readonly on a write to read-only data and
% misaligned on a misaligned address, as the check does; a forged guard
% shows as unchecked(span).
test(guard_semantics) :-
    Alloc = let(tmp(p), p, alloc(8), [const(16)]),
    St = [Lo, Hi, Insts]>>( Insts = [Alloc, let(tmp(g), w, span_test(Lo, Hi), [tmp(p)]),
                                     let(tmp(x), l, ext(uw), [tmp(g)])] ),
    forall(member(Lo-Hi-R, [0-16-1, 0-17-0, 8-16-1, -1-8-0, 15-16-1, 16-17-0]),
           ( call(St, Lo, Hi, Is), reuse_l_fn(Is, M), once(run(M, f, [], 10, ret(R))) )),
    Free = call(void, global(free), [arg(p, tmp(p))]),
    reuse_l_fn([Alloc, Free, let(tmp(g), w, span_test(0, 1), [tmp(p)]),
                let(tmp(x), l, ext(uw), [tmp(g)])], Freed),
    once(run(Freed, f, [], 10, ret(0))),
    G = let(tmp(g), w, span_test(0, 16), [tmp(p)]),
    Ld = [let(tmp(x), l, raw_load(l, 0), [tmp(r)])],
    reuse_l_fn([Alloc, G, Free, let(tmp(r), a, renew_if(0, 8, read, 1), [tmp(p), tmp(g)])|Ld], AfterFree),
    valid_module(AfterFree), once(run(AfterFree, f, [], 10, trap(out_of_bounds))),
    reuse_l_fn([Alloc, G, let(tmp(r), a, renew_if(0, 8, read, 1), [tmp(p), tmp(g)])|Ld], Live),
    valid_module(Live), once(run(Live, f, [], 10, ret(0))),
    % G = 0 (the span is wider than the object) runs the full check.
    G0 = let(tmp(g), w, span_test(0, 32), [tmp(p)]),
    F16 = flight(tmp(p16), add, [address(tmp(p)), const(16)], lower(tmp(p))),
    reuse_l_fn([Alloc, G0, F16, let(tmp(r), a, renew_if(0, 8, read, 1), [tmp(p16), tmp(g)])|Ld], Out),
    valid_module(Out), once(run(Out, f, [], 10, trap(out_of_bounds))),
    F1 = flight(tmp(p1), add, [address(tmp(p)), const(1)], lower(tmp(p))),
    reuse_l_fn([Alloc, G, F1, let(tmp(r), a, renew_if(0, 8, read, 8), [tmp(p1), tmp(g)])|Ld], Mis),
    valid_module(Mis), once(run(Mis, f, [], 10, trap(misaligned))),
    Ro = module([data(msg, ro(local), 1, [item(b, str("h"))]),
        func(g, local, w, [], [block(s, [], [
            let(tmp(p), p, copy, [global(msg)]),
            let(tmp(g), w, span_test(0, 1), [tmp(p)]),
            let(tmp(r), a, renew_if(0, 1, write, 1), [tmp(p), tmp(g)]),
            raw_store(b, 0, const(1), tmp(r))
        ], ret(tmp(g)))])]),
    valid_module(Ro), once(run(Ro, g, [], 10, trap(readonly))),
    reuse_l_fn([Alloc, let(tmp(g), w, copy, [const(1)]),
                let(tmp(r), a, renew_if(0, 64, read, 1), [tmp(p), tmp(g)])|Ld], Forged),
    guard_rejected(Forged), once(run(Forged, f, [], 10, unchecked(span))).

% The pass guards the loop's check of p+8, which no check before the
% loop dominates, with one span test at the end of s; all modules agree,
% guard_refines/2 accepts the result and refuses a moved check or a
% guard read from another name. Native: a guard test per access.
test(guard_pass) :-
    ir_module([func(f, local, l, [param(w, tmp(k))], [
        block(s, [], [
            let(tmp(p), p, alloc(8), [const(16)]),
            store(l, const(1), tmp(p)),
            let(tmp(p8), p, add, [tmp(p), const(8)])
        ], goto(h)),
        block(h, [phi(tmp(i), w, [s-const(0), b-tmp(i1)]),
                  phi(tmp(t), l, [s-const(0), b-tmp(t1)])], [
            let(tmp(m), w, cmp(slt, w), [tmp(i), tmp(k)])
        ], branch(tmp(m), b, e)),
        block(b, [], [
            let(tmp(o), p, alloc(8), [const(16)]),
            call(void, global(free), [arg(p, tmp(o))]),
            let(tmp(u), l, load(l), [tmp(p8)]),
            let(tmp(t1), l, add, [tmp(t), tmp(u)]),
            store(l, tmp(t1), tmp(p8)),
            let(tmp(i1), w, add, [tmp(i), const(1)])
        ], goto(h)),
        block(e, [], [], ret(tmp(t)))])], M),
    pizlonate_module(M, C0), reuse_checks(C0, C1), renew_checks(C1, C2),
    guard_checks(C2, C3), guard_refines(C2, C3), valid_module(C3),
    C3 = module([func(f, _, _, _, Bs)|_]),
    memberchk(block(s, _, SIs, _), Bs), last(SIs, let(tmp(G), w, span_test(8, 16), [tmp(p)])),
    memberchk(block(b, _, Is, _), Bs),
    findall(Op, member(let(_, a, Op, _), Is), Ops),
    % The store renews the guarded read's proof (round 4).
    Ops = [renew_if(0, 8, read, 1), renew(0, 8, write, 1)],
    forall(member(Mod, [M, C0, C3]),
           ( once(run(Mod, f, [3], 100, ret(R))), R == 0 )),
    filc_module_asm(C3, Lines),
    findall(x, member(ins(cmp, l, [imm(0), mem(_, rbp)]), Lines), Tests), length(Tests, 1),
    memberchk(ins(test, b, [imm(6), mem(-2, rcx)]), Lines),
    % A loop with nothing to guard, and a function without loops, are
    % unchanged.
    guard_fn([], [], NoChecks), guard_checks(NoChecks, NoChecks1), NoChecks1 == NoChecks,
    renew_fn([block(s, [], [], ret(const(0)))], NoLoop),
    guard_checks(NoLoop, NoLoop1), NoLoop1 == NoLoop,
    % Refused: the guarded check moved, or a renew_if reading another name.
    C3 = module([func(f, L, Rt, Ps, Bs3)|Rest]),
    select(block(b, Ph, Is, J), Bs3, block(b, Ph, Moved, J), BsMoved),
    Is = [I0, I1, I2|IsRest], Moved = [I1, I0, I2|IsRest],
    \+ guard_refines(C2, module([func(f, L, Rt, Ps, BsMoved)|Rest])),
    G \== k,
    select(block(b, Ph, Is, J), Bs3, block(b, Ph, Other, J), BsOther),
    maplist([I, O]>>( I = let(Q, a, renew_if(A1, A2, A3, A4), [P, _])
                      -> O = let(Q, a, renew_if(A1, A2, A3, A4), [P, tmp(k)]) ; O = I ), Is, Other),
    \+ guard_refines(C2, module([func(f, L, Rt, Ps, BsOther)|Rest])).

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

% Emitting a block's instructions and a data object's items leaves no
% choicepoint: one per instruction kept a 30k-instruction block's frames
% (libaom) past the 1 GB stack, and one per item an 800k-item table's.
test(emission_deterministic) :-
    list_to_assoc([tmp(a)-8, tmp(b)-16, tmp(p)-24, lower(tmp(p))-32,
                   tmp(q)-40, lower(tmp(q))-48], Slots),
    Is = [let(tmp(a), w, add, [tmp(b), const(2)]),
          let(tmp(b), l, ext(sw), [tmp(a)]),
          flight(tmp(q), add, [address(tmp(p)), const(8)], lower(tmp(p)))],
    filc_amd64:function_ctx(f, void, Slots, [block(b, [], Is, ret)], 64, 64,
                            sel(none, reference), Ctx),
    call_cleanup(phrase(filc_amd64:insts(Is, 0, b, Ctx), Lines), Det = true),
    Det == true, Lines = [_|_],
    call_cleanup(foldl(filc_amd64:payload_item,
                       [item(b, const(1)), item(h, const(2)), item(w, const(3))],
                       _, 0-[], Size-[]), Det1 = true),
    Det1 == true, Size == 7.

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

% Item 6a (docs/perf.md): with local selection a check of Size =< 16
% has no borrow test after `sub $Size` (upper >= lower >= 16); larger
% checks keep it, and so does the reference (stack) selection.
test(borrow_test_sizes) :-
    forall(member(Size-Mode-Borrow,
                  [1-temps-no, 8-temps-no, 10-temps-no,
                   17-temps-yes, 2147483647-temps-yes,
                   1-stack-yes, 8-stack-yes, 10-stack-yes]),
        ( M = module([func(f, export, l, [param(p, tmp(p))], [
              block(s, [], [
                  let(tmp(q), a, check(0, Size, read, 1), [tmp(p)]),
                  let(tmp(r), l, raw_load(l, 0), [tmp(q)])
              ], ret(tmp(r)))])]),
          filc_module_asm(M, Mode, Lines, _),
          once(append(_, [ins(sub,q,[imm(Size),reg(rdx)])|After], Lines)),
          After = [Next|_],
          ( Next = ins(jb,none,_) -> Borrow == yes ; Borrow == no ),
          % The remaining tests stay: null, lower and upper.
          memberchk(ins(jz,none,_), Lines),
          memberchk(ins(ja,none,_), Lines) )).

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

%% Atomic compare-exchange (ir.pl, cas(T))

% cas_fn(+Name, +Insts, +R, -Func): a filc function of no arguments
% running Insts over a 16-byte object p (an l at 0, a w at 8) and
% returning tmp(R).
cas_fn(Name, Insts, R, func(Name, export, l, [], [block(s, [], [
        let(tmp(p), p, alloc(8), [const(16)]),
        let(tmp(q), p, add, [tmp(p), const(8)]),
        store(l, const(0x1122334455667788), tmp(p)),
        store(w, const(0xfffffffe), tmp(q))|Insts], ret(tmp(R)))])).

% The old value either way; New written only when old equals Expected,
% on the cas's width: a narrow cas compares Expected's low bytes and
% extends old as load(T) does. Expected values by hand: 0x1122334455667788
% is 1234605616436508552; sw of 0xfffffffe is -2, 2^64 - 2 at l.
test(cas_semantics) :-
    Old = 1234605616436508552,
    Specs = [
        cas_fn(unequal, [let(tmp(r), l, cas(l), [const(5), const(9), tmp(p)])], r),
        cas_fn(unequal_kept, [let(tmp(o), l, cas(l), [const(5), const(9), tmp(p)]),
                              let(tmp(r), l, load(l), [tmp(p)])], r),
        cas_fn(equal, [let(tmp(r), l, cas(l), [const(Old), const(42), tmp(p)])], r),
        cas_fn(equal_written, [let(tmp(o), l, cas(l), [const(Old), const(42), tmp(p)]),
                               let(tmp(r), l, load(l), [tmp(p)])], r),
        % Expected's high bytes are not compared: 0x1fffffffe matches.
        cas_fn(narrow, [let(tmp(r), l, cas(sw), [const(0x1fffffffe), const(7), tmp(q)])], r),
        cas_fn(narrow_written, [let(tmp(o), l, cas(uw), [const(0x1fffffffe), const(7), tmp(q)]),
                                let(tmp(r), l, load(uw), [tmp(q)])], r),
        cas_fn(narrow_unequal, [let(tmp(o), l, cas(ub), [const(0xfd), const(7), tmp(q)]),
                                let(tmp(r), l, load(uw), [tmp(q)])], r),
        % Aligned to its width: a 4-byte cas at p+2 traps though a
        % 4-byte store there would not.
        cas_fn(misaligned, [let(tmp(m), p, add, [tmp(p), const(2)]),
                            let(tmp(r), l, cas(uw), [const(0), const(1), tmp(m)])], r),
        cas_fn(misaligned_store, [let(tmp(m), p, add, [tmp(p), const(2)]),
                                  store(w, const(1), tmp(m)),
                                  let(tmp(r), l, load(l), [tmp(p)])], r)
    ],
    findall(F, ( member(cas_fn(N, I, R), Specs), cas_fn(N, I, R, F) ), Fns),
    ir_module(Fns, M),
    module_fn_args_outcome(M, unequal, [], ret(Old)),
    module_fn_args_outcome(M, unequal_kept, [], ret(Old)),
    module_fn_args_outcome(M, equal, [], ret(Old)),
    module_fn_args_outcome(M, equal_written, [], ret(42)),
    module_fn_args_outcome(M, narrow, [], ret(18446744073709551614)),
    module_fn_args_outcome(M, narrow_written, [], ret(7)),
    module_fn_args_outcome(M, narrow_unequal, [], ret(0xfffffffe)),
    module_fn_args_outcome(M, misaligned, [], trap(_)),
    module_fn_args_outcome(M, misaligned_store, [], ret(_)).

% A pointer cas compares addresses only. Slot holds a's pair; Expected
% x has a's address and no capability, so the cas succeeds and stores
% b's pair, and the result is the slot's old pair, a's, not x's: both
% are dereferenced. A different address fails and leaves the slot.
test(cas_pointer_semantics) :-
    Setup = [let(tmp(a), p, alloc(8), [const(8)]),
             let(tmp(b), p, alloc(8), [const(8)]),
             let(tmp(s), p, alloc(8), [const(8)]),
             store(l, const(3), tmp(a)), store(l, const(5), tmp(b)),
             store(p, tmp(a), tmp(s)),
             let(tmp(i), l, ptoi, [tmp(a)]),
             let(tmp(x), p, itop, [tmp(i)])],
    Fn = [Name, Body, R]>>(append(Setup, Body, Is),
             F = func(Name, export, l, [], [block(s, [], Is, ret(tmp(R)))]),
             nb_setval(cas_fn, F)),
    findall(F, ( member(N-B-R, [
        old-[let(tmp(o), p, cas(p), [tmp(x), tmp(b), tmp(s)]),
             let(tmp(r), l, load(l), [tmp(o)])]-r,
        new-[let(tmp(o), p, cas(p), [tmp(x), tmp(b), tmp(s)]),
             let(tmp(n), p, load(p), [tmp(s)]),
             let(tmp(r), l, load(l), [tmp(n)])]-r,
        kept-[let(tmp(o), p, cas(p), [tmp(b), tmp(x), tmp(s)]),
              let(tmp(n), p, load(p), [tmp(s)]),
              let(tmp(r), l, load(l), [tmp(n)])]-r,
        % The failed cas's result is a's pair too.
        failed-[let(tmp(o), p, cas(p), [tmp(b), tmp(x), tmp(s)]),
                let(tmp(r), l, load(l), [tmp(o)])]-r
      ]), call(Fn, N, B, R), nb_getval(cas_fn, F) ), Fns),
    ir_module(Fns, M),
    module_fn_args_outcome(M, old, [], ret(3)),
    module_fn_args_outcome(M, new, [], ret(5)),
    module_fn_args_outcome(M, kept, [], ret(3)),
    module_fn_args_outcome(M, failed, [], ret(3)).

% Checked cas: right after its own write check at its width's
% alignment, never on a reused proof, and it ends every live proof, so
% a load after it cannot read a proof made before it; the reuse pass
% keeps such a check. A cas left unchecked is rejected.
test(cas_checked) :-
    C = let(tmp(q), a, check(0, 8, write, 1), [tmp(a)]),
    S = raw_store(l, 0, const(1), tmp(q)),
    L = let(tmp(x), l, raw_load(l, 0), [tmp(q)]),
    Cb = let(tmp(r), a, check(0, 8, write, 8), [tmp(b)]),
    X = let(tmp(y), l, raw_cas(l, 0), [tmp(r), const(1), const(2)]),
    reuse_fn([C, S, Cb, raw_store(l, 0, const(3), tmp(r)), L], Plain), valid_module(Plain),
    reuse_fn([Cb, X], Ok), valid_module(Ok),
    reuse_fn([C, S, Cb, X, L], Across), reuse_rejected(Across),
    reuse_fn([C, S, let(tmp(y), l, raw_cas(l, 0), [tmp(q), const(1), const(2)])], Reused),
    reuse_rejected(Reused),
    catch(( reuse_fn([Cb, raw_store(l, 0, const(3), tmp(r)),
                      let(tmp(y), l, cas(l), [const(1), const(2), tmp(a)])], Un),
            valid_module(Un), fail ), nanofil_error(Msg), true),
    sub_atom(Msg, _, _, _, 'cas(l) in checked IR'),
    % The pass keeps the load's check after a cas of another pointer.
    Src = module([func(f, local, w, [param(p, tmp(a)), param(p, tmp(b))], [block(s, [], [
        store(l, const(1), tmp(a)),
        let(tmp(y), l, cas(l), [const(1), const(2), tmp(b)]),
        let(tmp(x), l, load(l), [tmp(a)])], ret(const(0)))])]),
    valid_module(Src), pizlonate_module(Src, Ck), reuse_checks(Ck, Re), Re == Ck,
    Ck = module([func(_, _, _, _, [block(_, _, Is, _)])]),
    aggregate_all(count, member(let(_, a, check(_, _, _, _), _), Is), 3).

% An object a cas reads stays an object through -O: promotion must not
% delete it under the cas (escape.pl), so the cas still sees its stores.
test(cas_object_escapes) :-
    ir_module([func(f, export, l, [], [block(s, [], [
        let(tmp(p), p, alloc(8), [const(8)]),
        store(l, const(4), tmp(p)),
        let(tmp(o), l, cas(l), [const(4), const(6), tmp(p)]),
        let(tmp(n), l, load(l), [tmp(p)]),
        let(tmp(r), l, add, [tmp(o), tmp(n)])], ret(tmp(r)))])], M),
    optimize(o1, M, O), valid_module(O),
    O = module([func(_, _, _, _, [block(_, _, Is, _)])]),
    memberchk(let(_, _, alloc(_), _), Is),
    module_fn_args_outcome(O, f, [], ret(10)).

% Fixed-register asm (docs/asm-fixed.md): the validator takes exactly the
% registers M reads, in order, and an ordered subset of those it writes,
% all `w`; the interpreter steps over the fences and pause and stops at
% the others with their inputs, also inside a callee; -O keeps every
% asm_fixed and the lets its inputs need.
asm_fn(A, Ret, module([func(f, local, w, [param(w, tmp(x))],
                            [block(s, [], [let(tmp(y), w, add, [tmp(x), const(1)]), A], Ret)])])).

test(asm_fixed_validation) :-
    forall(member(A, [asm_fixed(cpuid, [a-tmp(y), c-const(0)], [a-tmp(r), b-tmp(r2), c-tmp(r3), d-tmp(r4)]),
                      asm_fixed(cpuid, [a-tmp(y), c-tmp(y)], [b-tmp(r)]),
                      asm_fixed(cpuid, [a-const(7), c-const(0)], []),
                      asm_fixed(xgetbv, [c-tmp(y)], [a-tmp(r), d-tmp(r2)]),
                      asm_fixed(rdtsc, [], [d-tmp(r)]),
                      asm_fixed(rdtscp, [], [a-tmp(r), c-tmp(r2), d-tmp(r3)]),
                      asm_fixed(lfence, [], []), asm_fixed(sfence, [], []), asm_fixed(pause, [], [])]),
           ( asm_fn(A, ret(tmp(y)), M), valid_module(M), reads_back(M) )),
    forall(member(A, [asm_fixed(mfence, [], []),                         % mfence is fence
                      asm_fixed(rdpid, [], [a-tmp(r)]),                  % not on the list
                      asm_fixed(cpuid, [a-tmp(y)], [a-tmp(r)]),          % missing c input
                      asm_fixed(cpuid, [c-const(0), a-tmp(y)], []),      % misordered
                      asm_fixed(rdtsc, [a-tmp(y)], [a-tmp(r)]),          % extra input
                      asm_fixed(rdtsc, [], [c-tmp(r)]),                  % rdtsc does not write c
                      asm_fixed(rdtsc, [], [d-tmp(r), a-tmp(r2)]),       % misordered outputs
                      asm_fixed(rdtsc, [], [a-tmp(r), a-tmp(r2)]),       % duplicate output
                      asm_fixed(rdtsc, [], [a-tmp(r), d-tmp(r)]),        % one temp twice
                      asm_fixed(pause, [], [a-tmp(r)])]),
           ( asm_fn(A, ret(tmp(y)), M), asm_rejected(M, 'bad fixed-register asm') )),
    % Inputs of class p and l are refused (the frontend truncates an l
    % first); outputs are w.
    forall(member(Cl, [p, l]),
           ( M = module([func(f, local, w, [param(Cl, tmp(x))],
                              [block(s, [], [asm_fixed(xgetbv, [c-tmp(x)], [])], ret(const(0)))])]),
             ( Cl == p -> asm_rejected(M, 'use ptoi') ; asm_rejected(M, 'has class l, not w') ) )),
    U = module([func(f, local, l, [],
                     [block(s, [], [asm_fixed(rdtsc, [], [a-tmp(r)])], ret(tmp(r)))])]),
    asm_rejected(U, 'class w but is used as l').

% asm_rejected(+M, +Why): validating M fails with a message containing Why.
asm_rejected(M, Why) :-
    catch(( valid_module(M), fail ), nanofil_error(Msg), true),
    once(sub_atom(Msg, _, _, _, Why)).

% In plain mode a w input can be a derived address: its object escapes,
% so promotion keeps the alloc and the let that defines the input.
test(asm_fixed_escape) :-
    M0 = module([func(f, local, w, [],
                      [block(s, [], [let(tmp(a), l, alloc(8), [const(8)]),
                                     store(w, const(1), tmp(a)),
                                     let(tmp(x), w, add, [tmp(a), const(4)]),
                                     asm_fixed(cpuid, [a-tmp(x), c-const(0)], [b-tmp(r)])],
                             ret(tmp(r)))])]),
    valid_module(M0),
    optimize(o1(small, full), M0, M), valid_module(M),
    M = module([func(f, _, _, _, Bs)]),
    findall(I, ( member(block(_, _, Is, _), Bs), member(I, Is) ), Is),
    memberchk(let(tmp(x), _, _, _), Is).

test(asm_fixed_interp) :-
    forall(member(Mn, [lfence, sfence, pause]),
           ( asm_fn(asm_fixed(Mn, [], []), ret(tmp(y)), M),
             once(run(M, f, [41], 10, O)), O == ret(42) )),
    asm_fn(asm_fixed(cpuid, [a-tmp(y), c-const(3)], [a-tmp(r)]), ret(tmp(r)), C),
    once(run(C, f, [6], 10, O1)), O1 == unknown(asm(cpuid, [7, 3])),
    % In a callee, the caller stops with the same outcome.
    C = module([F]),
    G = func(g, local, w, [],
             [block(s, [], [call(result(tmp(v), w), global(f), [arg(w, const(1))])], ret(tmp(v)))]),
    once(run(module([F, G]), g, [], 10, O2)), O2 == unknown(asm(cpuid, [2, 3])),
    outcome_text(O2, T), sub_atom(T, 0, _, _, 'unknown asm cpuid').

test(asm_fixed_kept) :-
    % Neither the pause (no outputs) nor the cpuid with an unused output
    % goes, nor the let its input reads, while the dead let z does.
    M0 = module([func(f, local, w, [param(w, tmp(x))],
                      [block(s, [], [let(tmp(y), w, add, [tmp(x), const(1)]),
                                     let(tmp(z), w, add, [tmp(x), const(2)]),
                                     asm_fixed(pause, [], []),
                                     asm_fixed(cpuid, [a-tmp(y), c-const(0)], [b-tmp(r)])],
                             ret(const(0)))])]),
    optimize(o1(small, full), M0, module([func(f, _, _, _, Bs)])),
    findall(I, ( member(block(_, _, Is, _), Bs), member(I, Is) ), Is),
    \+ memberchk(let(tmp(z), _, _, _), Is),
    memberchk(asm_fixed(pause, [], []), Is),
    memberchk(asm_fixed(cpuid, [a-V, c-const(0)], [b-_]), Is),
    ( V = tmp(Y) -> memberchk(let(tmp(Y), w, _, _), Is) ; true ).

test(asm_fixed_lines) :-
    phrase(asm:line_text(asm_fixed(cpuid)), Cs), atom_chars(A, Cs),
    sub_atom(A, B1, _, _, 'movq %rbx, %rsi'), sub_atom(A, B2, _, _, cpuid),
    sub_atom(A, B3, _, _, 'movl %ebx, %edi'), sub_atom(A, B4, _, _, 'movq %rsi, %rbx'),
    B1 < B2, B2 < B3, B3 < B4,
    phrase(asm:line_text(asm_fixed(rdtscp)), Ds), Ds == ['\t', rdtscp, '\n'].

% A vector access is checked at its full width before any of its 8-byte
% chunks (docs/vector-access.md): each access(K, A, 16, Align) comes
% just before the first chunk at A, and every chunk at A or A + const
% comes after an access at A. Align is the access's: 1 through __m128i_u or a packed
% struct's member, the type's capped at 8 otherwise.
test(vector_access_precedes_chunks) :-
    setup_call_cleanup(
        ( setenv('NANOFIL_VECTORS', '1'), setenv('NANOFIL_VECTOR_ACCESS', '1') ),
        ( c_tokens("typedef long long v2 __attribute__((vector_size(16)));
                    typedef long long v2u __attribute__((vector_size(16), aligned(1)));
                    struct P { char c; v2u v; } __attribute__((packed));
                    void f(v2 *d, const v2 *s, const v2u *u, v2u *w, struct P *p) {
                        v2u x = *u; *d = *s; *w = x; p->v = *d; }", 'va.c', Ts),
          c_parse(Ts, C), once(c_module(C, module(Is))) ),
        ( unsetenv('NANOFIL_VECTORS'), unsetenv('NANOFIL_VECTOR_ACCESS') )),
    memberchk(func(f, _, _, _, [block(_, _, Body, _)]), Is),
    findall(K-Al, member(access(K, _, 16, Al), Body), Accesses),
    forall(member(A, [read-1, read-8, write-8, write-1]), memberchk(A, Accesses)),
    forall(nth0(I, Body, access(_, A, _, _)),
           ( I1 is I + 1, nth0(I1, Body, First), chunk_at(First, Body, A) )),
    forall(( member(access(_, A, _, _), Body), nth0(J, Body, In), chunk_at(In, Body, A) ),
           ( nth0(I, Body, access(_, A, _, _)), I < J )), !.

% chunk_at(+Inst, +Body, +A): Inst loads or stores an 8-byte chunk at A
% or at A + const.
chunk_at(let(_, l, load(l), [Addr]), Body, A) :- chunk_addr(Addr, Body, A).
chunk_at(store(l, _, Addr), Body, A) :- chunk_addr(Addr, Body, A).
chunk_addr(A, _, A) :- !.
chunk_addr(tmp(T), Body, A) :- memberchk(let(tmp(T), p, add, [A, const(_)]), Body).
