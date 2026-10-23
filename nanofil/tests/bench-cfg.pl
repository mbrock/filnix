/*  Benchmark: functional analyses (cfg.pl) against tabled relations over
    versioned facts and over incremental facts (cfg_tabled.pl), on the
    largest function of each file. Also checks that all three agree.

    Run from nanofil/src:
      python3 -I ../tests/bigfn.py 1 300 > /tmp/big.c
      ../bin/nanofil --script ../tests/bench-cfg.pl /tmp/big.c... </dev/null

    Scenarios, each timed in CPU seconds:
      facts    asserting the function as facts (tabled styles only)
      dom      dominators and dominance frontiers
      live     temp liveness of the frontend's output
      promote  liveness again after promote rewrote most blocks: the
               functional version recomputes; versioned facts assert the
               new version and drop the old tables; incremental tabling
               retracts and asserts the changed facts and re-queries
      edit     liveness after deleting one instruction in one block
*/
:- use_module('../src/ir').
:- use_module('../src/qbe_parse').
:- use_module('../src/c_lex').
:- use_module('../src/c_parse').
:- use_module('../src/c_lower').
:- use_module('../src/cfg').
:- use_module('../src/cfg_tabled').
:- use_module('../src/promote').
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(library(ordsets)).
:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).

:- initialization(main).

main :-
    current_prolog_flag(argv, Argv),
    maplist(arg_atom, Argv, Files),
    format("~w~t~12|~w~t~20|~w~t~28|~w~t~42|~w~t~54|~w~t~66|~w~n",
           [file, blocks, temps, scenario, functional, versioned, incremental]),
    catch(maplist(bench_file, Files), E,
          ( format("bench-cfg: ~q~n", [E]), halt(1) )),
    halt.

% Trealla gives argv as character lists, SWI as atoms.
arg_atom(A, A) :- atom(A), !.
arg_atom(Cs, A) :- atom_chars(A, Cs).

load(File, M) :-
    (   atom_concat(_, '.c', File)
    ->  phrase_from_file(seq(Cs), File), c_tokens(Cs, File, Ts),
        c_parse(Ts, Items), c_module(Items, M)
    ;   parse_qbe_file(File, M)
    ),
    valid_module(M).

bench_file(File) :-
    load(File, module(Items)),
    findall(N-F, ( member(F, Items), F = func(_, _, _, _, Bs), length(Bs, N) ), NFs),
    msort(NFs, Sorted), last(Sorted, NB-F),
    F = func(_, _, _, _, Blocks),
    module_mode(module(Items), Mode),
    promote_func(Mode, F, func(_, _, _, _, Blocks2)),
    edit(Blocks, Blocks3),
    def_temps(Blocks, NT),
    file_base_name(File, Base),
    Row = row(Base, NB, NT),
    % dominators and frontiers
    time(( fn_cfg(Blocks, Cfg), dominators(Cfg, Idom), frontiers(Cfg, Idom, DF) ), TF1),
    time(assert_version(1, Blocks), TV0),
    time(inc_load(Blocks), TI0),
    report(Row, facts, '-', TV0, TI0),
    % The tabled dominators take a reachability table per block, so they
    % grow with the cube of the size; past 400 blocks they take minutes.
    (   NB =< 400
    ->  time(( v_idoms(1, IPs), findall(X-Y, v_frontier(1, X, Y), DFPs) ), TV1),
        agree_dom(Idom, DF, IPs, DFPs)
    ;   TV1 = skipped
    ),
    report(Row, dom, TF1, TV1, '-'),
    % liveness
    time(temp_liveness(Blocks, In1, _), TF2),
    time(findall(B-T, v_live_in(1, B, T), VIn1), TV2),
    time(findall(B-T, i_live_in(B, T), IIn1), TI2),
    agree_live(In1, VIn1), agree_live(In1, IIn1),
    report(Row, live, TF2, TV2, TI2),
    % after promote
    time(temp_liveness(Blocks2, In2, _), TF3),
    time(( assert_version(2, Blocks2), retract_version(1), findall(B-T, v_live_in(2, B, T), VIn2) ), TV3),
    time(( inc_update(Blocks2), findall(B-T, i_live_in(B, T), IIn2) ), TI3),
    agree_live(In2, VIn2), agree_live(In2, IIn2),
    report(Row, promote, TF3, TV3, TI3),
    % one small edit, from the promoted version
    time(temp_liveness(Blocks3, In3, _), TF4),
    time(( assert_version(3, Blocks3), retract_version(2), findall(B-T, v_live_in(3, B, T), VIn3) ), TV4),
    inc_clear, inc_load(Blocks2), findall(x, i_live_in(_, _), _),
    time(( inc_update(Blocks3), findall(B-T, i_live_in(B, T), IIn3) ), TI4),
    agree_live(In3, VIn3), agree_live(In3, IIn3),
    report(Row, edit, TF4, TV4, TI4),
    retract_version(3), inc_clear,
    sum_live(In1, S1), sum_live(In2, S2),
    format("  live-in pairs: ~w before promote, ~w after~n", [S1, S2]).

time(G, T) :-
    statistics(cputime, T0),
    call(G), !,
    statistics(cputime, T1),
    T is T1 - T0.

report(row(F, NB, NT), S, A, B, C) :-
    fmt_t(A, TA), fmt_t(B, TB), fmt_t(C, TC),
    format("~w~t~12|~w~t~20|~w~t~28|~w~t~42|~w~t~54|~w~t~66|~w~n", [F, NB, NT, S, TA, TB, TC]).

fmt_t(T, A) :- number(T), !, format(atom(A), "~3f s", [T]).
fmt_t(T, T).

def_temps(Blocks, N) :-
    findall(T, ( member(blk(_, Ps, Is, _), Blocks),
                 ( member(phi(t(T), _, _), Ps) ; member(I, Is), inst_def(I, T) ) ), Ts),
    sort(Ts, S), length(S, N).

% Delete the first instruction of a block near the middle (liveness only
% needs the facts to change, not the IR to stay valid).
edit(Blocks0, Blocks) :-
    length(Blocks0, N), Mid is N // 2,
    findall(I, ( between(Mid, N, I), nth1(I, Blocks0, blk(_, _, Is, _)), Is = [_|_] ), [K|_]),
    nth1(K, Blocks0, blk(L, Ps, [_|Is], J)),
    nth1(K, Blocks0, _, Rest),
    nth1(K, Blocks, blk(L, Ps, Is, J), Rest).

agree_dom(Idom, DF, IPs, DFPs) :-
    assoc_to_list(Idom, I1), msort(IPs, I2),
    (   I1 == I2 -> true ; throw(disagree(idom)) ),
    findall(X-Y, ( gen_assoc(X, DF, Ys), member(Y, Ys) ), D1),
    sort(D1, S1), sort(DFPs, S2),
    (   S1 == S2 -> true ; throw(disagree(frontier)) ).

agree_live(In, Pairs) :-
    findall(B-T, ( gen_assoc(B, In, Ts), member(T, Ts) ), P1),
    sort(P1, S1), sort(Pairs, S2),
    (   S1 == S2 -> true
    ;   ord_subtract(S1, S2, Missing), ord_subtract(S2, S1, Extra),
        length(S1, N1), length(S2, N2),
        throw(disagree(liveness, N1, N2, Missing, Extra))
    ).

sum_live(In, S) :- findall(N, ( gen_assoc(_, In, Ts), length(Ts, N) ), Ns), sum_list(Ns, S).

file_base_name(F, B) :-
    atom_chars(F, Cs),
    (   append(_, ['/'|Rest], Cs), \+ memberchk('/', Rest) -> atom_chars(B, Rest) ; B = F ).
