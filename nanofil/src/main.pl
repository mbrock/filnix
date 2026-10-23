/*  nanofil command line (the impure driver).

      check FILE              parse and validate
      print FILE              parse, validate, print QBE text
      run FILE FN ARG...      interpret $FN on integer arguments
      difftest FILE OUTDIR    write OUTDIR/{expected.txt,harness.c,printed.ssa}
                              for the file's "# run: $fn arg..." lines

    difftest's expected.txt holds the interpreter's result for every run
    line whose outcome a native run can reproduce (a known return value);
    harness.c prints the same lines from native code. Other outcomes are
    reported on stdout and left out of the comparison.
*/
:- use_module(ir).
:- use_module(qbe_parse).
:- use_module(qbe_print).
:- use_module(interp).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).

:- initialization(main).

main :-
    current_prolog_flag(argv, ArgvChars),
    maplist(atom_chars, Argv, ArgvChars),
    catch(( command(Argv) -> halt(0) ; format(user_error, "nanofil: failed~n", []), halt(1) ),
          E,
          ( report(E), halt(1) )).

report(nanofil_error(M)) :- !, format(user_error, "nanofil: ~w~n", [M]).
report(E) :- format(user_error, "nanofil: ~q~n", [E]).

load(File, M) :-
    parse_qbe_file(File, M),
    valid_module(M).

command([check, File]) :- load(File, _), format("ok~n", []).
command([print, File]) :- load(File, M), print_module(M).
command([run, File, Fn|ArgAtoms]) :-
    load(File, M),
    maplist(atom_number, ArgAtoms, Args0),
    func_named(M, Fn, func(_, _, _, Params, _)),
    maplist(canonical, Params, Args0, Args),
    once(run(M, Fn, Args, 1000000, Out)),
    outcome_text(Out, T),
    format("~w~n", [T]).
command([difftest, File, Dir]) :-
    load(File, M),
    run_lines(File, Runs),
    maplist(evaluate(M), Runs, Results),
    include(comparable, Results, Cmp),
    exclude(comparable, Results, Skipped),
    atom_concat(Dir, '/expected.txt', ExpF),
    atom_concat(Dir, '/harness.c', HarF),
    atom_concat(Dir, '/printed.ssa', PrF),
    write_file(ExpF, expected_lines(Cmp)),
    write_file(HarF, harness(M, Cmp)),
    write_file(PrF, module_chars(M)),
    length(Cmp, NC), length(Skipped, NS),
    format("~w: ~w runs compared, ~w not comparable~n", [File, NC, NS]),
    forall(member(r(Fn, Args, Out), Skipped),
           ( outcome_text(Out, T), call_text(Fn, Args, CT),
             format("  ~w = ~w~n", [CT, T]) )).

canonical(par(K, _), A0, A) :- modulus(K, M), A is A0 mod M.

evaluate(M, run(Fn, Args0), r(Fn, Args, Out)) :-
    (   func_named(M, Fn, func(_, export, _, Params, _)) -> true
    ;   throw(nanofil_error(Fn-'run line names a function that is not exported'))
    ),
    (   length(Params, N), length(Args0, N) -> true
    ;   throw(nanofil_error(Fn-'run line has the wrong number of arguments'))
    ),
    maplist(canonical, Params, Args0, Args),
    (   once(run(M, Fn, Args, 1000000, Out)) -> true
    ;   call_text(Fn, Args, CT),
        throw(nanofil_error(CT-'interpreter found no outcome'))
    ).

comparable(r(_, _, ret(V))) :- integer(V).
comparable(r(_, _, ret)).

call_text(Fn, Args, T) :-
    atomic_list_concat(Args, ', ', A),
    format(atom(T), '$~w(~w)', [Fn, A]).

write_file(F, G) :-
    phrase(G, Cs),
    open(F, write, S),
    format(S, "~s", [Cs]),
    close(S).

expected_lines([]) --> [].
expected_lines([r(Fn, Args, Out)|Rs]) -->
    { call_text(Fn, Args, CT), outcome_text(Out, T) },
    format_("~w = ~w~n", [CT, T]),
    expected_lines(Rs).

harness(M, Rs) -->
    "#include <stdio.h>\n#include <stdint.h>\n\n",
    { findall(Fn, member(r(Fn, _, _), Rs), Fns0), sort(Fns0, Fns) },
    prototypes(Fns, M),
    "\nint main(void) {\n",
    harness_calls(Rs, M),
    "    return 0;\n}\n".

prototypes([], _) --> [].
prototypes([Fn|Fns], M) -->
    { func_named(M, Fn, func(_, _, Ret, Params, _)),
      c_type(Ret, RT),
      findall(T, ( member(par(K, _), Params), c_type(K, T) ), Ts),
      ( Ts == [] -> PA = void ; atomic_list_concat(Ts, ', ', PA) ) },
    format_("extern ~w ~w(~w);~n", [RT, Fn, PA]),
    prototypes(Fns, M).

c_type(w, uint32_t).
c_type(l, uint64_t).
c_type(void, void).

harness_calls([], _) --> [].
harness_calls([r(Fn, Args, _)|Rs], M) -->
    { func_named(M, Fn, func(_, _, Ret, _, _)),
      call_text(Fn, Args, CT),
      findall(A, ( member(X, Args), format(atom(A), '~wull', [X]) ), CAs),
      atomic_list_concat(CAs, ', ', CA) },
    (   { Ret == void }
    ->  format_("    ~w(~w); printf(\"%s = ret\\n\", \"~w\");~n", [Fn, CA, CT])
    ;   format_("    printf(\"%s = ret %llu\\n\", \"~w\", (unsigned long long)~w(~w));~n",
                [CT, Fn, CA])
    ),
    harness_calls(Rs, M).

%% "# run: $fn a b c" lines

run_lines(File, Runs) :-
    phrase_from_file(lines(Ls), File),
    foldl(run_line, Ls, Runs, []).

lines([L|Ls]) --> line(L), !, lines(Ls).
lines([]) --> [].
line(L) --> [C], { C \== '\n' }, !, rest_line(Cs), { L = [C|Cs] }.
line([]) --> "\n".
rest_line([]) --> "\n", !.
rest_line([C|Cs]) --> [C], !, rest_line(Cs).
rest_line([]) --> [].

run_line(L, Runs0, Runs) :-
    (   append("# run: $", Rest, L)
    ->  words(Rest, [FnCs|ArgCss]),
        atom_chars(Fn, FnCs),
        maplist(chars_number, ArgCss, Args),
        Runs0 = [run(Fn, Args)|Runs]
    ;   Runs0 = Runs
    ).

chars_number(Cs, N) :- number_chars(N, Cs).

words(Cs, Ws) :- phrase(words_(Ws), Cs).
words_(Ws) --> " ", !, words_(Ws).
words_([[C|Cs]|Ws]) --> [C], word(Cs), !, words_(Ws).
words_([]) --> [].
word([C|Cs]) --> [C], { C \== ' ' }, !, word(Cs).
word([]) --> [].
