/*  nanofil command line (the impure driver).

      check FILE              parse and validate
      print FILE              parse, validate, print QBE text
      compile FILE            parse, validate, print x86-64 assembly
      cc FILE                 compile C (.c or preprocessed .i) to Fil-C assembly
      cc-ir FILE              compile C, print the IR as QBE text
      tokens FILE             print C token terms, without locations
      run FILE FN ARG...      interpret $FN on integer arguments
      difftest FILE OUTDIR    write OUTDIR/{expected.txt,harness.c,printed.ssa}
                              for the file's "# run: $fn arg..." lines

    -O before the command runs the middle end (opt.pl) after loading.
    Without it the IR goes to the backend as loaded, which is the
    reference the optimized path is checked against. With -O, difftest
    also runs every run line on the unoptimized module and fails unless
    each optimized outcome refines the original one (translation
    validation), and prints how many allocs promote removed.

    difftest's expected.txt holds the interpreter's result for every run
    line whose outcome a native run can reproduce (a known return value);
    harness.c prints the same lines from native code. Other outcomes are
    reported on stdout and left out of the comparison.
*/
:- use_module(ir).
:- use_module(qbe_parse).
:- use_module(qbe_print).
:- use_module(interp).
:- use_module(amd64).
:- use_module(filc_amd64).
:- use_module(asm).
:- use_module(c_lex).
:- use_module(c_pp).
:- use_module(c_parse).
:- use_module(c_lower).
:- use_module(opt).
:- use_module(promote).
:- use_module(library(lists)).
:- use_module(library(format)).
:- use_module(library(pio)).
:- use_module(library(dcgs)).
:- use_module(library(pairs)).

:- initialization(main).

main :-
    % Trealla gives argv as character lists, SWI as atoms.
    current_prolog_flag(argv, Argv1),
    maplist(arg_atom, Argv1, Argv0),
    (   Argv0 = ['-O'|Argv] -> Opt = o1 ; Argv = Argv0, Opt = o0 ),
    % halt/1 outside catch/3: SWI implements halt as an exception.
    catch(( command(Opt, Argv) -> S = 0 ; format(user_error, "nanofil: failed~n", []), S = 1 ),
          E,
          ( report(E), S = 1 )),
    halt(S).

arg_atom(A, A) :- atom(A), !.
arg_atom(Cs, A) :- atom_chars(A, Cs).

report(nanofil_error(M)) :- !, format(user_error, "nanofil: ~w~n", [M]).
report(E) :- format(user_error, "nanofil: ~q~n", [E]).

load(File, M) :-
    (   atom_concat(_, '.c', File) ; atom_concat(_, '.i', File) )
    ->  load_c(File, M)
    ;   parse_qbe_file(File, M),
        valid_module(M).

load_c(File, M) :-
    load_c_tokens(File, Ts),
    (   c_parse(Ts, Items) -> true ; throw(nanofil_error('C parse failed')) ),
    c_module(Items, M),
    valid_module(M).

load_c_tokens(File, Ts) :-
    ( atom_concat(_, '.i', File) ->
        phrase_from_file(seq(Cs), File), c_tokens(Cs, File, Ts)
    ; ( getenv('FILCC', Clang) -> true ; Clang=filcc ),
      pp_profile(Clang, Profile), pp_file(File, Profile, Ts)
    ).

command(_, [tokens, File]) :-
    load_c_tokens(File, Ts),
    forall(member(tok(T,_), Ts), (write_canonical(T),write('.'),nl)).
command(_, [check, File]) :- load(File, _), format("ok~n", []).
command(Opt, [print, File]) :- load(File, M0), optimize(Opt, M0, M), print_module(M).
command(Opt, [compile, File]) :-
    load(File, M0),
    % Promote can remove every p from a module; the ABI is the original's.
    module_mode(M0, Mode),
    optimize(Opt, M0, M),
    (   Mode == filc -> filc_module_asm(M, Asm) ; module_asm(M, Asm) ),
    print_asm(Asm).
command(Opt, [cc, File]) :-
    load_c(File, M0),
    optimize(Opt, M0, M),
    filc_module_asm(M, Asm),
    print_asm(Asm).
command(Opt, ['cc-ir', File]) :- load_c(File, M0), optimize(Opt, M0, M), print_module(M).
command(Opt, [run, File, Fn|ArgAtoms]) :-
    load(File, M0),
    optimize(Opt, M0, M),
    maplist(atom_number, ArgAtoms, Args0),
    func_named(M, Fn, func(_, _, _, Params, _)),
    maplist(canonical, Params, Args0, Args),
    once(run(M, Fn, Args, 1000000, Out)),
    outcome_text(Out, T),
    format("~w~n", [T]).
command(Opt, [difftest, File, Dir]) :-
    load(File, M0),
    module_mode(M0, Mode),
    optimize(Opt, M0, M),
    run_lines(File, Runs),
    % One findall over all runs, so each run's heap is reclaimed on
    % backtracking before the next starts.
    % valid_module's clauses leave choice points that throw on retry.
    (   Opt == o1 -> once(valid_module(M)) ; true ),
    findall(R-V, ( member(Run, Runs), validated(Opt, M0, M, Run, R, V) ), RVs),
    pairs_keys_values(RVs, Results, Vs),
    (   Opt == o0 -> true
    ;   alloc_count(M0, N0), alloc_count(M, N1),
        format("~w: promote: ~w allocs -> ~w~n", [File, N0, N1]),
        forall(member(bad(CT, T0, T), Vs),
               format("VALIDATION FAILED ~w ~w: ~w before the middle end, ~w after~n",
                      [File, CT, T0, T])),
        (   memberchk(bad(_, _, _), Vs)
        ->  throw(nanofil_error('translation validation failed'))
        ;   true
        )
    ),
    include(comparable(Mode), Results, Cmp),
    exclude(comparable(Mode), Results, Skipped),
    atom_concat(Dir, '/expected.txt', ExpF),
    atom_concat(Dir, '/harness.c', HarF),
    atom_concat(Dir, '/printed.ssa', PrF),
    atom_concat(Dir, '/mode', ModeF),
    write_file(ExpF, expected_lines(Cmp)),
    write_file(HarF, harness(Mode, M, Cmp)),
    write_file(PrF, module_chars(M)),
    write_file(ModeF, fmt("~w~n", [Mode])),
    length(Cmp, NC), length(Skipped, NS),
    format("~w: ~w runs compared, ~w not comparable~n", [File, NC, NS]),
    forall(member(r(Fn, Args, Out), Skipped),
           ( outcome_text(Out, T), call_text(Fn, Args, CT),
             format("  ~w = ~w~n", [CT, T]) )).

% Translation validation: the unoptimized module's outcome on the same
% run must allow the optimized one's. Both runs happen in the same
% findall step, so an unknown result keeps its constraints. Promote keeps
% every block and branch, so a correct result needs exactly the blocks
% the original needs: both run with the same fuel, starting small and
% growing until the original finishes. A broken pass that loops then
% ends as out_of_fuel, cheaply (the interpreter's memory grows quickly
% with the number of blocks run, so a looping run at full fuel would
% exhaust it).
validated(o0, _, M, Run, R, ok) :- evaluate(M, Run, 1000000, R).
validated(o1, M0, M, Run, R, V) :-
    fuel_step(Fuel),
    evaluate(M0, Run, Fuel, r(Fn, Args, Out0)),
    ( Out0 \== out_of_fuel ; Fuel == 1000000 ), !,
    evaluate(M, Run, Fuel, R),
    R = r(_, _, Out),
    (   refines(Out0, Out) -> V = ok
    ;   call_text(Fn, Args, CT), outcome_text(Out0, T0), outcome_text(Out, T),
        V = bad(CT, T0, T)
    ).

fuel_step(F) :- member(F, [1000, 8000, 64000, 512000, 1000000]).

canonical(par(K, _), A0, A) :- modulus(K, M), A is A0 mod M.

evaluate(M, Run, R) :- evaluate(M, Run, 1000000, R).

evaluate(M, run(Fn, Args0), Fuel, r(Fn, Args, Out)) :-
    (   func_named(M, Fn, func(_, export, _, Params, _)) -> true
    ;   throw(nanofil_error(Fn-'run line names a function that is not exported'))
    ),
    (   length(Params, N), length(Args0, N) -> true
    ;   throw(nanofil_error(Fn-'run line has the wrong number of arguments'))
    ),
    maplist(canonical, Params, Args0, Args),
    (   once(run(M, Fn, Args, Fuel, Out)) -> true
    ;   call_text(Fn, Args, CT),
        throw(nanofil_error(CT-'interpreter found no outcome'))
    ).

% A trap is a Fil-C safety panic natively; nothing else has a native
% counterpart.
comparable(_, r(_, _, ret(V))) :- integer(V).
comparable(_, r(_, _, ret)).
comparable(filc, r(_, _, trap(_))).

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
    { call_text(Fn, Args, CT),
      ( Out = trap(_) -> T = trap ; outcome_text(Out, T) ) },
    fmt("~w = ~w~n", [CT, T]),
    expected_lines(Rs).

harness(plain, M, Rs) -->
    "#include <stdio.h>\n#include <stdint.h>\n\n",
    { findall(Fn, member(r(Fn, _, _), Rs), Fns0), sort(Fns0, Fns) },
    prototypes(Fns, M),
    "\nint main(void) {\n",
    harness_calls(Rs, M),
    "    return 0;\n}\n".
% Fil-C: one run per process, selected by argv[1], since a trap ends the
% process. The call text is printed first, so a trap leaves it unfinished.
harness(filc, M, Rs) -->
    "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n",
    { findall(Fn, member(r(Fn, _, _), Rs), Fns0), sort(Fns0, Fns) },
    prototypes(Fns, M),
    "\nint main(int argc, char **argv) {\n    switch (atoi(argv[1])) {\n",
    filc_cases(Rs, 0, M),
    "    }\n    return 0;\n}\n".

filc_cases([], _, _) --> [].
filc_cases([R|Rs], I, M) -->
    { R = r(Fn, Args, _), call_text(Fn, Args, CT) },
    fmt("    case ~w: fputs(\"~w = \", stdout); fflush(stdout);~n", [I, CT]),
    harness_calls([R], M, bare),
    "        break;\n",
    { I1 is I + 1 },
    filc_cases(Rs, I1, M).

prototypes([], _) --> [].
prototypes([Fn|Fns], M) -->
    { func_named(M, Fn, func(_, _, Ret, Params, _)),
      c_type(Ret, RT),
      findall(T, ( member(par(K, _), Params), c_type(K, T) ), Ts),
      ( Ts == [] -> PA = void ; atomic_list_concat(Ts, ', ', PA) ) },
    fmt("extern ~w ~w(~w);~n", [RT, Fn, PA]),
    prototypes(Fns, M).

c_type(w, uint32_t).
c_type(l, uint64_t).
c_type(void, void).

harness_calls(Rs, M) --> harness_calls(Rs, M, labelled).

harness_calls([], _, _) --> [].
harness_calls([r(Fn, Args, _)|Rs], M, Style) -->
    { func_named(M, Fn, func(_, _, Ret, _, _)),
      call_text(Fn, Args, CT),
      findall(A, ( member(X, Args), format(atom(A), '~wull', [X]) ), CAs),
      atomic_list_concat(CAs, ', ', CA) },
    (   { Style == bare, Ret == void }
    ->  fmt("        ~w(~w); puts(\"ret\");~n", [Fn, CA])
    ;   { Style == bare }
    ->  fmt("        printf(\"ret %llu\\n\", (unsigned long long)~w(~w));~n", [Fn, CA])
    ;   { Ret == void }
    ->  fmt("    ~w(~w); printf(\"%s = ret\\n\", \"~w\");~n", [Fn, CA, CT])
    ;   fmt("    printf(\"%s = ret %llu\\n\", \"~w\", (unsigned long long)~w(~w));~n",
                [CT, Fn, CA])
    ),
    harness_calls(Rs, M, Style).

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

% library(format)'s format_//2 raises type_error(list, '') for an argument
% of '' (Trealla 12f4cbd), which a call with no arguments produces.
fmt(F, As) --> { format(chars(Cs), F, As) }, seq(Cs).
