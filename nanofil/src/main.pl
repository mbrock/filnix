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
% Compile-only commands do not need the interpreter or its CLP(Z) solver.
:- if(current_prolog_flag(dialect, swi)).
:- autoload(interp, [run/5, prepare/2, run_prepared/5, outcome_text/2]).
:- else.
:- use_module(interp).
:- endif.
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
    current_prolog_flag(argv, RawArgv),
    maplist(arg_atom, RawArgv, Argv0),
    (   Argv0 = ['-O'|Argv] -> Opt = o1 ; Argv = Argv0, Opt = o0 ),
    % halt/1 outside catch/3: SWI implements halt as an exception.
    catch(( command(Opt, Argv)
          ->  Status = 0
          ;   format(user_error, "nanofil: failed~n", []),
              Status = 1
          ),
          Error,
          ( report(Error), Status = 1 )),
    halt(Status).

arg_atom(A, A) :- atom(A), !.
arg_atom(Cs, A) :- atom_chars(A, Cs).

report(nanofil_error(Msg)) :- !, format(user_error, "nanofil: ~w~n", [Msg]).
report(Error) :- format(user_error, "nanofil: ~q~n", [Error]).

%% Loading

% A .c or .i file goes through the C frontend, anything else is QBE text.
load_module(File, Module) :-
    (   atom_concat(_, '.c', File) ; atom_concat(_, '.i', File) )
    ->  load_c(File, Module)
    ;   parse_qbe_file(File, Module),
        valid_module(Module).

load_c(File, Module) :-
    load_c_tokens(File, Tokens),
    (   c_parse(Tokens, Items) -> true
    ;   throw(nanofil_error('C parse failed'))
    ),
    c_module(Items, Module),
    valid_module(Module).

% A .i file is already preprocessed; anything else goes through c_pp with
% the predefined macros and include paths of $FILCC (default filcc).
load_c_tokens(File, Tokens) :-
    (   atom_concat(_, '.i', File)
    ->  phrase_from_file(seq(Cs), File),
        c_tokens(Cs, File, Tokens)
    ;   ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
        pp_profile(Clang, Profile),
        pp_file(File, Profile, Tokens)
    ).

%% Commands

command(_, [tokens, File]) :-
    load_c_tokens(File, Tokens),
    forall(member(tok(Token, _), Tokens),
           ( write_canonical(Token), write('.'), nl )).
command(_, [check, File]) :-
    load_module(File, _),
    format("ok~n", []).
command(Opt, [print, File]) :-
    load_module(File, Module0),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt, [compile, File]) :-
    load_module(File, Module0),
    % Promote can remove every p from a module; the ABI is the original's.
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    (   Mode == filc -> filc_module_asm(Module, Asm)
    ;   module_asm(Module, Asm)
    ),
    print_asm(Asm).
command(Opt, [cc, File]) :-
    load_c(File, Module0),
    optimize(Opt, Module0, Module),
    filc_module_asm(Module, Asm),
    print_asm(Asm).
command(Opt, ['cc-ir', File]) :-
    load_c(File, Module0),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt, [run, File, Fn|ArgAtoms]) :-
    load_module(File, Module0),
    optimize(Opt, Module0, Module),
    maplist(atom_number, ArgAtoms, Args0),
    func_named(Module, Fn, func(_, _, _, Params, _)),
    maplist(canonical_arg, Params, Args0, Args),
    max_fuel(Fuel),
    once(run(Module, Fn, Args, Fuel, Outcome)),
    outcome_text(Outcome, Text),
    format("~w~n", [Text]).
command(Opt, [difftest, File, Dir]) :-
    load_module(File, Module0),
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    run_lines(File, Runs),
    % valid_module's clauses leave choice points that throw on retry.
    (   Opt == o1 -> once(valid_module(Module)) ; true ),
    prepare(Module0, Prepared0),
    prepare(Module, Prepared),
    % One findall over all runs, so each run's heap is reclaimed on
    % backtracking before the next starts.
    findall(Result-Verdict,
            ( member(Run, Runs),
              validated_run(Opt, Module0-Prepared0, Module-Prepared, Run,
                            Result, Verdict)
            ),
            ResultVerdicts),
    pairs_keys_values(ResultVerdicts, Results, Verdicts),
    (   Opt == o0 -> true
    ;   report_validation(File, Module0, Module, Verdicts)
    ),
    include(comparable(Mode), Results, Compared),
    exclude(comparable(Mode), Results, Skipped),
    atom_concat(Dir, '/expected.txt', ExpectedFile),
    atom_concat(Dir, '/harness.c', HarnessFile),
    atom_concat(Dir, '/printed.ssa', PrintedFile),
    atom_concat(Dir, '/mode', ModeFile),
    write_file(ExpectedFile, expected_lines(Compared)),
    write_file(HarnessFile, harness(Mode, Module, Compared)),
    write_file(PrintedFile, module_chars(Module)),
    write_file(ModeFile, fmt("~w~n", [Mode])),
    length(Compared, NCompared),
    length(Skipped, NSkipped),
    format("~w: ~w runs compared, ~w not comparable~n",
           [File, NCompared, NSkipped]),
    forall(member(r(Fn, Args, Outcome), Skipped),
           ( outcome_text(Outcome, Text),
             call_text(Fn, Args, CallText),
             format("  ~w = ~w~n", [CallText, Text]) )).

% The -O difftest report: promote's effect, then every validation
% failure, which together make the command fail.
report_validation(File, Module0, Module, Verdicts) :-
    alloc_count(Module0, Allocs0),
    alloc_count(Module, Allocs),
    format("~w: promote: ~w allocs -> ~w~n", [File, Allocs0, Allocs]),
    forall(member(bad(CallText, Text0, Text), Verdicts),
           format("VALIDATION FAILED ~w ~w: ~w before the middle end, ~w after~n",
                  [File, CallText, Text0, Text])),
    (   memberchk(bad(_, _, _), Verdicts)
    ->  throw(nanofil_error('translation validation failed'))
    ;   true
    ).

%% Running and validating

% Fuel (blocks run) for a command-line run and the last validation step.
max_fuel(1000000).

/* validated_run(+Opt, +Original, +Optimized, +Run, -Result, -Verdict):
   Result is Run's r/3 on the module that difftest compares, and Verdict
   ok or bad(CallText, OriginalText, OptimizedText).

   Translation validation: the unoptimized module's outcome on the same
   run must allow the optimized one's. Both runs happen in the same
   findall step, so an unknown result keeps its constraints. Promote keeps
   every block and branch, so a correct result needs exactly the blocks
   the original needs: both run with the same fuel, starting small and
   growing until the original finishes. A broken pass that loops then
   ends as out_of_fuel, cheaply (the interpreter's memory grows quickly
   with the number of blocks run, so a looping run at full fuel would
   exhaust it). */
validated_run(o0, _, Optimized, Run, Result, ok) :-
    max_fuel(Fuel),
    evaluate_run(Optimized, Run, Fuel, Result).
validated_run(o1, Original, Optimized, Run, Result, Verdict) :-
    fuel_step(Fuel),
    evaluate_run(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    ( Outcome0 \== out_of_fuel ; Fuel == MaxFuel ), !,
    evaluate_run(Optimized, Run, Fuel, Result),
    Result = r(_, _, Outcome),
    (   refines(Outcome0, Outcome) -> Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

% Growing fuel limits, ending at max_fuel.
fuel_step(Fuel) :- member(Fuel, [1000, 8000, 64000, 512000, 1000000]).

% An argument reduced modulo its parameter's class.
canonical_arg(par(Class, _), Arg0, Arg) :-
    modulus(Class, Modulus),
    Arg is Arg0 mod Modulus.

% evaluate_run(+Module-Prepared, +Run, +Fuel, -Result): run a "# run:"
% line on a module and the interpreter's preparation of it.
evaluate_run(Module-Prepared, run(Fn, Args0), Fuel, r(Fn, Args, Outcome)) :-
    (   func_named(Module, Fn, func(_, export, _, Params, _)) -> true
    ;   throw(nanofil_error(Fn-'run line names a function that is not exported'))
    ),
    (   length(Params, N), length(Args0, N) -> true
    ;   throw(nanofil_error(Fn-'run line has the wrong number of arguments'))
    ),
    maplist(canonical_arg, Params, Args0, Args),
    (   once(run_prepared(Prepared, Fn, Args, Fuel, Outcome)) -> true
    ;   call_text(Fn, Args, CallText),
        throw(nanofil_error(CallText-'interpreter found no outcome'))
    ).

% A trap is a Fil-C safety panic natively; nothing else has a native
% counterpart.
comparable(_, r(_, _, ret(V))) :- integer(V).
comparable(_, r(_, _, ret)).
comparable(filc, r(_, _, trap(_))).

call_text(Fn, Args, Text) :-
    atomic_list_concat(Args, ', ', ArgText),
    format(atom(Text), '$~w(~w)', [Fn, ArgText]).

%% difftest output files

write_file(File, Body) :-
    phrase(Body, Cs),
    open(File, write, Stream),
    format(Stream, "~s", [Cs]),
    close(Stream).

expected_lines([]) --> [].
expected_lines([r(Fn, Args, Outcome)|Results]) -->
    { call_text(Fn, Args, CallText),
      (   Outcome = trap(_) -> Text = trap
      ;   outcome_text(Outcome, Text)
      ) },
    fmt("~w = ~w~n", [CallText, Text]),
    expected_lines(Results).

harness(plain, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n\n",
    { harness_functions(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(void) {\n",
    harness_calls(Results, Module, labelled),
    "    return 0;\n}\n".
% Fil-C: one run per process, selected by argv[1], since a trap ends the
% process. The call text is printed first, so a trap leaves it unfinished.
harness(filc, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n",
    { harness_functions(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(int argc, char **argv) {\n    switch (atoi(argv[1])) {\n",
    filc_cases(Results, 0, Module),
    "    }\n    return 0;\n}\n".

% The functions the results call, each once.
harness_functions(Results, Fns) :-
    findall(Fn, member(r(Fn, _, _), Results), Fns0),
    sort(Fns0, Fns).

filc_cases([], _, _) --> [].
filc_cases([Result|Results], I, Module) -->
    { Result = r(Fn, Args, _),
      call_text(Fn, Args, CallText) },
    fmt("    case ~w: fputs(\"~w = \", stdout); fflush(stdout);~n",
        [I, CallText]),
    harness_calls([Result], Module, bare),
    "        break;\n",
    { I1 is I + 1 },
    filc_cases(Results, I1, Module).

prototypes([], _) --> [].
prototypes([Fn|Fns], Module) -->
    { func_named(Module, Fn, func(_, _, Ret, Params, _)),
      c_type(Ret, RetType),
      findall(Type, ( member(par(Class, _), Params), c_type(Class, Type) ),
              ParamTypes),
      (   ParamTypes == [] -> ParamText = void
      ;   atomic_list_concat(ParamTypes, ', ', ParamText)
      ) },
    fmt("extern ~w ~w(~w);~n", [RetType, Fn, ParamText]),
    prototypes(Fns, Module).

c_type(w, uint32_t).
c_type(l, uint64_t).
c_type(void, void).

% harness_calls(+Results, +Module, +Style): Style labelled prints
% "CALL = ret N" lines from one main; bare prints "ret N" inside a case.
harness_calls([], _, _) --> [].
harness_calls([r(Fn, Args, _)|Results], Module, Style) -->
    { func_named(Module, Fn, func(_, _, Ret, _, _)),
      call_text(Fn, Args, CallText),
      findall(CArg, ( member(X, Args), format(atom(CArg), '~wull', [X]) ),
              CArgs),
      atomic_list_concat(CArgs, ', ', CArgText) },
    (   { Style == bare, Ret == void }
    ->  fmt("        ~w(~w); puts(\"ret\");~n", [Fn, CArgText])
    ;   { Style == bare }
    ->  fmt("        printf(\"ret %llu\\n\", (unsigned long long)~w(~w));~n",
            [Fn, CArgText])
    ;   { Ret == void }
    ->  fmt("    ~w(~w); printf(\"%s = ret\\n\", \"~w\");~n",
            [Fn, CArgText, CallText])
    ;   fmt("    printf(\"%s = ret %llu\\n\", \"~w\", (unsigned long long)~w(~w));~n",
            [CallText, Fn, CArgText])
    ),
    harness_calls(Results, Module, Style).

%% "# run: $fn a b c" lines

run_lines(File, Runs) :-
    phrase_from_file(lines(Lines), File),
    foldl(run_line, Lines, Runs, []).

lines([L|Ls]) --> line(L), !, lines(Ls).
lines([]) --> [].

line(L) --> [C], { C \== '\n' }, !, rest_of_line(Cs), { L = [C|Cs] }.
line([]) --> "\n".

rest_of_line([]) --> "\n", !.
rest_of_line([C|Cs]) --> [C], !, rest_of_line(Cs).
rest_of_line([]) --> [].

run_line(Line, Runs0, Runs) :-
    (   append("# run: $", Rest, Line)
    ->  words(Rest, [FnCs|ArgCss]),
        atom_chars(Fn, FnCs),
        maplist(chars_number, ArgCss, Args),
        Runs0 = [run(Fn, Args)|Runs]
    ;   Runs0 = Runs
    ).

chars_number(Cs, N) :- number_chars(N, Cs).

% The space-separated words of Cs.
words(Cs, Words) :- phrase(word_list(Words), Cs).

word_list(Ws) --> " ", !, word_list(Ws).
word_list([[C|Cs]|Ws]) --> [C], word(Cs), !, word_list(Ws).
word_list([]) --> [].

word([C|Cs]) --> [C], { C \== ' ' }, !, word(Cs).
word([]) --> [].

% library(format)'s format_//2 raises type_error(list, '') for an argument
% of '' (Trealla 12f4cbd), which a call with no arguments produces.
fmt(Format, Args) --> { format(chars(Cs), Format, Args) }, seq(Cs).
