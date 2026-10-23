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
:- autoload(interp, [run/5, module_prepared/2, run_prepared/5, outcome_text/2]).
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
    (   Argv0 = ['-O'|Argv]
    ->  Opt = o1
    ;   Argv = Argv0,
        Opt = o0
    ),
    % halt/1 outside catch/3: SWI implements halt as an exception.
    catch(( command(Opt, Argv)
          ->  Status = 0
          ;   format(user_error, "nanofil: failed~n", []),
              Status = 1
          ),
          Error,
          ( report(Error),
            Status = 1
          )),
    halt(Status).

% arg_atom(+Arg, -Atom): Atom is the command-line argument Arg, which
% is an atom (SWI) or a character list (Trealla).
arg_atom(Atom, Atom) :-
    atom(Atom),
    !.
arg_atom(Cs, Atom) :-
    atom_chars(Atom, Cs).

% report(+Error): print Error on stderr, a nanofil_error by its message
% and anything else as a quoted term. Error is any ball, so the last
% clause is a default and the cut stays.
report(nanofil_error(Msg)) :-
    !,
    format(user_error, "nanofil: ~w~n", [Msg]).
report(Error) :-
    format(user_error, "nanofil: ~q~n", [Error]).

%% Loading

% file_module(+File, -Module): Module is the valid IR module in File. A
% .c or .i file goes through the C frontend, anything else is QBE text.
file_module(File, Module) :-
    (   (   atom_concat(_, '.c', File)
        ;   atom_concat(_, '.i', File)
        )
    ->  c_file_module(File, Module)
    ;   parse_qbe_file(File, Module),
        valid_module(Module)
    ).

% c_file_module(+File, -Module): Module is the valid IR module of the C
% file.
c_file_module(File, Module) :-
    c_file_tokens(File, Tokens),
    (   c_parse(Tokens, Items) -> true
    ;   throw(nanofil_error('C parse failed'))
    ),
    c_module(Items, Module),
    valid_module(Module).

% c_file_tokens(+File, -Tokens): Tokens are the C tokens of File. A .i
% file is already preprocessed; anything else goes through c_pp with the
% predefined macros and include paths of $FILCC (default filcc).
c_file_tokens(File, Tokens) :-
    (   atom_concat(_, '.i', File)
    ->  phrase_from_file(seq(Cs), File),
        c_tokens(Cs, File, Tokens)
    ;   ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
        pp_profile(Clang, Profile),
        pp_file(File, Profile, Tokens)
    ).

%% Commands

% command(+Opt, +Args): carry out the command line Args (without -O),
% running the middle end when Opt is o1 (-O given) and not when o0.
% Fails or throws when the command does.
command(_, [tokens, File]) :-
    c_file_tokens(File, Tokens),
    forall(member(tok(Token, _), Tokens),
           ( write_canonical(Token), write('.'), nl )).
command(_, [check, File]) :-
    file_module(File, _),
    format("ok~n", []).
command(Opt, [print, File]) :-
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt, [compile, File]) :-
    file_module(File, Module0),
    % Promote can remove every p from a module; the ABI is the original's.
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    mode_module_asm(Mode, Module, Asm),
    print_asm(Asm).
command(Opt, [cc, File]) :-
    c_file_module(File, Module0),
    optimize(Opt, Module0, Module),
    filc_module_asm(Module, Asm),
    print_asm(Asm).
command(Opt, ['cc-ir', File]) :-
    c_file_module(File, Module0),
    optimize(Opt, Module0, Module),
    print_module(Module).
command(Opt, [run, File, Fn|ArgAtoms]) :-
    file_module(File, Module0),
    optimize(Opt, Module0, Module),
    maplist(atom_number, ArgAtoms, Args0),
    func_named(Module, Fn, func(_, _, _, Params, _)),
    maplist(canonical_arg, Params, Args0, Args),
    max_fuel(Fuel),
    once(run(Module, Fn, Args, Fuel, Outcome)),
    outcome_text(Outcome, Text),
    format("~w~n", [Text]).
command(Opt, [difftest, File, Dir]) :-
    file_module(File, Module0),
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    file_runs(File, Runs),
    opt_valid_module(Opt, Module),
    module_prepared(Module0, Prepared0),
    module_prepared(Module, Prepared),
    % One findall over all runs, so each run's heap is reclaimed on
    % backtracking before the next starts.
    findall(Result-Verdict,
            ( member(Run, Runs),
              validated_run(Opt, Module0-Prepared0, Module-Prepared, Run,
                            Result, Verdict)
            ),
            ResultVerdicts),
    pairs_keys_values(ResultVerdicts, Results, Verdicts),
    opt_report_validation(Opt, File, Module0, Module, Verdicts),
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
             format("  ~w = ~w~n", [CallText, Text])
           )).

% mode_module_asm(+Mode, +Module, -Asm): Asm is the asm.pl lines of
% Module by the backend for Mode, filc or plain.
mode_module_asm(plain, Module, Asm) :- module_asm(Module, Asm).
mode_module_asm(filc, Module, Asm) :- filc_module_asm(Module, Asm).

% opt_valid_module(+Opt, +Module): with -O (o1), the optimized Module is
% valid. valid_module's clauses leave choice points that throw on retry.
opt_valid_module(o0, _).
opt_valid_module(o1, Module) :- once(valid_module(Module)).

% opt_report_validation(+Opt, +File, +Module0, +Module, +Verdicts): with
% -O (o1), report_validation/4.
opt_report_validation(o0, _, _, _, _).
opt_report_validation(o1, File, Module0, Module, Verdicts) :-
    report_validation(File, Module0, Module, Verdicts).

% report_validation(+File, +Module0, +Module, +Verdicts): print the -O
% difftest report: promote's effect, then every validation failure,
% which together make the command throw.
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
    module_run_result(Optimized, Run, Fuel, Result).
validated_run(o1, Original, Optimized, Run, Result, Verdict) :-
    fuel_step(Fuel),
    module_run_result(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    (   Outcome0 \== out_of_fuel
    ;   Fuel == MaxFuel
    ),
    % Commit to the first fuel step at which the original finishes, or
    % to the last one.
    !,
    module_run_result(Optimized, Run, Fuel, Result),
    Result = r(_, _, Outcome),
    (   refines(Outcome0, Outcome) -> Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

% fuel_step(-Fuel) is multi: Fuel is one of the growing fuel limits,
% smallest first, ending at max_fuel.
fuel_step(Fuel) :-
    member(Fuel, [1000, 8000, 64000, 512000, 1000000]).

% canonical_arg(+Param, +Arg0, -Arg): Arg is Arg0 reduced modulo the
% class of Param.
canonical_arg(par(Class, _), Arg0, Arg) :-
    modulus(Class, Modulus),
    Arg is Arg0 mod Modulus.

% module_run_result(+Module-Prepared, +Run, +Fuel, -Result): Result is
% the r(Fn, Args, Outcome) of the "# run:" line Run on a module and the
% interpreter's preparation of it, with Fuel. Throws if the line does
% not fit the module or the interpreter finds no outcome.
module_run_result(Module-Prepared, run(Fn, Args0), Fuel,
                  r(Fn, Args, Outcome)) :-
    (   func_named(Module, Fn, func(_, export, _, Params, _)) -> true
    ;   throw(nanofil_error(
                  Fn-'run line names a function that is not exported'))
    ),
    (   length(Params, N), length(Args0, N) -> true
    ;   throw(nanofil_error(
                  Fn-'run line has the wrong number of arguments'))
    ),
    maplist(canonical_arg, Params, Args0, Args),
    (   once(run_prepared(Prepared, Fn, Args, Fuel, Outcome)) -> true
    ;   call_text(Fn, Args, CallText),
        throw(nanofil_error(CallText-'interpreter found no outcome'))
    ).

% comparable(+Mode, +Result) is semidet: a native run in Mode (plain or
% filc) reproduces Result's outcome, a known return value or, for
% filc, a trap, which is a Fil-C safety panic natively. Nothing else has
% a native counterpart.
comparable(_, r(_, _, ret(V))) :-
    integer(V).
comparable(_, r(_, _, ret)).
comparable(filc, r(_, _, trap(_))).

% call_text(+Fn, +Args, -Text): Text is the atom '$Fn(A1, A2, ...)'.
call_text(Fn, Args, Text) :-
    atomic_list_concat(Args, ', ', ArgText),
    format(atom(Text), '$~w(~w)', [Fn, ArgText]).

%% difftest output files

% write_file(+File, :Body_2): write the characters Body_2 (a DCG body)
% describes to File.
write_file(File, Body_2) :-
    phrase(Body_2, Cs),
    open(File, write, Stream),
    format(Stream, "~s", [Cs]),
    close(Stream).

% expected_lines(+Results)//: one "CALL = OUTCOME" line per result, a
% trap's outcome shown as just "trap" (the native run cannot tell why).
expected_lines([]) --> [].
expected_lines([r(Fn, Args, Outcome)|Results]) -->
    { call_text(Fn, Args, CallText),
      (   Outcome = trap(_) -> Text = trap
      ;   outcome_text(Outcome, Text)
      ) },
    fmt("~w = ~w~n", [CallText, Text]),
    expected_lines(Results).

% harness(+Mode, +Module, +Results)//: a C program that calls Module's
% functions as Results do and prints what expected_lines//1 prints.
harness(plain, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n\n",
    { results_fns(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(void) {\n",
    harness_calls(Results, Module, labelled),
    "    return 0;\n}\n".
% Fil-C: one run per process, selected by argv[1], since a trap ends the
% process. The call text is printed first, so a trap leaves it unfinished.
harness(filc, Module, Results) -->
    "#include <stdio.h>\n#include <stdint.h>\n#include <stdlib.h>\n\n",
    { results_fns(Results, Fns) },
    prototypes(Fns, Module),
    "\nint main(int argc, char **argv) {\n    switch (atoi(argv[1])) {\n",
    filc_cases(Results, 0, Module),
    "    }\n    return 0;\n}\n".

% results_fns(+Results, -Fns): Fns is the ordset of the functions
% Results call.
results_fns(Results, Fns) :-
    findall(Fn, member(r(Fn, _, _), Results), Fns0),
    sort(Fns0, Fns).

% filc_cases(+Results, +I, +Module)//: the switch cases I, I+1, ... of
% the Fil-C harness, one per result.
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

% prototypes(+Fns, +Module)//: an extern C declaration of each of Fns.
prototypes([], _) --> [].
prototypes([Fn|Fns], Module) -->
    { func_named(Module, Fn, func(_, _, Ret, Params, _)),
      c_type(Ret, RetType),
      findall(Type, ( member(par(Class, _), Params), c_type(Class, Type) ),
              ParamTypes),
      types_text(ParamTypes, ParamText) },
    fmt("extern ~w ~w(~w);~n", [RetType, Fn, ParamText]),
    prototypes(Fns, Module).

% types_text(+Types, -Text): Text is the C parameter list of Types.
types_text([], void).
types_text([Type|Types], Text) :-
    atomic_list_concat([Type|Types], ', ', Text).

% c_type(?Class, ?Type): Type is the C type of the IR class.
c_type(w, uint32_t).
c_type(l, uint64_t).
c_type(void, void).

% harness_calls(+Results, +Module, +Style)//: Style labelled prints
% "CALL = ret N" lines from one main; bare prints "ret N" inside a case.
harness_calls([], _, _) --> [].
harness_calls([r(Fn, Args, _)|Results], Module, Style) -->
    { func_named(Module, Fn, func(_, _, Ret, _, _)),
      call_text(Fn, Args, CallText),
      findall(CArg, ( member(X, Args), format(atom(CArg), '~wull', [X]) ),
              CArgs),
      atomic_list_concat(CArgs, ', ', CArgText) },
    harness_call(Style, Ret, Fn, CArgText, CallText),
    harness_calls(Results, Module, Style).

% harness_call(+Style, +Ret, +Fn, +CArgText, +CallText)//: the line of
% harness_calls//3 for one call of Fn, which returns Ret.
harness_call(Style, Ret, Fn, CArgText, CallText) -->
    { ret_result(Ret, Result) },
    style_call(Style, Result, Fn, CArgText, CallText).

% ret_result(?Ret, ?Result): a function that returns Ret has a Result of
% none or value.
ret_result(void, none).
ret_result(w, value).
ret_result(l, value).
ret_result(p, value).
ret_result(tuple(_), value).

% style_call(+Style, +Result, +Fn, +CArgText, +CallText)//: as
% harness_call//5, for a call with Result.
style_call(bare, Result, Fn, CArgText, _) -->
    bare_call(Result, Fn, CArgText).
style_call(labelled, Result, Fn, CArgText, CallText) -->
    labelled_call(Result, Fn, CArgText, CallText).

% bare_call(+Result, +Fn, +CArgText)//: a case's line for a call of Fn.
bare_call(none, Fn, CArgText) -->
    fmt("        ~w(~w); puts(\"ret\");~n", [Fn, CArgText]).
bare_call(value, Fn, CArgText) -->
    fmt("        printf(\"ret %llu\\n\", (unsigned long long)~w(~w));~n",
        [Fn, CArgText]).

% labelled_call(+Result, +Fn, +CArgText, +CallText)//: main's line for
% a call of Fn.
labelled_call(none, Fn, CArgText, CallText) -->
    fmt("    ~w(~w); printf(\"%s = ret\\n\", \"~w\");~n",
        [Fn, CArgText, CallText]).
labelled_call(value, Fn, CArgText, CallText) -->
    fmt("    printf(\"%s = ret %llu\\n\", \"~w\", (unsigned long long)~w(~w));~n",
        [CallText, Fn, CArgText]).

%% "# run: $fn a b c" lines

% file_runs(+File, -Runs): Runs is the run(Fn, Args) term of each "#
% run:" line of File, in order.
file_runs(File, Runs) :-
    phrase_from_file(lines(Lines), File),
    foldl(line_runs, Lines, Runs, []).

% lines(-Lines)//: Lines are the character lists of the text's lines,
% without their newlines.
lines([Line|Lines]) -->
    line(Line),
    !,
    lines(Lines).
lines([]) --> [].

% line(-Line)//: one nonempty line up to and including its newline (or
% the end of the text), or an empty line. Line is unified after the
% cut, which keeps line//1 steadfast.
line(Line) -->
    [C],
    { C \== '\n' },
    !,
    rest_of_line(Cs),
    { Line = [C|Cs] }.
line([]) --> "\n".

% rest_of_line(-Cs)//: the characters Cs up to the next newline, which
% is consumed, or to the end of the text.
rest_of_line([]) -->
    "\n",
    !.
rest_of_line([C|Cs]) -->
    [C],
    !,
    rest_of_line(Cs).
rest_of_line([]) --> [].

% line_runs(+Line, ?Runs0, ?Runs): Runs0-Runs is the difference list of
% the run(Fn, Args) term of Line if it is a run line, and empty if not.
line_runs(Line, Runs0, Runs) :-
    (   append("# run: $", Rest, Line)
    ->  chars_words(Rest, [FnCs|ArgCss]),
        atom_chars(Fn, FnCs),
        maplist(chars_number, ArgCss, Args),
        Runs0 = [run(Fn, Args)|Runs]
    ;   Runs0 = Runs
    ).

% chars_number(+Cs, -N): N is the number the characters Cs spell.
chars_number(Cs, N) :-
    number_chars(N, Cs).

% chars_words(+Cs, -Words): Words are the space-separated words of Cs.
chars_words(Cs, Words) :-
    phrase(words(Words), Cs).

% words(-Words)//: the space-separated words Words.
words(Words) -->
    " ",
    !,
    words(Words).
words([[C|Cs]|Words]) -->
    [C],
    word(Cs),
    !,
    words(Words).
words([]) --> [].

% word(-Cs)//: the longest run Cs of characters other than space.
word([C|Cs]) -->
    [C],
    { C \== ' ' },
    !,
    word(Cs).
word([]) --> [].

% library(format)'s format_//2 raises type_error(list, '') for an argument
% of '' (Trealla 12f4cbd), which a call with no arguments produces.
% fmt(+Format, +Args)//: the characters format/3 makes of Format and Args.
fmt(Format, Args) -->
    { format(chars(Cs), Format, Args) },
    seq(Cs).
