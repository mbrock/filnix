/*  The nanofil command line: the impure driver that reads a C or IR
    file, runs it through the compiler's stages and prints the result.

    ## Commands

    | Command | Does |
    |---|---|
    | `check FILE` | read and validate; prints `ok` |
    | `print FILE` | read, validate, print the IR (ir_text.pl) |
    | `compile FILE` | read, validate, print x86-64 assembly |
    | `cc FILE` | compile C (`.c`, or preprocessed `.i`) to Fil-C assembly |
    | `cc-ir FILE` | compile C, print the IR (unchecked; the Fil-C backend's input is pizlonated) |
    | `tokens FILE` | print C token terms, without locations |
    | `run FILE FN ARG...` | interpret FN on integer arguments |
    | `difftest FILE OUTDIR` | write `OUTDIR/expected.txt`, `OUTDIR/harness.c` and `OUTDIR/mode` for the file's `run(Fn, Args)` facts |

    A FILE ending in `.c` or `.i` goes through the C frontend; any other
    FILE is IR text. A `.c` file is preprocessed with the predefined
    macros and include paths of `$FILCC` (default `filcc`).

    ```diagram
    ┌──────┐  ┌─────────┐  ┌─────────┐
    │ c_pp │─▶│ c_parse │─▶│ c_lower │──┐
    └──────┘  └─────────┘  └─────────┘  │
      ┌─────────────────────────────────┘
      ▼
    ┌──────────┐  ┌───────────┐  ┌────────────┐
    │ opt (-O) │─▶│ pizlonate │─▶│ filc_amd64 │
    └──────────┘  └───────────┘  └────────────┘
    ```

    `cc` runs the whole pipeline; c_pp lexes with c_lex. IR text enters
    at the middle end, and a module in plain mode goes to amd64.pl
    instead of pizlonate and filc_amd64.

    ## -O

    `-O` before the command runs the middle end (opt.pl) after loading.
    Without it the IR goes to the backend as loaded, which is the
    reference the optimized path is checked against. With `-O`,
    difftest also runs every run line on the unoptimized module and
    fails unless each optimized outcome refines the original one
    (translation validation), and prints how many allocs promote
    removed.

    `--registers=stack|local|function|operands|cells` independently selects
    reference emission, validated block-local scalar caching, validated
    whole-function register homes for scalars (docs/perf.md item 3), or
    those homes with validated register operands (item 3, step 3b), or
    those with frame-word loads forwarded too (item 5a-loads) in the
    Fil-C backend. The default is cells with `-O` and stack without
    it; NANOFIL_REGISTERS supplies the same choice to build harnesses, and
    `-O --registers=stack` keeps the reference emission.
    The plain backend is unchanged. Options precede the command.

    `--branches=reference|selected` independently selects the reference
    branch on a stored boolean, or a branch on the flags of a compare
    that only the branch reads, with jumps to the next block left to
    fall through (docs/perf.md). The default is selected with `-O` and
    reference without it; NANOFIL_BRANCHES supplies the same choice, and
    `-O --branches=reference` keeps the reference branches.

    `--memcpy=call|inline` independently selects the reference call for
    every memcpy and memmove, or, for a constant 1 to 16 bytes to a
    function the module does not define, an inline copy in front of
    that call, taken only when the runtime's checks would pass and
    neither object has aux (docs/perf.md item 7a). The default is
    inline with `-O` and call without it; NANOFIL_MEMCPY supplies the
    same choice, and nanofil-cc passes call for -fno-builtin,
    -fno-builtin-memcpy, -fno-builtin-memmove and -ffreestanding.

    `--inline=none|small` independently selects no inlining, or, with
    `-O`, inlining of small static functions before promotion
    (src/inline.pl, docs/perf.md item 4). The default is none;
    NANOFIL_INLINE supplies the same choice. Under small a trap inside an
    inlined function reports its caller's name, as filcc -O2 does
    without -g.

    `--checks=reference|reuse` independently selects the reference checked
    IR, a check before every access, or check reuse after pizlonation
    (src/check_reuse.pl, docs/m7.md). The default is reference;
    NANOFIL_CHECKS supplies the same choice. With reuse, `cc`, `compile`
    and difftest's pizlonation comparison use the reused module.

    ## difftest

    expected.txt holds the interpreter's result for every run line whose
    outcome a native run can reproduce: a known return value, or for a
    Fil-C module a trap, written just `trap`. harness.c prints the same
    lines from native code; for a Fil-C module it makes one call per
    process, chosen by `argv[1]`, since a trap ends the process. mode
    holds `plain` or `filc`. Other outcomes are reported on stdout and
    left out of the comparison.

    For a Fil-C module, difftest also runs every run line on the
    pizlonated module and fails unless each outcome is the same, traps
    and their reasons included.
*/
:- use_module(ir).
:- use_module(ir_text).
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
:- use_module(pizlonate).
:- use_module(check_reuse).
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
    % halt/1 outside catch/3: SWI implements halt as an exception.
    catch(( ( register_default(Default),
              checks_default(Checks0),
              inline_default(Inline0),
              inline_options(Argv0,Inline0,Inline,Argv1),
              options(Argv1,o0,Default,Checks0,Level,Registers,Checks,Argv),
              opt_selection(Level,Inline,Opt),
              command(Opt,Registers,Checks,Argv) )
          ->  Status = 0
          ;   format(user_error, "nanofil: failed~n", []),
              Status = 1
          ),
          Error,
          ( report(Error),
            Status = 1
          )),
    halt(Status).

% The emission choices: emit(Registers, Branches, Copies).
register_default(emit(Registers, Branches, Copies)) :-
    % Unbound until options/8: the defaults depend on -O.
    ( getenv('NANOFIL_REGISTERS',R) -> register_mode(R), Registers = R ; true ),
    ( getenv('NANOFIL_BRANCHES',B) -> branches_mode(B), Branches = B ; true ),
    ( getenv('NANOFIL_MEMCPY',M) -> memcpy_mode(M), Copies = M ; true ).
register_mode(R) :-
    ( memberchk(R,[stack,local,function,operands,cells]) -> true
    ; throw(nanofil_error('registers must be stack, local, function, operands or cells')) ).
branches_mode(B) :-
    ( memberchk(B,[reference,selected]) -> true
    ; throw(nanofil_error('branches must be reference or selected')) ).
memcpy_mode(M) :-
    ( memberchk(M,[call,inline]) -> true
    ; throw(nanofil_error('memcpy must be call or inline')) ).
checks_default(Checks) :-
    ( getenv('NANOFIL_CHECKS',C) -> Checks = C ; Checks = reference ),
    checks_mode(Checks).
checks_mode(C) :-
    ( memberchk(C,[reference,reuse]) -> true
    ; throw(nanofil_error('checks must be reference or reuse')) ).
% inline_options(+Argv0, +Inline0, -Inline, -Argv): Argv is Argv0 less
% its --inline= options, the last of which gives Inline.
inline_options([], I, I, []).
inline_options([A|As], I0, I, Args) :-
    (   atom(A), atom_concat('--inline=', I1, A)
    ->  inline_mode(I1), inline_options(As, I1, I, Args)
    ;   Args = [A|Args1], inline_options(As, I0, I, Args1)
    ).
inline_default(Inline) :-
    ( getenv('NANOFIL_INLINE',I) -> Inline = I ; Inline = none ),
    inline_mode(Inline).
inline_mode(I) :-
    ( memberchk(I,[none,small]) -> true
    ; throw(nanofil_error('inline must be none or small')) ).
% opt_selection(+Level, +Inline, -Opt): the middle end's selection
% (opt.pl); inlining needs -O.
opt_selection(o0, _, o0).
opt_selection(o1, none, o1).
opt_selection(o1, small, o1(small)).
% opt_level(+Opt, -Level): o0 or o1, for difftest's validation.
opt_level(o0, o0).
opt_level(o1, o1).
opt_level(o1(_), o1).

options(['-O'|As],_,R,C,O,Rs,Cs,Args) :- !, options(As,o1,R,C,O,Rs,Cs,Args).
options([A|As],O,emit(_,B,M),C,Opt,Rs,Cs,Args) :-
    atom_concat('--registers=',R,A), !, register_mode(R),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,emit(R,_,M),C,Opt,Rs,Cs,Args) :-
    atom_concat('--branches=',B,A), !, branches_mode(B),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,emit(R,B,_),C,Opt,Rs,Cs,Args) :-
    atom_concat('--memcpy=',M,A), !, memcpy_mode(M),
    options(As,O,emit(R,B,M),C,Opt,Rs,Cs,Args).
options([A|As],O,R,_,Opt,Rs,Cs,Args) :-
    atom_concat('--checks=',C,A), !, checks_mode(C),
    options(As,O,R,C,Opt,Rs,Cs,Args).
options(Args,O,emit(R,B,M),C,O,emit(R,B,M),C,Args) :-
    registers_default(O,R), branches_default(O,B), memcpy_default(O,M).

% registers_default(+Opt, ?Registers) and branches_default(+Opt,
% ?Branches): with no option or environment variable, -O selects
% whole-function registers with register operands and frame cells, and
% branch selection,
% and its absence keeps the reference emission.
registers_default(_, R) :- nonvar(R), !.
registers_default(o0, stack).
registers_default(o1, cells).
branches_default(_, B) :- nonvar(B), !.
branches_default(o0, reference).
branches_default(o1, selected).
% memcpy_default(+Opt, ?Copies): -O inlines small constant copies.
memcpy_default(_, M) :- nonvar(M), !.
memcpy_default(o0, call).
memcpy_default(o1, inline).

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
% .c or .i file goes through the C frontend, anything else is IR text.
file_module(File, Module) :-
    (   (   atom_concat(_, '.c', File)
        ;   atom_concat(_, '.i', File)
        )
    ->  c_file_module(File, Module)
    ;   read_ir_file(File, Module, _),
        valid_module(Module)
    ).

% c_file_module(+File, -Module): Module is the valid IR module of the C
% file.
c_file_module(File, Module) :-
    c_file_tokens(File, Tokens),
    (   c_parse(Tokens, Items) -> true
    ;   throw(nanofil_error('C parse failed'))
    ),
    % Deterministic stages: a leftover choicepoint would keep the tokens
    % and items of a large translation unit (SQLite) alive to the end.
    once(c_module(Items, Module)),
    once(valid_module(Module)).

% c_file_tokens(+File, -Tokens): Tokens are the C tokens of File. A .i
% file is already preprocessed; anything else goes through c_pp with the
% predefined macros and include paths of $FILCC (default filcc).
c_file_tokens(File, Tokens) :-
    (   atom_concat(_, '.i', File)
    ->  % once/1: seq//1's last alternative would stay a choicepoint for
        % the rest of the compile.
        once(phrase_from_file(seq(Cs), File, [type(binary)])),
        once(c_tokens(Cs, File, Tokens0))
    ;   ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
        pp_profile(Clang, Profile),
        pp_file(File, Profile, Tokens0)
    ),
    (   getenv('NANOFIL_STD', Std), Std \== c17
    ->  (   Std == c23 -> c23_tokens(Tokens0, Tokens)
        ;   throw(nanofil_error('NANOFIL_STD must be c17 or c23'))
        )
    ;   Tokens = Tokens0
    ).

%% Commands

/* release_stacks: collect garbage and return unused stack memory to the
   system between the stages of a large compile. SWI grows its stacks
   between collections and keeps them grown, and its stack limit counts
   what is allocated, not what is live: gnulib's test-intprops.c, whose
   main has 87,000 blocks, never has more than about 210 MB live, yet
   the frontend leaves the trail at 250 MB and the middle end the global
   stack at 1 GB, and the next collection, which must shift them first,
   exceeds the default 1 GB limit. A host without these predicates
   skips them. */
release_stacks :-
    catch(garbage_collect, error(existence_error(_, _), _), true),
    catch(trim_stacks, error(existence_error(_, _), _), true).

% Only native emission needs Registers; only the Fil-C checked stage
% needs Checks (difftest runs it too); other commands consume Opt.
command(Opt, Registers, Checks, [compile, File]) :- !,
    file_module(File, Module0),
    % Promote can remove every p from a module; the ABI is the original's.
    module_mode(Module0, Mode),
    optimize(Opt, Module0, Module),
    mode_print_asm(Mode, Registers, Checks, Module).
command(Opt, Registers, Checks, [cc, File]) :- !,
    c_file_module(File, Module0),
    release_stacks,
    once(optimize(Opt, Module0, Module)),
    release_stacks,
    mode_print_asm(filc, Registers, Checks, Module).
command(Opt, _, Checks, [difftest, File, Dir]) :- !,
    difftest(Opt, Checks, File, Dir).
command(Opt, _, _, Args) :- command(Opt,Args).

% command(+Opt, +Args): carry out the command line Args (without options),
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
difftest(Sel, Checks, File, Dir) :-
    file_module(File, Module0),
    module_mode(Module0, Mode),
    optimize(Sel, Module0, Module),
    opt_level(Sel, Opt),
    file_runs(File, Runs),
    opt_valid_module(Opt, Module),
    module_prepared(Module0, Prepared0),
    module_prepared(Module, Prepared),
    % One findall over all runs, so each run's heap is reclaimed on
    % backtracking before the next starts.
    findall(Result-Verdict,
            ( member(Run, Runs),
              validated_run(Sel, Module0-Prepared0, Module-Prepared, Run,
                            Result, Verdict)
            ),
            ResultVerdicts),
    pairs_keys_values(ResultVerdicts, Results, Verdicts),
    opt_report_validation(Opt, File, Module0, Module, Verdicts),
    mode_pizlonation_agrees(Mode, Checks, File, Module-Prepared, Runs),
    include(comparable(Mode), Results, Compared),
    exclude(comparable(Mode), Results, Skipped),
    atom_concat(Dir, '/expected.txt', ExpectedFile),
    atom_concat(Dir, '/harness.c', HarnessFile),
    atom_concat(Dir, '/mode', ModeFile),
    write_file(ExpectedFile, expected_lines(Compared)),
    write_file(HarnessFile, harness(Mode, Module, Compared)),
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

% mode_print_asm(+Mode, +Registers, +Checks, +Module): print the
% assembly of Module by the backend for Mode, filc or plain. Fil-C
% prints one item at a time (filc_module_emit/3), since a large module's
% lines (SQLite's) need not all be held at once.
mode_print_asm(plain, _, _, Module) :-
    module_asm(Module, Asm), print_asm(Asm).
mode_print_asm(filc, Registers, Checks, Module) :-
    checked_module(Checks, Module, Checked),
    filc_module_emit(Checked, Registers, print_asm).

% checked_module(+Checks, +Module, -Checked): Checked is Module
% pizlonated, with check reuse (docs/m7.md) when Checks is reuse, which
% must be valid checked IR (ir.pl): the validator verifies the passes.
% Reuse must also change nothing but which proof a covered access reads.
checked_module(Checks, Module, Checked) :-
    once(pizlonate_module(Module, Checked0)),
    release_stacks,
    once(valid_module(Checked0)),
    release_stacks,
    checks_module(Checks, Checked0, Checked).

checks_module(reference, Checked, Checked).
checks_module(reuse, Checked0, Checked) :-
    once(reuse_checks(Checked0, Checked)),
    (   reuse_refines(Checked0, Checked) -> true
    ;   throw(nanofil_error('check reuse changed more than proofs'))
    ),
    once(valid_module(Checked)).

/* mode_pizlonation_agrees(+Mode, +File, +Module-Prepared, +Runs): for a
   filc module, the pizlonated Module has the same outcome as Module on
   every run, traps and their reasons included, or the command throws:
   the explicit checks are exactly the implicit ones. A missing or too
   weak check shows as the outcome unchecked(Why). Both run with the same
   fuel, since pizlonate keeps every block. */
mode_pizlonation_agrees(plain, _, _, _, _).
mode_pizlonation_agrees(filc, Checks, File, Module-Prepared, Runs) :-
    checked_module(Checks, Module, Checked),
    module_prepared(Checked, CheckedPrepared),
    findall(Bad,
            ( member(Run, Runs),
              pizlonation_verdict(Module-Prepared, Checked-CheckedPrepared,
                                  Run, Bad),
              Bad \== ok
            ),
            Bads),
    forall(member(bad(CallText, Text0, Text), Bads),
           format("PIZLONATION FAILED ~w ~w: ~w unchecked, ~w checked~n",
                  [File, CallText, Text0, Text])),
    (   Bads == [] -> true
    ;   throw(nanofil_error('pizlonation changed an outcome'))
    ).

pizlonation_verdict(Original, Checked, Run, Verdict) :-
    fuel_step(Fuel),
    module_run_result(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    (   Outcome0 \== out_of_fuel
    ;   Fuel == MaxFuel
    ),
    !,
    module_run_result(Checked, Run, Fuel, r(_, _, Outcome)),
    (   (   ground(Outcome0) -> Outcome0 == Outcome
        ;   \+ \+ Outcome0 = Outcome
        )
    ->  Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

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
validated_run(Sel, Original, Optimized, Run, Result, Verdict) :-
    opt_level(Sel, o1),
    fuel_step(Fuel),
    module_run_result(Original, Run, Fuel, r(Fn, Args, Outcome0)),
    max_fuel(MaxFuel),
    (   Outcome0 \== out_of_fuel
    ;   Fuel == MaxFuel
    ),
    % Commit to the first fuel step at which the original finishes, or
    % to the last one.
    !,
    optimized_fuel(Sel, Fuel, Fuel1),
    module_run_result(Optimized, Run, Fuel1, Result),
    Result = r(_, _, Outcome),
    (   refines(Outcome0, Outcome) -> Verdict = ok
    ;   call_text(Fn, Args, CallText),
        outcome_text(Outcome0, Text0),
        outcome_text(Outcome, Text),
        Verdict = bad(CallText, Text0, Text)
    ).

% optimized_fuel(+Sel, +Fuel, -Fuel1): the optimized module's fuel.
% Inlining adds a join block per inlined call, at most one block run
% for each block the original runs.
optimized_fuel(o1, Fuel, Fuel).
optimized_fuel(o1(_), Fuel, Fuel1) :- Fuel1 is 2 * Fuel.

% fuel_step(-Fuel) is multi: Fuel is one of the growing fuel limits,
% smallest first, ending at max_fuel.
fuel_step(Fuel) :-
    member(Fuel, [1000, 8000, 64000, 512000, 1000000]).

% canonical_arg(+Param, +Arg0, -Arg): Arg is Arg0 reduced modulo the
% class of Param.
canonical_arg(param(Class, _), Arg0, Arg) :-
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
% filc, a trap or a reached unreachable, both a Fil-C safety panic
% natively. Nothing else has a native counterpart.
comparable(_, r(_, _, ret(V))) :-
    integer(V).
comparable(_, r(_, _, ret)).
comparable(filc, r(_, _, trap(_))).
comparable(filc, r(_, _, unreachable)).

% call_text(+Fn, +Args, -Text): Text is the atom 'Fn(A1, A2, ...)'.
call_text(Fn, Args, Text) :-
    atomic_list_concat(Args, ', ', ArgText),
    format(atom(Text), '~w(~w)', [Fn, ArgText]).

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
% Only Fil-C mode compares unreachable, which panics there.
expected_lines([]) --> [].
expected_lines([r(Fn, Args, Outcome)|Results]) -->
    { call_text(Fn, Args, CallText),
      (   Outcome = trap(_) -> Text = trap
      ;   Outcome == unreachable -> Text = trap
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
      findall(Type, ( member(param(Class, _), Params), c_type(Class, Type) ),
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

%% Runs

% file_runs(+File, -Runs): Runs are the run(Fn, Args) facts of IR File,
% in order.
file_runs(File, Runs) :- read_ir_file(File, _, Runs).

% library(format)'s format_//2 raises type_error(list, '') for an argument
% of '' (Trealla 12f4cbd), which a call with no arguments produces.
% fmt(+Format, +Args)//: the characters format/3 makes of Format and Args.
fmt(Format, Args) -->
    { format(chars(Cs), Format, Args) },
    seq(Cs).
