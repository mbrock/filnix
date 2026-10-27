/*  The playground's driver: one C file through nanofil's pipeline.

    play(+File, +Opt, -Stages): Stages lists stage(Name, Seconds, Result)
    for preprocessing, parsing, lowering, validation, each selected
    middle-end pass (Opt is o0, o1, or passes(Names)), pizlonation
    (Fil-C's checks made explicit), check reuse when Names include
    check_reuse (docs/m7.md) and the Fil-C backend, and what they
    made: term(syntax, Items), term(lowered, M0) (as lowering made it),
    term(Pass, M) for each selected optimization,
    term(ir, Module) (the checked IR), term(check_reuse, Module) (with
    covered checks deleted), term(asm, Lines), text(ir, Chars) (the module
    the backend compiled) and
    text(asm, Chars). Stops at the first stage that fails or throws,
    whose Result is then failed or error(E).

    The preprocessor profile is profile.pl's frozen answer (no clang in a
    browser), read once from profile.data beside this file.

    Runs on SWI-Prolog (after src/swi/compat.pl) and Trealla, natively or
    in WebAssembly.
*/
:- module(play, [play/3, play_report/2]).

:- use_module(ir).
:- use_module(c_pp).
:- use_module(c_parse).
:- use_module(c_lower).
:- use_module(opt).
:- use_module(ir_text).
:- use_module(pizlonate).
:- use_module(check_reuse).
:- use_module(filc_amd64).
:- use_module(asm).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(format)).
:- use_module(library(dcgs)).

:- dynamic(frozen_profile/1).

profile(P) :-
    frozen_profile(P0),
    !,
    P = P0.
profile(profile(Macros, Dirs, features(none, Answers))) :-
    ( getenv('NANOFIL_PLAY_PROFILE', F0) -> true ; F0 = '/nanofil/src/profile.data' ),
    ( atom(F0) -> F = F0 ; atom_chars(F, F0) ),
    open(F, read, S),
    read(S, profile(Pairs, Dirs, Answers)),
    close(S),
    list_to_assoc(Pairs, Macros),
    assertz(frozen_profile(profile(Macros, Dirs, features(none, Answers)))).

play(File, Opt, Stages) :-
    stages(File, Opt, Stages).

stages(File, Opt, Stages) :-
    timed(profile, profile(Profile), S0),
    Stages = [S0|Ss0],
    (   ok(S0) -> stages_pp(File, Opt, Profile, Ss0) ; Ss0 = [] ).

stages_pp(File, Opt, Profile, [S|Ss]) :-
    timed(preprocess, pp_file(File, Profile, Tokens), S),
    (   ok(S) -> stages_parse(Opt, Tokens, Ss) ; Ss = [] ).

stages_parse(Opt, Tokens, [S|Ss]) :-
    timed(parse, c_parse(Tokens, Items), S),
    (   ok(S) -> Ss = [term(syntax, Items)|Ss1], stages_lower(Opt, Items, Ss1) ; Ss = [] ).

stages_lower(Opt, Items, [S, V|Ss]) :-
    timed(lower, c_module(Items, M0), S),
    (   ok(S)
    ->  timed(validate, valid_module(M0), V),
        Ss = [term(lowered, M0)|Ss0],
        (   ok(V) -> stages_opt(Opt, M0, Ss0) ; Ss0 = [] )
    ;   V = stage(validate, 0, skipped), Ss = []
    ).

% passes(Names) may also name check_reuse, which runs after pizlonation
% (docs/m7.md), not in the middle end.
stages_opt(Opt0, M0, Stages) :-
    (   Opt0 = passes(Names), memberchk(check_reuse, Names)
    ->  exclude(==(check_reuse), Names, Rest), Opt = passes(Rest), Checks = reuse
    ;   Opt = Opt0, Checks = reference
    ),
    optimization_passes(Opt, Passes),
    stages_passes(Passes, Checks, M0, Stages).

stages_passes([], Checks, M, Stages) :- stages_pizlonate(M, Checks, Stages).
stages_passes([Pass|Passes], Checks, M0, [S|Ss]) :-
    timed(Pass, ( optimize_pass(Pass, M0, M), valid_module(M) ), S),
    (   ok(S)
    ->  Ss = [term(Pass, M)|Ss1],
        stages_passes(Passes, Checks, M, Ss1)
    ;   Ss = []
    ).

% The IR shown is the checked module the backend compiles: Fil-C's
% checks and pollchecks in the IR (docs/pizlonation.md), validated as
% the cc command validates it.
stages_pizlonate(M, Checks, [S, term(ir, C)|Ss]) :-
    timed(pizlonate, ( pizlonate_module(M, C), valid_module(C) ), S),
    (   ok(S) -> stages_checks(Checks, C, Ss) ; Ss = [] ).

% With reuse, the backend compiles the module check_reuse made, accepted
% as the cc command accepts it: refinement, then validation.
stages_checks(reference, C, Ss) :- stages_print(C, Ss).
stages_checks(reuse, C, [S|Ss]) :-
    timed(check_reuse, ( reuse_checks(C, R), reuse_refines(C, R), valid_module(R) ), S),
    (   ok(S) -> Ss = [term(check_reuse, R)|Ss1], stages_print(R, Ss1) ; Ss = [] ).

stages_print(C, [P|Ss]) :-
    timed(print_ir, phrase(module_text(C), IR), P),
    (   ok(P) -> Ss = [text(ir, IR)|Ss1], stages_asm(C, Ss1) ; Ss = [] ).

stages_asm(C, [S|Ss]) :-
    timed(backend, filc_module_asm(C, Lines), S),
    (   ok(S)
    ->  timed(print_asm, with_output_to(chars(Asm), print_asm(Lines)), P),
        Ss = [term(asm, Lines), P, text(asm, Asm)]
    ;   Ss = []
    ).

ok(stage(_, _, ok)).

timed(Name, Goal, stage(Name, T, R)) :-
    statistics(cputime, T0),
    catch(( call(Goal) -> R = ok ; R = failed ), E, R = error(E)),
    statistics(cputime, T1),
    T is T1 - T0.

% play_report(+File, +Opt): run play/3 and print each stage on its own
% line, then the IR and the assembly between marker lines, for callers
% that read standard output (the JS side, and native benchmarks).
play_report(File, Opt) :-
    play(File, Opt, Stages),
    forall(member(stage(N, T, R), Stages),
           (   R = error(E)
           ->  format("stage ~w ~4f error ~q~n", [N, T, E])
           ;   format("stage ~w ~4f ~w~n", [N, T, R])
           )),
    forall(member(text(K, Cs), Stages),
           format("~~~~~~ ~w~n~s", [K, Cs])),
    forall(member(term(ir, Term), Stages),
           (   format("~~~~~~ ir-term~n", []),
               writeq(Term), write('.'), nl
           )).
