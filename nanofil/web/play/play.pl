/*  The playground's driver: one C file through nanofil's pipeline.

    play(+File, +Opt, -Stages): Stages lists stage(Name, Seconds, Result)
    for preprocessing, parsing, lowering, validation, each selected
    middle-end pass (Opt is o0, o1, or passes(Names)), pizlonation
    (Fil-C's checks made explicit) and the Fil-C backend, and what they
    made: term(syntax, Items), term(lowered, M0) (as lowering made it),
    term(Pass, M) for each selected optimization,
    term(ir, Module) (the checked IR), term(asm, Lines), text(ir, Chars) and
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

stages_opt(Opt, M0, Stages) :-
    optimization_passes(Opt, Passes),
    stages_passes(Passes, M0, Stages).

stages_passes([], M, Stages) :- stages_pizlonate(M, Stages).
stages_passes([Pass|Passes], M0, [S|Ss]) :-
    timed(Pass, ( optimize_pass(Pass, M0, M), valid_module(M) ), S),
    (   ok(S)
    ->  Ss = [term(Pass, M)|Ss1],
        stages_passes(Passes, M, Ss1)
    ;   Ss = []
    ).

% The IR shown is the checked module the backend compiles: Fil-C's
% checks and pollchecks in the IR (docs/pizlonation.md), validated as
% the cc command validates it.
stages_pizlonate(M, [S, term(ir, C), P|Ss]) :-
    timed(pizlonate, ( pizlonate_module(M, C), valid_module(C) ), S),
    (   ok(S)
    ->  timed(print_ir, phrase(module_text(C), IR), P),
        Ss = [text(ir, IR)|Ss1],
        stages_asm(C, Ss1)
    ;   P = stage(print_ir, 0, skipped), Ss = []
    ).

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
