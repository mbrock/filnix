/*  Freeze filcc's preprocessor profile for the browser playground.

    In a browser there is no clang to ask, so pp_profile/2 runs here,
    natively, and its answer is written as one fact:

      profile(MacroPairs, Dirs, Answers).

    MacroPairs is the macro assoc as a list, Dirs the include search
    path renamed /inc/0, /inc/1, ... (build.sh copies the headers there)
    and Answers the feature answers. Each original directory is printed
    to stderr as "dir N PATH" so build.sh can copy from it.

    Usage: nanofil --script profile.pl OUT [PREFIX]
    PREFIX (default none) goes before /inc, for native runs of the bundle.
*/
:- use_module(c_pp).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(format)).

:- initialization(main).

main :-
    current_prolog_flag(argv, [Out0|Rest]),
    ( atom(Out0) -> Out = Out0 ; atom_chars(Out, Out0) ),
    ( Rest = [Pre0|_] -> ( atom(Pre0) -> Pre = Pre0 ; atom_chars(Pre, Pre0) ) ; Pre = '' ),
    nb_setval(play_prefix, Pre),
    ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
    pp_profile(Clang, profile(Macros, Paths, features(_, Answers))),
    assoc_to_list(Macros, Pairs),
    length(Paths, N),
    numlist_(0, N, Ns),
    maplist(dir_name, Ns, Dirs),
    forall(nth0(I, Paths, P), format(user_error, "dir ~w ~w~n", [I, P])),
    open(Out, write, S),
    write_canonical(S, profile(Pairs, Dirs, Answers)),
    write(S, '.'), nl(S),
    close(S),
    halt(0).

numlist_(N, N, []) :- !.
numlist_(I, N, [I|Is]) :- J is I + 1, numlist_(J, N, Is).

dir_name(I, D) :- nb_getval(play_prefix, Pre), format(atom(D), "~w/inc/~w", [Pre, I]).
