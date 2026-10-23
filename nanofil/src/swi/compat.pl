/*  Running nanofil on SWI-Prolog.

    nanofil is written for Trealla's (and Scryer's) dialect. Loading this
    file first makes SWI-Prolog run it unchanged:

    - library(dcgs), library(format), library(pio) and library(clpz)
      resolve to the small modules in this directory;
    - double_quotes is chars in every module, as in Trealla. SWI scopes
      the flag per module, so it is set as each module starts;
    - argv is a list of atoms in SWI and of character lists in Trealla;
      main.pl accepts both;
    - files, pipes and the standard streams are UTF-8, as in Trealla,
      whatever the locale (the Nix build sandbox has none);
    - `:- initialization(G)` becomes SWI's `initialization(G, main)`, so a
      program that ends with halt/1 exits quietly with that status.

    bin/nanofil loads it when NANOFIL_HOST=swi (the default).
*/
:- prolog_load_context(directory, Dir),
   asserta(user:file_search_path(library, Dir)).
:- set_prolog_flag(double_quotes, chars).
:- set_prolog_flag(encoding, utf8).
:- forall(member(S, [user_input, user_output, user_error]),
          set_stream(S, encoding(utf8))).

user:term_expansion((:- module(M, Es)),
                    [(:- module(M, Es)), (:- set_prolog_flag(double_quotes, chars))]).
user:term_expansion((:- initialization(G)), (:- initialization(G, main))) :-
    \+ getenv('NANOFIL_PROFILE', _).
% NANOFIL_PROFILE=N: run the program under SWI's profiler and print the N
% predicates with the most self time to stderr when it halts.
user:term_expansion((:- initialization(G)),
                    (:- initialization(user:nanofil_profile(M:G), main))) :-
    getenv('NANOFIL_PROFILE', _),
    prolog_load_context(module, M).

user:nanofil_profile(G) :-
    getenv('NANOFIL_PROFILE', N0), atom_number(N0, N),
    at_halt(with_output_to(user_error,
                           show_profile([top(N), cumulative(false)]))),
    profile(G).
