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

    bin/nanofil loads it when NANOFIL_HOST=swi (the default), or runs a
    saved state of it and main.pl (NANOFIL_STATE, from --save-state).
*/
:- prolog_load_context(directory, Dir),
   asserta(user:file_search_path(library, Dir)).
:- set_prolog_flag(double_quotes, chars).
% A saved state (bin/nanofil's NANOFIL_STATE) does not rerun directives,
% so the encodings are set again when it starts.
user:utf8_streams :-
    set_prolog_flag(encoding, utf8),
    forall(member(S, [user_input, user_output, user_error]),
           set_stream(S, encoding(utf8))).
:- user:utf8_streams.
:- initialization(user:utf8_streams, restore).

% NANOFIL_STACK_LIMIT=BYTES raises SWI's 1 GB stack limit, from source or
% a saved state alike (a state ignores --stack-limit): the SQLite
% amalgamation with FTS5 needs about 3 GB. nanofil-cc sets it to 4 GB
% only to compile again a file that overflowed the default.
%
% SWI collects the global stack when it holds more than factor(F) times
% what the last collection left, else grows it, and raises an overflow
% when growing would pass the limit, without collecting first. With the
% default factor 3 a compile overflowed 1 GB with a third of that live:
% GLib's resource blobs (gtk3's 11 MB gtkresources.c, 256 MB live while
% lexing) and SQLite with nixpkgs' and the shell's flags. Factor 2 uses
% the limit; their compile times are unchanged.
user:nanofil_stack_limit :-
    (   getenv('NANOFIL_STACK_LIMIT', A), atom_number(A, N)
    ->  set_prolog_flag(stack_limit, N)
    ;   true
    ),
    set_prolog_stack(global, factor(2)).
:- user:nanofil_stack_limit.
:- initialization(user:nanofil_stack_limit, restore).

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
