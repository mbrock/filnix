/*  Load the playground on SWI-Prolog, natively or in WebAssembly. The
    bundle (build.sh) puts this file in nanofil/src beside the driver.

    dterm.pl and play_view.pl are written in SWI's own dialect, so they
    load first; then src/swi/compat.pl, which makes every module after it
    read double-quoted text as character lists, then nanofil and play.pl.
    dterm's `initialization(main, main)` would build the wiki and halt,
    so it is dropped. library(process) resolves to ../play-lib/process.pl,
    a stub: WebAssembly has no processes, and the profile is frozen.
*/
:- prolog_load_context(directory, Dir),
   atom_concat(Dir, '/../play-lib', Lib),
   asserta(user:file_search_path(library, Lib)).

:- asserta((user:term_expansion((:- initialization(main, main)), []) :-
               prolog_load_context(module, dterm))).
:- use_module('../web/dterm').
:- use_module(play_view).
:- consult('swi/compat').
:- use_module(play).
