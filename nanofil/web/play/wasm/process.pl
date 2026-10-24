/*  library(process) for SWI-Prolog in WebAssembly, which cannot start
    processes. c_pp.pl loads library(process) for pp_profile/2, which the
    playground never calls (its profile is frozen, profile.pl); any call
    throws.
*/
:- module(process, [process_create/3, process_wait/2]).

process_create(Exe, _, _) :-
    throw(error(resource_error(process(Exe)), context(process_create/3, 'no processes in WebAssembly'))).

process_wait(_, _) :-
    throw(error(resource_error(process), context(process_wait/2, 'no processes in WebAssembly'))).
