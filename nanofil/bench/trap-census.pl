/* Campaign 7's non-class-a sites. residual.pl owns the class-a census.
   Read each provenance-bearing module once; count static instructions,
   not executions. Retain identities so every total can be audited. */
:- use_module(library(lists)).
:- initialization(main).

main :-
    catch((census -> halt(0) ; halt(1)), E, (print_message(error, E), halt(1))).

census :-
    current_prolog_flag(argv, Files),
    maplist(read_module, Files, Modules),
    findall(N, (member(module(Items), Modules), member(func(N, _, _, _, Bs), Items),
                member(block(_, _, Is, _), Bs), member(let(_, _, va_args, _), Is)), OwnVA),
    append([error, fprintf, printf, sprintf, wprintf, fcntl], OwnVA, VA0), sort(VA0, VA),
    findall(S, (nth0(J, Files, F), nth0(J, Modules, M), file_site(F, M, VA, S)), Sites),
    forall(member(S, Sites), (write_canonical(S), write('.'), nl)),
    findall(K, member(obligation(_, _, _, _, K, _), Sites), Keys),
    msort(Keys, Sorted), clumped(Sorted, Counts),
    forall(member(K-N, Counts), format('~q.~n', [count(K, N)])).

read_module(File, Module) :-
    setup_call_cleanup(open(File, read, S),
                       (read_term(S, Module, []), read_term(S, End, [])), close(S)),
    ( Module = module(_), End == end_of_file -> true
    ; throw(error(domain_error(checked_module_file, File), census)) ).

file_site(File, module(Items), VA, obligation(File, N, L, I, Kind, Inst)) :-
    member(func(N, _, _, _, Bs), Items), member(block(L, _, Is, _), Bs),
    nth0(I, Is, Inst), kind(Inst, VA, Kind).

kind(let(_, _, check_function, _), _, function_check).
kind(let(_, _, va_args, _), _, va_args).
kind(let(_, _, va_arg, _), _, va_arg).
kind(call(_, global(N), _), _, direct_call(N)).
kind(raw_call(_, global(N), _), _, direct_call(N)).
kind(call(_, global(free), _), _, libc_free).
kind(call(_, global(N), _), VA, variadic_call(N)) :- memberchk(N, VA).
kind(call(_, P, _), _, indirect_call) :- P \= global(_).
kind(raw_call(_, P, _), _, indirect_call) :- P \= global(_).
