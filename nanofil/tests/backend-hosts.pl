/* Frontend-free back-end products for tests/backend-hosts.sh. Run from
   src with bin/nanofil --script; every argument is an IR fixture. */
:- use_module('../src/ir').
:- use_module('../src/ir_text').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module('../src/filc_amd64').
:- use_module('../src/asm').
:- use_module(library(lists)).

:- initialization(main).

main :-
    current_prolog_flag(argv, Args),
    catch(((maplist(file_products, Args), wide_products) -> Status = 0 ; Status = 1),
          E, (write(user_error, E), nl(user_error), Status = 1)),
    halt(Status).

file_products(Arg) :-
    ( atom(Arg) -> File = Arg ; atom_chars(File, Arg) ),
    format('% ~w~n', [File]),
    read_ir_file(File, M0, _), module_products(M0).

% Forty scalar parameters keep enough homes live for masks wider than
% 64 bits. Pinned Trealla drops the high bits of A /\ \ B when B's
% complement is a negative machine integer; small ABI fixtures miss it.
wide_products :-
    numlist(1, 40, Is),
    findall(param(l, tmp(X)), (member(I, Is), format(atom(X), 'x~w', [I])), Ps),
    findall(let(tmp(R), l, add, [tmp(P), tmp(X)]),
            (member(I, Is), J is I-1, format(atom(X), 'x~w', [I]),
             format(atom(P), 'r~w', [J]), format(atom(R), 'r~w', [I])), Adds),
    module_products(module([func(wide, export, l, [param(p,tmp(p))|Ps], [
        block(start, [], [let(tmp(r0),l,load(l),[tmp(p)])|Adds], ret(tmp(r40)))])])).

module_products(M0) :-
    valid_module(M0),
    optimize(o1(wide, full), M0, M), valid_module(M),
    print_module(M),
    pizlonate_module(M, C), valid_module(C),
    print_module(C),
    forall(member(R, [stack, temps, pointers]),
           filc_module_emit(C, emit(R, selected, inline), print_asm)).
