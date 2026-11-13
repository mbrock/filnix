% Select named functions in link order and reject missing names.
:- initialization(main, main).
main :-
    current_prolog_flag(argv, [F|Ns]), read_file_to_terms(F, [module(Is)], []),
    maplist([N, A]>>atom_string(A, N), Ns, As),
    forall(member(A, As),
           (memberchk(func(A, _, _, _, _), Is) -> true
           ; format(user_error, 'missing function in linked units: ~w~n', [A]), halt(1))),
    include([I]>>(I = func(N, _, _, _, _), memberchk(N, As)), Is, Sel),
    length(As, K), length(Sel, K),
    write_canonical(module(Sel)), write('.'), nl.
