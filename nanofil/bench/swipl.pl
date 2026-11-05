% SWI-Prolog's own benchmark suite (bench/ in its sources, the van Roy
% programs and later additions) as one workload for run.py: each program
% runs its calibrated count of iterations scaled by Factor, and only the
% program names and counts are printed, so every build's output is the
% same.
%
%   swipl swipl.pl BENCH-DIR FACTOR

:- initialization(main, main).

main :-
    current_prolog_flag(argv, [Dir, FactorAtom]),
    atom_number(FactorAtom, Factor),
    atom_concat(Dir, '/run.pl', Run),
    load_files(user:Run, [silent(true)]),
    forall(use_program(P, N, Factor),
           ( ntimes(P:top, N),
             format("~w ~w~n", [P, N]) )).
