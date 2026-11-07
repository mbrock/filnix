/* The checked stage of main.pl, including its refinement/validation
   gates, for already optimized cc-ir products. Unlike outcomes, accept
   pointer-free/empty objects too: the census must not omit such units. */
:- use_module('../src/ir').
:- use_module('../src/ir_text').
:- use_module('../src/pizlonate').
:- use_module('../src/check_reuse').
:- use_module('../src/half_check').
:- initialization(main).

main :-
    catch((checked -> halt(0) ; halt(1)), E, (print_message(error, E), halt(1))).

checked :-
    current_prolog_flag(argv, [File]),
    read_ir_file(File, Module, []), valid_module(Module),
    once(pizlonate_module(Module, C0)), valid_module(C0),
    once(reuse_checks(forward, C0, C1)), reuse_refines(forward, C0, C1),
    once(renew_checks(any, C1, C2)), renew_refines(any, C1, C2),
    once(half_checks(C2, Checked)), half_refines(C2, Checked),
    valid_module(Checked),
    write_canonical(Checked), write('.'), nl.
