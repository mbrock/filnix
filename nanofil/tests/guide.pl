/*  The guide's example outputs (docs/guide.md), from nanofil's own
    predicates, for the stages the command line does not print.

    Usage, from the directory of FILE (tests/guide.sh does this):

        bin/nanofil --script tests/guide.pl STAGE FILE

    Each STAGE prints one product of compiling FILE, restricted to its
    function `sum` where the product is a module:

    | STAGE | Prints |
    |---|---|
    | `pp` | c_pp's tokens of line 9, with their locations |
    | `parse` | c_parse's item for `sum` |
    | `elaborate` | the typed trees c_types' elaborate/4 gave lowering for lines 9 and 10 |
    | `context` | the first records of `sum`'s context (provenance.pl) |
    | `promote` | the module after promote alone |
    | `checked` | the -O module after pizlonation, checks as the reference keeps them |
    | `renew` | the same after check_reuse's reuse and renew, the -O default |
    | `mutant` | what the validator says when one check is made too weak |
    | `abi` | filc_abi's frame for `sum`, and its entry actions |
    | `homes` | the register map amd64_regs proposed and its checker accepted |

    The -O stages use the -O defaults (inlining small, simplification
    full). SWI-Prolog only: it prints with print_term/2 and wraps
    predicates to see what they were given.
*/
:- use_module('../src/ir').
:- use_module('../src/ir_text').
:- use_module('../src/c_pp').
:- use_module('../src/c_parse').
:- use_module('../src/c_lower').
:- use_module('../src/c_types').
:- use_module('../src/opt').
:- use_module('../src/pizlonate').
:- use_module('../src/check_reuse').
:- use_module('../src/filc_abi').
:- use_module('../src/filc_amd64').
:- use_module('../src/amd64_regs').
:- use_module(library(prolog_wrap)).
:- use_module(library(pprint)).

:- initialization(main).

:- dynamic(seen/2).

main :-
    current_prolog_flag(argv, [Stage, File]),
    (   stage(Stage, File) -> halt(0)
    ;   format(user_error, "guide: stage ~w failed~n", [Stage]), halt(1)
    ).

tokens(File, Tokens) :-
    ( getenv('FILCC', Clang) -> true ; Clang = filcc ),
    pp_profile(Clang, Profile),
    pp_file(File, Profile, Tokens).

c_lowered(File, M) :-
    tokens(File, Tokens), c_parse(Tokens, Items),
    once(c_module(Items, M)), once(valid_module(M)).

optimized(File, M) :-
    c_lowered(File, M0), once(optimize(o1(small, full), M0, M)).

checked(File, C) :-
    optimized(File, M), once(pizlonate_module(M, C)), once(valid_module(C)).

% The -O default, --checks=renew, as main.pl's checks_module/3 runs it.
renewed(File, C) :-
    checked(File, C0),
    once(reuse_checks(C0, C1)), reuse_refines(C0, C1),
    once(renew_checks(C1, C)), renew_refines(C1, C),
    once(valid_module(C)).

stage(pp, File) :-
    tokens(File, Tokens),
    forall(( member(T, Tokens), T = tok(_, _:9) ), ( writeq(T), nl )).
stage(parse, File) :-
    tokens(File, Tokens), c_parse(Tokens, Items),
    member(F, Items), F = fundef(_, _, dcl(some(sum), _, _), _), !,
    term(F).
stage(elaborate, File) :-
    wrap_predicate(c_types:elaborate(E, _, Loc, X), guide, W,
                   ( W, assertz(seen(E-Loc, X)) )),
    c_lowered(File, _),
    forall(( member(Line, [9, 10]), seen(E-(_:Line), X), E = assign(_, _, _) ),
           ( format("% ~q~n", [E]), term(X) )).
stage(context, File) :-
    c_lowered(File, module(Items)),
    memberchk(context(sum, Records), Items),
    length(Prefix, 8), append(Prefix, _, Records),
    forall(member(R, Prefix), ( writeq(R), nl )).
stage(promote, File) :-
    c_lowered(File, M0), once(optimize_pass(promote, M0, M)),
    print_sum(M).
stage(checked, File) :-
    checked(File, C), print_sum(C).
stage(renew, File) :-
    checked(File, C0), renewed(File, C),
    with_output_to(string(S0), print_sum(C0)),
    with_output_to(string(S), print_sum(C)),
    (   S == S0 -> format("% unchanged~n", []) ; write(S) ).
stage(mutant, File) :-
    checked(File, module(Items0)),
    select(func(sum, L, R, Ps, Bs0), Items0, func(sum, L, R, Ps, Bs), Items),
    once(weakened_first_check(Bs0, Bs)),
    catch(( valid_module(module(Items)) -> Verdict = accepted ; Verdict = failed ),
          nanofil_error(Msg), Verdict = Msg),
    format("~w~n", [Verdict]).
stage(abi, File) :-
    wrap_predicate(filc_abi:lower_function(Po, S, F, Li, P), guide, W,
                   ( W, ( F = func(sum, _, _, _, _) -> assertz(seen(abi, P)) ; true ) )),
    checked(File, C),
    once(filc_module_asm(C, stack, _, _)),
    once(seen(abi, abi_function(_, _, _, _, Frame, Entry, _, _, _, _))),
    term(Frame), term(Entry),
    ignore((Po, S, Li) = (_, _, _)).
stage(homes, File) :-
    wrap_predicate(amd64_regs:regs_asm(Mode, Meta, B, A, Checked, Report), guide, W,
                   ( W, ( Mode \== map -> assertz(seen(regs, Meta-Checked-Report)) ; true ) )),
    renewed(File, C),
    once(filc_module_asm(C, emit(pointers, selected, inline), _, _)),
    once(seen(regs, regs_metadata(_, Impl, Homes, _)-checked(_, Map)-Report)),
    Impl == pizlonatedFIP1066_sum,
    format("% ~q~n", [Report]),
    forall(member(home(D, Ks), Homes),
           (   memberchk(D-Reg, Map) -> format("~q -> ~w~n", [home(D, Ks), Reg])
           ;   format("~q stays in the frame~n", [home(D, Ks)])
           )),
    forall(member(root(D, N), Homes), format("~q: the frame record, never a home~n", [root(D, N)])),
    ignore((B, A) = (_, _)).

% weakened_first_check(+Blocks0, -Blocks): the first check before a raw
% load covers 2 bytes less than the load reads.
weakened_first_check(Bs0, Bs) :-
    append(Pre, [block(L, Phis, Is0, J)|Post], Bs0),
    append(Before, [let(Q, a, check(Lo, Hi0, Rights, Al), [P]),
                    Load|After], Is0),
    Load = let(_, _, raw_load(_, _), _),
    !,
    Hi is Hi0 - 2,
    format("% ~q~n", [let(Q, a, check(Lo, Hi, Rights, Al), [P])]),
    append(Before, [let(Q, a, check(Lo, Hi, Rights, Al), [P]), Load|After], Is),
    append(Pre, [block(L, Phis, Is, J)|Post], Bs).

print_sum(module(Items)) :-
    include([I]>>( I = func(sum, _, _, _, _) ), Items, Funcs),
    print_module(module(Funcs)).

term(T) :-
    print_term(T, [right_margin(72), tab_width(0), output(current_output)]),
    write('.'), nl.
