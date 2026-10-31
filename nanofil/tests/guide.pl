/*  The guide's example outputs (docs/guide.md), from nanofil's own
    predicates, for the stages the command line does not print.

    Usage, from the directory of FILE (tests/guide.sh does this):

        bin/nanofil --script tests/guide.pl STAGE FILE [TERMS]

    Each STAGE prints one product of compiling FILE, restricted to its
    function `sum` where the product is a module. With TERMS, it also
    writes the fact `output(STAGE, Items)` there: the same product as
    the terms the stage printed, for the guide's page (web/dterm.pl). An
    item is `term(T)`, a term; `comment(S)`, a `%` line; `text(S)`, a
    line of text; or `note(T, S)`, a term with words after it. A
    comment is a term when the stage printed one.

    | STAGE | Prints |
    |---|---|
    | `pp` | c_pp's tokens of line 9, with their locations |
    | `lower` | the IR of `sum`, as `nanofil cc-ir` prints it |
    | `optimized` | the same after the middle end, as `nanofil -O cc-ir` prints it |
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
    current_prolog_flag(argv, [Stage, File|Terms]),
    (   stage(Stage, File, Items)
    ->  forall(member(Text-_, Items), write(Text)),
        forall(member(Out, Terms), write_items(Out, Stage, Items)),
        halt(0)
    ;   format(user_error, "guide: stage ~w failed~n", [Stage]), halt(1)
    ).

% write_items(+Path, +Stage, +Items): output(Stage, Draws), the terms
% the stage printed, as a clause in Path.
write_items(Path, Stage, Items) :-
    pairs_values(Items, Draws),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
                       portray_clause(S, output(Stage, Draws)),
                       close(S)).

% An item: the text the stage prints for it, and what it is as a term.
t(T, Text-term(T)) :- with_output_to(string(Text), term(T)).
q(T, Text-term(T)) :- format(string(Text), "~q~n", [T]).
c(S, Text-comment(S)) :- format(string(Text), "% ~w~n", [S]).
cq(T, Text-comment(T)) :- format(string(Text), "% ~q~n", [T]).

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

stage(pp, File, Items) :-
    tokens(File, Tokens),
    findall(I, ( member(T, Tokens), T = tok(_, _:9), q(T, I) ), Items).
stage(parse, File, [I]) :-
    tokens(File, Tokens), c_parse(Tokens, Items),
    member(F, Items), F = fundef(_, _, dcl(some(sum), _, _), _), !,
    t(F, I).
stage(elaborate, File, Items) :-
    wrap_predicate(c_types:elaborate(E, _, Loc, X), guide, W,
                   ( W, assertz(seen(E-Loc, X)) )),
    c_lowered(File, _),
    findall([C, I],
            ( member(Line, [9, 10]), seen(E-(_:Line), X), E = assign(_, _, _),
              cq(E, C), t(X, I) ),
            Iss),
    append(Iss, Items).
stage(context, File, Items) :-
    c_lowered(File, module(Ms)),
    memberchk(context(sum, Records), Ms),
    length(Prefix, 8), append(Prefix, _, Records),
    maplist(q, Prefix, Items).
stage(lower, File, Items) :-
    c_lowered(File, M), sum_items(M, Items).
stage(optimized, File, Items) :-
    optimized(File, M), sum_items(M, Items).
stage(promote, File, Items) :-
    c_lowered(File, M0), once(optimize_pass(promote, M0, M)),
    sum_items(M, Items).
stage(checked, File, Items) :-
    checked(File, C), sum_items(C, Items).
stage(renew, File, Items) :-
    checked(File, C0), renewed(File, C),
    sum_items(C0, Items0), sum_items(C, Items1),
    (   Items1 == Items0 -> c(unchanged, I), Items = [I] ; Items = Items1 ).
stage(mutant, File, [C, Verdict-text(Verdict0)]) :-
    checked(File, module(Items0)),
    select(func(sum, L, R, Ps, Bs0), Items0, func(sum, L, R, Ps, Bs), Items),
    once(weakened_first_check(Bs0, Bs, Weak)),
    cq(Weak, C),
    catch(( valid_module(module(Items)) -> Verdict0 = accepted ; Verdict0 = failed ),
          nanofil_error(Msg), Verdict0 = Msg),
    format(string(Verdict), "~w~n", [Verdict0]).
stage(abi, File, [I1, I2]) :-
    wrap_predicate(filc_abi:lower_function(Po, S, F, Li, P), guide, W,
                   ( W, ( F = func(sum, _, _, _, _) -> assertz(seen(abi, P)) ; true ) )),
    checked(File, C),
    once(filc_module_asm(C, stack, _, _)),
    once(seen(abi, abi_function(_, _, _, _, Frame, Entry, _, _, _, _))),
    t(Frame, I1), t(Entry, I2),
    ignore((Po, S, Li) = (_, _, _)).
stage(homes, File, Items) :-
    wrap_predicate(amd64_regs:regs_asm(Mode, Meta, B, A, Checked, Report), guide, W,
                   ( W, ( Mode \== map -> assertz(seen(regs, Meta-Checked-Report)) ; true ) )),
    renewed(File, C),
    once(filc_module_asm(C, emit(pointers, selected, inline), _, _)),
    once(seen(regs, regs_metadata(_, Impl, Homes, _)-checked(_, Map)-Report)),
    Impl == pizlonatedFIP1066_sum,
    cq(Report, R),
    findall(I, ( member(home(D, Ks), Homes), home_item(home(D, Ks), Map, I) ), Is),
    findall(Text-note(root(D, N), 'the frame record, never a home'),
            ( member(root(D, N), Homes),
              format(string(Text), "~q: the frame record, never a home~n", [root(D, N)]) ),
            Rs),
    append([[R], Is, Rs], Items),
    ignore((B, A) = (_, _)).

home_item(H, Map, Text-term(H -> Reg)) :-
    H = home(D, _), memberchk(D-Reg, Map), !,
    format(string(Text), "~q -> ~w~n", [H, Reg]).
home_item(H, _, Text-note(H, 'stays in the frame')) :-
    format(string(Text), "~q stays in the frame~n", [H]).

% weakened_first_check(+Blocks0, -Blocks, -Weak): the first check before
% a raw load covers 2 bytes less than the load reads; Weak is the
% weakened instruction.
weakened_first_check(Bs0, Bs, let(Q, a, check(Lo, Hi, Rights, Al), [P])) :-
    append(Pre, [block(L, Phis, Is0, J)|Post], Bs0),
    append(Before, [let(Q, a, check(Lo, Hi0, Rights, Al), [P]),
                    Load|After], Is0),
    Load = let(_, _, raw_load(_, _), _),
    !,
    Hi is Hi0 - 2,
    append(Before, [let(Q, a, check(Lo, Hi, Rights, Al), [P]), Load|After], Is),
    append(Pre, [block(L, Phis, Is, J)|Post], Bs).

% sum_items(+Module, -Items): Module's function sum, printed as
% print_module/1 prints it.
sum_items(module(Items), [Text-term(F)]) :-
    memberchk(F, Items), F = func(sum, _, _, _, _), !,
    with_output_to(string(Text), print_module(module([F]))).

term(T) :-
    print_term(T, [right_margin(72), tab_width(0), output(current_output)]),
    write('.'), nl.
