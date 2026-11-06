/*  Mutants of a checked module, judged by ir:valid_module/1, for the
    Rocq model's validator gate (docs/rocq.md, rocq/valid.sh).

    Reads `nanofil outcomes FILE`'s output on stdin and keeps its first
    term, the checked module, without its context(_, _) items. Prints that
    module, then verdict(Fn, Id, Func, Verdict) for each function Fn of
    it: Id is base for the function as it is, or a mutation; Func is
    the function after it; Verdict is valid when valid_module/1 accepts
    the module with Func in place of Fn, else invalid. Run from
    nanofil/src:

      ../bin/nanofil outcomes FILE | ../bin/nanofil --script ../rocq/mutants.pl

    The mutations aim at what the validator decides: a check deleted or
    moved from its access, a check narrowed or its rights or alignment
    changed, a raw access moved, a poll edge removed, a free inserted
    between evidence and its use, a reuse form given another proof. At
    most 150 per function are kept, evenly spaced.
*/
:- use_module('../src/ir').
:- use_module('../src/provenance', [code_items/2]).
:- use_module(library(lists)).

:- initialization(main).

main :-
    read_term(user_input, module(All), []),
    code_items(All, Items),
    M = module(Items),
    format("~k.~n", [M]),
    forall(member(func(Fn, Lk, Ret, Ps, Bs), Items),
           ( F = func(Fn, Lk, Ret, Ps, Bs),
             findall(Id-F1, mutant(F, Id, F1), Ms0),
             thin(Ms0, 150, Ms),
             forall(member(Id-F1, [base-F|Ms]),
                    ( verdict(Items, F, F1, V),
                      format("~k.~n", [verdict(Fn, Id, F1, V)]) )) )),
    halt.

verdict(Items, F, F1, V) :-
    maplist(replaced(F, F1), Items, Items1),
    (   catch(once(valid_module(module(Items1))), _, fail) -> V = valid ; V = invalid ).

replaced(F, F1, I, I1) :- ( I == F -> I1 = F1 ; I1 = I ).

% thin(+Xs, +N, -Ys): at most N of Xs, evenly spaced.
thin(Xs, N, Ys) :-
    length(Xs, L),
    (   L =< N -> Ys = Xs
    ;   Step is (L + N - 1) // N,
        findall(X, ( nth0(I, Xs, X), I mod Step =:= 0 ), Ys)
    ).

% mutant(+F, -Id, -F1): F1 is F mutated as Id says.
mutant(F, Id, F1) :-
    F = func(Fn, Lk, Ret, Ps, Bs),
    nth0(B, Bs, block(L, Phis, Is, J)),
    block_mutant(Is, J, F, Id0, Is1, J1),
    Id = at(L, Id0),
    nth0(B, Bs, _, Rest), nth0(B, Bs1, block(L, Phis, Is1, J1), Rest),
    F1 = func(Fn, Lk, Ret, Ps, Bs1).

block_mutant(Is, J, _, delete(I), Is1, J) :-
    nth0(I, Is, _, Is1).
block_mutant(Is, J, _, swap(I), Is1, J) :-
    append(Pre, [A, B|Post], Is), length(Pre, I),
    append(Pre, [B, A|Post], Is1).
block_mutant(Is, J, _, Id, Is1, J) :-
    nth0(I, Is, Inst, Rest),
    inst_mutant(Inst, Id0, Inst1),
    Id = change(I, Id0),
    nth0(I, Is1, Inst1, Rest).
block_mutant(Is, J, _, free(I), Is1, J) :-
    nth0(I, Is, _),
    nth0(I, Is1, call(void, global(free), [arg(p, const(0))]), Is).
block_mutant(Is, J, F, Id, Is1, J) :-
    nth0(I, Is, let(D, a, Op, [tmp(Q1)|Args]), Rest),
    memberchk(Op, [renew(_, _, _, _), half_check(_, _, _, _, _), renew_hull(_, _, _, _)]),
    other_proof(F, Q1, Q2),
    Id = reprove(I, Q2),
    nth0(I, Is1, let(D, a, Op, [tmp(Q2)|Args]), Rest).
block_mutant(Is, J, _, unpoll, Is, J1) :-
    jump_unpolled(J, J1).

jump_unpolled(goto(poll(L)), goto(L)).
jump_unpolled(branch(V, poll(L), T), branch(V, L, T)).
jump_unpolled(branch(V, T, poll(L)), branch(V, T, L)).

other_proof(func(_, _, _, _, Bs), Q1, Q2) :-
    once(( member(block(_, _, Is, _), Bs), member(let(tmp(Q2), a, _, _), Is), Q2 \== Q1 )).

inst_mutant(let(D, a, Op, Args), Id, let(D, a, Op1, Args)) :- check_mutant(Op, Id, Op1).
inst_mutant(let(D, K, raw_load(T, Off), Args), off(Dlt), let(D, K, raw_load(T, Off1), Args)) :-
    member(Dlt, [-1, 1]), Off1 is Off + Dlt.
inst_mutant(raw_store(W, Off, V, A), off(Dlt), raw_store(W, Off1, V, A)) :-
    member(Dlt, [-1, 1]), Off1 is Off + Dlt.

check_mutant(Op, Id, Op1) :-
    Op =.. [Name|Xs], check_bounds(Name, Pre, Xs, Lo, Hi, R, Al, Post),
    (   Lo1 is Lo + 1, Lo1 < Hi, Id = lo, append(Pre, [Lo1, Hi, R, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   Hi1 is Hi - 1, Lo < Hi1, Id = hi, append(Pre, [Lo, Hi1, R, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   flip(R, R1), Id = rights, append(Pre, [Lo, Hi, R1, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   Al < 16, Al1 is Al * 2, Id = align, append(Pre, [Lo, Hi, R, Al1|Post], Pre1), Op1 =.. [Name|Pre1]
    ).

flip(read, write).
flip(write, read).

% check_bounds(+Name, -Pre, +Xs, -Lo, -Hi, -Rights, -Align, -Post): a
% check-like op's arguments around its (Lo, Hi, Rights, Align).
check_bounds(Name, [], [Lo, Hi, R, Al], Lo, Hi, R, Al, []) :-
    memberchk(Name, [check, renew, renew_hull, renew_if, check_limit]).
check_bounds(check_ahead, [], [Lo, Hi, R, Al, AHi], Lo, Hi, R, Al, [AHi]).
check_bounds(half_check, [B], [B, Lo, Hi, R, Al], Lo, Hi, R, Al, []).
