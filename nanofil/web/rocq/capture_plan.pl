:- encoding(utf8).
/* Build-time capture plan, using exactly the source renderer's lexer.
   swipl capture_plan.pl FILE.v... emits character-offset command spans
   and the proof states the renderer needs. Bullets/braces are separate
   Rocq commands, not tactics or sentence terminators. */
:- use_module(library(http/json)).
:- use_module(rocq_syntax).
:- initialization(main, main).

main :-
    current_prolog_flag(argv, Files), maplist(plan, Files, Plans),
    json_write_dict(current_output, Plans), nl.

plan(File, _{file:File, commands:Commands, proofs:Proofs}) :-
    rocq_read_file(File, Text, rocq(Items, _)), string_codes(Text, Cs),
    rocq_lex(Cs, Tokens, _), commands(Tokens, Commands),
    findall(P, proof_in(Items, P), Proofs).

commands([], []).
commands(Ts0, [_{start:F, end:T}|Cs]) :-
    Ts0 = [t(_, F, _)|_], rocq_focus_tokens(Ts0, _, T, Ts), !, commands(Ts, Cs).
commands([t(_, F, _)|Ts], [_{start:F, end:T}|Cs]) :-
    append(_, [t(dot, _, T)|Rest], Ts), !, commands(Rest, Cs).

proof_in(Items, P) :- member(I, Items),
    ( I = block(_, Body, _), proof_in(Body, P)
    ; I = proved(S, pf(Steps, qed(_-End, Kind))),
      arg(1, S, _-Start),
      findall(T, member(step(_-T, _, _), Steps), Ends),
      P = _{start:Start, end:End, kind:Kind, steps:Ends}
    ).
