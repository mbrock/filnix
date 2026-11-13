/* Run with swipl -q -s nanofil/web/rocq/tests/render.pl -g run_tests -t halt.
   The public source drawer must draw matches used as Ltac let values,
   whether the body is an inline tactic or another structured match. */
:- use_module('../rocq_draw').
:- use_module(library(plunit)).
:- use_module(library(sgml)).

:- begin_tests(rocq_render).

test(match_in_let_value, [forall(member(Body,
    ["idtac K", "lazymatch type of I with ?Q => idtac K end"]))]) :-
    format(string(Tactic),
      "let K := lazymatch type of I with ?P => P end in ~s.", [Body]),
    call_with_time_limit(2, phrase(rocq_fence(
      ["Goal True.", "Proof.", Tactic, "exact I.", "Qed."]), Codes)),
    string_codes(Html, Codes),
    setup_call_cleanup(open_string(Html, Stream),
      load_html(stream(Stream), DOM, []), close(Stream)),
    assertion((sub_term(element(span, Attrs, _), DOM),
               memberchk(class='rq-tac-match', Attrs))),
    assertion((sub_term(element(span, Attrs, [lazymatch]), DOM),
               memberchk(class=kw, Attrs))),
    assertion(\+ (sub_term(element(_, Attrs, _), DOM),
                   memberchk(class='tactic rq-unparsed', Attrs))),
    assertion((sub_term(element(span, Attrs, ['Qed']), DOM),
               memberchk(class=kw, Attrs))).

:- end_tests(rocq_render).
