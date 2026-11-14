:- encoding(utf8).
/* Run with swipl -q -s nanofil/web/rocq/tests/render.pl -g run_tests -t halt.
   The public source drawer must draw matches used as Ltac let values,
   whether the body is an inline tactic or another structured match. */
:- use_module('../rocq_draw').
:- use_module(library(plunit)).
:- use_module(library(sgml)).

:- begin_tests(rocq_render).

test(call_spec_inputs) :-
    string_codes("Goal True. Proof. call_spec. call_spec with (b, reg, wa - b, xs). exact I. Qed.", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    Items = [proved(_, pf([step(_, _, Plain), step(_, _, With)|_], _))],
    rocq_syntax:rocq_tactic_tokens(Plain, P),
    rocq_syntax:rocq_tactic_tokens(With, W),
    assertion(P = call(call_spec, [])),
    assertion(W = call(call_spec, [clause(with, [term(tuple(_, [_, _, _, _]))])])).

test(tactic_notation_body) :-
    string_codes("Tactic Notation \"load_cell\" constr(H) \"by\" tactic3(side) := iApply (rule with H); [reflexivity | side |].", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [tacnotation(_, [literal("load_cell"), argument(constr, n(_, 'H')),
        literal("by"), argument(tactic3, n(_, side))], dispatch(_, [_, _, _]))]).

test(singleton_class) :-
    string_codes("Class Defines (g : G) (n : string) (f : F) : Prop := defines : lookup g n = Some f.", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [rec(_, 'Class', n(_, 'Defines'), _, _, singleton,
        [field(_, defines, [], bin(_, =, _, _), none)])]).

test(sealed_module_definition) :-
    fence_dom(["Module R : Runtime := InterpRuntime.", "Module LG0 := Logic R."], DOM),
    assertion(sub_term(element(span, [class='op wide colon'], [':']), DOM)),
    assertion(sub_term('Runtime', DOM)),
    assertion(sub_term('InterpRuntime', DOM)),
    findall(Attrs, (sub_term(element(div, Attrs, _), DOM),
        memberchk(class='clause rq-module-def', Attrs)), Modules),
    assertion(Modules = [_, _]).

test(named_generalizing_binder) :-
    string_codes("Context `{P : !Program (hlc := hlc) Σ} `{H : !Defines ge \"name\" fn}.", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [decl(_, 'Context', [bs([
        b(_, gen('{', [bang(cast(_, id(_, 'P'), app(_, _, _)))]), [], none),
        b(_, gen('{', [bang(cast(_, id(_, 'H'), app(_, _, [_, str(_, "name"), _])))]), [], none)])])]).

test(existing_instances, [forall(member(Prefix, ["", "Local ", "#[global] "]))]) :-
    string_concat(Prefix, "Existing Instance program_heap.", Text),
    string_codes(Text, Cs), rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [dir(_, ['Existing', 'Instance', program_heap])]).

test(recursive_let_and_evaluation) :-
    fence_dom(["Ltac count n := let rec walk x acc := lazymatch x with O => acc | S ?k => walk k constr:(S acc) end in let z := eval vm_compute in (n + 2) in walk z constr:(0)."], DOM),
    assertion(sub_term(element(span, [class=kw], ['let rec']), DOM)),
    assertion(sub_term(element(span, [class=kw], [eval]), DOM)),
    assertion(sub_term(element(span, [class=kw], [lazymatch]), DOM)),
    assertion((sub_term(element(div, Attrs, _), DOM), memberchk(class='clause rq-ltac', Attrs))),
    text_of(DOM, Text),
    assertion(sub_atom(Text, _, _, _, vm_compute)),
    assertion((sub_term(element(span, As, _), DOM), memberchk('data-v'=acc, As))).

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

% Context's generalizing binders are one instance binder per class, set
% without their ` and ! markers, in one group the printer breaks between.
test(context_binders) :-
    fence_dom(["Context `{!invGS_gen hlc Σ, !gen_heapGS L V Σ} {A : Type} (x y : A)."], DOM),
    once(( sub_term(element(span, Attrs, Kids), DOM), memberchk(class='c sig rq-ctx', Attrs) )),
    assertion(memberchk('data-d'=args, Attrs)),
    assertion(Kids = [element(span, [class=kw], ['Context'])|_]),
    findall(C, ( sub_term(element(span, As, _), Kids), memberchk(class=C, As), split_string(C, " ", "", Ws), memberchk("binder", Ws) ), Bs),
    assertion(Bs == ['braces binder rq-inst', 'braces binder rq-inst', 'braces binder', 'paren binder']),
    text_of(Kids, Text),
    assertion(\+ sub_atom(Text, _, _, _, '`')),
    assertion(\+ sub_atom(Text, _, _, _, '!')).

% Print Assumptions is a command row naming its theorem, not raw text.
test(print_assumptions) :-
    fence_dom(["Theorem t : True.", "Proof.", "exact I.", "Qed.", "Print Assumptions t."], DOM),
    assertion(\+ ( sub_term(element(pre, As, _), DOM), memberchk(class='rq-raw', As) )),
    assertion(( sub_term(element(div, As1, _), DOM), memberchk(class='clause rq-cmd', As1) )),
    assertion(( sub_term(element(span, [class=kw], ['Print Assumptions']), DOM) )).

% A file's let? binds a pattern, and a mutual Fixpoint draws each body
% under its own keyword; neither is copied as text.
test(let_question_and_mutual) :-
    fence_dom(["Fixpoint f (n : nat) : nat := match n with O => O | S m => g m end",
               "with g (n : nat) : nat := let? (a, _) := h n in a."], DOM),
    assertion(\+ ( sub_term(element(pre, As, _), DOM), memberchk(class='rq-raw', As) )),
    assertion(sub_term(element(span, [class=kw], ['Fixpoint']), DOM)),
    assertion(sub_term(element(span, [class=kw], [with]), DOM)),
    assertion(sub_term(element(span, [class=kw], ['let?']), DOM)),
    findall(V, ( sub_term(element(span, As1, [V]), DOM), memberchk('data-v'=a, As1) ), Vs),
    assertion(Vs = [_, _|_]).

fence_dom(Lines, DOM) :-
    call_with_time_limit(2, phrase(rocq_fence(Lines), Codes)),
    string_codes(Html, Codes),
    setup_call_cleanup(open_string(Html, Stream),
      load_html(stream(Stream), DOM, []), close(Stream)).

text_of(DOM, Text) :-
    findall(A, ( sub_term(A, DOM), atom(A), \+ sub_term(_=A, DOM) ), As),
    atomic_list_concat(As, Text).

:- end_tests(rocq_render).
