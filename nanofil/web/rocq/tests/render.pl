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

% A theories page sees only theories names and its own; a glibc page's
% name such as Section lookup must not capture Term.v's lookup.
test(page_scope) :-
    assertion(\+ rocq_draw:page_in_scope('rocq-theories-soundness-Evidence', 'rocq-glibc-stdio-ErrlistEnoent')),
    assertion(rocq_draw:page_in_scope('rocq-glibc-stdio-ErrlistEnoent', 'rocq-glibc-zsys-OsWorld')),
    assertion(rocq_draw:page_in_scope('rocq-glibc-stdio-ErrlistEnoent', 'rocq-theories-core-Term')).

% In t; [a | b.. | c], b.. covers the goals between a's and c's.
test(dispatch_rest) :-
    string_codes("Goal True /\\ True. Proof. split; [done..|]. Qed.", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    Items = [proved(_, pf([step(_, _, Ts)|_], _))],
    rocq_syntax:rocq_tactic_tokens(Ts, T),
    assertion(T = dispatch(call(split, []), [rest(call(done, [])), empty])).

% Rocq 9.2 deprecates Notation x := t for Abbreviation x := t.
test(abbreviation) :-
    string_codes("Abbreviation twice f x := (f (f x)) (only parsing).", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [notation(_, 'Abbreviation', "twice f x", paren(_, app(_, id(_, f), _)), ['(', only, parsing, ')'])]).

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

% The glibc code generator writes the name of a temporary between single
% guillemets. The name is one token whatever symbols it holds, so chk(buf+8)
% inside it is not an application and -> is not an arrow.
test(quoted_temporary_name) :-
    string_codes("Lemma a (e : env) : lookup ‹chk(buf+8)@L4› e = lookup ‹s->_lock› e.", Cs),
    rocq_syntax:rocq_parse_codes(Cs, Items, _),
    assertion(Items = [proved(thm(_, 'Lemma', _, _,
        bin(_, =, app(_, id(_, lookup), [id(_, '‹chk(buf+8)@L4›'), id(_, e)]),
                  app(_, id(_, lookup), [id(_, '‹s->_lock›'), id(_, e)]))), _)]),
    fence_dom(["Lemma a (e : env) : lookup ‹chk(buf+8)@L4› e = lookup ‹s->_lock› e.", "Proof.", "Admitted."], DOM),
    assertion(sub_term(element(span, [class=g], ['‹chk(buf+8)@L4›']), DOM)),
    assertion(sub_term(element(span, [class=g], ['‹s->_lock›']), DOM)),
    assertion(\+ ( sub_term(element(_, As, _), DOM), memberchk(class=C, As), sub_atom(C, _, _, _, unparsed) )).

% IRNotation functions draw as structured block grids with role colours,
% badges, temporary subscripts, block anchors and Fil-C safety markers.
test(ir_notation_function) :-
    fence_dom([
        "Definition f : func :=",
        "  ir_fn{ \"export\" \"scan\"(P %\"buf\", L %\"len\") -> (RClass W) {",
        "  @\"start\":",
        "    %\"base\" = %\"buf\" +p %\"len\";",
        "    (Flight (a \"v23\") Sub [(FAddress (t \"base\")); (FValue (Const 16))] (LowerOf (t \"base\")));",
        "    %\"chk0\" : A = (Check 0 1 Read 1) %\"v23\";",
        "    %\"b\" : W = (RawLoad (LdNarrow Ub) 0) %\"chk0\";",
        "    store Ww [%\"chk0\" + 0] <- %\"b\";",
        "    call %\"r\" : W = $\"helper\"(W %\"b\")",
        "    => goto poll \"loop\";",
        "  @\"loop\" [%\"k\" : L = phi(\"start\" => #0, \"loop\" => %\"k1\")]:",
        "    %\"k1\" : L = Add %\"k\", #1;",
        "    %\"done\" : W = (Cmp Eq L) %\"k\", %\"len\"",
        "    => br %\"done\" ? \"exit\" : \"loop\";",
        "  @\"exit\":",
        "    => ret %\"r\"",
        "} }."
    ], DOM),
    assertion(( sub_term(element(div, As, _), DOM), memberchk(class='rq-ir rq-ir-fn', As) )),
    findall(L, ( sub_term(element(div, BAs, _), DOM), memberchk(class='rq-ir-label', BAs),
                 memberchk('data-ir-label'=L, BAs) ), Labels),
    assertion(Labels == [start, loop, exit]),
    % Block jump targets link to their block anchors within the function.
    assertion(( sub_term(element(a, LAs, _), DOM), memberchk(class='rq-ir-lbl', LAs),
                memberchk('data-ir-label'=loop, LAs), memberchk(href=Href, LAs),
                sub_atom(Href, 0, 1, _, '#') )),
    % Check, RawLoad, RawStore and poll rows carry the safety margin marker.
    findall(C, ( sub_term(element(div, RAs, _), DOM), memberchk(class=C, RAs),
                 sub_atom(C, _, _, _, ' pz') ), PzRows),
    assertion(length(PzRows, 4)),
    % Temporaries carry data-v with trailing digits subscripted (k1 -> k sub 1).
    assertion(( sub_term(element(span, TAs, Kids), DOM), memberchk('data-v'='%k1', TAs),
                memberchk('data-tmp'=k1, TAs), sub_term(element(sub, [], ['1']), Kids) )),
    % LHS wraps temp and class so dterm.js breaks after = rather than after :.
    assertion(( sub_term(element(span, [class='rq-ir-lhs'], _), DOM) )),
    % Compound ops unwrap outer parens and badges; Flight Sub escape formats as -p.
    assertion(( sub_term(element(span, CAs, ['Check']), DOM), memberchk(class='rq-ir-op-check', CAs) )),
    assertion(( sub_term(element(span, MAs, ['RawLoad']), DOM), memberchk(class='rq-ir-op-memory', MAs) )),
    assertion(( sub_term(element(span, BAs2, ['Ub']), DOM), memberchk(class='rq-ir-type', BAs2) )),
    assertion(( sub_term(element(span, FAs, ['−p']), DOM), memberchk(class='op wide rq-ir-op', FAs) )),
    assertion(( sub_term(element(span, GAs, _), DOM), memberchk(class='rq-ir-global', GAs) )).

% Standalone ir_blk, ir[...] and inline ir{...} forms parse and draw cleanly.
test(ir_notation_forms) :-
    fence_dom([
        "Definition blk : block := ir_blk{ @\"entry\": alloca \"x\" 8 => ret void }.",
        "Definition seq : list inst := ir[ %\"v0\" : W = Add #1, #2; store.ptr [%\"p\" + 0] <- %\"q\" ].",
        "Definition one : inst := ir{ rawcall void %\"fn\"() }."
    ], DOM),
    assertion(( sub_term(element(div, As1, _), DOM), memberchk(class='rq-ir rq-ir-blk', As1) )),
    assertion(( sub_term(element(div, As2, _), DOM), memberchk(class='rq-ir rq-ir-seq', As2) )),
    assertion(( sub_term(element(span, As3, _), DOM), memberchk(class='rq-ir-inline', As3) )),
    assertion(\+ ( sub_term(element(pre, As4, _), DOM), memberchk(class='rq-raw', As4) )).

fence_dom(Lines, DOM) :-
    call_with_time_limit(2, phrase(rocq_fence(Lines), Codes)),
    string_codes(Html, Codes),
    setup_call_cleanup(open_string(Html, Stream),
      load_html(stream(Stream), DOM, []), close(Stream)).

text_of(DOM, Text) :-
    findall(A, ( sub_term(A, DOM), atom(A), \+ sub_term(_=A, DOM) ), As),
    atomic_list_concat(As, Text).

:- end_tests(rocq_render).
