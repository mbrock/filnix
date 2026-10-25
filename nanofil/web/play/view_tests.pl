/* Public UI contracts: rendered HTML and the playground's queries.
   Run: /tmp/swipl/bin/swipl -q -s nanofil/web/play/view_tests.pl -g run_tests -t halt </dev/null
   Synthetic records exercise edge cases; workbench fixtures are actual
   compiler output. No assertion depends on the renderer's private view. */
:- encoding(utf8).
:- asserta((user:term_expansion((:- initialization(main, main)), []) :-
               prolog_load_context(module, dterm))).
:- use_module('../dterm').
:- use_module(play_view).
:- use_module(library(plunit)).
:- use_module(library(readutil)).
:- use_module(library(sgml)).
:- consult('../workbench/samples').
:- prolog_load_context(directory, Dir), assertz(test_directory(Dir)).

:- begin_tests(play_view).

render(File, M, DOM) :-
    phrase(ir_module(ir, File, M), Cs), string_codes(H, Cs),
    setup_call_cleanup(open_string(H, S), load_html(stream(S), DOM, []), close(S)).
value_node(DOM, Raw, Attrs, Children) :-
    sub_term(element(_, Attrs, Children), DOM), memberchk('data-tmp'=Raw, Attrs), !.
has(Text, Part) :- sub_string(Text, _, _, _, Part), !.
has_class(Attrs, Class) :- memberchk(class=Classes, Attrs), atomic_list_concat(Words, ' ', Classes), memberchk(Class, Words).
goal_lines(DOM, Lines) :-
    findall(L, ( sub_term(element(_, Attrs, _), DOM), has_class(Attrs, goal),
                 memberchk('data-line'=L, Attrs) ), Lines).
% A single setup seam supplies a completed compile, without running clang
% or needing the frozen browser preprocessor profile. Assertions below
% use only public rendering/query results.
compiled(File, M) :- play_view:remember(File, [term(ir, M)]).
fixture(Stage, module([F, context(sum, Rs)])) :-
    test_directory(Dir), format(atom(Rel), '../workbench/sum-~w.ir', [Stage]),
    directory_file_path(Dir, Rel, Path), read_file_to_terms(Path, Items, []),
    F = func(sum, _, _, _, _), memberchk(F, Items), memberchk(context(sum, Rs), Items).

test(names_subscripts_types_and_identity_survive_removed_definitions) :-
    Rs = [binding(a, x2, schar, none), binding(b, x2, int, none), binding(global(g), g, int, none),
          origin(derived(expr, 1), at('a.c', 5), typed(val, int, load), []),
          value(old, named(a, value), []),
          history(displaced, chk3, named(a, value), [], replaced(const(0))),
          value(v12, named(a, value), [derived(expr, 1)]), value(chk3, none, []),
          value(v13, named(b, value), []), value(v4, named(a, address), []),
          value(v5, named(a, piece), []), value(v6, named(global(g), address), []),
          alias(old, tmp(v12), named(a, value), [])],
    Params = [param(w, tmp(v12)), param(w, tmp(v13)), param(p, tmp(v4)),
              param(w, tmp(v5)), param(a, tmp(chk3)), param(p, tmp(v6))],
    F0 = func(f, local, w, [param(w, tmp(old))|Params], [block(start, [], [], ret(tmp(v12)))]),
    F1 = func(f, local, w, Params, [block(start, [], [
        local_load(tmp(part), w, sw, local, 0), flight(tmp(ptr), copy, [const(0)], none)
    ], ret(tmp(v12)))]),
    render('a.c', module([F0, context(f, Rs)]), Before),
    render('a.c', module([F1, context(f, Rs)]), After),
    value_node(Before, v12, _, Display), value_node(After, v12, Attrs, Display),
    assertion(memberchk(x2, Display)), assertion(memberchk(element(sub, [], ['2']), Display)),
    assertion(memberchk('data-binding'=a, Attrs)),
    memberchk(title=Tip, Attrs), has(Tip, "IR class: w"),
    has(Tip, "C expression type: int"), has(Tip, "C binding type: schar"),
    value_node(After, v13, ShadowAttrs, Shadow),
    assertion(memberchk('data-binding'=b, ShadowAttrs)), assertion(Shadow \== Display),
    value_node(After, v4, AddressAttrs, Address), assertion(memberchk('data-role'=address, AddressAttrs)),
    assertion(memberchk(element(sub, [], ['0']), Address)),
    memberchk(title=AddressTip, AddressAttrs), has(AddressTip, "IR class: p"), has(AddressTip, "C binding type: schar"),
    value_node(After, v5, PieceAttrs, _), assertion(memberchk('data-role'=piece, PieceAttrs)),
    value_node(After, chk3, ReusedAttrs, Reused), assertion(memberchk('data-role'=temporary, ReusedAttrs)),
    assertion(memberchk(element(sub, [], ['3']), Reused)),
    value_node(After, v6, GlobalAttrs, _), assertion(memberchk('data-binding'='global(g)', GlobalAttrs)),
    value_node(After, part, PartAttrs, _), memberchk(title=PartTip, PartAttrs), has(PartTip, "IR class: w"),
    value_node(After, ptr, PtrAttrs, _), memberchk(title=PtrTip, PtrAttrs), has(PtrTip, "IR class: p").

test(raw_numeric_ids_have_subscripts_and_handwritten_ids_remain_intact) :-
    Raws = [v12, chk3, 'pr.2', custom_007, 'odd"<&', plain, '123'],
    findall(param(w, tmp(Raw)), member(Raw, Raws), Params),
    render('absent.c', module([func(f, local, void, Params, [block(start, [], [], ret)])]), DOM),
    forall(member(Raw-Number, [v12-'12', chk3-'3', 'pr.2'-'2', custom_007-'007']),
           ( value_node(DOM, Raw, _, Children), assertion(memberchk(element(sub, [], [Number]), Children)) )),
    forall(member(Raw, ['odd"<&', plain, '123']),
           ( value_node(DOM, Raw, _, Children), assertion(memberchk(Raw, Children)),
             assertion(\+ member(element(sub, _, _), Children)) )).

test(context_is_not_an_executable_item_definition_or_import) :-
    Call = call(void, global(real), []),
    F = func(f, local, void, [], [block(start, [], [Call], ret)]),
    Rs = [binding(global(phantom), phantom, int, none),
          origin(o, none, typed(val, int, call(void, global(ghost), [])), []),
          origin(o2, none, typed(val, int, Call), [])],
    M = module([F, context(f, Rs)]), render('a.c', M, DOM),
    assertion(\+ sub_term(phantom, DOM)), assertion(\+ sub_term(ghost, DOM)),
    compiled('a.c', M), play_symbol(f, Function), assertion(Function.kind == function),
    play_symbol(real, Import), assertion(Import.calls == 1),
    assertion(\+ play_symbol(phantom, _)), assertion(\+ play_symbol(ghost, _)).

test(source_queries_and_rows_agree_without_claiming_ambiguous_lines) :-
    Rs = [origin(fn, at('a.c', 1), statement(function), []),
          origin(o, at('a.c', 5), typed(val, int, add), [fn]),
          origin(h, at('h.h', 5), statement(return), []),
          origin(other, at('a.c', 6), statement(return), []),
          origin(g, none, generated(pizlonate, check), [o]),
          site(phi(p), [g]), site(inst(start, 1), [o]),
          site(inst(start, 2), [o, h]), site(inst(start, 3), [o, missing]), site(jump(start), [o, other])],
    F = func(f, local, w, [], [
          block(old, [], [loc('a.c', 2), let(tmp(v0), w, copy, [const(0)])], goto(start)),
          block(start, [phi(tmp(p), w, [old-tmp(v0)])],
                [loc('a.c', 99), let(tmp(v1), w, copy, [tmp(p)]),
                 let(tmp(v2), w, copy, [tmp(v1)]), let(tmp(v3), w, copy, [tmp(v2)])], ret(tmp(v3)))]),
    M = module([F, context(f, Rs)]), render('a.c', M, DOM), goal_lines(DOM, Lines),
    assertion(Lines == ['2', '2', '5', '5']),
    compiled('a.c', M), play_lines(Counts),
    findall(L-N, ( member(C, Counts), L = C.line, N = C.n ), Pairs), assertion(Pairs == [2-2, 5-2]).

test(source_context_is_sparse_and_preserves_literal_text) :-
    tmp_file_stream(text, File, S), format(S, '    puts("a  b");~n', []), close(S),
    setup_call_cleanup(true, (
        Rs = [origin(o, at(File, 1), statement(return), []),
              site(inst(start, 0), [o]), site(inst(start, 1), [o]), site(jump(start), [o])],
        F = func(f, local, w, [], [block(start, [],
                 [let(tmp(v0), w, copy, [const(0)]), let(tmp(v1), w, copy, [tmp(v0)])], ret(tmp(v1)))]),
        render(File, module([F, context(f, Rs)]), DOM),
        findall(Body, ( sub_term(element(_, Attrs, Body), DOM), has_class(Attrs, 'source-hint') ), Hints),
        assertion(Hints = [_]), assertion(sub_term(element(code, _, ['puts("a  b");']), Hints)),
        goal_lines(DOM, Lines), assertion(Lines == ['1', '1', '1'])
    ), delete_file(File)).

test(real_compiler_fixtures_and_metadata_free_sample_share_renderer) :-
    fixture(o0, M0), fixture(o1, M1),
    render('../play/examples/sum.c', M0, Before), render('../play/examples/sum.c', M1, After),
    % Surviving compiler identities keep their visible spelling/subscript.
    findall(Raw, ( sub_term(element(_, Attrs, _), After), memberchk('data-tmp'=Raw, Attrs),
                   value_node(Before, Raw, _, _) ), Raws0), sort(Raws0, Raws),
    assertion(Raws \== []),
    forall(member(Raw, Raws), ( value_node(Before, Raw, _, Display), value_node(After, Raw, _, Display) )),
    compiled('../play/examples/sum.c', M1), play_lines(Counts),
    assertion(( member(C, Counts), get_dict(line, C, 5), get_dict(n, C, N), N > 0 )),
    goal_lines(After, Lines), assertion(memberchk('5', Lines)),
    sample_ir(F), render('absent.c', module([F]), Plain),
    value_node(Plain, v22, PlainAttrs, PlainDisplay),
    assertion(memberchk('data-role'=temporary, PlainAttrs)),
    assertion(memberchk(element(sub, [], ['22']), PlainDisplay)).

:- end_tests(play_view).
