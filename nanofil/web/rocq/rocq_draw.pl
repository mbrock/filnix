:- encoding(utf8).
/*  rocq_draw: Rocq drawn as dterm draws Prolog, by what it is.

    rocq_syntax.pl reads Rocq into terms; this module draws them, for the
    pages of dterm_rocq.pl and for Rocq written inside nanofil's documents
    (dterm_guide.pl's formal.md):

    - an inductive type is a table of its constructors, each with its
      arguments; a relation whose constructors have premises (a step
      relation) is a column of inference rules, premises over a line over
      the conclusion, named by the constructor;
    - a record is a table of its fields;
    - a theorem, an axiom and a lemma are their statement as a rule:
      what is quantified, the hypotheses over the line, the conclusion
      under it; the proof folds under it, a row per tactic, indented by
      its bullets;
    - a definition is its signature over its body; `match` is a table of
      patterns and results, `if` a table of conditions, `let` a binding
      over its body;
    - inline, a term is set as dterm sets Prolog: an application is its
      function and arguments, and dterm.js breaks it at the width it gets
      (data-d=args and data-d=op, as for Prolog and Nix). Rocq's ASCII
      notations are drawn as their glyphs (∀ λ → ∧ ≠ ≤ ×), and a file's
      own infix notation folds the application it abbreviates back into
      it, as Rocq prints it;
    - a bound variable is a variable (hovering it lights up its other
      uses), a name the corpus defines links to its definition, and a
      constructor is drawn as one;
    - comments are where they were written: (** coqdoc *) is prose, its
      `* Heading` a heading and `[term]` a term; (* comments *) are notes,
      or asides beside the line they end. `name/N` and `module.pl` link to
      nanofil's Prolog.
*/
:- module(rocq_draw, [rocq_items//1, rocq_inline//1, rocq_fence//1, rocq_prose//1, rocq_prose_inline//1, rocq_layout//0,
                      rocq_set_source/2, rocq_set_states/1, rocq_index_items/3, rocq_items_names/2,
                      rocq_global/5, rocq_prolog_pred/2, comment_heading/3, comment_prose_lines/2,
                      note_kind/3]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(uri)).
:- use_module(rocq_syntax).
:- use_module('../concepts').
:- prolog_load_context(directory, D), directory_file_path(D, '../c/c_draw.pl', P),
   ( exists_file(P) -> assertz(rocq_c_drawn) ; true ).
:- dynamic rocq_c_drawn/0.
:- if(rocq_c_drawn).
:- use_module('../c/c_draw', [c_fence//1, c_inline//1, c_inline_auto//1]).
:- else.
c_fence(_) --> { fail }.
c_inline(_) --> { fail }.
c_inline_auto(_) --> { fail }.
:- endif.

:- include('../dterm_html').

github('https://github.com/mbrock/filnix/blob/main/').

%  rocq_global(Short, Qualified, Page, Kind, File): a name the drawn files
%  define, on Page (Page.html) at the anchor Qualified. Kind is type,
%  ctor, field, def, lemma, axiom, param or module.
%  rocq_prolog_pred(Name, Module): nanofil's Prolog defines Name in
%  Module.pl, for links from comments (prefix in rq_prolog).
:- dynamic rocq_global/5, rocq_prolog_pred/2.

%% State

%  rocq_set_source(+Text, +Comments): the source the positions are in and
%  the comments still to draw, cm(From, To, Text, Kind).
rocq_set_source(Text, Cms) :-
    nb_setval(rq_text, Text), nb_setval(rq_notes, Cms), nb_setval(rq_mod, []),
    rocq_set_states(none),
    ( nb_current(rq_page, _) -> true ; nb_setval(rq_page, none) ),
    ( nb_current(rq_file, _) -> true ; nb_setval(rq_file, none) ).

%  rocq_set_states(+States): build-time Rocq states keyed by source end
%  offset, or none for unexecuted snippets in prose.
rocq_set_states(States) :- nb_setval(rq_states, States).

src_text(F-T, S) :- nb_getval(rq_text, Text), L is T - F, sub_string(Text, F, L, _, S).

line_of(O, L) :- nb_getval(rq_text, Text), sub_string(Text, 0, O, _, Pre),
    split_string(Pre, "\n", "", Ls), length(Ls, L).

note_kind(Text, cm(F, T, S), cm(F, T, S, Kind)) :-
    sub_string(Text, 0, F, _, Pre),
    % The last line, including an empty one after a newline. Searching
    % every newline for a later one made comment placement quadratic.
    split_string(Pre, "\n", "", Lines), last(Lines, Line),
    ( split_string(Line, "", " \t", [""]) -> Kind = own ; Kind = trailing ).

%% The index of names

%  rocq_index_items(+Page, +File, +Items): assert rocq_global/5 for each
%  name Items define, qualified by the modules they are in.
rocq_index_items(Page, File, Items) :- index_items(Items, [], false, Page, File).

index_items(Is, Mod, InSec, Page, File) :- forall(member(I, Is), index_item(I, Mod, InSec, Page, File)).

index_item(proved(S, _), Mod, InSec, Page, File) :- !, index_item(S, Mod, InSec, Page, File).
%  A section's name is not a name Rocq can refer to, so it is indexed
%  only on its own page: Section lookup in a glibc file must not catch
%  every reference to Term.v's lookup.
index_item(block(module(_, Kind, n(_, N), _, _), Body, _), Mod, InSec, Page, File) :- !,
    ( Kind == section -> K = sec(module) ; K = module ),
    add_global(N, Mod, Page, K, File),
    ( Kind == section -> Mod1 = Mod, InSec1 = true ; append(Mod, [N], Mod1), InSec1 = InSec ),
    index_items(Body, Mod1, InSec1, Page, File).
index_item(S, Mod, InSec, Page, File) :-
    forall(defines(S, N, K0),
           ( ( InSec == true, S = decl(_, _, _) -> K = sec(K0) ; K = K0 ),
             add_global(N, Mod, Page, K, File) )).

add_global(N, Mod, Page, K, File) :-
    qualify(Mod, N, Q),
    ( rocq_global(N, Q, Page, _, _) -> true ; assertz(rocq_global(N, Q, Page, K, File)) ).

qualify([], N, N) :- !.
qualify(Mod, N, Q) :- append(Mod, [N], Ps), atomic_list_concat(Ps, '.', Q).

defines(ind(_, _, Bs), N, K) :- member(ib(n(_, T), _, _, Cs), Bs),
    ( N = T, K = type ; member(ctor(_, N, _, _), Cs), K = ctor ).
defines(rec(_, _, n(_, T), _, _, C, Fs), N, K) :-
    ( N = T, K = type ; C = n(_, N), K = ctor ; member(field(_, N, _, _, _), Fs), K = field ).
defines(def(_, _, n(_, N), _, _, _), N, def).
defines(mutual(_, Ds), N, K) :- member(D, Ds), defines(D, N, K).
defines(tacdef(_, n(_, N), _, _), N, def).
defines(thm(_, _, n(_, N), _, _), N, lemma).
defines(decl(_, Kw, Gs), N, K) :- member(g(Ns, _), Gs), member(n(_, N), Ns),
    ( axiom_kw(Kw) -> K = axiom ; K = param ).

axiom_kw(Kw) :- memberchk(Kw, ['Axiom', 'Axioms', 'Conjecture', 'Hypothesis', 'Hypotheses']).

%  rocq_items_names(+Items, -Names): n(Offset, Name, Anchor, Kind) for the
%  names a page's contents list, in source order.
rocq_items_names(Items, Ns) :- phrase(item_names(Items, []), Ns).

item_names([], _) --> [].
item_names([I|Is], Mod) --> item_name(I, Mod), item_names(Is, Mod).

item_name(proved(S, _), Mod) --> !, item_name(S, Mod).
item_name(block(module(F-_, Kind, n(_, N), _, _), Body, _), Mod) --> !,
    { qualify(Mod, N, Q), ( Kind == section -> Mod1 = Mod ; append(Mod, [N], Mod1) ) },
    [n(F, N, Q, module)], item_names(Body, Mod1).
item_name(S, Mod) --> { arg(1, S, F-_), findall(N-K, ( defines(S, N, K), K \== ctor, K \== field ), NKs) },
    seq_names(NKs, F, Mod).

seq_names([], _, _) --> [].
seq_names([N-K|Ns], F, Mod) --> { qualify(Mod, N, Q) }, [n(F, N, Q, K)], seq_names(Ns, F, Mod).

%  global_href(+Name, -Href, -Kind): Name, as written (maybe qualified),
%  is defined in the corpus.
global_ref(X, Href, Kind) :-
    nb_getval(rq_page, Page), Page \== none,
    (   nb_getval(rq_mod, Mod), qualify(Mod, X, Q0), rocq_global(_, Q0, Page, K0, _) -> Q = Q0, P = Page
    ;   rocq_global(_, X, Page, K0, _) -> Q = X, P = Page
    ;   rocq_global(_, X, P0, K0, _), K0 \= sec(_), page_in_scope(Page, P0) -> Q = X, P = P0
    ;   atom_concat('R.', S0, X), atom_concat('Runtime.', S0, Q),
        rocq_global(S0, Q, P0, K0, _), page_in_scope(Page, P0) -> P = P0
    ;   atomic_list_concat([F, S0], '.', X), atom_concat('-', F, End),
        rocq_global(S0, Q, P0, K0, _), K0 \= sec(_), sub_atom(P0, _, _, 0, End) -> P = P0
    ;   last_part(X, S),
        findall(Q1-P1-K1, ( rocq_global(S, Q1, P1, K1, _), ( P1 == Page ; K1 \= sec(_), page_in_scope(Page, P1) ) ), Hits),
        Hits \== [],
        (   member(Q-Page-K0, Hits) -> P = Page
        ;   page_tree(Page, Tree), Tree \== theories,
            include([_-PT-_]>>(page_tree(PT, T1), T1 == Tree), Hits, TreeHits),
            TreeHits = [Q-P-K0|_], forall(member(_-P1-_, TreeHits), P1 == P) -> true
        ;   Hits = [Q-P-K0|_], forall(member(_-P1-_, Hits), P1 == P)
        )
    ),
    unsec(K0, Kind),
    uri_encoded(fragment, Q, Frag),
    ( P == Page -> format(atom(Href), "#~w", [Frag]) ; format(atom(Href), "~w.html#~w", [P, Frag]) ).

unsec(sec(K), K) :- !.
unsec(K, K).

%  The theories are in scope everywhere; backend, glibc and spikes only in
%  their own directory.
page_in_scope(Page, P) :-
    (   P == Page -> true
    ;   sub_atom(P, 0, _, _, 'rocq-theories-') -> true
    ;   page_tree(Page, Tree), page_tree(P, Tree0), Tree0 == Tree
    ).

%  page_tree(+Page, -Tree): call it with Tree unbound, since the last
%  clause would otherwise put any page in theories.
page_tree(P, backend) :- sub_atom(P, 0, _, _, 'rocq-backend-'), !.
page_tree(P, glibc) :- sub_atom(P, 0, _, _, 'rocq-glibc-'), !.
page_tree(P, spikes) :- sub_atom(P, 0, _, _, 'rocq-spikes-'), !.
page_tree(_, theories).

last_part(X, S) :- atomic_list_concat(Ps, '.', X), last(Ps, S).

%  Constructors of Rocq's library, drawn as constructors.
std_ctor(X) :- memberchk(X, ['None', 'Some', true, false, nil, cons, inl, inr, pair, 'O', 'S', tt, 'I',
                            left, right, 'Eq', 'Lt', 'Gt', 'Z0', 'Zpos', 'Zneg', exist, existT, conj, eq_refl]).
std_type(X) :- memberchk(X, ['Type', 'Prop', 'Set', 'Z', nat, bool, list, option, string, prod, sum, unit,
                            'N', positive, 'True', 'False', eq]).

name_kind(X, K) :- nb_getval(rq_page, P), P \== none, global_ref(X, _, K), !.
name_kind(X, ctor) :- std_ctor(X), !.
name_kind(X, type) :- std_type(X), !.
name_kind(X, ctor) :- nb_getval(rq_page, none), atom_codes(X, [C|_]), between(0'A, 0'Z, C), \+ sub_atom(X, _, _, _, '.'), !.
name_kind(_, other).

is_ctor(X) :- name_kind(X, ctor).

kind_class(ctor, "a").
kind_class(type, "ty").
kind_class(field, "f").
kind_class(def, "f").
kind_class(param, "f").
kind_class(lemma, "lem").
kind_class(axiom, "lem").
kind_class(module, "module").
kind_class(other, "g").

%% Terms

%  term(+E, +Env): E inline; Env the names bound around it.
term(E, Env) --> term_(E, Env), !.

term_(id(_, X), Env) --> name_ref(X, Env).
term_(hole(_), _) --> el(span, "v anon", [title="_"], "_").
term_(meta(_, X), _) --> el(span, "rq-meta", ( "?", var_def(X) )).
term_(ltac(_, T), Env) --> { tactic_structural(T) }, !, kw("ltac:"), "(", tactic_block(T, Env), ")".
term_(ltac(_, T), Env) --> kw("ltac:"), el(span, paren, tactic_inline(T, Env)).
term_(num(_, N), _) --> el(span, n, esc(N)).
term_(str(_, S), _) --> el(span, s, ( "\"", esc(S), "\"" )).
term_(explicit(_, X), Env) --> el(span, explicit, ( el(span, at, "@"), name_ref(X, Env) )).
term_(app(P, id(_, F), [A, B]), Env) --> { notation_fold(F, 2, Op) }, !, term(bin(P, Op, A, B), Env).
term_(app(_, F, As), Env) -->
    el(span, "c app", ['data-d'=args], ( head_(F, Env), el(span, args, items(As, Env)) )).
%  2 ^ 48 as a power: a caret beside ∧ reads as a conjunction.
term_(bin(_, '^', L, R), Env) --> { R = num(_, _) ; R = id(_, _) }, !,
    el(span, "o rq-pow", [title="^"], ( term(L, Env), el(sup, "rq-exp", term(R, Env)) )).
term_(bin(_, Op, L, R), Env) -->
    el(span, o, ['data-d'=op], ( term(L, Env), "\u00A0", op_(Op), " ", term(R, Env) )).
term_(chain(_, [O1, O2], [A, B, C]), Env) -->
    el(span, o, ['data-d'=op], ( term(A, Env), "\u00A0", op_(O1), " ", term(B, Env), "\u00A0", op_(O2), " ", term(C, Env) )).
term_(pre(_, Op, E), Env) --> { spaced_prefix(Op) }, !, el(span, "o pre", ( op_(Op), "\u00A0", term(E, Env) )).
term_(pre(_, Op, E), Env) --> el(span, "o pre", ( op_(Op), term(E, Env) )).
term_(paren(_, E), Env) --> el(span, paren, term(E, Env)).
term_(cast(_, E, T), Env) -->
    el(span, paren, ( term(E, Env), "\u00A0", el(span, "op wide", [title=":"], ":"), " ", term(T, Env) )).
term_(tuple(_, Es), Env) --> el(span, "c tuple", ['data-d'=args], el(span, args, sep_items(Es, Env, ","))).
term_(forall(_, Bs, B), Env) --> quant("∀", forall, Bs, ",", B, Env).
term_(exists(_, Bs, B), Env) --> quant("∃", exists, Bs, ",", B, Env).
term_(fun(_, Bs, B), Env) --> quant("λ", fun, Bs, "\u00A0⇒", B, Env).
term_(let(_, Lhs, Ty, V, B), Env) -->
    { lhs_names(Lhs, Ns), append(Ns, Env, Env1) },
    el(span, "o let", ( kw("let"), " ", lhs_(Lhs, Env, Env1), opt_type(Ty, Env), "\u00A0", defeq, " ", term(V, Env), " ",
                        kw("in"), " ", term(B, Env1) )).
term_(letstar(_, n(_, X), V, B), Env) -->
    el(span, "o let", ( kw("let*"), " ", var_def(X), "\u00A0", defeq, " ", term(V, Env), " ", kw("in"), " ", term(B, [X|Env]) )).
term_(letpat(_, Pat, V, B), Env) -->
    { alts_vars([[Pat]], Vs), append(Vs, Env, Env1) },
    el(span, "o let", ( kw("let"), " ", el(span, tick, "'"), term(Pat, Env1), "\u00A0", defeq, " ", term(V, Env), " ",
                        kw("in"), " ", term(B, Env1) )).
term_(letq(_, Pat, V, B), Env) -->
    { alts_vars([[Pat]], Vs), append(Vs, Env, Env1) },
    el(span, "o let", ( kw("let?"), " ", term(Pat, Env1), "\u00A0", defeq, " ", term(V, Env), " ",
                        kw("in"), " ", term(B, Env1) )).
term_(letfix(_, n(_, F), Bs, Ty, V, B), Env) -->
    { binders_env(Bs, [F|Env], EnvV) },
    el(span, "o let", ( kw("let fix"), " ", var_def(F), binders_(Bs, Env), opt_type(Ty, EnvV), "\u00A0", defeq, " ",
                        term(V, EnvV), " ", kw("in"), " ", term(B, [F|Env]) )).
term_(fix(_, n(_, F), Bs, Ty, B), Env) -->
    { binders_env(Bs, [F|Env], EnvB) },
    el(span, "o let", ( kw("fix"), " ", var_def(F), binders_(Bs, Env), opt_type(Ty, EnvB), "\u00A0", defeq, " ",
                        term(B, EnvB) )).
term_(named(_, X, E), Env) --> el(span, "paren rq-named", ( el(span, "rq-arg-name", esc(X)), "\u00A0", defeq, " ", term(E, Env) )).
term_(aspat(_, P, n(_, X)), Env) --> term(P, Env), " ", kw("as"), " ", var_def(X).
term_(bits(_, E, Ds), Env) -->
    { atom_chars(Ds, Cs), foldl([C, S0, S]>>atomic_list_concat([S0, '~', C], S), Cs, '', Text) },
    term(E, Env), el(span, "rq-bits", [title="a positive's binary digits: p~0 is 2p, p~1 is 2p + 1"], esc(Text)).
term_(orpat(_, Ps), Env) --> el(span, paren, bar_items(Ps, Env)).
term_(ifis(_, C, P, T, E), Env) -->
    el(span, "o if", ( kw("if"), " ", term(C, Env), " ", kw("is"), " ", term(P, Env), " ", kw("then"), " ", term(T, Env),
                       " ", kw("else"), " ", term(E, Env) )).
term_(if(_, C, T, E), Env) -->
    el(span, "o if", ( kw("if"), " ", term(C, Env), " ", kw("then"), " ", term(T, Env), " ", kw("else"), " ", term(E, Env) )).
term_(match(_, Ss, _, Brs), Env) -->
    el(span, "o match", ( kw("match"), " ", scrutinees(Ss, Env), " ", kw("with"), " ",
                          inline_branches(Brs, Env), " ", kw("end") )).
term_(list(_, []), _) --> el(span, "l empty", "[ ]").
term_(list(_, Es), Env) --> el(span, l, ['data-d'=args], sep_items(Es, Env, ";")).
term_(record(_, Fs), Env) --> el(span, "c rec", ['data-d'=args], el(span, "args recbr", rec_fields(Fs, Env))).
term_(scope(_, E, K), Env) --> term(E, Env), el(span, scope, [title="scope"], ( "%", esc(K) )).
term_(mixfix(_, Parts), Env) --> seq(Parts, mixfix_part(Env)).
term_(ir_inst(_, I), Env) --> el(span, "rq-ir-inline", ir_ssa_draw(I, Env)).
term_(ir_list(_, Is), Env) -->
    el(span, "c rq-ir-inline rq-ir-inline-list", ['data-d'=args],
       el(span, "args l", ir_inline_ssa_items(Is, Env))).
term_(ir_blk(_, B), Env) --> el(span, "rq-ir-inline rq-ir-inline-blk", ir_blk_inline(B, Env)).
term_(ir_fn(_, Lk, Name, Ps, Ret, Bs), Env) -->
    el(span, "rq-ir-inline rq-ir-inline-fn", ir_fn_inline(Lk, Name, Ps, Ret, Bs, Env)).
term_(braces(_, E), Env) --> el(span, braces, term(E, Env)).
term_(sig(_, n(_, X), T, Q), Env) -->
    el(span, "braces sig", ( var_def(X), "\u00A0", el(span, "op wide", ":"), " ", term(T, Env), " ",
                             el(span, "op wide", "|"), " ", term(Q, [X|Env]) )).

%  Iris, set as its papers set it: an update's masks around its arrow, a
%  weakest precondition's mask under WP and its postcondition in braces,
%  a big operator's binders under the operator.
term_(pure(_, E), Env) --> el(span, "rq-pure", ( el(span, "op", "⌜"), term(E, Env), el(span, "op", "⌝") )).
term_(const(_, C), _) --> el(span, "rq-const", esc(C)).
term_(unit(_), _) --> el(span, a, "()").
term_(insert(_, K, V), Env) -->
    el(span, "rq-insert", ( el(span, op, "<["), term(K, Env), "\u00A0", defeq, " ", term(V, Env), el(span, op, "]>") )).
term_(proj(_, E, Op), Env) --> term(E, Env), el(span, "rq-proj", [title=Op], esc(Op)).
term_(gfunctors(_, Es), Env) --> el(span, "rq-gfunctors", ( el(span, op, "#"), term(list(0-0, Es), Env) )).
term_(fupd(_, Ms, A), Env) --> el(span, "o pre rq-upd", ( update(Ms, "|⇛", Env), "\u00A0", term(A, Env) )).
term_(laterN(_, N, A), Env) --> el(span, "o pre", ( el(span, op, step_later(N, Env)), term(A, Env) )).
term_(stepupd(_, Ms, N, A), Env) -->
    el(span, "o pre rq-upd", ( update(Ms, "|⇛", step_later(N, Env), Env), "\u00A0", term(A, Env) )).
term_(stepupdw(_, Ms, N, L, R), Env) -->
    el(span, o, ['data-d'=op], ( term(L, Env), "\u00A0", update(Ms, "⇛", step_later(N, Env), Env), " ", term(R, Env) )).
term_(fupdw(_, Ms, L, R), Env) -->
    el(span, o, ['data-d'=op], ( term(L, Env), "\u00A0", update(Ms, "⇛", Env), " ", term(R, Env) )).
term_(pointsto(_, Op, L, Ms, R), Env) -->
    el(span, o, ['data-d'=op], ( term(L, Env), "\u00A0", el(span, "op wide rq-pointsto", [title=Op], ( esc(Op), seq(Ms, pointsto_mod(Env)) )),
                                 " ", term(R, Env) )).
term_(indexed(_, Op, N, none, A), Env) --> !,
    el(span, "o pre", ( el(span, op, ( esc(Op), el(sub, none, term(N, Env)) )), "\u00A0", term(A, Env) )).
term_(indexed(_, Op, N, L, R), Env) -->
    el(span, o, ['data-d'=op], ( term(L, Env), "\u00A0", el(span, "op wide", ( esc(Op), el(sub, none, term(N, Env)) )), " ", term(R, Env) )).
term_(wp(_, E, At, Post), Env) -->
    el(span, "c app rq-wp", ['data-d'=args],
       ( el(span, "rq-wp-head", ( kw("WP"), wp_at(At, Env) )),
         el(span, args, ( el(span, arg, term(E, Env)), " ", el(span, arg, post(Post, Env)) )) )).
term_(triple(_, Pre, E, At, Bs, Ret, Q), Env) -->
    { binders_env(Bs, Env, EnvQ) },
    el(span, "c app rq-triple", ['data-d'=args],
       el(span, args, ( el(span, arg, ( el(span, "op rq-triple-brace", "⦃"), term(Pre, Env), el(span, "op rq-triple-brace", "⦄") )), " ",
                        el(span, arg, ( term(E, Env), wp_at(At, Env) )), " ",
                        el(span, arg, ( el(span, "op rq-triple-brace", "⦃"),
                                        ( { Bs == [] } -> [] ; binders_(Bs, Env), el(span, sep, "."), " " ),
                                        kw("RET"), " ", term(Ret, EnvQ), el(span, sep, ";"), " ", term(Q, EnvQ),
                                        el(span, "op rq-triple-brace", "⦄") )) ))).
term_(bigop(_, Op, Kind, binds(K, Xs), Cs, B), Env) -->
    { findall(X, ( ( K = n(_, X) ; member(n(_, X), Xs) ), X \== '_' ), Vs), append(Vs, Env, Env1),
      format(atom(Title), "[~w ~w]", [Op, Kind]) },
    el(span, "c quant rq-big", ['data-d'=args],
       ( el(span, "q rq-big-op", [title=Title], ( esc(Op), el(sub, "rq-big-binds", big_binds(K, Xs, Cs, Env)) )),
         el(span, args, el(span, arg, term(B, Env1))) )).
term_(bigall(_, Op, E), Env) --> el(span, "o pre rq-big", ( el(span, "q rq-big-op", [title=Op], esc(Op)), "\u00A0", term(E, Env) )).
term_(eval(_, Ws, E), Env) --> kw("Eval"), " ", el(span, "rq-mods", esc_words(Ws)), " ", kw("in"), " ", term(E, Env).

spaced_prefix(Op) :- memberchk(Op, ['⊢', '|==>', '●', '◯', '✓', '£']) ; sub_atom(Op, 0, _, _, '<').

mixfix_part(_, S) --> { string(S) }, !, esc(S).
mixfix_part(Env, E) --> term(E, Env).

%  An update's arrow, with one mask after it, or two around it.
%  A step-taking update's later and count follow in the same operator.
update(Ms, Arrow, Env) --> update(Ms, Arrow, [], Env).
update([], Arrow, Tail, _) --> el(span, "op wide rq-upd-arrow", ( esc(Arrow), Tail )).
update([E], Arrow, Tail, Env) --> el(span, "op wide rq-upd-arrow", ( esc(Arrow), el(sup, "rq-mask", term(E, Env)), Tail )).
update([E1, E2], Arrow, Tail, Env) -->
    el(span, "op wide rq-upd-arrow", ( el(sup, "rq-mask", term(E1, Env)), esc(Arrow), el(sup, "rq-mask", term(E2, Env)), Tail )).

%  The later of a step-taking update, with its count: ▷ⁿ.
step_later(none, _) --> !, "▷".
step_later(N, Env) --> "▷", el(sup, "rq-mask", term(N, Env)).

pointsto_mod(Env, name(G)) --> el(sub, "rq-mask", term(G, Env)).
pointsto_mod(Env, own(Q)) --> el(sup, "rq-mask", term(Q, Env)).
pointsto_mod(Env, dfrac(D)) --> el(sup, "rq-mask", term(D, Env)).
pointsto_mod(_, persistent) --> el(sup, "rq-mask", "□").

wp_at(none, _) --> [].
wp_at(at(S, M), Env) --> el(sub, "rq-mask", ( ( { S == none } -> [] ; term(S, Env), "; " ), term(M, Env) )).

post(post(none, Q), Env) --> el(span, "rq-post", ( el(span, op, "{"), term(Q, Env), el(span, op, "}") )).
post(post(n(_, X), Q), Env) -->
    { X == '_' -> Env1 = Env ; Env1 = [X|Env] },
    el(span, "rq-post", ( el(span, op, "{"), var_def(X), el(span, sep, "."), " ", term(Q, Env1), el(span, op, "}") )).

big_binds(K, Xs, Cs, Env) -->
    ( { K = n(_, KX) } -> var_def(KX), el(span, op, "↦") ; [] ),
    sep_defs(Xs), el(span, op, "∈"), sep_terms(Cs, Env).

sep_defs([n(_, X)]) --> !, var_def(X).
sep_defs([n(_, X)|Xs]) --> var_def(X), ";", sep_defs(Xs).
sep_terms([C], Env) --> !, term(C, Env).
sep_terms([C|Cs], Env) --> term(C, Env), ";", sep_terms(Cs, Env).

bar_items([P], Env) --> !, term(P, Env).
bar_items([P|Ps], Env) -->
    el(span, o, ['data-d'=op], ( term(P, Env), " ", el(span, "op wide bar", [title="|"], "|"), " ", bar_items(Ps, Env) )).

items([E], Env) --> !, el(span, arg, term(E, Env)).
items([E|Es], Env) --> el(span, arg, term(E, Env)), " ", items(Es, Env).

sep_items([E], Env, _) --> !, el(span, arg, term(E, Env)).
sep_items([E|Es], Env, Sep) --> el(span, arg, ( term(E, Env), el(span, sep, esc(Sep)) )), " ", sep_items(Es, Env, Sep).

rec_fields([], _) --> [].
rec_fields([fld(_, N, E)|Fs], Env) -->
    el(span, arg, ( name_ref(N, []), "\u00A0", defeq, " ", term(E, Env), ( { Fs == [] } -> [] ; el(span, sep, ";") ) )),
    ( { Fs == [] } -> [] ; " " ), rec_fields(Fs, Env).
rec_fields([fldb(_, N, Bs, E)|Fs], Env) -->
    { binders_env(Bs, Env, Env1) },
    el(span, arg, ( name_ref(N, []), binders_(Bs, Env), "\u00A0", defeq, " ", term(E, Env1), ( { Fs == [] } -> [] ; el(span, sep, ";") ) )),
    ( { Fs == [] } -> [] ; " " ), rec_fields(Fs, Env).

defeq --> el(span, "op wide defeq", [title=":="], "≔").
kw(S) --> el(span, kw, esc(S)).

quant(Sym, Title, Bs, Sep, B, Env) -->
    { binders_env(Bs, Env, Env1) },
    el(span, "c quant", ['data-d'=args],
       ( el(span, q, [title=Title], esc(Sym)),
         el(span, args, ( quant_binders(Bs, Env, Sep), el(span, arg, term(B, Env1)) )) )).

quant_binders([], _, _) --> [].
quant_binders([B|Bs], Env, Sep) -->
    el(span, arg, ( binder_(B, Env), ( { Bs == [] } -> el(span, "sep qsep", esc(Sep)) ; [] ) )),
    " ", quant_binders(Bs, Env, Sep).

head_(id(_, X), Env) --> !, name_ref(X, Env, head).
head_(E, Env) --> term(E, Env).

%  A name: a bound variable, a name the corpus defines (linked), a
%  constructor or type of Rocq's library, or any other name.
name_ref(X, Env) --> name_ref(X, Env, arg).
name_ref(X, Env, _) --> { memberchk(X, Env) }, !, var_(X).
name_ref(X, _, Pos) -->
    { name_kind(X, K), kind_class(K, C0), ( Pos == head, K == other -> C = "f" ; C = C0 ) },
    (   { \+ nb_current(rq_button, true), global_ref(X, Href, _) } -> el(a, C, [href=Href], esc(X))
    ;   el(span, C, esc(X))
    ).

%  A variable, with its digits as a subscript (r0 is r₀) and ' as a prime.
var_(X) --> el(span, v, ['data-v'=X], var_text(X)).
var_def(X) --> el(span, "v def", ['data-v'=X], var_text(X)).

var_text(X) -->
    { atom_codes(X, Cs), reverse(Cs, R0), span(==(0''), R0, Ps, R1), length(Ps, NP),
      span([C]>>code_type(C, digit), R1, RD, RS),
      ( RS == [] -> reverse(R1, Stem), Ds = [] ; reverse(RS, Stem), reverse(RD, Ds) ) },
    esc(Stem), ( { Ds == [] } -> [] ; el(sub, none, esc(Ds)) ), primes(NP).

primes(0) --> !, [].
primes(N) --> "′", { N1 is N - 1 }, primes(N1).

op_(Op) --> { op_glyph(Op, G) -> true ; atom_codes(Op, G) }, el(span, "op wide", [title=Op], esc(G)).

op_glyph('->', "→").
op_glyph('<->', "↔").
op_glyph('/\\', "∧").
op_glyph('\\/', "∨").
op_glyph('~', "¬").
op_glyph('<>', "≠").
op_glyph('<=', "≤").
op_glyph('>=', "≥").
op_glyph('<=?', "≤?").
op_glyph('>=?', "≥?").
op_glyph('*', "×").
op_glyph('-', "−").
op_glyph('=>', "⇒").
op_glyph('-∗', "−∗").
op_glyph('∗-∗', "∗−∗").
op_glyph('|==>', "|⇛").
op_glyph('==∗', "⇛").
op_glyph('~~>', "⇝").
op_glyph('-d>', "→ᵈ").
op_glyph('-n>', "→ⁿᵉ").

%  Binders: (x y : T) as a box, {x} in braces, bare names as they are.
%  A name, binders and result type: the result can move below a long
%  signature instead of forcing its own continuations beyond the page.
%  The keyword opens the group, so a phone can set a long type on the line
%  under the keyword rather than in a column past the name.
sig_(Kw, Class, N, [], none, _) --> !, kw(Kw), " ", el(span, Class, esc(N)).
sig_(Kw, Class, N, Bs, Ty, Env) -->
    el(span, "c sig", ['data-d'=args],
       ( kw(Kw), " ", el(span, Class, esc(N)), el(span, "args binders", sig_items(Bs, Ty, Env)) )).

sig_items(Bs0, Ty, Env) --> { split_gen(Bs0, Bs) }, sig_items_(Bs, Ty, Env).

sig_items_([], none, _) --> !, [].
sig_items_([], Ty, Env) --> el(span, arg, ( el(span, "op wide colon", [title=":"], ":"), " ", term(Ty, Env) )).
sig_items_([B|Bs], Ty, Env) -->
    el(span, arg, binder_(B, Env)),
    ( { Bs == [], Ty == none } -> [] ; " ", sig_items_(Bs, Ty, Env) ).

binders_(Bs0, Env) --> { split_gen(Bs0, Bs) }, binders__(Bs, Env).

binders__([], _) --> [].
binders__([B|Bs], Env) --> " ", binder_(B, Env), binders__(Bs, Env).

%  split_gen(+Binders, -Split): `{!invGS Σ, !gen_heapGS L V Σ} is two
%  instance binders, inst(Open, Class), each drawn as {invGS Σ} is: the
%  backquote and ! only steer implicit generalization, which the reader
%  does not need to see.
split_gen([], []).
split_gen([b(P, gen(Open, Items), _, _)|Bs0], Bs) :- !,
    findall(b(P, inst(Open, E), [], none), ( member(I, Items), ( I = bang(E) -> true ; E = I ) ), Is),
    split_gen(Bs0, Bs1), append(Is, Bs1, Bs).
split_gen([B|Bs0], [B|Bs]) :- split_gen(Bs0, Bs).

binder_(b(_, pattern(P), _, _), Env) --> !, el(span, tick, "'"), term(P, Env).
binder_(b(P, gen(Open, Items), _, _), Env) --> !,
    { split_gen([b(P, gen(Open, Items), [], none)], [B|Bs]) }, binder_(B, Env), binders__(Bs, Env).
binder_(b(_, inst(Open, E), _, _), Env) --> !,
    { Open == '(' -> C = "paren binder rq-inst" ; C = "braces binder rq-inst" },
    el(span, C, [title="an instance of this class"], term(E, Env)).
binder_(b(_, struct, [n(_, X)], _), _) --> !, el(span, "struct", ( "{", kw("struct"), " ", esc(X), "}" )).
binder_(b(_, brace, Ns, Ty), Env) --> !, el(span, "braces binder", ( vars(Ns), opt_type(Ty, Env) )).
binder_(b(_, _, Ns, none), _) --> !, vars(Ns).
binder_(b(_, bare, Ns, Ty), Env) --> !, vars(Ns), opt_type(Ty, Env).
binder_(b(_, paren, Ns, Ty), Env) --> el(span, "paren binder", ( vars(Ns), opt_type(Ty, Env) )).

vars([]) --> [].
vars([n(_, X)]) --> !, var_def(X).
vars([n(_, X)|Ns]) --> var_def(X), " ", vars(Ns).

opt_type(none, _) --> !, [].
opt_type(T, Env) --> "\u00A0", el(span, "op wide colon", [title=":"], ":"), " ", term(T, Env).

binders_env(Bs, Env0, Env) :- foldl(binder_env, Bs, Env0, Env).

binder_env(b(_, pattern(P), _, _), E0, E) :- !, alts_vars([[P]], Vs), append(Vs, E0, E).
binder_env(b(_, _, Ns, _), E0, E) :- foldl([n(_, X), A0, A]>>( X == '_' -> A = A0 ; A = [X|A0] ), Ns, E0, E).

lhs_names(name(n(_, X), _), [X]).
lhs_names(tuple(Ns), Xs) :- maplist([n(_, X), X]>>true, Ns, Xs).

lhs_(name(n(_, X), Bs), Env, _) --> var_def(X), binders_(Bs, Env).
lhs_(tuple(Ns), _, _) --> el(span, "c tuple", el(span, args, tuple_vars(Ns))).

tuple_vars([n(_, X)]) --> !, el(span, arg, var_def(X)).
tuple_vars([n(_, X)|Ns]) --> el(span, arg, ( var_def(X), el(span, sep, ",") )), " ", tuple_vars(Ns).

scrutinees([S], Env) --> !, scrutinee(S, Env).
scrutinees([S|Ss], Env) --> scrutinee(S, Env), el(span, sep, ","), " ", scrutinees(Ss, Env).
scrutinee(as(E, n(_, X)), Env) --> !, term(E, Env), " ", kw("as"), " ", var_def(X).
scrutinee(E, Env) --> term(E, Env).

inline_branches([], _) --> [].
inline_branches([br(Alts, R)|Bs], Env) -->
    { alts_vars(Alts, Vs), append(Vs, Env, Env1) },
    el(span, branch, ( alts_(Alts, Env1), "\u00A0", el(span, "op wide", [title="=>"], "⇒"), " ", term(R, Env1) )),
    ( { Bs == [] } -> [] ; " ", el(span, "op wide bar", "|"), " ", inline_branches(Bs, Env) ).

alts_([A], Env) --> !, pats_(A, Env).
alts_([A|As], Env) -->
    el(span, o, ['data-d'=op], ( pats_(A, Env), " ", el(span, "op wide bar", [title="|"], "|"), " ", alts_(As, Env) )).

pats_([P], Env) --> !, term(P, Env).
pats_([P|Ps], Env) --> term(P, Env), el(span, sep, ","), " ", pats_(Ps, Env).

%  The variables a pattern binds: its names that are not constructors.
alts_vars(Alts, Vs) :- findall(V, ( member(A, Alts), member(P, A), pat_var(P, V) ), Vs0), sort(Vs0, Vs).

pat_var(id(_, X), X) :- X \== '_', \+ is_ctor(X), \+ sub_atom(X, _, _, _, '.').
pat_var(app(_, _, As), V) :- member(A, As), pat_var(A, V).
pat_var(paren(_, E), V) :- pat_var(E, V).
pat_var(orpat(_, Es), V) :- member(E, Es), pat_var(E, V).
pat_var(tuple(_, Es), V) :- member(E, Es), pat_var(E, V).
pat_var(bin(_, _, L, R), V) :- ( pat_var(L, V) ; pat_var(R, V) ).
pat_var(list(_, Es), V) :- member(E, Es), pat_var(E, V).
pat_var(scope(_, E, _), V) :- pat_var(E, V).
pat_var(aspat(_, P, n(_, X)), V) :- ( V = X ; pat_var(P, V) ).

%% Blocks

%  blk(+E, +Env): E as a block: match, if and let as tables and rows,
%  anything else as one goal.
blk(E, Env) --> { block(E) }, !, blk_(E, Env).
blk(E, Env) --> { node_pos(E, _-T) }, el(div, goal, term(E, Env)), aside_after(T).

block(match(_, _, _, _)).
block(if(_, _, _, _)).
block(let(_, _, _, _, _)).
block(letstar(_, _, _, _)).
block(letpat(_, _, _, _)).
block(letq(_, _, _, _)).
block(letfix(_, _, _, _, _, _)).
block(fix(_, _, _, _, _)).
block(ir_fn(_, _, _, _, _, _)).
block(ir_blk(_, _)).
block(ir_list(_, [_|_])).
block(fun(_, _, B)) :- block(B).
block(forall(_, _, B)) :- block(B).
block(exists(_, _, B)) :- block(B).
block(app(_, paren(_, F), _)) :- block(F), !.
block(app(_, _, As)) :- member(A, As), block(A), !.
block(tuple(_, Es)) :- member(E, Es), block(E), !.
block(bin(_, _, L, R)) :- ( block(L) ; block(R) ), !.
block(paren(_, E)) :- block(E).
block(scope(_, E, _)) :- block(E).

blk_(paren(_, E), Env) --> blk(E, Env).
%  A block's scope (match … end%I) only told Rocq how to read it.
blk_(scope(_, E, _), Env) --> blk(E, Env).
blk_(ir_fn(_, Lk, Name, Ps, Ret, Bs), Env) --> ir_fn_block(Lk, Name, Ps, Ret, Bs, Env).
blk_(ir_blk(_, B), Env) --> ir_blk_standalone(B, Env).
blk_(ir_list(_, Is), Env) --> ir_list_block(Is, Env).
blk_(bin(_, Op, L, R), Env) -->
    el(div, "rq-equation", ( blk(L, Env), el(div, "goal", op_(Op)), blk(R, Env) )).
blk_(tuple(_, Es), Env) --> el(div, "rq-tuple", seq(Es, tuple_part(Env))).
%  An application with a block among its arguments, such as fold_left over
%  a λ whose body is a match: the function and the arguments before the
%  block on a line, the rest under it, a row each.
%  An unfolded fixpoint applied to its arguments: the fixpoint in its
%  parentheses, then the arguments on a line.
blk_(app(_, paren(_, F), As), Env) --> { block(F) }, !,
    el(div, "rq-app", ( el(div, "rq-tuple", blk(F, Env)), el(div, "goal app-tail", items(As, Env)) )).
blk_(app(_, F, As), Env) -->
    { append(Inline, [B|Rest], As), block(B), ! },
    el(div, "rq-app",
       ( el(div, "goal app-head", ( { Inline == [] } -> head_(F, Env)
                                  ; el(span, "c app", ['data-d'=args], ( head_(F, Env), el(span, args, items(Inline, Env)) )) )),
         el(div, "app-args", seq([B|Rest], app_arg(Env))) )).
blk_(match(_, Ss, _, Brs), Env) -->
    el(div, "rq-match",
       ( el(div, "goal match-head", ( kw("match"), " ", scrutinees(Ss, Env), " ", kw("with") )),
         el(div, "cases match", branch_rows(Brs, Env)) )).
blk_(if(P, C, T, E), Env) --> { if_chain(if(P, C, T, E), Cases) }, el(div, "cases stack rq-if", if_rows(Cases, Env)).
blk_(let(_, Lhs, Ty, V, B), Env) -->
    { lhs_names(Lhs, Ns), append(Ns, Env, Env1) },
    let_block(( kw("let"), " ", lhs_(Lhs, Env, Env1), opt_type(Ty, Env) ), V, Env, B, Env1).
blk_(letstar(_, n(_, X), V, B), Env) --> let_block(( kw("let*"), " ", var_def(X) ), V, Env, B, [X|Env]).
blk_(letpat(_, Pat, V, B), Env) -->
    { alts_vars([[Pat]], Vs), append(Vs, Env, Env1) },
    let_block(( kw("let"), " ", el(span, tick, "'"), term(Pat, Env1) ), V, Env, B, Env1).
blk_(letq(_, Pat, V, B), Env) -->
    { alts_vars([[Pat]], Vs), append(Vs, Env, Env1) },
    let_block(( kw("let?"), " ", term(Pat, Env1) ), V, Env, B, Env1).
blk_(letfix(_, n(_, F), Bs, Ty, V, B), Env) -->
    { binders_env(Bs, [F|Env], EnvV) },
    let_block(( kw("let fix"), " ", var_def(F), binders_(Bs, Env), opt_type(Ty, EnvV) ), V, EnvV, B, [F|Env]).

blk_(fix(_, n(_, F), Bs, Ty, B), Env) -->
    { binders_env(Bs, [F|Env], EnvB) },
    el(div, "rq-fun", ( el(div, "goal fun-head", ( kw("fix"), " ", var_def(F), binders_(Bs, Env), opt_type(Ty, EnvB), "\u00A0", defeq )),
                        el(div, "fun-body", blk(B, EnvB)) )).
blk_(fun(_, Bs, B), Env) --> quant_block("λ", Bs, "⇒", B, Env).
blk_(forall(_, Bs, B), Env) --> quant_block("∀", Bs, ",", B, Env).
blk_(exists(_, Bs, B), Env) --> quant_block("∃", Bs, ",", B, Env).

quant_block(Symbol, Bs, Sep, B, Env) -->
    { binders_env(Bs, Env, Env1) },
    el(div, "rq-fun", ( el(div, "goal fun-head", ( el(span, q, esc(Symbol)), binders_(Bs, Env), " ", "\u00A0", el(span, "sep qsep", esc(Sep)) )),
                        el(div, "fun-body", blk(B, Env1)) )).

%  A binding over its body: its value on the line, or under it when the
%  value is a block.
let_block(Head, V, EnvV, B, EnvB) -->
    el(div, "rq-let",
       ( (   { block(V) }
         ->  el(div, "goal let-head", ( Head, "\u00A0", defeq )),
             el(div, "let-value", blk(V, EnvV)), el(div, "goal let-in", kw("in"))
         ;   el(div, "goal let-head", ( Head, "\u00A0", defeq, " ", term(V, EnvV), " ", kw("in") ))
         ),
         el(div, "let-body", blk(B, EnvB)) )).
app_arg(Env, A) --> el(div, "app-arg", blk(A, Env)).

tuple_part(Env, E) --> el(div, "tuple-part", blk(E, Env)).

branch_rows([], _) --> [].
branch_rows([br(Alts, R)|Bs], Env) -->
    { Alts = [[P|_]|_], node_pos(P, F-_), alts_vars(Alts, Vs), append(Vs, Env, Env1) },
    notes_before(F),
    el(div, case, ( el(div, cond, el(div, goals, el(div, goal, alts_(Alts, Env1)))),
                    el(div, arrow, [title="=>"], "⇒"),
                    el(div, then, el(div, goals, blk(R, Env1))) )),
    branch_rows(Bs, Env).

if_chain(if(_, C, T, E), [if(C, T)|Cs]) :- !, ( E = if(_, _, _, _) -> if_chain(E, Cs) ; Cs = [else(E)] ).

if_rows([], _) --> [].
if_rows([if(C, T)|Cs], Env) -->
    el(div, case, ( el(div, cond, el(div, goals, blk(C, Env))), el(div, arrow, "→"),
                    el(div, then, el(div, goals, blk(T, Env))) )),
    if_rows(Cs, Env).
if_rows([else(E)|Cs], Env) -->
    el(div, "case plain", ( el(div, cond, kw("else")), el(div, arrow, []), el(div, then, el(div, goals, blk(E, Env))) )),
    if_rows(Cs, Env).

%% Checked IR (IRNotation.v)

%  Checked IR functions, blocks and instruction sequences drawn in the
%  playground's visual grammar (play_view.pl): a function is its signature
%  over a grid of labeled blocks, each block its entry phis, body
%  instructions and jump terminator, one row per operation so dterm.js
%  breaks wide lines at the width each block receives. Constructors link
%  to Syntax.v, temporaries highlight across the function via data-v,
%  block labels link and highlight within the function, and Fil-C checks,
%  raw accesses and pollchecks carry the safety margin rule.

ir_fn_block(Lk, Name, Ps, Ret, Bs, Env) -->
    { ( nb_current(rq_ir_labels, Prev) -> true ; Prev = none ),
      (   Bs = blocks(BlockList), \+ nb_current(rq_button, true)
      ->  next_ir_prefix(Prefix),
          findall(Lab, member(ir_block(_, str(_, Lab), _, _, _), BlockList), Labels),
          nb_setval(rq_ir_labels, prefix(Prefix, Labels))
      ;   nb_setval(rq_ir_labels, none)
      ) },
    el(div, "rq-ir rq-ir-fn",
       ( el(div, "goal rq-ir-head", ir_fn_head(Lk, Name, Ps, Ret, Env)),
         ir_body_blocks(Bs, Env) )),
    { nb_setval(rq_ir_labels, Prev) }.

ir_blk_standalone(B, Env) -->
    el(div, "rq-ir rq-ir-blk", el(div, "rq-ir-blocks", ir_block_row(Env, B))).

ir_list_block(Is, Env) -->
    el(div, "rq-ir rq-ir-seq", seq(Is, ir_inst_row(Env))).

next_ir_prefix(Prefix) :-
    ( nb_current(rq_ir_seq, N0) -> N is N0 + 1 ; N = 1 ),
    nb_setval(rq_ir_seq, N),
    format(atom(Prefix), "ir~d--", [N]).

ir_block_anchor(Lab, Id) :-
    nb_current(rq_ir_labels, prefix(Prefix, Labels)),
    memberchk(Lab, Labels),
    uri_encoded(fragment, Lab, Frag),
    atom_concat(Prefix, Frag, Id).

ir_fn_head(Lk, Name, Ps, Ret, Env) -->
    el(span, "c rq-ir-fn-sig", ['data-d'=args],
       ( ir_linkage(Lk, Env), "\u00A0", ir_fn_name(Name, Env),
         ir_param_list(Ps, Env) )),
    "\u00A0", el(span, "op wide", [title="->"], "→"), "\u00A0", ir_ret_type(Ret, Env).

ir_linkage(str(_, S), _) --> !,
    { format(string(Tip), "linkage: ~s", [S]) },
    el(span, "rq-ir-linkage", [title=Tip], esc(S)).
ir_linkage(E, Env) --> term(E, Env).

ir_fn_name(str(_, S), _) --> !,
    { format(string(Tip), "IR function symbol \"~s\"", [S]) },
    el(span, "rq-ir-fn-name", [title=Tip], esc(S)).
ir_fn_name(E, Env) --> term(E, Env).

ir_param_list([], _) --> !, el(span, "args rq-ir-empty", []).
ir_param_list(Ps, Env) --> el(span, args, ir_params(Ps, Env)).

ir_params([ir_param(K, D)], Env) --> !,
    el(span, arg, ( ir_class_badge(K, Env), "\u00A0", ir_tmp_def(D, Env) )).
ir_params([ir_param(K, D)|Ps], Env) -->
    el(span, arg, ( ir_class_badge(K, Env), "\u00A0", ir_tmp_def(D, Env), el(span, sep, ",") )), " ",
    ir_params(Ps, Env).

ir_ret_type(E, Env) --> { ir_unparen(E, app(_, id(_, 'RClass'), [K])) }, !,
    ir_class_badge(K, Env).
ir_ret_type(E, _) --> { ir_unparen(E, id(_, 'RVoid')) }, !,
    ir_sym('RVoid', "void", "rq-ir-class rq-ir-void", "RVoid: no return value").
ir_ret_type(E, Env) --> { ir_unparen(E, app(_, id(_, 'RTuple'), [list(_, Ks)])) }, !,
    el(span, "c tuple", ['data-d'=args], el(span, args, ir_class_tuple(Ks, Env))).
ir_ret_type(E, Env) --> term(E, Env).

ir_class_tuple([K], Env) --> !, el(span, arg, ir_class_badge(K, Env)).
ir_class_tuple([K|Ks], Env) -->
    el(span, arg, ( ir_class_badge(K, Env), el(span, sep, ",") )), " ", ir_class_tuple(Ks, Env).

ir_body_blocks(blocks([]), _) --> !,
    el(div, "rq-ir-blocks rq-ir-empty-body", el(div, "goal rq-ir-void", "{ }")).
ir_body_blocks(blocks(Bs), Env) --> !,
    el(div, "rq-ir-blocks", seq(Bs, ir_block_row(Env))).
ir_body_blocks(expr(Xs), Env) -->
    el(div, "rq-ir-blocks",
       el(div, "goal rq-ir-escape-block", ( kw("blocks"), " ", term(Xs, Env) ))).

ir_block_row(Env, ir_escape(X)) --> !,
    { node_pos(X, F-T) },
    notes_before(F),
    el(div, "rq-ir-block rq-ir-block-escape",
       el(div, "goal rq-ir-escape-block", ( term(X, Env), aside_after(T) ))).
ir_block_row(Env, ir_block(F-_, L, Phis, Ins, J)) -->
    notes_before(F),
    { L = str(_, Lab), \+ nb_current(rq_button, true), ir_block_anchor(Lab, Id) -> As = [id=Id] ; As = [] },
    el(div, "rq-ir-block", As,
       ( ir_block_label_cell(L, Env),
         el(div, goals,
            ( seq(Phis, ir_phi_row(Env)),
              ir_block_insts(Ins, Env),
              ir_jump_row(J, Env) )) )).

ir_block_label_cell(str(_, Lab), _) --> !,
    { format(string(Tip), "basic block @\"~s\"", [Lab]) },
    el(div, "rq-ir-label", ['data-ir-label'=Lab, title=Tip],
       ( el(span, "rq-ir-sigil", "@"), esc(Lab), el(span, neck, ":") )).
ir_block_label_cell(E, Env) -->
    el(div, "rq-ir-label", ( el(span, "rq-ir-sigil", "@"), term(E, Env), el(span, neck, ":") )).

ir_phi_row(Env, ir_escape(X)) --> !,
    { node_pos(X, F-T) },
    notes_before(F),
    el(div, "goal rq-ir-phi", term(X, Env)), aside_after(T).
ir_phi_row(Env, ir_phi(F-T, D, K, Incs)) -->
    notes_before(F),
    el(div, "goal rq-ir-phi", ir_phi_draw(D, K, Incs, Env)), aside_after(T).

ir_phi_draw(D, K, Incs, Env) -->
    el(span, o, ['data-d'=op],
       ( el(span, "rq-ir-lhs", ( ir_tmp_def(D, Env), "\u00A0", el(span, "rq-ir-colon", [title=":"], ":"), "\u00A0",
                                 ir_class_badge(K, Env) )),
         "\u00A0", el(span, "op wide", [title="="], "="), " ",
         el(span, "c rq-ir-phi-call", ['data-d'=args],
            ( ir_sym('Phi', "phi", "rq-ir-op-control", "Phi: selects the incoming value for the predecessor block control arrived from"),
              el(span, args, ir_incomings(Incs, Env)) )) )).

ir_incomings([ir_inc(Lab, V)], Env) --> !,
    el(span, arg, ( ir_label_ref(Lab, Env), "\u00A0", el(span, "op wide", [title="=>"], "⇒"), "\u00A0", ir_opnd(V, Env) )).
ir_incomings([ir_inc(Lab, V)|Is], Env) -->
    el(span, arg, ( ir_label_ref(Lab, Env), "\u00A0", el(span, "op wide", [title="=>"], "⇒"), "\u00A0", ir_opnd(V, Env),
                    el(span, sep, ",") )), " ",
    ir_incomings(Is, Env).

ir_block_insts(insts(Is), Env) --> !, seq(Is, ir_inst_row(Env)).
ir_block_insts(code(Xs), Env) --> { ir_unparen(Xs, ir_list(_, Is)) }, !, seq(Is, ir_inst_row(Env)).
ir_block_insts(code(Xs), Env) -->
    { node_pos(Xs, F-T) },
    notes_before(F),
    el(div, "goal rq-ir-inst", ( kw("code"), " ", term(Xs, Env) )), aside_after(T).

ir_inst_row(Env, ir_s(F-T, I)) -->
    { ir_ssa_pz(I) -> C = "goal rq-ir-inst pz" ; C = "goal rq-ir-inst" },
    notes_before(F),
    el(div, C, ir_ssa_draw(I, Env)), aside_after(T).

ir_jump_row(ir_s(F-T, J), Env) -->
    { ir_ssa_pz(J) -> C = "goal rq-ir-jump pz" ; C = "goal rq-ir-jump" },
    notes_before(F),
    el(div, C, ( el(span, "op rq-ir-term-arrow", [title="=>"], "⇒"), "\u00A0", ir_ssa_draw(J, Env) )),
    aside_after(T).

ir_ssa_draw(ir_s(_, I), Env) --> !, ir_ssa_draw(I, Env).
ir_ssa_draw(ir_escape(X), Env) --> { ir_escape_draw(X, Env, Goal) }, !, call(Goal).
ir_ssa_draw(ir_escape(X), Env) --> !, term(X, Env).
ir_ssa_draw(ir_let(D, K, Op, Args), Env) --> !,
    el(span, o, ['data-d'=op],
       ( el(span, "rq-ir-lhs", ( ir_tmp_def(D, Env), "\u00A0", el(span, "rq-ir-colon", [title=":"], ":"), "\u00A0",
                                 ir_class_badge(K, Env) )),
         "\u00A0", el(span, "op wide", [title="="], "="), " ",
         ir_op_applied(Op, Args, Env) )).
ir_ssa_draw(ir_flight(D, Base, Off), Env) --> !,
    el(span, o, ['data-d'=op],
       ( ir_tmp_def(D, Env), "\u00A0", el(span, "op wide", [title="="], "="), " ",
         el(span, o, ['data-d'=op],
            ( ir_opnd(Base, Env), "\u00A0",
              ir_sym('Flight', "+p", "op wide rq-ir-op", "Flight Add (LowerOf base): pointer arithmetic preserving base's Fil-C capability"),
              " ", ir_opnd(Off, Env) )) )).
ir_ssa_draw(ir_store(Sz, Addr, Off, Src), Env) --> !,
    el(span, o, ['data-d'=op],
       ( el(span, "rq-ir-lhs",
            ( ir_sym('RawStore', "store", "rq-ir-op-memory", "RawStore: write value to memory at proven address + offset"),
              "\u00A0", ir_type_badge(Sz, Env), "\u00A0", ir_mem_addr(Addr, Off, Env) )),
         "\u00A0", el(span, "op wide rq-ir-store-arrow", [title="<-"], "←"), " ",
         ir_opnd(Src, Env) )).
ir_ssa_draw(ir_store_ptr(Addr, Off, Src), Env) --> !,
    el(span, o, ['data-d'=op],
       ( el(span, "rq-ir-lhs",
            ( ir_sym('RawStorePointer', "store.ptr", "rq-ir-op-memory", "RawStorePointer: write pointer and capability at proven address + offset"),
              "\u00A0", ir_mem_addr(Addr, Off, Env) )),
         "\u00A0", el(span, "op wide rq-ir-store-arrow", [title="<-"], "←"), " ",
         ir_opnd(Src, Env) )).
ir_ssa_draw(ir_alloca(X, Sz), Env) --> !,
    ir_sym('LocalAlloc', "alloca", "rq-ir-op-memory", "LocalAlloc: allocate zeroed stack local object"),
    "\u00A0", ir_local_name(X, Env), "\u00A0", ir_num_or_term(Sz, Env).
ir_ssa_draw(ir_call(Kw, Res, Fn, Args), Env) --> !,
    { ( Kw == rawcall -> Ctor = 'RawCall', KwS = "rawcall", Cls = "rq-ir-op-check",
        Tip = "RawCall: call proven function address (class F) with no check"
      ; Ctor = 'Call', KwS = "call", Cls = "rq-ir-op-control",
        Tip = "Call: check callee capability and invoke function" ) },
    (   { Res = res(D, K) }
    ->  el(span, o, ['data-d'=op],
           ( el(span, "rq-ir-lhs",
                ( ir_sym(Ctor, KwS, Cls, Tip), "\u00A0", ir_tmp_def(D, Env), "\u00A0",
                  el(span, "rq-ir-colon", [title=":"], ":"), "\u00A0", ir_class_badge(K, Env) )),
             "\u00A0", el(span, "op wide", [title="="], "="), " ",
             ir_call_target(Fn, Args, Env) ))
    ;   ir_sym(Ctor, KwS, Cls, Tip), "\u00A0",
        ir_sym('CVoid', "void", "rq-ir-void", "CVoid: no return value"), "\u00A0",
        ir_call_target(Fn, Args, Env)
    ).
ir_ssa_draw(ir_goto(Edge), Env) --> !,
    ir_sym('JGoto', "goto", "rq-ir-op-control", "JGoto: jump unconditionally to block"),
    "\u00A0", ir_edge_draw(Edge, Env).
ir_ssa_draw(ir_br(Cond, Yes, No), Env) --> !,
    ir_sym('JBranch', "br", "rq-ir-op-control", "JBranch: jump to first block if condition is nonzero, else second"),
    "\u00A0",
    el(span, o, ['data-d'=op],
       ( ir_opnd(Cond, Env), "\u00A0", el(span, "op wide", [title="?"], "?"), " ",
         el(span, o, ['data-d'=op],
            ( ir_edge_draw(Yes, Env), "\u00A0", el(span, "op wide", [title=":"], ":"), " ",
              ir_edge_draw(No, Env) )) )).
ir_ssa_draw(ir_ret(void), _) --> !,
    ir_sym('JRetVoid', "ret", "rq-ir-op-control", "JRetVoid: return from void function"),
    "\u00A0", el(span, "rq-ir-void", "void").
ir_ssa_draw(ir_ret(val(V)), Env) --> !,
    ir_sym('JRet', "ret", "rq-ir-op-control", "JRet: return value from function"),
    "\u00A0", ir_opnd(V, Env).
ir_ssa_draw(ir_unreachable, _) -->
    ir_sym('JUnreachable', "unreachable", "rq-ir-op-control", "JUnreachable: traps immediately if control reaches this point").

ir_mem_addr(Addr, Off, Env) -->
    el(span, "l rq-ir-addr",
       ( ir_opnd(Addr, Env), "\u00A0", el(span, op, "+"), "\u00A0", ir_num_or_term(Off, Env) )).

%  Common Gallina instruction escapes that IRNotation has no short
%  spelling for: Flight with Sub (or a different capability donor) and
%  Touch. Drawing them in the same IR visual grammar keeps temporary
%  subscripts and hover highlights consistent across the function.
ir_escape_draw(X0, Env, ir_flight_sub_draw(Dst, Base, Off, Env)) :-
    ir_unparen(X0, app(_, id(_, 'Flight'), [Dst0, Op0, list(_, [A1, A2]), Lower0])),
    ir_name_str(Dst0, Dst),
    ir_unparen(Op0, id(_, 'Sub')),
    ir_flight_arg(A1, addr(Base)),
    ir_flight_arg(A2, val(Off)),
    ir_flight_lower(Lower0, of(Donor)),
    ir_opnd_same(Base, Donor), !.
ir_escape_draw(X0, Env, ir_flight_gen_draw(Dst, Op0, FArgs, Lower, Env)) :-
    ir_unparen(X0, app(_, id(_, 'Flight'), [Dst0, Op0, list(_, FArgs0), Lower0])),
    ir_name_str(Dst0, Dst),
    maplist(ir_flight_arg, FArgs0, FArgs),
    ir_flight_lower(Lower0, Lower), !.
ir_escape_draw(X0, Env, ir_touch_draw(Q, Env)) :-
    ir_unparen(X0, app(_, id(_, 'Touch'), [Q0])),
    ir_name_str(Q0, Q), !.

ir_name_str(E0, str(P, S)) :-
    ir_unparen(E0, app(_, id(_, F), [str(P, S)])),
    memberchk(F, ['TAtom', a]).

ir_gallina_opnd(E0, tmp(str(P, S))) :-
    ir_unparen(E0, app(_, id(_, t), [str(P, S)])), !.
ir_gallina_opnd(E0, tmp(Dst)) :-
    ir_unparen(E0, app(_, id(_, 'Tmp'), [Dst0])), ir_name_str(Dst0, Dst), !.
ir_gallina_opnd(E0, global(G)) :-
    ir_unparen(E0, app(_, id(_, 'Global'), [G0])), ir_name_str(G0, G), !.
ir_gallina_opnd(E0, const(N)) :-
    ir_unparen(E0, app(_, id(_, 'Const'), [N])), !.
ir_gallina_opnd(E, val(E)).

ir_flight_arg(E0, addr(V)) :-
    ir_unparen(E0, app(_, id(_, 'FAddress'), [V0])), !, ir_gallina_opnd(V0, V).
ir_flight_arg(E0, val(V)) :-
    ir_unparen(E0, app(_, id(_, 'FValue'), [V0])), !, ir_gallina_opnd(V0, V).

ir_flight_lower(E0, none) :- ir_unparen(E0, id(_, 'LowerNone')), !.
ir_flight_lower(E0, of(V)) :-
    ir_unparen(E0, app(_, id(_, 'LowerOf'), [V0])), !, ir_gallina_opnd(V0, V).

ir_opnd_same(tmp(str(_, S)), tmp(str(_, S))).
ir_opnd_same(global(str(_, S)), global(str(_, S))).

ir_flight_sub_draw(Dst, Base, Off, Env) -->
    el(span, o, ['data-d'=op],
       ( ir_tmp_def(Dst, Env), "\u00A0", el(span, "op wide", [title="="], "="), " ",
         el(span, o, ['data-d'=op],
            ( ir_opnd(Base, Env), "\u00A0",
              ir_sym('Flight', "−p", "op wide rq-ir-op", "Flight Sub (LowerOf base): pointer subtraction preserving base's Fil-C capability"),
              " ", ir_opnd(Off, Env) )) )).

ir_flight_gen_draw(Dst, Op, FArgs, Lower, Env) -->
    el(span, o, ['data-d'=op],
       ( ir_tmp_def(Dst, Env), "\u00A0", el(span, "op wide", [title="="], "="), " ",
         el(span, "c app rq-ir-op-app", ['data-d'=args],
            ( el(span, "c rq-ir-op-call", ['data-d'=args],
                 ( ir_sym('Flight', "Flight", "rq-ir-op", "Flight: pointer arithmetic with explicit capability donor"),
                   el(span, args, ( el(span, arg, ( ir_op_draw(Op, Env), el(span, sep, ",") )), " ",
                                    el(span, arg, ir_lower_draw(Lower, Env)) )) )),
              el(span, args, ir_flight_args_draw(FArgs, Env)) )) )).

ir_lower_draw(none, _) -->
    ir_sym('LowerNone', "lower none", "rq-ir-void", "LowerNone: null capability").
ir_lower_draw(of(V), Env) -->
    ir_sym('LowerOf', "lower", "rq-ir-op", "LowerOf: copy capability from this pointer"), "\u00A0", ir_opnd(V, Env).

ir_flight_args_draw([A], Env) --> !, el(span, arg, ir_flight_arg_draw(A, Env)).
ir_flight_args_draw([A|As], Env) -->
    el(span, arg, ( ir_flight_arg_draw(A, Env), el(span, sep, ",") )), " ", ir_flight_args_draw(As, Env).

ir_flight_arg_draw(addr(V), Env) --> ir_opnd(V, Env).
ir_flight_arg_draw(val(V), Env) --> ir_opnd(V, Env).

ir_touch_draw(Q, Env) -->
    ir_sym('Touch', "touch", "rq-ir-op-check", "Touch: consume proof temporary from a preceding vector check"),
    "\u00A0", ir_tmp_use(Q, Env).

ir_local_name(str(_, S), _) --> !,
    { format(string(Tip), "stack local \"~s\"", [S]) },
    el(span, "rq-ir-local", [title=Tip], esc(S)).
ir_local_name(E, Env) --> term(E, Env).

ir_call_target(Fn, Args, Env) -->
    el(span, "c rq-ir-call-args", ['data-d'=args],
       ( ir_opnd(Fn, Env),
         ( { Args == [] } -> el(span, "args rq-ir-empty", [])
         ; el(span, args, ir_call_args(Args, Env)) ) )).

ir_call_args([ir_arg(K, V)], Env) --> !,
    el(span, arg, ( ir_class_badge(K, Env), "\u00A0", ir_opnd(V, Env) )).
ir_call_args([ir_arg(K, V)|As], Env) -->
    el(span, arg, ( ir_class_badge(K, Env), "\u00A0", ir_opnd(V, Env), el(span, sep, ",") )), " ",
    ir_call_args(As, Env).

ir_op_applied(Op, [], Env) --> !, ir_op_draw(Op, Env).
ir_op_applied(Op, Args, Env) -->
    el(span, "c app rq-ir-op-app", ['data-d'=args],
       ( ir_op_draw(Op, Env), el(span, args, ir_opnd_args(Args, Env)) )).

ir_opnd_args([A], Env) --> !, el(span, arg, ir_opnd(A, Env)).
ir_opnd_args([A|As], Env) -->
    el(span, arg, ( ir_opnd(A, Env), el(span, sep, ",") )), " ", ir_opnd_args(As, Env).

%  Operations: unwrap Rocq's level-0 parentheses around compound ops and
%  group static parameters in dterm bows, coloured by role (compute,
%  memory, Fil-C check), while keeping every constructor linked to Syntax.v.
ir_op_draw(Op0, Env) --> { ir_unparen(Op0, Op) }, ir_op_draw_(Op, Env).

ir_op_draw_(id(_, Name), _) --> { ir_op_gloss(Name, Role, Tip) }, !,
    { ir_role_class(Role, Cls) },
    ir_sym(Name, Name, Cls, Tip).
ir_op_draw_(app(_, id(_, 'Cmp'), [Cond, Cls]), Env) --> !,
    ir_op_call('Cmp', op, [cond(Cond), cls(Cls)], Env).
ir_op_draw_(app(_, id(_, 'Ext'), [Ty]), Env) --> !,
    ir_op_call('Ext', op, [ty(Ty)], Env).
ir_op_draw_(app(_, id(_, 'ExtF'), [Cls]), Env) --> !,
    ir_op_call('ExtF', op, [cls(Cls)], Env).
ir_op_draw_(app(_, id(_, 'FloatToInt'), [Cls, Sg]), Env) --> !,
    ir_op_call('FloatToInt', op, [cls(Cls), ty(Sg)], Env).
ir_op_draw_(app(_, id(_, 'IntToFloat'), [Cls, Sg]), Env) --> !,
    ir_op_call('IntToFloat', op, [cls(Cls), ty(Sg)], Env).
ir_op_draw_(app(_, id(_, 'Setjmp'), [Kind]), Env) --> !,
    ir_op_call('Setjmp', op, [raw(Kind)], Env).
ir_op_draw_(app(_, id(_, 'Alloc'), [Align]), Env) --> !,
    ir_op_call('Alloc', memory, [num(Align)], Env).
ir_op_draw_(app(_, id(_, Head), [Lo, Hi, R, Align]), Env) -->
    { memberchk(Head, ['Check', 'Renew', 'RenewHull', 'RenewIf', 'CheckLimit']) }, !,
    ir_op_call(Head, check, [range(Lo, Hi), right(R), num(Align)], Env).
ir_op_draw_(app(_, id(_, 'CheckAhead'), [Lo, Hi, R, Align, Ahi]), Env) --> !,
    ir_op_call('CheckAhead', check, [range(Lo, Hi), right(R), num(Align), num(Ahi)], Env).
ir_op_draw_(app(_, id(_, 'HalfCheck'), [B, Lo, Hi, R, Align]), Env) --> !,
    ir_op_call('HalfCheck', check, [cond(B), range(Lo, Hi), right(R), num(Align)], Env).
ir_op_draw_(app(_, id(_, 'SpanTest'), [Lo, Hi]), Env) --> !,
    ir_op_call('SpanTest', check, [range(Lo, Hi)], Env).
ir_op_draw_(app(_, id(_, 'Limit'), [Sz]), Env) --> !,
    ir_op_call('Limit', check, [num(Sz)], Env).
ir_op_draw_(app(_, id(_, 'CheckLocal'), [X, Off, Bytes, R, Align]), Env) --> !,
    ir_op_call('CheckLocal', check, [raw(X), num(Off), num(Bytes), right(R), num(Align)], Env).
ir_op_draw_(app(_, id(_, 'RawLoad'), [LdTy, Off]), Env) --> !,
    ir_op_call('RawLoad', memory, [load_ty(LdTy), num(Off)], Env).
ir_op_draw_(app(_, id(_, 'RawLoadPointer'), [Off, Es]), Env) --> !,
    ir_op_call('RawLoadPointer', memory, [num(Off), raw(Es)], Env).
ir_op_draw_(app(_, id(_, 'RawCas'), [CasTy, Off]), Env) --> !,
    ir_op_call('RawCas', memory, [cas_ty(CasTy), num(Off)], Env).
ir_op_draw_(Op, Env) --> term(Op, Env).

ir_op_call(Head, Role, Params, Env) -->
    { ( ir_op_gloss(Head, _, Tip) -> true ; atom_string(Head, Tip) ),
      ir_role_class(Role, Cls) },
    el(span, "c rq-ir-op-call", ['data-d'=args],
       ( ir_sym(Head, Head, Cls, Tip),
         el(span, args, ir_op_params(Params, Env)) )).

ir_op_params([P], Env) --> !, el(span, arg, ir_op_param(P, Env)).
ir_op_params([P|Ps], Env) -->
    el(span, arg, ( ir_op_param(P, Env), el(span, sep, ",") )), " ", ir_op_params(Ps, Env).

ir_op_param(cls(E), Env) --> !, ir_class_badge(E, Env).
ir_op_param(cond(E), Env) --> !, ir_cond_badge(E, Env).
ir_op_param(ty(E), Env) --> !, ir_type_badge(E, Env).
ir_op_param(right(E), Env) --> !, ir_right_badge(E, Env).
ir_op_param(range(Lo, Hi), Env) --> !,
    el(span, "rq-ir-range", [title="byte offset range [lo, hi)"],
       ( ir_num_or_term(Lo, Env), el(span, "op tight", ".."), ir_num_or_term(Hi, Env) )).
ir_op_param(load_ty(E), Env) --> !,
    (   { ir_unparen(E, app(_, id(_, 'LdNarrow'), [N])) } -> ir_type_badge(N, Env)
    ;   ir_type_badge(E, Env)
    ).
ir_op_param(cas_ty(E), Env) --> !,
    (   { ir_unparen(E, app(_, id(_, 'CasNarrow'), [N])) } -> ir_type_badge(N, Env)
    ;   ir_type_badge(E, Env)
    ).
ir_op_param(num(E), Env) --> !, ir_num_or_term(E, Env).
ir_op_param(raw(E), Env) --> term(E, Env).

ir_num_or_term(num(_, N), _) --> !, el(span, n, esc(N)).
ir_num_or_term(E, _) --> { ir_neg_num(E, N) }, !, el(span, n, ( "−", esc(N) )).
ir_num_or_term(E, Env) --> term(E, Env).

ir_neg_num(pre(_, '-', num(_, N)), N) :- !.
ir_neg_num(paren(_, E), N) :- ir_neg_num(E, N).

ir_unparen(paren(_, E0), E) :- !, ir_unparen(E0, E).
ir_unparen(E, E).

%  Operands: %tmp (purple SSA value with trailing-digit subscript and
%  hover highlighting via data-v), $global (green), #const (gold).
ir_tmp_def(X, Env) --> ir_tmp_(def, X, Env).
ir_tmp_use(X, Env) --> ir_tmp_(use, X, Env).

ir_tmp_(Role, str(_, Name), _) --> !,
    { atom_string(Raw, Name),
      atom_concat('%', Raw, VarKey),
      ir_raw_value_name(Raw, Stem, Sub),
      ( Role == def -> Cls = "v ir-value def" ; Cls = "v ir-value" ),
      format(string(Tip), "SSA temporary %\"~s\"", [Name]) },
    el(span, Cls, ['data-v'=VarKey, 'data-tmp'=Raw, title=Tip],
       ( el(span, "value-role", "%"), esc(Stem),
         ( { Sub == none } -> [] ; el(sub, none, esc(Sub)) ) )).
ir_tmp_(Role, E, Env) -->
    { Role == def -> Cls = "ir-value def" ; Cls = "ir-value" },
    el(span, Cls, ( el(span, "value-role", "%"), term(E, Env) )).

%  Subscript trailing digits of unnamed compiler temporaries (v12, chk3,
%  pr.2, k0, acc1), matching dterm.pl's raw_value_name/3.
ir_raw_value_name(Raw, Stem, Digits) :-
    atom_codes(Raw, Cs), append(Stem0, Digits, Cs),
    Stem0 \== [], Digits \== [], last(Stem0, Last), \+ between(0'0, 0'9, Last),
    maplist([C]>>between(0'0, 0'9, C), Digits), !,
    ( append(S, [Sep], Stem0), memberchk(Sep, [0'., 0'_]), S \== [] -> Stem = S ; Stem = Stem0 ).
ir_raw_value_name(Raw, Raw, none).

ir_opnd(tmp(X), Env) --> !, ir_tmp_use(X, Env).
ir_opnd(global(str(_, S)), _) --> !,
    { format(string(Tip), "global symbol $\"~s\"", [S]) },
    el(span, "rq-ir-global", [title=Tip], ( el(span, "value-role", "$"), esc(S) )).
ir_opnd(global(X), Env) --> !,
    el(span, "rq-ir-global", ( el(span, "value-role", "$"), term(X, Env) )).
ir_opnd(const(X), Env) --> !,
    (   { X = num(_, N) }
    ->  { format(string(Tip), "constant #~w", [N]) },
        el(span, "rq-ir-const", [title=Tip], ( el(span, "value-role", "#"), el(span, n, esc(N)) ))
    ;   { ir_neg_num(X, N) }
    ->  { format(string(Tip), "constant #(-~w)", [N]) },
        el(span, "rq-ir-const", [title=Tip], ( el(span, "value-role", "#"), el(span, n, ( "−", esc(N) )) ))
    ;   el(span, "rq-ir-const", ( el(span, "value-role", "#"), term(X, Env) ))
    ).
ir_opnd(val(X), Env) --> term(X, Env).

ir_edge_draw(to(L), Env) --> !, ir_label_ref(L, Env).
ir_edge_draw(poll(L), Env) --> !,
    ir_sym('Poll', "poll", "rq-ir-op-check", "Poll: garbage-collection safepoint check on this edge"),
    "\u00A0", ir_label_ref(L, Env).
ir_edge_draw(edge(X), Env) --> term(X, Env).

ir_label_ref(str(_, Lab), _) --> !,
    { format(string(Tip), "block @\"~s\"", [Lab]) },
    (   { \+ nb_current(rq_button, true), ir_block_anchor(Lab, Id) }
    ->  { atom_concat('#', Id, Href) },
        el(a, "rq-ir-lbl", [href=Href, 'data-ir-label'=Lab, title=Tip],
           ( el(span, "rq-ir-sigil", "@"), esc(Lab) ))
    ;   el(span, "rq-ir-lbl", ['data-ir-label'=Lab, title=Tip],
           ( el(span, "rq-ir-sigil", "@"), esc(Lab) ))
    ).
ir_label_ref(E, Env) -->
    el(span, "rq-ir-lbl", ( el(span, "rq-ir-sigil", "@"), term(E, Env) )).

ir_class_badge(id(_, K), _) --> { ir_class_gloss(K, Tip) }, !,
    ir_sym(K, K, "rq-ir-class", Tip).
ir_class_badge(E, Env) --> term(E, Env).

ir_type_badge(id(_, T), _) --> { ir_type_gloss(T, Tip) }, !,
    ir_sym(T, T, "rq-ir-type", Tip).
ir_type_badge(E, Env) --> term(E, Env).

ir_cond_badge(id(_, C), _) --> { ir_cond_gloss(C, Tip) }, !,
    ir_sym(C, C, "rq-ir-cond", Tip).
ir_cond_badge(E, Env) --> term(E, Env).

ir_right_badge(id(_, R), _) --> { ir_right_gloss(R, Cls, Tip) }, !,
    ir_sym(R, R, Cls, Tip).
ir_right_badge(E, Env) --> term(E, Env).

ir_sym(RocqName, Label, Class, Tip) -->
    (   { \+ nb_current(rq_button, true), global_ref(RocqName, Href, _) }
    ->  el(a, Class, [href=Href, title=Tip], esc(Label))
    ;   el(span, Class, [title=Tip], esc(Label))
    ).

%  Inline fallback when an IR block, list or function appears inside a
%  Gallina expression (where only inline spans are valid HTML).
ir_inline_ssa_items([I], Env) --> !, el(span, arg, ir_ssa_draw(I, Env)).
ir_inline_ssa_items([I|Is], Env) -->
    el(span, arg, ( ir_ssa_draw(I, Env), el(span, sep, ";") )), " ", ir_inline_ssa_items(Is, Env).

ir_blk_inline(ir_escape(X), Env) --> !, term(X, Env).
ir_blk_inline(ir_block(_, L, Phis, Ins, J), Env) -->
    ir_label_ref(L, Env),
    ( { Phis == [] } -> el(span, neck, ":") ; " ", el(span, l, ir_inline_phis(Phis, Env)), el(span, neck, ":") ),
    " ", ir_inline_insts(Ins, Env), el(span, "op rq-ir-term-arrow", [title="=>"], "⇒"), " ", ir_ssa_draw(J, Env).

ir_inline_phis([P], Env) --> !, ir_inline_phi(P, Env).
ir_inline_phis([P|Ps], Env) --> ir_inline_phi(P, Env), el(span, sep, ";"), " ", ir_inline_phis(Ps, Env).
ir_inline_phi(ir_escape(X), Env) --> !, term(X, Env).
ir_inline_phi(ir_phi(_, D, K, Incs), Env) --> ir_phi_draw(D, K, Incs, Env).

ir_inline_insts(insts([]), _) --> !, [].
ir_inline_insts(insts(Is), Env) --> !, ir_inline_ssa_items(Is, Env), " ".
ir_inline_insts(code(Xs), Env) --> kw("code"), " ", term(Xs, Env), " ".

ir_fn_inline(Lk, Name, Ps, Ret, Bs, Env) -->
    ir_fn_head(Lk, Name, Ps, Ret, Env), " ",
    (   { Bs = blocks(BlockList) }
    ->  el(span, braces, ir_inline_blocks(BlockList, Env))
    ;   { Bs = expr(Xs) }, kw("blocks"), " ", term(Xs, Env)
    ).

ir_inline_blocks([], _) --> [].
ir_inline_blocks([B], Env) --> !, ir_blk_inline(B, Env).
ir_inline_blocks([B|Bs], Env) --> ir_blk_inline(B, Env), el(span, sep, ";"), " ", ir_inline_blocks(Bs, Env).

%  Rows pizlonation wrote: capability checks, raw accesses, raw calls
%  and safepoint poll edges.
ir_ssa_pz(ir_s(_, I)) :- !, ir_ssa_pz(I).
ir_ssa_pz(ir_let(_, _, Op, _)) :- !, ir_op_pz(Op).
ir_ssa_pz(ir_store(_, _, _, _)) :- !.
ir_ssa_pz(ir_store_ptr(_, _, _)) :- !.
ir_ssa_pz(ir_call(rawcall, _, _, _)) :- !.
ir_ssa_pz(ir_goto(poll(_))) :- !.
ir_ssa_pz(ir_br(_, Y, N)) :- !, ( Y = poll(_) ; N = poll(_) ).
ir_ssa_pz(ir_escape(X)) :-
    ir_unparen(X, app(_, id(_, F), _)),
    memberchk(F, ['RawStore', 'RawStorePointer', 'RawCall', 'Touch']).

ir_op_pz(Op0) :-
    ir_unparen(Op0, Op),
    ( Op = id(_, H) ; Op = app(_, id(_, H), _) ),
    memberchk(H, ['Check', 'CheckAhead', 'Renew', 'RenewHull', 'HalfCheck', 'SpanTest',
                  'RenewIf', 'Limit', 'CheckLimit', 'CheckLocal', 'CheckFunction',
                  'RawLoad', 'RawLoadPointer', 'RawCas']).

ir_role_class(op, "rq-ir-op").
ir_role_class(memory, "rq-ir-op-memory").
ir_role_class(check, "rq-ir-op-check").
ir_role_class(control, "rq-ir-op-control").

ir_class_gloss('W', "W: 32-bit integer (word)").
ir_class_gloss('L', "L: 64-bit integer (long)").
ir_class_gloss('P', "P: pointer with Fil-C capability").
ir_class_gloss('A', "A: proven address cleared by a capability check").
ir_class_gloss('F', "F: proven function entry address").
ir_class_gloss('Single', "Single: 32-bit IEEE float").
ir_class_gloss('Double', "Double: 64-bit IEEE float").
ir_class_gloss('Extended', "Extended: 80-bit extended float").

ir_type_gloss('Wb', "Wb: 1-byte (8-bit) width").
ir_type_gloss('Wh', "Wh: 2-byte (16-bit) width").
ir_type_gloss('Ww', "Ww: 4-byte (32-bit) width").
ir_type_gloss('Wl', "Wl: 8-byte (64-bit) width").
ir_type_gloss('Wp', "Wp: 8-byte pointer with capability").
ir_type_gloss('Ws', "Ws: 4-byte float width").
ir_type_gloss('Wd', "Wd: 8-byte double width").
ir_type_gloss('Wx', "Wx: 10-byte extended float width").
ir_type_gloss('Sb', "Sb: signed 8-bit byte").
ir_type_gloss('Ub', "Ub: unsigned 8-bit byte").
ir_type_gloss('Sh', "Sh: signed 16-bit halfword").
ir_type_gloss('Uh', "Uh: unsigned 16-bit halfword").
ir_type_gloss('Sw', "Sw: signed 32-bit word").
ir_type_gloss('Uw', "Uw: unsigned 32-bit word").
ir_type_gloss('LdL', "LdL: load 64-bit integer").
ir_type_gloss('LdS', "LdS: load 32-bit float").
ir_type_gloss('LdD', "LdD: load 64-bit float").
ir_type_gloss('LdX', "LdX: load 80-bit extended float").
ir_type_gloss('CasL', "CasL: 64-bit integer compare-and-exchange").
ir_type_gloss('CasP', "CasP: pointer compare-and-exchange").
ir_type_gloss('Signed', "Signed: two's-complement signed integer").
ir_type_gloss('Unsigned', "Unsigned: unsigned integer").

ir_cond_gloss('Eq', "Eq: =").
ir_cond_gloss('Ne', "Ne: ≠").
ir_cond_gloss('Slt', "Slt: <, signed").
ir_cond_gloss('Sle', "Sle: ≤, signed").
ir_cond_gloss('Sgt', "Sgt: >, signed").
ir_cond_gloss('Sge', "Sge: ≥, signed").
ir_cond_gloss('Ult', "Ult: <, unsigned").
ir_cond_gloss('Ule', "Ule: ≤, unsigned").
ir_cond_gloss('Ugt', "Ugt: >, unsigned").
ir_cond_gloss('Uge', "Uge: ≥, unsigned").
ir_cond_gloss('Lt', "Lt: <").
ir_cond_gloss('Le', "Le: ≤").
ir_cond_gloss('Gt', "Gt: >").
ir_cond_gloss('Ge', "Ge: ≥").
ir_cond_gloss('Ord', "Ord: ordered (neither is NaN)").
ir_cond_gloss('Unord', "Unord: unordered (one is NaN)").
ir_cond_gloss('Upper', "Upper: check upper bound only").
ir_cond_gloss('Lower', "Lower: check lower bound only").

ir_right_gloss('Read', "rq-ir-cond", "Read: read access right").
ir_right_gloss('Write', "rq-ir-right-write", "Write: write access right (rejected by read-only capabilities)").

ir_op_gloss('Add', op, "Add: +").
ir_op_gloss('Sub', op, "Sub: −").
ir_op_gloss('Mul', op, "Mul: ×").
ir_op_gloss('Div', op, "Div: ÷, signed").
ir_op_gloss('Udiv', op, "Udiv: ÷, unsigned").
ir_op_gloss('Rem', op, "Rem: remainder, signed").
ir_op_gloss('Urem', op, "Urem: remainder, unsigned").
ir_op_gloss('And', op, "And: bitwise and").
ir_op_gloss('Or', op, "Or: bitwise or").
ir_op_gloss('Xor', op, "Xor: bitwise exclusive or").
ir_op_gloss('Shl', op, "Shl: shift left").
ir_op_gloss('Shr', op, "Shr: logical shift right (zero-fill)").
ir_op_gloss('Sar', op, "Sar: arithmetic shift right (sign-extending)").
ir_op_gloss('Neg', op, "Neg: negate").
ir_op_gloss('Copy', op, "Copy: value copy (or materialize global pointer)").
ir_op_gloss('Ptoi', op, "Ptoi: pointer to integer (drops capability)").
ir_op_gloss('Itop', op, "Itop: integer to pointer (null capability)").
ir_op_gloss('Select', op, "Select: second value if first is nonzero, else third").
ir_op_gloss('Cmp', op, "Cmp: compare two values (1 if condition holds, else 0)").
ir_op_gloss('Ext', op, "Ext: sign- or zero-extend narrow integer").
ir_op_gloss('ExtF', op, "ExtF: widen floating-point value").
ir_op_gloss('Truncd', op, "Truncd: double to single").
ir_op_gloss('Truncx', op, "Truncx: extended float to narrower format").
ir_op_gloss('FloatToInt', op, "FloatToInt: truncate float to integer").
ir_op_gloss('IntToFloat', op, "IntToFloat: convert integer to float").
ir_op_gloss('Cast', op, "Cast: reinterpret bit pattern between integer and float").
ir_op_gloss('Sqrt', op, "Sqrt: IEEE square root").
ir_op_gloss('VaArgs', op, "VaArgs: variadic argument cursor").
ir_op_gloss('VaArg', op, "VaArg: read next variadic argument").
ir_op_gloss('Setjmp', op, "Setjmp: save return context").
ir_op_gloss('Alloc', memory, "Alloc: allocate zeroed heap object with fresh Fil-C capability").
ir_op_gloss('RawLoad', memory, "RawLoad: read memory at proven address + offset (no check of its own)").
ir_op_gloss('RawLoadPointer', memory, "RawLoadPointer: read pointer and capability at proven address + offset").
ir_op_gloss('RawCas', memory, "RawCas: atomic compare-and-exchange at proven address + offset").
ir_op_gloss('Check', check, "Check: verify pointer bounds [lo, hi), rights and alignment; yields proven address A").
ir_op_gloss('CheckAhead', check, "CheckAhead: verify current span [lo, ahi) and ahead span [ahi, hi)").
ir_op_gloss('Renew', check, "Renew: reuse a dominating check's bounds for a derived pointer").
ir_op_gloss('RenewHull', check, "RenewHull: reuse bounds within the hull of two dominating checks").
ir_op_gloss('HalfCheck', check, "HalfCheck: test one bound when the other is already proved").
ir_op_gloss('SpanTest', check, "SpanTest: return 1 if pointer object covers [lo, hi), else 0").
ir_op_gloss('RenewIf', check, "RenewIf: reuse bounds guarded by a passing SpanTest").
ir_op_gloss('Limit', check, "Limit: capture opaque bounds snapshot for accesses of size bytes").
ir_op_gloss('CheckLimit', check, "CheckLimit: verify access against a captured Limit").
ir_op_gloss('CheckLocal', check, "CheckLocal: prove in-bounds access to a named stack local").
ir_op_gloss('CheckFunction', check, "CheckFunction: verify pointer is an exact function entry").

%% Statements as rules

%  rule_parts(+T, -Binders, -Premises, -Conclusion): T is
%  forall Binders, P1 -> … -> Pn -> C, foralls between the premises
%  gathered with the first.
rule_parts(T, Bs, Ps, C) :- rule_parts_(T, Bs, Ps, C).

rule_parts_(forall(_, Bs0, B), Bs, Ps, C) :- !, rule_parts_(B, Bs1, Ps, C), append(Bs0, Bs1, Bs).
rule_parts_(bin(_, Op, L, R), Bs, [L|Ps], C) :- memberchk(Op, ['->', '→']), !, rule_parts_(R, Bs, Ps, C).
rule_parts_(paren(_, E), Bs, Ps, C) :- E = forall(_, _, _), !, rule_parts_(E, Bs, Ps, C).
rule_parts_(C, [], [], C).

%  rule(+Name, +Binders, +Type, +Env): Type as a rule: its variables, its
%  premises over a line, its conclusion. Name is drawn beside the line.
rule(Label, Bs0, T, Env0) -->
    { rule_parts(T, Bs1, Ps, C), append(Bs0, Bs1, Bs), binders_env(Bs, Env0, Env) },
    el(div, rule,
       ( ( { Bs == [] } -> [] ; el(div, "rule-vars", ( el(span, q, [title=forall], "∀"), binders_(Bs, Env0) )) ),
         (   { Ps == [] }
         ->  el(div, "rule-concl alone", ( blk(C, Env), Label ))
         ;   el(div, premises, seq(Ps, premise(Env))),
             el(div, "rule-line", Label),
             el(div, "rule-concl", blk(C, Env))
         ) )).

premise(Env, P) --> { node_pos(P, F-T) }, notes_before(F), blk(P, Env), aside_after(T).

%% Sentences

%  rocq_items(+Items): a page's sentences, from the source set by
%  rocq_set_source/2, each with the comments before it.
rocq_items(Items) --> { runs(Items, Runs) }, seq(Runs, run_).

%  Consecutive directives (Require, Import, Open Scope) are one block.
runs([], []).
runs([dir(P, W)|Is0], [dirs([dir(P, W)|Ds])|Rs]) :- !, take_dirs(Is0, Ds, Is), runs(Is, Rs).
runs([I|Is], [I|Rs]) :- runs(Is, Rs).

take_dirs([dir(P, W)|Is0], [dir(P, W)|Ds], Is) :- !, take_dirs(Is0, Ds, Is).
take_dirs(Is, [], Is).

run_(dirs(Ds)) --> !, { Ds = [dir(F-_, _)|_] }, notes_before(F), el(div, "rq-dirs", seq(Ds, dir_)), html_flush.
run_(I) --> { item_from(I, F) }, notes_before(F), item_(I), html_flush.

item_from(proved(S, _), F) :- !, item_from(S, F).
item_from(block(S, _, _), F) :- !, item_from(S, F).
item_from(S, F) :- arg(1, S, F-_).

dir_(dir(_-T, Ws)) --> el(div, "rq-dir", dir_words(Ws)), aside_after(T).

dir_words([]) --> [].
dir_words([W|Ws]) -->
    ( { dir_keyword(W) } -> kw(W) ; el(span, "module", esc(W)) ),
    ( { Ws == [] } -> [] ; " " ), dir_words(Ws).

dir_keyword(W) :- memberchk(W, ['From', 'Require', 'Import', 'Export', 'Open', 'Close', 'Scope', 'Set', 'Unset',
                                'Arguments', 'Hint', 'Local', 'Global', 'Declare', 'Delimit', 'Bind', 'Implicit',
                                'Types', 'Generalizable', 'Create', 'HintDb', 'Opaque', 'Transparent', 'Typeclasses', 'Coercion']).

item_(block(module(F-_, Kind, n(_, N), Bs, Open), Body, End)) --> !,
    { nb_getval(rq_mod, Mod0), qualify(Mod0, N, Q), ( Kind == section -> Mod1 = Mod0 ; append(Mod0, [N], Mod1) ),
      module_kw(Kind, KwS), binders_env(Bs, [], Env) },
    el(section, "rq-module", [id=Q],
       ( el(div, "clause rq-module-head",
            el(div, head, ( line_link(F), kw(KwS), " ", el(span, "module-name", esc(N)), binders_(Bs, []),
                            ( { Open = open(Sig) -> Args = [] ; Open = open(Sig, Args) } ->
                                "\u00A0", el(span, "op wide colon", ":"), " ", name_ref(Sig, Env), seq(Args, module_arg)
                            ; [] ) ))),
         { nb_setval(rq_mod, Mod1) },
         el(div, "rq-module-body", rocq_items(Body)),
         { nb_setval(rq_mod, Mod0) },
         ( { End = endm(_-T, _) } -> notes_upto(T) ; [] ) )).
%  A statement quoted without its proof (a document's fence) is only the
%  statement: no empty proof under it.
item_(proved(S, pf([], none))) --> !, item_(S).
item_(proved(S, Pf)) --> !, item_(S), proof_(S, Pf).
item_(proof_start(_)) --> !, [].
item_(ind(_, _, Bodies)) --> !, seq(Bodies, ind_body).
item_(rec(F-T, Kw, n(_, N), Bs, Sort, Ctor, Fs)) --> !,
    { anchor(N, Id), binders_env(Bs, [], Env) },
    el(div, "clause rq-rec", [id=Id],
       ( el(div, head, ( line_link(F), sig_(Kw, "ty def", N, Bs, Sort, Env),
                         ( { Ctor = n(_, C) } -> "\u00A0", defeq, " ", ctor_def(C) ; [] ) )),
         el(table, "rq-fields", el(tbody, none, seq(Fs, field_row(Env)))) )),
    notes_upto(T).
%  Mutual fixpoints: each body drawn as a definition, the later ones
%  under the keyword with, with the comments written before each.
item_(mutual(_, [D|Ds])) --> !, item_(D), seq(Ds, mutual_def).

%  An Example proved by tactics is a statement, drawn as a theorem is.
item_(def(P, 'Example', N, Bs, Ty, none)) --> { Ty \== none }, !, item_(thm(P, 'Example', N, Bs, Ty)).
item_(def(F-T, Kw, n(_, N), Bs, Ty, Body)) --> !,
    { anchor(N, Id), binders_env(Bs, [], Env) },
    el(div, "clause rq-def", [id=Id],
       ( el(div, head, ( line_link(F), sig_(Kw, "f def", N, Bs, Ty, Env),
                         ( { Body == none } -> [] ; "\u00A0", defeq ) )),
         ( { Body == none } -> [] ; el(div, "rq-body", blk(Body, Env)) ) )),
    notes_upto(T).
item_(tacdef(F-T, n(_, N), Args, Body)) --> !,
    { anchor(N, Id), maplist([n(_, X), X]>>true, Args, Env) },
    el(div, "clause rq-ltac", [id=Id],
       ( el(div, head, ( line_link(F), kw("Ltac"), " ", el(span, "f def", esc(N)),
                         " ", vars(Args), "\u00A0", defeq )),
         el(div, "rq-body", tactic_block(Body, Env)) )),
    notes_upto(T).
item_(thm(F-T, Kw, Name, Bs, Ty)) --> !,
    { Name = n(_, N) -> anchor(N, Id), As = [id=Id] ; N = '', As = [] },
    el(div, "clause rq-thm", As,
       ( el(div, "rq-thm-head", ( line_link(F), kw(Kw), " ", el(span, "lem def", esc(N)) )),
         rule([], Bs, Ty, []) )),
    notes_upto(T).
item_(decl(F-T, Kw, Gs)) --> { axiom_kw(Kw) }, !,
    seq(Gs, axiom_(F, Kw)), notes_upto(T).
%  Context, Variable and Parameter: one name group is Kw x y : T; more
%  binders are one group for the printer, which breaks only between them.
%  The keyword is the group's head, so on a phone the binders can start
%  on the line under it rather than in a column beside it.
item_(decl(F-T, Kw, Gs)) --> !,
    { Gs = [bs(Bs0)] -> split_gen(Bs0, Bs) ; maplist([g(Ns, Ty), b(none, group, Ns, Ty)]>>true, Gs, Bs) },
    el(div, "clause rq-param",
       el(div, head, ( line_link(F),
                       (   { Bs = [b(_, group, Ns, Ty)] } -> kw(Kw), " ", param_names(Ns), opt_type(Ty, [])
                       ;   el(span, "c sig rq-ctx", ['data-d'=args], ( kw(Kw), el(span, "args binders", param_binders(Bs)) ))
                       ) ))),
    notes_upto(T).
%  Rocq needs the parentheses around a notation's meaning; the reader
%  does not.
item_(notation(F-T, Kw, S, E, Mods)) --> !,
    { E = paren(_, E1) -> true ; E1 = E },
    el(div, "clause rq-notation",
       el(div, head, ( line_link(F), kw(Kw), " ", notation_pattern(S, E), "\u00A0", defeq, " ", term(E1, []),
                       ( { Mods == [] } -> [] ; " ", el(span, "rq-mods", esc_words(Mods)) ) ))),
    notes_upto(T).
%  Module M := F A, a functor applied, as one line.
item_(module(F-T, Kind, n(_, N), Bs, Open)) -->
    { ( Open = defined([M|As]) -> Signature = none ; Open = defined([M|As], Signature) ),
      nb_getval(rq_mod, Mod0), qualify(Mod0, N, Q), module_kw(Kind, KwS) }, !,
    el(div, "clause rq-module-def", [id=Q],
       el(div, head, ( line_link(F), kw(KwS), " ", el(span, "module-name", esc(N)), binders_(Bs, []),
                       ( { Signature = signature(Sig, Args) } ->
                           "\u00A0", el(span, "op wide colon", ":"), " ", name_ref(Sig, []), seq(Args, module_arg)
                       ; [] ), "\u00A0", defeq, " ",
                       name_ref(M, []), seq(As, module_arg) ))),
    notes_upto(T).
%  Print Assumptions lt_spec, Extract Constant Z.of_nat => "…": the
%  keywords, then each word of the arguments, a name linked to its
%  definition and foreign code in the code face. A string of several
%  lines at the end is a block under the command, its later lines without
%  the indent they share (dterm_html.pl's dedent/2).
item_(cmd(F-T, Kws, Toks)) --> !,
    { atomic_list_concat(Kws, ' ', Kw), cmd_words(Toks, Ws0),
      (   append(Ws, [[t(str(_), SF, ST)]], Ws0), src_text(SF-ST, S), sub_string(S, _, _, _, "\n")
      ->  split_string(S, "\n", "", [L|Ls]), dedent(Ls, Ds), atomic_list_concat([L|Ds], '\n', Code)
      ;   Ws = Ws0, Code = none
      ) },
    el(div, "clause rq-cmd",
       ( el(div, head, ( line_link(F),
                         (   { Ws == [] } -> kw(Kw)
                         ;   el(span, "c rq-cmd-args", ['data-d'=args], ( kw(Kw), el(span, args, cmd_args(Ws)) ))
                         ) )),
         ( { Code == none } -> [] ; el(pre, "s rq-code rq-code-block", esc(Code)) ) )),
    notes_upto(T).
item_(endm(P, _)) --> !, raw_(P).
item_(S) --> { arg(1, S, P) }, raw_(P).

module_arg(A) --> " ", name_ref(A, []).

mutual_def(D) --> { arg(1, D, F-_) }, notes_before(F), item_(D).

%  cmd_words(+Toks, -Words): tokens written without a space between them
%  (--anf-variant, "nf_id",) are one word.
cmd_words([], []).
cmd_words([t(K, F, T)|Ts0], [[t(K, F, T)|W]|Ws]) :- cmd_word(T, Ts0, W, Ts), cmd_words(Ts, Ws).

cmd_word(T, [t(K, T, T1)|Ts0], [t(K, T, T1)|W], Ts) :- !, cmd_word(T1, Ts0, W, Ts).
cmd_word(_, Ts, [], Ts).

cmd_args([W]) --> !, el(span, arg, cmd_word_(W)).
cmd_args([W|Ws]) --> el(span, arg, cmd_word_(W)), " ", cmd_args(Ws).

%  A word that starts with - is an option, -O or --anf-variant.
cmd_word_([t(sym(S), F, T0)|W]) --> { sub_atom(S, 0, 1, _, -) }, !,
    { last([t(sym(S), F, T0)|W], t(_, _, T)), src_text(F-T, Text) }, el(span, "rq-flag", esc(Text)).
cmd_word_(W) --> seq(W, cmd_tok).

cmd_tok(t(id(X), _, _)) --> { memberchk(X, ['From', 'Include']) }, !, kw(X).
cmd_tok(t(id(X), _, _)) --> !, name_ref(X, []).
cmd_tok(t(num(_), F, T)) --> !, { src_text(F-T, N) }, el(span, n, esc(N)).
cmd_tok(t(str(_), F, T)) --> !, { src_text(F-T, S) }, el(span, "s rq-code", esc(S)).
cmd_tok(t(sym('=>'), _, _)) --> !, el(span, "op wide", [title="=>"], "⇒").
cmd_tok(t(_, F, T)) --> { src_text(F-T, S) }, el(span, op, esc(S)).

module_kw(module_type, "Module Type").
module_kw(module, "Module").
module_kw(section, "Section").

raw_(F-T) --> { src_text(F-T, S) }, el(pre, "rq-raw", ( line_link(F), esc(S) )), notes_upto(T).

esc_words(Ws) --> { atomic_list_concat(Ws, ' ', A0), atom_string(A0, A1),
                    foldl([X-Y, S0, S]>>( atomic_list_concat(Parts, X, S0), atomic_list_concat(Parts, Y, S) ),
                          ["( "-"(", " )"-")"], A1, A) }, esc(A).

anchor(N, Id) :- nb_getval(rq_mod, Mod), qualify(Mod, N, Id).

ctor_def(C) --> { anchor(C, Id) }, el(span, "a def", [id=Id], esc(C)).

%  An inductive type: a table of its constructors, or, when they have
%  premises, a column of rules.
ind_body(ib(n(F-_, N), Bs, Ty, Cs)) -->
    { anchor(N, Id), binders_env(Bs, [], Env) },
    el(div, "clause rq-ind", [id=Id],
       ( el(div, "head rq-ind-head",
            ( line_link(F), sig_("Inductive", "ty def", N, Bs, Ty, Env), "\u00A0", defeq )),
         (   { member(ctor(_, _, _, CT), Cs), CT \== none, rule_parts(CT, _, [_|_], _) }
         ->  el(div, rules, seq(Cs, ctor_rule(Env)))
         ;   el(table, "rq-ctors", el(tbody, none, seq(Cs, ctor_row(Env))))
         ) )).

ctor_row(Env, ctor(F-T, C, Bs, Ty)) -->
    notes_rows(F, 4),
    { anchor(C, Id), aside_text(T, Aside) },
    el(tr, none, [id=Id],
       ( el(td, bar, "|"),
         el(td, ctor, el(span, "a def", esc(C))),
         el(td, "ctor-args", el(div, goal,
            el(span, "c sig", ['data-d'=args], el(span, "args binders", sig_items(Bs, Ty, Env))))),
         el(td, "ctor-aside", ( { Aside == none } -> [] ; el(span, aside, rocq_prose_inline(Aside)) )) )).

ctor_rule(Env, ctor(F-T, C, Bs, Ty)) -->
    notes_before(F),
    { anchor(C, Id) },
    el(div, "clause rq-rule", [id=Id],
       (   { Ty == none }
       ->  el(div, "rule-concl alone", ( el(div, goal, ( el(span, "a def", esc(C)), binders_(Bs, Env) )) ))
       ;   rule(el(span, "rule-name", el(span, "a def", esc(C))), Bs, Ty, Env)
       )),
    aside_after(T).

field_row(Env, field(F-T, N, Bs, Ty, D)) -->
    notes_rows(F, 3),
    { anchor(N, Id), aside_text(T, Aside) },
    el(tr, none, [id=Id],
       ( el(td, "field-name", el(span, "f def", esc(N))),
         el(td, "field-type", el(div, goal,
            ( el(span, "c sig", ['data-d'=args], el(span, "args binders", sig_items(Bs, Ty, Env))),
              ( { D == none } -> [] ; "\u00A0", defeq, " ", term(D, Env) ) ))),
         el(td, "field-aside", ( { Aside == none } -> [] ; el(span, aside, rocq_prose_inline(Aside)) )) )).

axiom_(F, Kw, g(Ns, Ty)) -->
    { Ns = [n(_, N)|_], anchor(N, Id) },
    el(div, "clause rq-thm rq-axiom", [id=Id],
       ( el(div, "rq-thm-head", ( line_link(F), kw(Kw), " ", el(span, "lem def", esc(N)) )),
         rule([], [], Ty, []) )).

param_binders([B]) --> !, el(span, arg, param_binder(B)).
param_binders([B|Bs]) --> el(span, arg, param_binder(B)), " ", param_binders(Bs).

%  A name group's names are the section's (defines/3), each its anchor;
%  the names of other binders are drawn as definitions too.
param_binder(b(_, group, Ns, Ty)) --> !, el(span, "paren binder", ( param_names(Ns), opt_type(Ty, []) )).
param_binder(b(_, paren, Ns, Ty)) --> !, el(span, "paren binder", ( seq_defs(Ns), opt_type(Ty, []) )).
param_binder(b(_, brace, Ns, Ty)) --> !, el(span, "braces binder", ( seq_defs(Ns), opt_type(Ty, []) )).
param_binder(B) --> binder_(B, []).

param_names([n(_, N)|Ns]) --> { anchor(N, Id) }, el(span, "f def", [id=Id], esc(N)), ( { Ns == [] } -> [] ; " ", param_names(Ns) ).

seq_defs([n(_, N)]) --> !, el(span, "f def", esc(N)).
seq_defs([n(_, N)|Ns]) --> el(span, "f def", esc(N)), " ", seq_defs(Ns).

%  "c ⟶ r": the words of the pattern that the meaning binds are its
%  variables.
notation_pattern(S, E) -->
    { split_string(S, " ", "", Ws), findall(X, sub_id(E, X), Xs) },
    el(span, "notation", [title=S], seq_sp(Ws, notation_word(Xs))).

notation_word(Xs, W) --> { atom_string(A, W), memberchk(A, Xs) }, !, var_(A).
notation_word(_, W) --> el(span, "op wide", esc(W)).

seq_sp([], _) --> [].
seq_sp([X], G) --> !, call(G, X).
seq_sp([X|Xs], G) --> call(G, X), " ", seq_sp(Xs, G).

sub_id(id(_, X), X).
sub_id(E, X) :- compound(E), E =.. [_, _|As], member(A, As), ( is_list(A) -> member(A1, A) ; A1 = A ), compound(A1), sub_id(A1, X).

line_link(F) -->
    { nb_getval(rq_file, File), File \== none, !, line_of(F, L), github(G),
      format(atom(Href), "~w~w#L~w", [G, File, L]) },
    el(a, ln, [href=Href, title="source line"], esc(L)).
line_link(_) --> [].

%% Proofs

%  Real proof states are an optional build input, never reconstructed
%  from tactic names. Unexecuted prose snippets, and proofs whose states
%  the capture's budget dropped, retain their source view.
proof_(S, pf(Steps, End)) -->
    { nb_getval(rq_states, States), States \== none,
      arg(1, S, _-Start), atom_number(Key, Start), get_dict(Key, States, Initial), !,
      End = qed(_-Finish, Kw),
      include([X]>>(X = step(_, _, _)), Steps, Tacs), length(Tacs, N),
      foldl(step_depth, Steps, Rows, [], _),
      format(atom(Id), "proof-~d", [Start]),
      findall(snap(T, D, Bs, F, Ts), member(row(D, Bs, F-T, Ts), Rows), Snaps),
      append([snap(Start, 0, [], none, [])|Snaps], [snap(Finish, 0, [], end(Kw), [])], All),
      focus_tree(0, All, Timeline),
      exclude([R]>>(R = row(close, _, _, _)), Rows, OpenRows), focus_tree(0, OpenRows, Script),
      format(string(Count), "~d tactics", [N]) },
    el(details, "rq-proof rq-captured", [id=Id],
       ( el(summary, none, ( el(span, "proof-invite", "Explore proof"), " ", el(span, "proof-count", esc(Count)) )),
         el(div, "rq-explorer",
            ( el(div, "rq-proof-controls", [hidden=hidden],
                 ( el(button, none, [type=button, 'data-move'= -1, 'aria-label'="Previous proof step", title="Previous step (←)"], "←"),
                   el(output, "rq-position", ['aria-live'=polite], "Initial goal"),
                   el(button, none, [type=button, 'data-move'=1, 'aria-label'="Next proof step", title="Next step (→)"], "→") )),
              el(div, "rq-walk",
                 ( el(nav, "rq-timeline", [hidden=hidden, 'aria-label'="Proof steps"], focus_nodes(Timeline, proof_link(Id))),
                   el(div, "rq-states", ( snapshot(Id, States, snap(Start, 0, [], none, []), Initial),
                                          seq_tail(All, Id, States) )) )),
              el(details, "rq-script", ( el(summary, none, "Source script"), el(div, "proof-steps", focus_nodes(Script, tac_row)) )) )) )).
proof_(S, pf(Steps, End)) -->
    { include([St]>>(St = step(_, _, _)), Steps, Tacs), length(Tacs, N),
      ( End = qed(_, Kw) -> true ; Kw = '' ),
      ( N =:= 1 -> Count = "1 step" ; format(string(Count), "~d steps", [N]) ),
      proof_env(S, Tacs, Env),
      foldl(step_depth, Steps, Rows, [], _),
      exclude([R]>>(R = row(close, _, _, _)), Rows, OpenRows), focus_tree(0, OpenRows, Script) },
    el(details, "rq-proof",
       ( el(summary, none, ( kw("Proof"), " ", el(span, "proof-count", esc(Count)), " ", kw(Kw) )),
         { nb_setval(rq_proof_env, Env) },
         el(div, "proof-steps", focus_nodes(Script, tac_row)),
         { nb_delete(rq_proof_env) } )).

%  Without captured proof states, a proof's local names come from the
%  statement's binders and the names its tactics introduce.
proof_env(S, Tacs, Env) :-
    stmt_env(S, E0),
    findall(X, ( member(step(_, _, Ts), Tacs), rocq_tactic_tokens(Ts, T), tactic_intro_var(T, X) ), Xs),
    append(E0, Xs, E1), sort(E1, Env).

stmt_env(S, Env) :-
    ( S = thm(_, _, _, Bs, Ty) ; S = def(_, _, _, Bs, Ty, _) ), !,
    binders_env(Bs, [], E0),
    ( Ty \== none, rule_parts(Ty, QBs, _, _) -> binders_env(QBs, E0, Env) ; Env = E0 ).
stmt_env(_, []).

tactic_intro_var(T, X) :-
    sub_term(Sub, T),
    (   Sub = ip_name(n(_, X)), X \== '_'
    ;   Sub = clause(eqn, [token(id(X))])
    ;   Sub = tlet(n(_, X), _, _)
    ;   Sub = hyp(n(_, X), _)
    ).

% Source focus is a tree, independently of the captured command count.
% A repeated bullet starts a sibling; braces and deeper bullets nest.
focus_tree(_, [], []).
focus_tree(Level, [X|Xs], [focus(Kind, Children)|Tree]) :-
    focus_depth(X, D, Bs), D > Level, !,
    ( ( memberchk('{', Bs) ; member(focus(_), Bs) ) -> Kind = 'rq-focus rq-braced' ; Kind = 'rq-focus' ),
    focus_members(Xs, D, More, Rest), focus_tree(D, [X|More], Children), focus_tree(Level, Rest, Tree).
focus_tree(Level, [X|Xs], [X|Tree]) :- focus_tree(Level, Xs, Tree).

focus_depth(snap(_, D, Bs, _, _), D, Bs).
focus_depth(row(D, Bs, _, _), D, Bs).
focus_members([X|Xs], D, [X|More], Rest) :-
    focus_depth(X, DX, Bs), ( DX > D ; DX =:= D, exclude(==('}'), Bs, []) ), !,
    focus_members(Xs, D, More, Rest).
focus_members(Rest, _, [], Rest).

focus_nodes([], _) --> [].
focus_nodes([focus(Kind, Children)|Tree], Draw) --> !,
    el(div, Kind, focus_nodes(Children, Draw)), focus_nodes(Tree, Draw).
focus_nodes([X|Tree], Draw) --> call(Draw, X), focus_nodes(Tree, Draw).

seq_tail([_|Ss], Id, States) --> seq(Ss, snapshot_lookup(Id, States)).

proof_link(Id, Snap) -->
    { Snap = snap(T, D, _, F, _), format(atom(Target), "~w-~d", [Id, T]), format(atom(Style), "--depth:~d", [D]),
      ( integer(F) -> src_text(F-T, Label) ; F = end(Kw) -> Label = Kw ; Label = "Initial goal" ) },
    % A navigation button must not contain another interactive target.
    { nb_setval(rq_button, true) },
    el(button, "rq-step-link clause", [type=button, 'data-target'=Target, style=Style, 'aria-label'=Label], step_label(Snap)),
    { nb_setval(rq_button, false) }, html_flush.

step_label(snap(_, _, _, none, _)) --> !, el(span, "rq-step-name", esc("Initial goal")).
step_label(snap(_, _, _, end(Kw), _)) --> !, el(span, "rq-step-name", esc(Kw)).
step_label(snap(T, _, Bs, F, Ts)) -->
    { exclude(==('}'), Bs, Shown) },
    el(span, bullet, seq(Shown, bullet_)), tactic_text(F, T, Ts).

snapshot_lookup(Id, States, Snap) -->
    { Snap = snap(T, _, _, _, _), atom_number(Key, T),
      ( get_dict(Key, States, Goals) -> true ; throw(error(missing_proof_state(T), _)) ) },
    snapshot(Id, States, Snap, Goals).

snapshot(Id, _, Snap, Goals) -->
    { Snap = snap(T, _, _, F, _), format(atom(Sid), "~w-~d", [Id, T]),
      ( is_list(Goals) -> length(Goals, N) ; N = 0 ) },
    el(section, "rq-snapshot", [id=Sid],
       ( el(header, "rq-state-heading", ( el(h3, clause, step_label(Snap)), goal_count(N) )),
         el(p, "rq-changes", ['aria-live'=polite], []),
         ( { Goals == null }
         -> ( { F = end(Kw), memberchk(Kw, ['Qed', 'Defined']) }
            -> el(p, "rq-complete", "✓ Proof checked and closed by Rocq.")
            ; el(p, "rq-incomplete", "Proof ended without a checked closure.") )
         ; { Goals == [] }
         -> el(p, "rq-complete", "No remaining goals.")
         ; captured_goals(Goals) ) )), html_flush.

% One open goal is the usual case; only several are worth a word.
goal_count(N) --> { N > 1 }, !, { format(string(Count), "~d open", [N]) }, el(span, "rq-goal-count", esc(Count)).
goal_count(_) --> [].

captured_goals([G|Gs]) --> captured_goal(G), seq(Gs, secondary_goal).

captured_goal(G) -->
    { G.role == "focused", ! },
    el(div, "rq-proof-goal clause", ['data-goal-id'=G.id, 'data-role'=G.role], goal_contents(G)).
captured_goal(G) -->
    secondary_goal(G).

secondary_goal(G) -->
    el(details, "rq-other-goal", ( el(summary, none, ( esc(G.role), " goal" )),
        el(div, "rq-proof-goal clause", ['data-goal-id'=G.id, 'data-role'=G.role], goal_contents(G)) )).

goal_contents(G) -->
    { maplist(hyp_parts, G.hypotheses, Hyps), findall(N, ( member(hyp(Ns, _, _, _), Hyps), member(N, Ns) ), Env) },
    ( { Hyps == [] } -> []
    ; el(div, "rq-context", seq(Hyps, captured_hyp(Env))) ),
    (   { ipm_goal(G.conclusion, Zones, Goal) }
    ->  seq(Zones, ipm_zone(Env)),
        el(div, "rq-conclusion rq-ipm-goal", ['data-raw'=Goal], el(div, goal, captured_term(Goal, Env)))
    ;   el(div, "rq-conclusion", ['data-raw'=G.conclusion],
           ( el(span, "rq-turnstile", ['aria-label'="Goal"], "⊢"), el(div, goal, captured_term(G.conclusion, Env)) ))
    ), html_flush.

%  ipm_goal(+Text, -Zones, -Goal): the proof mode's goal as Iris prints
%  it: the persistent hypotheses over a ---□ rule, the spatial ones over
%  a ---∗ rule, then the goal; zone(Mark, Hyps) for each rule printed.
ipm_goal(Text, Zones, Goal) :-
    split_string(Text, "\n", "", Lines),
    ipm_lines(Lines, [], Zones, GoalLines), Zones \== [],
    atomic_list_concat(GoalLines, '\n', A), atom_string(A, Goal).

ipm_lines([L|Ls], Acc, [zone(Mark, Hyps)|Zs], G) :-
    string_concat("----------", _, L), sub_string(L, _, 1, 0, Mark), memberchk(Mark, ["□", "∗"]), !,
    ipm_hyps(Acc, Hyps), ipm_lines(Ls, [], Zs, G).
ipm_lines(Ls, [], [], Ls) :- \+ ( member(L, Ls), string_concat("----------", _, L) ), !.
ipm_lines([L|Ls], Acc, Zs, G) :- append(Acc, [L], Acc1), ipm_lines(Ls, Acc1, Zs, G).

%  "H" : P, continued on indented lines.
ipm_hyps([], []).
ipm_hyps([L|Ls], [ipm_hyp(Name, Ty, Raw)|Hs]) :-
    sub_string(L, 0, 1, _, "\""), sub_string(L, B, _, A, "\" : "), !,
    N is B - 1, sub_string(L, 1, N, _, Name), sub_string(L, _, A, 0, Ty0),
    indented(Ls, Cont, Rest),
    atomic_list_concat([Ty0|Cont], '\n', TyA), atom_string(TyA, Ty),
    atomic_list_concat([L|Cont], '\n', RawA), atom_string(RawA, Raw),
    ipm_hyps(Rest, Hs).

indented([L|Ls], [L|Cs], Rest) :- sub_string(L, 0, 1, _, " "), !, indented(Ls, Cs, Rest).
indented(Ls, [], Ls).

ipm_zone(Env, zone(Mark, Hyps)) -->
    ( { Hyps == [] } -> [] ; el(div, "rq-context rq-ipm-context", seq(Hyps, ipm_hyp(Env))) ),
    el(div, "rq-ipm-rule", ['aria-label'=Mark], el(span, "rq-ipm-mark", esc(Mark))).

ipm_hyp(Env, ipm_hyp(Name, Ty, Raw)) -->
    { atom_concat('"', Name, Key), ( short_hyp(Ty) -> C = "rq-hyp" ; C = "rq-hyp wide" ) },
    el(div, C, ['data-hyp'=Key, 'data-raw'=Raw],
       ( el(div, "rq-hyp-names", ( ipm_pattern(Name), " :" )),
         el(div, "rq-hyp-type goal", captured_term(Ty, Env)) )), html_flush.

% Parse the context with the same Gallina grammar, including newlines
% after colons and types containing colons, strings or record fields.
hyp_parts(Text, hyp(Names, Body, Ty, Text)) :-
    string_codes(Text, Cs), rocq_fragment_codes(Cs, context(Ns, Body, Ty)), !,
    maplist([n(_, N), N]>>true, Ns, Names).
hyp_parts(Text, hyp([], none, none, Text)).

captured_hyp(Env, hyp(Ns, Body, Ty, Raw)) -->
    { atomic_list_concat(Ns, ',', Key), ( Body == none, Ty \== none, short_hyp(Raw) -> C = "rq-hyp" ; C = "rq-hyp wide" ) },
    el(div, C, ['data-hyp'=Key, 'data-raw'=Raw],
       ( { Ty == none } -> el(code, "rq-unparsed", esc(Raw))
       ; el(div, "rq-hyp-names", ( sep_vars(Ns), ( { Body == none } -> " :" ; " :=" ) )),
         el(div, "rq-hyp-type goal",
            ( { Body == none } -> blk(Ty, Env)
            ; { block(Body) ; block(Ty) } -> blk(Body, Env), " : ", blk(Ty, Env)
            ; term(Body, Env), " : ", term(Ty, Env) )) )), html_flush.

% A short hypothesis shares its row with others when the context is wide;
% a long one, or a local definition, keeps the whole row.
short_hyp(Raw) :-
    split_string(Raw, " \n", " \n", Ws), exclude(==(""), Ws, Ws1),
    atomic_list_concat(Ws1, ' ', Flat), atom_length(Flat, L), L =< 34.

sep_vars([]) --> [].
sep_vars([N]) --> !, var_def(N).
sep_vars([N|Ns]) --> var_def(N), ", ", sep_vars(Ns).

captured_term(Text, Env) -->
    { string_codes(Text, Cs), rocq_fragment_codes(Cs, term(E)) }, !, blk(E, Env).
captured_term(Text, _) --> el(code, "rq-unparsed", [title="Rocq output; notation not yet supported by dterm"], esc(Text)).

%  The focus stack after each step's bullets, as Rocq keeps it: a bullet
%  closes the goals focused since the last bullet of its kind, { opens a
%  goal and } closes it.
step_depth(step(P, Bs, Ts), row(D, Bs, P, Ts), S0, S) :- foldl(bullet_focus, Bs, S0, S), length(S, D).
step_depth(bullets(Bs), row(close, Bs, none, []), S0, S) :- foldl(bullet_focus, Bs, S0, S).

bullet_focus('}', S0, S) :- !, ( append(_, ['{'|S], S0) -> true ; S = [] ).
bullet_focus('{', S, ['{'|S]) :- !.
bullet_focus(focus(_), S, ['{'|S]) :- !.
bullet_focus(B, S0, [B|S]) :- ( append(_, [B|S1], S0) -> S = S1 ; S = S0 ).

tac_row(row(close, _, _, _)) --> !, [].
tac_row(row(D, Bs, F-T, Ts)) -->
    { format(atom(Style), "--depth:~d", [D]), exclude(==('}'), Bs, Shown) },
    notes_before(F),
    el(div, "tac clause", [style=Style],
       ( el(span, bullet, seq(Shown, bullet_)),
         tactic_text(F, T, Ts) )),
    aside_after(T).

bullet_(B) --> { bullet_glyph(B, G) }, esc(G).

bullet_glyph('-', "–") :- !.
bullet_glyph('+', "+") :- !.
bullet_glyph('*', "∗") :- !.
bullet_glyph(focus(N), G) :- !, format(string(G), "~w: {", [N]).
bullet_glyph(B, B).

% One tactic tree for the source, timeline and snapshot heading. The raw
% source remains available when a tactic extension is not understood.
tactic_text(F, To, Ts) -->
    { rocq_tactic_tokens(Ts, T), src_text(F-To, Raw),
      ( tactic_env(F, To, Env) -> true ; nb_current(rq_proof_env, Env) -> true ; Env = [] ) }, !,
    el(span, "tactic", [title=Raw], tactic_block(T, Env)).
tactic_text(F, T, Ts) --> el(span, "tactic rq-unparsed", tac_tokens(Ts, F, T)).

% Locals before and after the command include both consumed hypotheses
% and newly introduced patterns. Read only their names, not their types.
tactic_env(F, T, Env) :-
    nb_getval(rq_states, States), States \== none,
    dict_pairs(States, _, Pairs),
    findall(O, ( member(K-_, Pairs), atom_number(K, O), O =< F ), Earlier),
    max_list(Earlier, Previous), atom_number(PrevKey, Previous), get_dict(PrevKey, States, Before),
    atom_number(Key, T), get_dict(Key, States, After), append(Before, After, Goals),
    findall(N, ( member(G, Goals), member(H, G.hypotheses),
                 once(sub_string(H, I, 1, _, ":")), sub_string(H, 0, I, _, Head),
                 split_string(Head, ", \n\t", "", Ns), member(S, Ns), S \== "", atom_string(N, S) ), Names),
    sort(Names, Env).

tactic_block(tmatch(K, Subject, Bs), Env) --> !,
    el(span, "rq-tac-match", ( el(span, "goal rq-tac-head", ( kw(K), " ", tactic_subject(Subject, Env), " ", kw("with") )),
        el(span, "cases match", tactic_branches(Bs, Env)), el(span, "rq-tac-end", kw("end")) )).
tactic_block(tbin(Op, L, R), Env) -->
    { tactic_structural(L) ; tactic_structural(R) }, !,
    el(span, "rq-tac-seq", ( el(span, "rq-tac-left", tactic_block(L, Env)),
        el(span, "rq-tac-sep", esc(Op)), el(span, "rq-tac-right", tactic_block(R, Env)) )).
tactic_block(prefix(K, T), Env) --> { tactic_structural(T) }, !,
    el(span, "rq-tac-prefix", ( kw(K), " ", tactic_block(T, Env) )).
tactic_block(do(N, T), Env) --> { tactic_structural(T) }, !,
    el(span, "rq-tac-prefix", ( el(span, none, ( kw(do), " ", esc(N) )), " ", tactic_block(T, Env) )).
tactic_block(select(S, T), Env) --> !,
    el(span, "rq-tac-select", ( el(span, "rq-selector", ( esc(S), ":" )), " ", tactic_block(T, Env) )).
tactic_block(choices(K, Ts), Env) --> { member(T, Ts), tactic_structural(T) }, !,
    el(span, "rq-tac-choices", ( kw(K), el(span, "l rq-tac-options", tactic_options(Ts, Env)) )).
tactic_block(dispatch(T, Ts), Env) --> { tactic_structural(T) ; member(B, Ts), tactic_structural(B) }, !,
    el(span, "rq-tac-seq", ( el(span, "rq-tac-left", tactic_block(T, Env)),
        el(span, "rq-tac-sep", ";"), el(span, "l rq-tac-options", tactic_options(Ts, Env)) )).
tactic_block(tlet(n(_, X), V, B), Env) --> { tactic_structural(B) }, !,
    el(span, "rq-tac-let", ( el(span, "goal rq-tac-head", ( kw("let"), " ", var_def(X), "\u00A0", defeq, " ", tactic_inline(V, Env), " ", kw("in") )),
                             tactic_block(B, [X|Env]) )).
tactic_block(tletrec(n(_, X), Args, V, B), Env) --> !,
    { maplist([n(_, A), A]>>true, Args, Ns), append(Ns, [X|Env], Inner) },
    el(span, "rq-tac-let", ( el(span, "goal rq-tac-head", ( kw("let rec"), " ", var_def(X), " ", vars(Args), "\u00A0", defeq )),
        tactic_block(V, Inner), el(span, "goal rq-tac-head", kw("in")), tactic_block(B, [X|Env]) )).
tactic_block(tgroup(T), Env) --> { tactic_structural(T) }, !,
    el(span, "rq-tac-group", ( "(", tactic_block(T, Env), ")" )).
tactic_block(T, Env) --> el(span, "goal rq-tac-inline", tactic_inline(T, Env)).

tactic_structural(tmatch(_, _, _)).
tactic_structural(choices(_, Ts)) :- member(T, Ts), tactic_structural(T).
tactic_structural(dispatch(T, Ts)) :- ( tactic_structural(T) ; member(B, Ts), tactic_structural(B) ).
tactic_structural(select(_, _)).
tactic_structural(prefix(_, T)) :- tactic_structural(T).
tactic_structural(do(_, T)) :- tactic_structural(T).
tactic_structural(tgroup(T)) :- tactic_structural(T).
tactic_structural(tlet(_, _, B)) :- tactic_structural(B).
tactic_structural(tletrec(_, _, _, _)).
tactic_structural(tbin(_, L, R)) :- ( tactic_structural(L) ; tactic_structural(R) ).

tactic_inline(tmatch(K, Subject, Bs), Env) --> tactic_block(tmatch(K, Subject, Bs), Env).
tactic_inline(tbin(Op, L, R), Env) -->
    el(span, "o rq-tac-chain", ['data-d'=op], ( tactic_inline(L, Env), " ",
        el(span, "op wide", [title=Op], esc(Op)), " ", tactic_inline(R, Env) )).
tactic_inline(prefix(K, T), Env) -->
    el(span, "c rq-tac-call", ['data-d'=args], ( kw(K), " ", el(span, "args rq-tac-args", el(span, arg, tactic_inline(T, Env))) )).
tactic_inline(do(N, T), Env) -->
    el(span, "c rq-tac-call", ['data-d'=args], ( kw(do), " ",
        el(span, "args rq-tac-args", ( el(span, arg, esc(N)), " ", el(span, arg, tactic_inline(T, Env)) )) )).
tactic_inline(tgroup(T), Env) --> el(span, paren, tactic_inline(T, Env)).
tactic_inline(choices(K, Ts), Env) -->
    el(span, "c rq-tac-call", ['data-d'=args], ( kw(K), " ",
        el(span, "args rq-tac-args", el(span, arg, tactic_alternatives(Ts, Env))) )).
tactic_inline(dispatch(T, Ts), Env) -->
    el(span, "o rq-tac-chain", ['data-d'=op], ( tactic_inline(T, Env), " ",
        el(span, "op wide", [title=";"], ";"), " ", tactic_alternatives(Ts, Env) )).
tactic_inline(tlet(n(_, X), V, B), Env) -->
    el(span, "o rq-tac-chain", ['data-d'=op], ( kw("let"), " ", var_def(X), "\u00A0", defeq, " ", tactic_inline(V, Env), " ",
        kw("in"), " ", tactic_inline(B, [X|Env]) )).
tactic_inline(tletrec(N, Args, V, B), Env) --> tactic_block(tletrec(N, Args, V, B), Env).
tactic_inline(teval(Ws, E), Env) -->
    { atomic_list_concat(Ws, ' ', Strategy) },
    el(span, "o rq-tac-chain", ['data-d'=op], ( kw(eval), " ", esc(Strategy), " ", kw("in"), " ", term(E, Env) )).
tactic_inline(call(N, []), Env) --> !, name_ref(N, Env, head).
tactic_inline(call(pose, [token(id(proof))|Ps]), Env) --> !,
    el(span, "c rq-tac-call", ['data-d'=args],
       ( name_ref(pose, Env, head), " ", kw(proof),
         ( { Ps == [] } -> [] ; " ", el(span, "args rq-tac-args", tactic_parts(Ps, Env)) ) )).
%  In the proof mode's tactics, a string is a pattern of hypothesis names.
tactic_inline(call(N, Ps), Env) -->
    { ( nb_current(rq_ipm, I0) -> true ; I0 = false ), ( ipm_tactic(N) -> I = true ; I = I0 ), nb_setval(rq_ipm, I) },
    el(span, "c rq-tac-call", ['data-d'=args], ( name_ref(N, Env, head), " ", el(span, "args rq-tac-args", tactic_parts(Ps, Env)) )),
    { nb_setval(rq_ipm, I0) }.
tactic_inline(empty, _) --> el(span, "rq-empty", []).
tactic_inline(rest(T), Env) --> tactic_inline(T, Env), "..".

ipm_tactic(N) :- atom_codes(N, [0'i, C|_]), between(0'A, 0'Z, C).

tactic_alternatives(Ts, Env) -->
    el(span, "l rq-tac-alternatives", tactic_chain(Ts, '|', tactic_inline, Env)).

% The same operator/argument groups as Gallina: short patterns stay a
% phrase, long sums and products break at their actual tree boundaries.
tactic_chain([T], _, Draw, Env) --> !, call(Draw, T, Env).
tactic_chain([T|Ts], Op, Draw, Env) -->
    el(span, o, ['data-d'=op], ( call(Draw, T, Env), " ",
        el(span, "op wide", [title=Op], esc(Op)), " ", tactic_chain(Ts, Op, Draw, Env) )).

tactic_parts([], _) --> [].
tactic_parts([P|Ps], Env) --> el(span, arg, tactic_part(P, Env)),
    ( { Ps == [] } -> [] ; " ", tactic_parts(Ps, Env) ).

tactic_part(ipm_intros(Is), Env) -->
    el(span, "c rq-intros", ['data-d'=args], el(span, "args rq-tac-args", ipm_items(Is, Env))).
tactic_part(ipm_as(Ps, Pat), Env) -->
    ( { Ps == [] } -> [] ; el(span, "paren rq-pattern", intro_items(Ps, Env)), " " ),
    ( { Pat = str(S) } -> ipm_pattern(S)
    ; { Pat = pure(P) }, el(span, "rq-ipm-pure", ( el(span, op, "%"), intro_pattern(Env, P) )) ).
tactic_part(ipm(H, Args, Spat), Env) -->
    el(span, "paren rq-ipm-term",
       ( ( { H = hyp(S) } -> ipm_pattern(S) ; term(H, Env) ),
         ( { Args == [] } -> [] ; " ", el(span, "op wide", [title="$!"], "$!"), " ", items(Args, Env) ),
         ( { Spat == none } -> [] ; " ", kw(with), " ", ipm_pattern(Spat) ) )).
tactic_part(terms(Es), Env) --> el(span, "c tuple", el(span, "args rq-tac-args", sep_items(Es, Env, ","))).
tactic_part(intro(Ps), Env) -->
    el(span, "c rq-intros", ['data-d'=args], el(span, "args rq-tac-args", intro_items(Ps, Env))).
tactic_part(clause(by, [tactic(T)]), Env) --> !,
    el(span, "c rq-tac-clause", ['data-d'=args], ( kw(by), " ", el(span, "args rq-tac-args", el(span, arg,
        ( { tactic_structural(T) } -> tactic_block(T, Env) ; tactic_inline(T, Env) ))) )).
tactic_part(clause(K, Ps), Env) -->
    el(span, "c rq-tac-clause", ['data-d'=args], ( kw(K), ( { K == eqn } -> ":" ; [] ), " ",
        el(span, "args rq-tac-args", tactic_parts(Ps, Env)) )).
tactic_part(term(E), Env) --> term(E, Env).
tactic_part(tactic(T), Env) --> el(span, paren, tactic_block(T, Env)).
tactic_part(binding(n(_, N), Op, E), Env) -->
    el(span, paren, ( var_def(N), "\u00A0", el(span, "op wide", [title=Op], esc(Op)), " ", term(E, Env) )).
tactic_part(context(E), Env) --> kw("context"), " [", term(E, Env), "]".
tactic_part(hyp(n(_, N), context(E)), Env) --> !,
    var_def(N), " : ", tactic_part(context(E), Env).
tactic_part(hyp(n(_, N), E), Env) -->
    var_def(N), " : ", term(E, Env).
tactic_part(group(Open, Ps, Close), Env) -->
    el(span, "l rq-token-group", ['data-d'=args], ( el(span, sep, esc(Open)), " ", tactic_parts(Ps, Env), " ", el(span, sep, esc(Close)) )).
tactic_part(token(id(X)), Env) --> !, name_ref(X, Env).
tactic_part(token(kw(X)), _) --> !, kw(X).
tactic_part(token(str(S)), _) --> { nb_current(rq_ipm, true) }, !, ipm_pattern(S).
tactic_part(token(str(S)), Env) --> !, term(str(0-0, S), Env).
tactic_part(token(K), _) --> { rocq_syntax:tok_text(K, S) }, el(span, "rq-token", esc(S)).

intro_pattern(_, ip_name(n(_, '_'))) --> !, term(hole(0-0), []).
intro_pattern(_, ip_name(n(_, N))) --> var_(N).
intro_pattern(_, ip_rewrite(Op)) -->
    { ( Op == '->' -> G = '→' ; G = '←' ) }, el(span, "op rq-rewrite", [title=Op], esc(G)).
intro_pattern(_, ip_auto(K)) --> el(span, "v anon", esc(K)).
intro_pattern(_, ip_fresh(n(_, N))) --> el(span, "rq-meta", ( "?", var_(N) )).
intro_pattern(_, ip_inj([])) --> !, el(span, "l rq-pattern", el(span, op, "=")).
intro_pattern(Env, ip_inj(Ps)) --> el(span, "l rq-pattern", ( el(span, op, "="), " ", intro_items(Ps, Env) )).
intro_pattern(Env, ip_and(Ps)) -->
    el(span, "paren rq-pattern rq-intro-and", tactic_chain(Ps, '&', intro_operand, Env)).
intro_pattern(Env, ip_or(Arms)) -->
    el(span, "l rq-pattern rq-intro-or", tactic_chain(Arms, '|', intro_sequence, Env)).
% A rewrite arrow is an operand here, not the chain's infix operator.
intro_operand(P, Env) --> el(span, arg, intro_pattern(Env, P)).
intro_sequence([], _) --> el(span, "rq-empty", []).
intro_sequence(Ps, Env) --> { Ps \== [] },
    el(span, "c rq-intros", ['data-d'=args], el(span, "args rq-tac-args", intro_items(Ps, Env))).
intro_items([P|Ps], Env) --> el(span, arg, intro_pattern(Env, P)),
    ( { Ps == [] } -> [] ; " ", intro_items(Ps, Env) ).

ipm_items([I|Is], Env) -->
    el(span, arg, ( { I = coq(Ps) } -> el(span, "paren rq-pattern", intro_items(Ps, Env)) ; { I = str(S) }, ipm_pattern(S) )),
    ( { Is == [] } -> [] ; " ", ipm_items(Is, Env) ).

%  A proof mode pattern, "[H1 %Hφ]": its names are the hypotheses', as
%  the proof state shows them, and its marks (% # $ [ ] & |) operators.
ipm_pattern(S) --> { string_codes(S, Cs) }, el(span, "rq-ipm", ipm_codes(Cs)).

ipm_codes([]) --> [].
ipm_codes([C|Cs0]) --> { ipm_name_char(C) }, !,
    { span(ipm_name_char, [C|Cs0], W, Cs), atom_codes(N, W) },
    ( { N == '_' } -> el(span, "v anon", "_") ; var_(N) ), ipm_codes(Cs).
ipm_codes([0' |Cs]) --> !, " ", ipm_codes(Cs).
ipm_codes([C|Cs]) --> el(span, "op rq-ipm-mark", esc_code(C)), ipm_codes(Cs).

ipm_name_char(C) :- code_type(C, csym) ; C == 0'' ; C >= 0x80, \+ memberchk(C, `□∗`).

tactic_subject(goal, _) --> kw("goal").
tactic_subject(type(E), Env) --> kw("type of"), " ", term(E, Env).
tactic_subject(term(E), Env) --> term(E, Env).

tactic_branches([], _) --> [].
tactic_branches([tbr(Ps, T)|Bs], Env) -->
    { findall(X, ( sub_term(meta(_, X), Ps) ; sub_term(hyp(n(_, X), _), Ps) ), Ns), append(Ns, Env, Env1) },
    el(span, case, ( el(span, cond, el(span, goals, el(span, "goal rq-tac-pattern",
                        el(span, "c rq-tac-call", ['data-d'=args], el(span, "args rq-tac-args", tactic_parts(Ps, Env1)))))),
                    el(span, arrow, "⇒"), el(span, then, el(span, goals, tactic_block(T, Env1))) )),
    tactic_branches(Bs, Env).

tactic_options([], _) --> [].
tactic_options([T|Ts], Env) -->
    el(span, "rq-tac-option", ( el(span, "rq-choice-bar", "|"), tactic_block(T, Env) )), tactic_options(Ts, Env).

tac_tokens([], O, T) --> { src_text(O-T, S) }, esc(S).
tac_tokens([t(K, F, To)|Ts], O, T) -->
    { src_text(O-F, Gap) }, esc(Gap),
    (   { K = id(X), global_ref(X, Href, Kind), kind_class(Kind, C) } -> el(a, C, [href=Href], esc(X))
    ;   { src_text(F-To, S) }, esc(S)
    ),
    tac_tokens(Ts, To, T).

%% Comments

notes_before(From) -->
    { nb_getval(rq_notes, Q0), partition([cm(O, _, _, _)]>>(O < From), Q0, Now, Q), nb_setval(rq_notes, Q) },
    seq(Now, note_).

%  The comments inside a sentence that nothing above drew, after it.
notes_upto(To) --> notes_before(To).

%  Comments among table rows: a row of their own.
notes_rows(From, Cols) -->
    { nb_getval(rq_notes, Q0), partition([cm(O, _, _, _)]>>(O < From), Q0, Now, Q), nb_setval(rq_notes, Q) },
    seq(Now, [C]>>el(tr, note, el(td, none, [colspan=Cols], note_(C)))).

note_(cm(_, _, Text, _)) -->
    { comment_heading(Text, Level, Title) }, !,
    { heading_id(Title, Id), format(atom(H), "h~d", [Level]), comment_prose_lines(Text, Lines0),
      ( Lines0 = [_|Rest] -> true ; Rest = [] ) },
    el(H, "rq-sec", [id=Id], rocq_prose_inline(Title)),
    ( { exclude(blank, Rest, []) } -> [] ; el(div, "rq-doc", rocq_prose(Rest)) ).
note_(cm(_, _, Text, _)) --> { sub_atom(Text, 0, _, _, '(**') }, !,
    { comment_prose_lines(Text, Lines) }, el(div, "rq-doc", rocq_prose(Lines)).
note_(cm(_, _, Text, _)) --> { comment_prose_lines(Text, Lines) }, el(div, note, rocq_prose(Lines)).

%  A trailing comment at the end of the line where a row ends sits
%  beside it.
aside_after(To) -->
    { aside_text(To, S), S \== none }, !, el(span, aside, rocq_prose_inline(S)), aside_after(To).
aside_after(_) --> [].

aside_text(To, S) :-
    nb_getval(rq_notes, [cm(O, _, Text, trailing)|Q]), O >= To,
    nb_getval(rq_text, Src), L is O - To, sub_string(Src, To, L, _, Gap), \+ sub_string(Gap, _, _, _, "\n"),
    \+ sub_string(Gap, _, _, _, "|"), !,
    nb_setval(rq_notes, Q), comment_prose_lines(Text, Ls), atomic_list_concat(Ls, ' ', A), atom_string(A, S).
aside_text(_, none).

%  comment_heading(+Text, -Level, -Title): (** * Title *) is a section,
%  h2; ** a subsection, h3; *** h4. In Markdown, (** ## Title *) is a
%  section and ### a subsection (# is the file's own title).
comment_heading(Text, Level, Title) :-
    sub_atom(Text, 0, _, _, '(**'), sub_string(Text, 3, _, 2, Body0),
    split_string(Body0, "\n", "", [First|_]), split_string(First, "", " ", [L0]),
    string_codes(L0, Cs), append(Marks, [0' |Rest], Cs), Marks = [M|_], memberchk(M, `*#`),
    forall(member(S, Marks), S == M), !,
    length(Marks, N0), ( M == 0'# -> N is N0 - 1, N >= 1 ; N = N0 ),
    Level is N + 1, Level =< 4,
    string_codes(Title0, Rest), split_string(Title0, "", " ", [Title]).

heading_id(Title, Id) :-
    downcase_atom(Title, D), atom_codes(D, Cs),
    maplist([C, W]>>( code_type(C, alnum) -> W = C ; W = 0'  ), Cs, Ws),
    atom_codes(A, Ws), atomic_list_concat(Parts, ' ', A), exclude(==(''), Parts, Ps),
    atomic_list_concat([sec|Ps], '-', Id).

%  comment_prose_lines(+Text, -Lines): a comment's text, without its
%  markers and common indentation.
comment_prose_lines(Text, Lines) :-
    ( sub_atom(Text, 0, _, _, '(**') -> K = 3 ; K = 2 ),
    sub_string(Text, K, _, 2, Body),
    split_string(Body, "\n", "", Ls00),
    maplist(rtrim, Ls00, Ls0),
    (   Ls0 = [First0|More], split_string(First0, "", " ", [First]), First \== ""
    ->  dedent(More, More1), Ls1 = [First|More1]
    ;   Ls1 = Ls0
    ),
    trim_blank_ends(Ls1, Ls2), dedent(Ls2, Lines).

rtrim(S0, S) :- string_codes(S0, Cs0), reverse(Cs0, R0), span([C]>>memberchk(C, ` \t`), R0, _, R), reverse(R, Cs),
    string_codes(S, Cs).

%% Prose

%  rocq_prose(+Lines): a comment's lines in dterm's little Markdown, with
%  coqdoc's [term] drawn as Rocq.
rocq_prose(Lines0) --> { dedent(Lines0, Lines), blocks(Lines, Bs) }, el(div, prose, seq(Bs, block_)).

block_(p(T)) --> el(p, none, rocq_prose_inline(T)).
block_(ul(Items)) --> el(ul, none, seq(Items, [T]>>el(li, none, rocq_prose_inline(T)))).
block_(pre(Lines)) --> { dedent(Lines, Ls), atomic_list_concat(Ls, '\n', T) }, el(pre, none, esc(T)).
block_(h(N, T)) --> { format(atom(H), "h~d", [N]) }, el(H, "prose-h", rocq_prose_inline(T)).
block_(table(Head, Rows)) -->
    el(table, "prose-table", ( el(thead, none, el(tr, none, seq(Head, [C]>>el(th, none, rocq_prose_inline(C))))),
                               el(tbody, none, seq(Rows, [R]>>el(tr, none, seq(R, [C]>>el(td, none, rocq_prose_inline(C)))))) )).
block_(embed(Name)) --> concept_embed(Name).
block_(fence(Lang, Lines)) --> { memberchk(Lang, ["rocq", "coq", ""]) }, !, rocq_fence(Lines).
block_(fence("c", Lines)) --> c_fence(Lines), !.
block_(fence(_, Lines)) --> { atomic_list_concat(Lines, '\n', T) }, el(pre, fence, esc(T)).

rocq_prose_inline(Text) --> { text_codes(Text, Cs) }, pi(Cs).

pi([]) --> !, [].
%  [[name]] and [[name|text]] link to a concept node (web/concepts.pl).
pi([0'[, 0'[|Cs0]) --> { concept_link_codes(Cs0, Name, Shown, Cs) }, !, concept_ref(Name, Shown), pi(Cs).
%  [text](url) is a link (in an embedded concept, from docs/concepts;
%  in a .v file's comment, from its directory); [term] is Rocq (coqdoc),
%  or code.
pi([0'[|Cs0]) --> { append(T, [0'], 0'(|Cs1], Cs0), \+ memberchk(0'], T), append(U, [0')|Cs], Cs1), \+ memberchk(0' , U) }, !,
    { string_codes(TS, T), atom_codes(UA, U), prose_href(UA, Href) },
    el(a, none, [href=Href], rocq_prose_inline(TS)), pi(Cs).
pi([0'[|Cs0]) --> { bracketed(Cs0, 1, Code, Cs) }, !, code_(Code), pi(Cs).
pi([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0) }, !, code_(Code), pi(Cs).
pi(Cs0) --> { word(Cs0, W, Cs1), W \== [] }, !, word_(W, Cs1).
pi([C|Cs]) --> esc_code(C), pi(Cs).

%  prose_href(+Url, -Href): a link written in a concept or a .v file, as
%  the site has it from a Rocq page. A .v file's relative link is first
%  made relative to docs/concepts, where concept_url/3 reads links.
prose_href(Url, Href) :-
    ( nb_current(rq_concepts, Pre) -> true ; Pre = '../' ),
    (   nb_current(rq_embedding, true) -> concept_url(Url, Pre, Href)
    ;   nb_current(rq_file, File), atom(File), file_name_extension(_, v, File),
        \+ sub_atom(Url, _, _, _, ':'), \+ sub_atom(Url, 0, _, _, '#')
    ->  ( sub_atom(Url, B, _, _, '#') -> sub_atom(Url, 0, B, _, Path), sub_atom(Url, B, _, 0, Frag) ; Path = Url, Frag = '' ),
        atomic_list_concat(Dir0, '/', File), append(Dir, [_], Dir0), reverse(Dir, Dir1),
        atomic_list_concat(Steps, '/', Path),
        foldl([S, R0, R]>>( S == '..' -> R0 = [_|R] ; S == '.' -> R = R0 ; R = [S|R0] ), Steps, Dir1, Rev),
        reverse(Rev, Repo),
        (   Repo = [nanofil, docs, D] -> Rel = ['..', D]
        ;   Repo = [nanofil|In] -> append(['..', '..'], In, Rel)
        ;   append(['..', '..', '..'], Repo, Rel)
        ),
        atomic_list_concat(Rel, '/', R1), atom_concat(R1, Frag, ConceptUrl),
        concept_url(ConceptUrl, Pre, Href)
    ;   Href = Url
    ).

%% Concepts

%  concept_ref(+Name, +Shown): a link to the concept Name, with its
%  summary in a card shown on hover, as dterm's predicate references
%  have (rq_concepts is the concept pages' directory, relative to this
%  page). Without concepts loaded it is its text.
concept_ref(_, Shown) --> { \+ concepts_loaded }, !, esc(Shown).
concept_ref(Name, Shown) --> { concept_resolve(Name, Id) }, !,
    { concept_href(Id, Href), concept_title(Id, Title), concept_summary(Id, Sum0), concept_plain(Sum0, Sum) },
    el(span, "pref cref", ( el(a, concept, [href=Href], esc(Shown)),
                           ( { nb_current(rq_in_card, true) } -> []
                           ; el(span, "sigcard concept-card", ['aria-hidden'=true],
                                ( el(span, "card-mod", ( esc(Title), rq_kind(Id) )),
                                  el(span, "card-text", in_card(rocq_prose_inline(Sum))) )) ) )).
concept_ref(Name, Shown) -->
    { nb_current(rq_file, F) -> true ; F = none },
    { format(user_error, "dterm-rocq: ~w: [[~w]] names no concept~n", [F, Name]) },
    el(span, broken, esc(Shown)).

concept_href(Id, Href) :-
    concept_page(Id, Page),
    ( nb_current(rq_concepts, Pre) -> true ; Pre = '../' ),
    atom_concat(Pre, Page, Href).

%  rq_kind(+Id): the mark, Fil-C or nanofil, that the concept pages give.
rq_kind(Id) --> { concept_kind(Id, K, _) }, !,
    { K == 'Fil-C' -> C = "kind kind-filc" ; K == 'Iris' -> C = "kind kind-iris" ; C = "kind kind-nanofil" }, " ", el(span, C, esc(K)).
rq_kind(_) --> [].

%  A card's text links nothing: no cards in cards, no names (rq_button).
in_card(G) -->
    { ( nb_current(rq_button, B0) -> true ; B0 = false ), nb_setval(rq_in_card, true), nb_setval(rq_button, true) },
    call(G),
    { nb_setval(rq_in_card, false), nb_setval(rq_button, B0) }.

%  concept_embed(+Name): ![[name]], the concept's whole text where it is
%  written, under its title. An embed inside an embed is a link.
concept_embed(Name) --> { \+ concepts_loaded }, !, el(p, none, esc(Name)).
concept_embed(Name) --> { nb_current(rq_embedding, true) }, !, el(p, none, concept_ref(Name, Name)).
concept_embed(Name) --> { concept_resolve(Name, Id) }, !,
    { concept_href(Id, Href), concept_title(Id, Title), concept(Id, _, Lines) },
    el(aside, "concept-embed",
       ( el(a, "concept-embed-title", [href=Href], ( esc(Title), rq_kind(Id) )),
         { nb_setval(rq_embedding, true) }, rocq_prose(Lines), { nb_setval(rq_embedding, false) } )).
concept_embed(Name) --> el(p, none, concept_ref(Name, Name)).

%  The text up to the ] that closes a [.
bracketed([0']|Cs], 1, [], Cs) :- !.
bracketed([0']|Cs0], D, [0']|B], Cs) :- !, D1 is D - 1, bracketed(Cs0, D1, B, Cs).
bracketed([0'[|Cs0], D, [0'[|B], Cs) :- !, D1 is D + 1, bracketed(Cs0, D1, B, Cs).
bracketed([C|Cs0], D, [C|B], Cs) :- C \== 0'\n, bracketed(Cs0, D, B, Cs).

word(Cs0, W, Cs) :- span([C]>>code_type(C, csym), Cs0, W, Cs).

span(P, [C|Cs0], [C|W], Cs) :- call(P, C), !, span(P, Cs0, W, Cs).
span(_, Cs, [], Cs).

%  name/N, module:name/N and name.pl link to nanofil's Prolog.
word_(M, [0':|Cs0]) --> { word(Cs0, W, [0'/|Cs1]), W \== [], span([C]>>code_type(C, digit), Cs1, Ds, Cs), Ds \== [],
                          atom_codes(MA, M), atom_codes(N, W), prolog_href(MA, N, Ds, Href) }, !,
    { append([M, `:`, W, `/`, Ds], Text) }, el(a, "ref pl", [href=Href], el(code, none, esc(Text))), pi(Cs).
word_(W, [0'/|Cs1]) --> { span([C]>>code_type(C, digit), Cs1, Ds, Cs), Ds \== [], atom_codes(N, W),
                          rocq_prolog_pred(N, M), prolog_href(M, N, Ds, Href) }, !,
    { append([W, `/`, Ds], Text) }, el(a, "ref pl", [href=Href], el(code, none, esc(Text))), pi(Cs).
word_(W, [0'., 0'p, 0'l|Cs]) --> { \+ ( Cs = [C|_], code_type(C, csym) ), atom_codes(M, W), rocq_prolog_pred(_, M),
                                   nb_current(rq_prolog, Pre), Pre \== none, format(atom(Href), "~w~w.html", [Pre, M]) }, !,
    el(a, "ref pl", [href=Href], ( esc(W), ".pl" )), pi(Cs).
word_(W, Cs) --> esc(W), pi(Cs).

prolog_href(M, N, Ds, Href) :-
    rocq_prolog_pred(N, M), nb_current(rq_prolog, Pre), Pre \== none,
    atom_codes(A, Ds), format(atom(Id), "~w/~w", [N, A]), uri_encoded(fragment, Id, Frag),
    format(atom(Href), "~w~w.html#~w", [Pre, M, Frag]).

%  Code in prose: a reference to nanofil's Prolog, Rocq when it reads as
%  Rocq, else code.
%  `c: EXPR`, and unmarked C beyond doubt, are C (c/c_draw.pl).
code_(Code) --> c_inline(Code), !.
code_(Code) --> c_inline_auto(Code), !.
code_(Code) --> { prolog_ref(Code, Href) }, !, el(a, "ref pl", [href=Href], el(code, none, esc(Code))).
%  name(Args) without a space is Prolog, as the comments quote it.
code_(Code) --> { append(_, [C, 0'(|_], Code), code_type(C, csym) }, !, el(code, none, esc(Code)).
%  name/N that is not nanofil's (ctx/6 of a fact) stays code.
code_(Code) --> { \+ memberchk(0' , Code), memberchk(0'/, Code) }, !, el(code, none, esc(Code)).
code_(Code) --> { rocq_fragment_codes(Code, Frag) }, !, el(code, "term rq", fragment_(Frag)).
code_(Code) --> el(code, none, esc(Code)).

%% Rocq in documents

%  The same layout choice on source pages and documents containing Rocq.
%  Hidden until the enhancement is available; without JS, CSS stays adaptive.
rocq_layout -->
    el(div, "rq-layout", [hidden=hidden],
       ( el(label, none, [for="rq-layout"], "Rocq layout"),
         el(select, none, [id="rq-layout"],
            ( el(option, none, [value=auto], "Adaptive"),
              el(option, none, [value=stack], "Stacked"),
              el(option, none, [value=table], "Side by side") )) )).

%  rocq_inline(+Codes): inline code of a document that is Rocq: a
%  sentence (Theorem t : …), a type's constructors (cap := None | Obj b),
%  a record's fields (ptr := { addr : Z; … }), a typed name
%  (step : config -> outcome), or a term that only Rocq writes: an
%  application of a constructor (Trap r) or a proposition (f x = true).
%  Rocq in prose is spaced, so code without a space (module:name/N) is
%  not. Fails otherwise, so the document draws the code as it would.
rocq_inline(Codes) -->
    { memberchk(0' , Codes), rocq_fragment_codes(Codes, Frag), prose_fragment(Frag) },
    { nb_current(rq_page, P0) -> true ; P0 = none },
    { nb_setval(rq_page, none), ( nb_current(rq_mod, M0) -> true ; M0 = [] ), nb_setval(rq_mod, []) },
    el(code, "term rq", fragment_(Frag)),
    { nb_setval(rq_page, P0), nb_setval(rq_mod, M0) }.
%  A proof-mode tactic with its patterns: iDestruct "H" as "[H1 H2]".
rocq_inline(Codes) -->
    { memberchk(0' , Codes), catch(rocq_lex(Codes, Toks, []), _, fail),
      rocq_tactic_tokens(Toks, T), T = call(N, [_|_]), ipm_tactic(N) },
    el(code, "term rq", el(span, tactic, tactic_block(T, []))).

prose_fragment(sentence(S)) :- S \= raw(_, _), S \= dir(_, _).
prose_fragment(alts(_, _)).
prose_fragment(fields(_, _)).
prose_fragment(typed(_, _)).
prose_fragment(term(E)) :- rocq_only(E).

rocq_only(app(_, id(_, F), _)) :- atom_codes(F, [C|_]), between(0'A, 0'Z, C), \+ sub_atom(F, _, _, _, '.').
rocq_only(bin(_, Op, _, _)) :- memberchk(Op, [=, '<>', '->', '<->', '/\\', '\\/', '=?', '<=?', '::']).
rocq_only(chain(_, _, _)).
rocq_only(forall(_, _, _)).
rocq_only(exists(_, _, _)).
rocq_only(fun(_, _, _)).
rocq_only(match(_, _, _, _)).
%  Iris: P ∗ Q, P -∗ Q, ℓ ↦ v, ▷ P, ⌜φ⌝, |==> P, WP e {{ Φ }} and the like.
rocq_only(bin(_, Op, _, _)) :- memberchk(Op, ['∗', '-∗', '⊢', '⊣⊢', '==∗', '∗-∗', '~~>']).
rocq_only(pre(_, Op, _)) :- memberchk(Op, ['▷', '□', '◇', '■', '⊢', '|==>', '✓']) ; sub_atom(Op, 0, _, _, '<').
rocq_only(E) :- functor(E, F, _), memberchk(F, [pure, laterN, fupd, fupdw, stepupd, stepupdw, pointsto, indexed, wp, triple, bigop, bigall, ir_fn, ir_blk, ir_list, ir_inst]).
rocq_only(app(_, id(_, F), _)) :- memberchk(F, [own, inv, iProp, uPred]).
rocq_only(scope(_, _, 'I')).

fragment_(term(E)) --> { fragment_vars(E, Env) }, term(E, Env).
fragment_(typed(n(_, N), T)) --> el(span, "f def", esc(N)), opt_type(T, []).
fragment_(alts(n(_, N), Cs)) -->
    el(span, "ty def", esc(N)), "\u00A0", defeq, " ", alt_terms(Cs).
fragment_(fields(n(_, N), Fs)) -->
    el(span, "ty def", esc(N)), "\u00A0", defeq, " ",
    el(span, "c rec", ['data-d'=args], el(span, "args recbr curly", inline_fields(Fs))).
fragment_(sentence(S)) --> sentence_inline(S).

fragment_vars(id(_, X), [X]) :-
    \+ sub_atom(X, _, _, _, '_'), \+ is_ctor(X), \+ std_type(X), \+ global_ref(X, _, _), !.
fragment_vars(id(_, _), []) :- !.
fragment_vars(E, Vs) :-
    findall(X, ( sub_id(E, X), \+ is_ctor(X), \+ std_type(X), \+ global_ref(X, _, _), \+ app_head(E, X) ), Vs0),
    sort(Vs0, Vs).

app_head(app(_, id(_, X), _), X).
app_head(T, X) :- compound(T), T =.. [_, _|As], member(A, As), ( is_list(A) -> member(A1, A) ; A1 = A ), compound(A1), app_head(A1, X).

alt_terms([C]) --> !, alt_term(C).
alt_terms([C|Cs]) --> alt_term(C), " ", el(span, "op wide bar", "|"), " ", alt_terms(Cs).

%  A constructor written with its argument names: Obj base.
alt_term(app(_, id(_, C), As)) --> !,
    el(span, "c app", ['data-d'=args], ( el(span, a, esc(C)), el(span, args, items_vars(As)) )).
alt_term(E) --> term(E, []).

items_vars([E]) --> !, el(span, arg, var_or_term(E)).
items_vars([E|Es]) --> el(span, arg, var_or_term(E)), " ", items_vars(Es).
var_or_term(id(_, X)) --> { \+ is_ctor(X) }, !, var_(X).
var_or_term(E) --> term(E, []).

inline_fields([field(_, N, _, Ty, _)|Fs]) -->
    el(span, arg, ( el(span, "f def", esc(N)), opt_type(Ty, []), ( { Fs == [] } -> [] ; el(span, sep, ";") ) )),
    ( { Fs == [] } -> [] ; " ", inline_fields(Fs) ).
inline_fields([]) --> [].

sentence_inline(thm(_, Kw, n(_, N), Bs, Ty)) --> !,
    { binders_env(Bs, [], Env) },
    kw(Kw), " ", el(span, "lem def", esc(N)), binders_(Bs, []), "\u00A0", el(span, "op wide colon", ":"), " ", term(Ty, Env).
sentence_inline(def(_, Kw, n(_, N), Bs, Ty, B)) --> !,
    { binders_env(Bs, [], Env) },
    kw(Kw), " ", el(span, "f def", esc(N)), binders_(Bs, []), opt_type(Ty, Env),
    ( { B == none } -> [] ; "\u00A0", defeq, " ", term(B, Env) ).
sentence_inline(module(_, Kind, n(_, N), Bs, _)) --> !,
    { module_kw(Kind, K) }, kw(K), " ", el(span, "module-name", esc(N)), binders_(Bs, []).
sentence_inline(decl(_, Kw, [g(Ns, Ty)])) --> !, kw(Kw), " ", seq_defs(Ns), opt_type(Ty, []).
sentence_inline(ind(_, Kw, [ib(n(_, N), Bs, Ty, Cs)])) --> !,
    kw(Kw), " ", el(span, "ty def", esc(N)), binders_(Bs, []), opt_type(Ty, []), "\u00A0", defeq, " ",
    seq_bar(Cs).
sentence_inline(rec(_, Kw, n(_, N), Bs, _, _, Fs)) --> !,
    kw(Kw), " ", el(span, "ty def", esc(N)), binders_(Bs, []), "\u00A0", defeq, " ",
    el(span, "c rec", el(span, "args recbr curly", inline_fields(Fs))).
sentence_inline(notation(_, Kw, S, E, _)) --> kw(Kw), " ", notation_pattern(S, E), "\u00A0", defeq, " ", term(E, []).

seq_bar([ctor(_, C, Bs, Ty)]) --> !, el(span, a, esc(C)), binders_(Bs, []), opt_type(Ty, []).
seq_bar([ctor(_, C, Bs, Ty)|Cs]) --> el(span, a, esc(C)), binders_(Bs, []), opt_type(Ty, []), " ", el(span, "op wide bar", "|"), " ", seq_bar(Cs).

%  rocq_fence(+Lines): a ```rocq fence of a document, drawn as a page
%  draws its sentences. A fence that does not read stays text.
rocq_fence(Lines) -->
    { atomic_list_concat(Lines, '\n', A), atom_string(A, Text), string_codes(Text, Cs),
      catch(rocq_parse_codes(Cs, Items, Cms0), _, fail), \+ ( member(raw(_, _), Items) ),
      maplist(note_kind(Text), Cms0, Cms),
      ( nb_current(rq_page, P0) -> true ; P0 = none ),
      ( nb_current(rq_file, F0) -> true ; F0 = none ),
      ( nb_current(rq_text, T0) -> true ; T0 = "" ),
      ( nb_current(rq_notes, N0) -> true ; N0 = [] ),
      nb_setval(rq_page, none), nb_setval(rq_file, none), rocq_set_source(Text, Cms) }, !,
    el(div, "dterm-rocq rq-fence", rocq_items(Items)),
    { nb_setval(rq_page, P0), nb_setval(rq_file, F0), nb_setval(rq_text, T0), nb_setval(rq_notes, N0) }.
rocq_fence(Lines) --> { atomic_list_concat(Lines, '\n', T) }, el(pre, "fence lang-rocq", esc(T)).

%  prolog_ref(+Code, -Href): Code is name/N or module:name/N of nanofil's
%  Prolog.
prolog_ref(Code, Href) :-
    (   append(MW, [0':|Rest], Code), MW \== [], atom_codes(M, MW) -> true ; Rest = Code ),
    append(W, [0'/|Ds], Rest), W \== [], Ds \== [], forall(member(D, Ds), code_type(D, digit)),
    atom_codes(N, W), ( var(M) -> rocq_prolog_pred(N, M) ; true ),
    prolog_href(M, N, Ds, Href).
