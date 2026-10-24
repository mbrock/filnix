/*  dterm: nanofil's Prolog source as web pages.

    The Prolog counterpart of the luv wiki's dexp boxes. Every term is read
    with its positions and comments, and drawn by what it is rather than
    how it was typed:

    - a compound is its functor followed by a box whose side borders are
      the parentheses, so arguments flow and wrap with the page width;
    - a clause is its head over its body, one goal per row;
    - if-then-else chains are tables of condition and consequence, and a
      plain disjunction is a stack of alternatives;
    - a predicate made only of short facts is a table of its tuples;
    - PlDoc comments are signatures and prose, `%%` lines are sections;
    - comparison operators get their mathematical glyphs, and trailing
      digits of variables are subscripts, so S0 reads as a state.

    - a doc/3 fact before a predicate (docs/dterm.md) is its signature,
      argument table, prose, citations and examples; the examples are run
      when the pages are built, loading the module as bin/nanofil does,
      and each is marked with its result;
    - each predicate lists what it calls and what calls it.

    Calls to predicates defined in the corpus link to their definitions.

    Usage: swipl dterm.pl -- OUT SRC-DIR... Writes OUT/index.html and one
    OUT/NAME.html per SRC-DIR/NAME.pl; dterm.css and dterm.js are expected
    beside the pages. Runs on SWI-Prolog only: it relies on read_term/3's
    comments and subterm_positions options.
*/
:- module(dterm, []).
:- encoding(utf8).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(uri)).

:- initialization(main, main).

github('https://github.com/mbrock/filnix/blob/main/nanofil/').

% Operators the sources use beyond ISO and SWI's defaults: library(clpz).
:- op(760, yfx, dterm_syntax:(#<==>)).
:- op(750, xfy, dterm_syntax:(#==>)).
:- op(750, yfx, dterm_syntax:(#<==)).
:- op(740, yfx, dterm_syntax:(#\/)).
:- op(730, yfx, dterm_syntax:(#\)).
:- op(720, yfx, dterm_syntax:(#/\)).
:- op(710,  fy, dterm_syntax:(#\)).
:- op(700, xfx, dterm_syntax:(#>)).
:- op(700, xfx, dterm_syntax:(#<)).
:- op(700, xfx, dterm_syntax:(#>=)).
:- op(700, xfx, dterm_syntax:(#=<)).
:- op(700, xfx, dterm_syntax:(#=)).
:- op(700, xfx, dterm_syntax:(#\=)).
:- op(450, xfx, dterm_syntax:(..)).
:- op(700, xfx, dterm_syntax:(in)).
:- op(700, xfx, dterm_syntax:(ins)).
% PlDoc modes, for reading signatures.
:- op(200, fy, dterm_sig:(?)).
:- op(200, fy, dterm_sig:(@)).
:- op(200, fy, dterm_sig:(!)).
:- op(200, fy, dterm_sig:(:)).

main :-
    current_prolog_flag(argv, [Out|Dirs]),
    findall(F, (member(D, Dirs), directory_file_path(D, '*.pl', P),
                expand_file_name(P, Fs), member(F, Fs)), Files0),
    sort(Files0, Files),
    maplist(read_source, Files, Sources),
    maplist(index_source, Sources),
    maplist(run_examples(Files), Sources),
    maplist(write_source_page(Out, Sources), Sources),
    directory_file_path(Out, 'index.html', Index),
    write_page(Index, index_page(Sources)).

%% Reading

%  src(Base, Text, Lines, Events): the file Base.pl as its text, the
%  character offset of each line start, and its clauses and comment groups
%  in source order.

read_source(File, src(Base, Text, Lines, Events)) :-
    file_base_name(File, Name),
    file_name_extension(Base, _, Name),
    read_file_to_string(File, Text, [encoding(utf8)]),
    line_starts(Text, Lines),
    setup_call_cleanup(open(File, read, S, [encoding(utf8)]),
                       read_clauses(S, Clauses, Comments0),
                       close(S)),
    append(Comments0, Comments),
    events(Clauses, Comments, Events).

read_clauses(S, Clauses, [Comments|Css]) :-
    read_term(S, T, [variable_names(Vs), subterm_positions(P),
                     comments(Cs), double_quotes(string),
                     module(dterm_syntax), term_position(TP)]),
    foldl(comment, Cs, Comments, []),
    (   T == end_of_file
    ->  Clauses = [], Css = []
    ;   name_variables(T, Vs),
        stream_position_data(line_count, TP, L),
        Clauses = [c(T, P, L, [])|Clauses1],
        read_clauses(S, Clauses1, Css)
    ).

%  A comment as one cm(Char, Line, Col, Text) per line, except a block
%  comment, which stays whole.
comment(Pos-Text, Cms0, Cms) :-
    stream_position_data(char_count, Pos, Char),
    stream_position_data(line_count, Pos, Line),
    stream_position_data(line_position, Pos, Col),
    (   string_concat("/*", _, Text)
    ->  Cms0 = [cm(Char, Line, Col, Text)|Cms]
    ;   split_string(Text, "\n", "", Parts),
        comment_lines(Parts, Char, Line, Col, Cms0, Cms)
    ).

comment_lines([], _, _, _, Cms, Cms).
comment_lines([T|Ts], Char, Line, Col, [cm(Char, Line, Col, T)|Cms0], Cms) :-
    string_length(T, Len),
    Char1 is Char + Len + 1, Line1 is Line + 1,
    comment_lines(Ts, Char1, Line1, 0, Cms0, Cms).

name_variables(T, Vs) :-
    maplist([N=V]>>(V = '$VAR'(N)), Vs),
    term_variables(T, Anon),
    maplist(=('$VAR'('_')), Anon).

line_starts(Text, ls(Starts)) :-
    string_codes(Text, Cs),
    findall(O, (O = 0 ; nth0(O0, Cs, 0'\n), O is O0 + 1), Os),
    Starts =.. [l|Os].

%  The line, counting from 1, of character offset O.
offset_line(ls(Starts), O, Line) :-
    functor(Starts, _, N),
    bsearch(Starts, O, 1, N, Line).

bsearch(_, _, L, L, L) :- !.
bsearch(S, O, L, H, Line) :-
    M is (L + H + 1) // 2,
    arg(M, S, X),
    (   X =< O -> bsearch(S, O, M, H, Line)
    ;   M1 is M - 1, bsearch(S, O, L, M1, Line)
    ).

%  Clauses with the comments inside them, and top-level comment groups,
%  in order.
events([], Cms, Es) :- groups(Cms, Es).
events([c(T, P, L, _)|Cs], Cms0, Es) :-
    arg(1, P, From), arg(2, P, To),
    partition([cm(O, _, _, _)]>>(O < From), Cms0, Before, Cms1),
    partition([cm(O, _, _, _)]>>(O < To), Cms1, Inside, Cms2),
    groups(Before, Gs),
    append(Gs, [clause(c(T, P, L, Inside))|Es1], Es),
    events(Cs, Cms2, Es1).

%  Consecutive full-line % comments form one group, as do the lines of a
%  PlDoc comment (%! then %) or of a %% section.
groups([], []).
groups([cm(_, L, _, Text)|Cms0], [G|Gs]) :-
    string_concat("/*", _, Text), !,
    G = group(block, L, [Text]),
    groups(Cms0, Gs).
groups([cm(_, L, _, Text)|Cms0], [group(Kind, L, [Text|Texts])|Gs]) :-
    line_kind(Text, Kind),
    group_lines(Kind, L, Cms0, Texts, Cms),
    groups(Cms, Gs).

line_kind(Text, doc) :- string_concat("%!", _, Text), !.
line_kind(Text, section) :- string_concat("%%", _, Text), !.
line_kind(_, note).

group_lines(Kind, L, [cm(_, L1, _, Text)|Cms0], [Text|Texts], Cms) :-
    L1 =:= L + 1,
    \+ string_concat("/*", _, Text),
    line_kind(Text, K1),
    continues(Kind, K1), !,
    group_lines(Kind, L1, Cms0, Texts, Cms).
group_lines(_, _, Cms, [], Cms).

continues(doc, doc).
continues(doc, note).
continues(section, section).
continues(note, note).

%  The text of a comment group's lines without comment markers, as a
%  list of strings, indentation kept.
group_text(group(block, _, [Text]), Lines) :- !,
    sub_string(Text, 2, _, 2, Body0),
    string_concat("  ", Body0, Body),
    split_string(Body, "\n", "", Lines0),
    trim_blank_ends(Lines0, Lines).
group_text(group(_, _, Texts), Lines) :-
    maplist(uncomment, Texts, Lines).

uncomment(Text, Line) :-
    string_codes(Text, Cs),
    phrase((marks, rest(R)), Cs),
    string_codes(Line, R).

marks --> "%", !, marks.
marks --> "!", !.
marks --> [].
rest(R, R, []).

trim_blank_ends(Ls0, Ls) :-
    exclude_leading_blank(Ls0, Ls1),
    reverse(Ls1, R1),
    exclude_leading_blank(R1, R2),
    reverse(R2, Ls).

exclude_leading_blank([L|Ls0], Ls) :- blank(L), !, exclude_leading_blank(Ls0, Ls).
exclude_leading_blank(Ls, Ls).

blank(S) :- split_string(S, "", " \t", [""]).

%% The corpus: what is defined where

:- dynamic defined/3, exported/2.

%  defined(Name/Arity, File, Id): Name/Arity is defined in File.pl at the
%  anchor Id. A DCG nonterminal name//N is stored with arity N + 2.
index_source(src(Base, _, _, Events)) :-
    forall(member(clause(c(T, _, _, _)), Events),
           ( clause_key(T, Key) -> define(Key, Base), index_calls(Base, Key, T) ; true )),
    forall(( member(clause(c((:- module(_, Exports)), _, _, _)), Events),
             member(E, Exports) ),
           ( export_key(E, K) -> assertz(exported(K, Base)) ; true )).

define(Key, Base) :-
    key_pred(Key, PI),
    (   defined(PI, Base, _) -> true
    ;   key_id(Key, Id), assertz(defined(PI, Base, Id))
    ).

export_key(N/A, N/A).
export_key(N//A, N/A2) :- A2 is A + 2.

key_pred(N/A, N/A).
key_pred(N//A, N/A2) :- A2 is A + 2.

key_id(N/A, Id) :- format(atom(Id), "~w/~w", [N, A]).
key_id(N//A, Id) :- format(atom(Id), "~w//~w", [N, A]).

clause_key((:- _), _) :- !, fail.
clause_key(doc(_, _, _), _) :- !, fail.
clause_key((H --> _), N//A) :- !,
    (   H = (H1, _) -> true ; H1 = H ),
    callable(H1), functor(H1, N, A).
clause_key((H :- _), N/A) :- !, callable(H), functor(H, N, A).
clause_key(H, N/A) :- callable(H), functor(H, N, A).

%  resolve(File, PI, Def, Id): a call to PI from File means the
%  definition in Def.pl at anchor Id: the file's own, else an exported one.
resolve(File, PI, File, Id) :- defined(PI, File, Id), !.
resolve(_, PI, F, Id) :- exported(PI, F), defined(PI, F, Id), !.
resolve(_, PI, F, Id) :- defined(PI, F, Id), !.

%  The href for a call to Name/Arity from File, if the corpus defines it.
pred_href(File, PI, Href) :-
    resolve(File, PI, F, Id),
    ( F == File -> Prefix = '' ; atom_concat(F, '.html', Prefix) ),
    uri_encoded(fragment, Id, Frag),
    format(atom(Href), "~w#~w", [Prefix, Frag]).

%% The call graph

:- dynamic calls/3.

%  calls(File, FromPI, ToPI): a clause of FromPI in File.pl calls ToPI,
%  which may or may not be defined in the corpus.
index_calls(Base, Key, T) :-
    key_pred(Key, From),
    (   clause_body(T, B, Mode)
    ->  forall(( body_call(B, Mode, To), To \== From, \+ calls(Base, From, To) ),
               assertz(calls(Base, From, To)))
    ;   true
    ).

clause_body((_ :- B), B, goal).
clause_body((_ --> B), B, dcg).

%  body_call(G, Mode, PI): goal G, in Mode goal or dcg, calls PI.
body_call('$VAR'(_), _, _) :- !, fail.
body_call(G, _, _) :- \+ callable(G), !, fail.
body_call((A, B), M, PI) :- !, ( body_call(A, M, PI) ; body_call(B, M, PI) ).
body_call((A ; B), M, PI) :- !, ( body_call(A, M, PI) ; body_call(B, M, PI) ).
body_call((A -> B), M, PI) :- !, ( body_call(A, M, PI) ; body_call(B, M, PI) ).
body_call((A *-> B), M, PI) :- !, ( body_call(A, M, PI) ; body_call(B, M, PI) ).
body_call(\+ A, M, PI) :- !, body_call(A, M, PI).
body_call(_:G, M, PI) :- !, body_call(G, M, PI).
body_call({}(G), dcg, PI) :- !, body_call(G, goal, PI).
body_call(G, dcg, _) :- ( G == [] ; G = [_|_] ; string(G) ), !, fail.
body_call(G, M, PI) :-
    G =.. [N|As], length(As, A0), extra_args(M, K), A is A0 + K,
    (   PI = N/A
    ;   meta_args(G, Metas), member(I-Spec, Metas), nth1(I, As, X),
        meta_call(Spec, X, PI)
    ).

meta_call(goal, X, PI) :- body_call(X, goal, PI).
meta_call(dcg, X, PI) :- body_call(X, dcg, PI).
meta_call(closure(K), X, N/A) :-
    callable(X), X \= '$VAR'(_), functor(X, N, A0), A is A0 + K.

%% Running the examples

:- dynamic ran/4.

%  ran(File, Head, I, Result): the Ith example of the doc/3 fact for Head
%  in File.pl gave Result, pass or fail. Modules that declare doc/3 are
%  loaded on SWI with src/swi/compat.pl, as bin/nanofil runs them.
run_examples(Files, src(Base, _, _, Events)) :-
    (   memberchk(clause(c((:- module(M, _)), _, _, _)), Events),
        memberchk(clause(c(doc(_, _, _), _, _, _)), Events)
    ->  file_name_extension(Base, pl, Name),
        member(File, Files), file_base_name(File, Name), !,
        file_directory_name(File, Dir),
        directory_file_path(Dir, 'swi/compat.pl', Compat),
        load_files(user:Compat, [if(not_loaded), silent(true)]),
        load_files(user:File, [if(not_loaded), silent(true)]),
        forall(( M:doc(H, _, Ps), nth1(I, Ps, E), example_form(E) ),
               ( functor(H, HN, HA), example_result(M, E, R),
                 assertz(ran(Base, HN/HA, I, R)) ))
    ;   true
    ).

example_form(example(_)).
example_form(example(_, _)).
example_form(fails(_)).

example_result(M, E, R) :-
    (   catch(example_holds(M, E), _, fail) -> R = pass ; R = fail ).

example_holds(M, example(G)) :- once(M:G).
example_holds(M, example(G, C)) :- once(( M:G, M:C )).
example_holds(M, fails(G)) :- \+ M:G.

%% Page structure

%  The entries of a file: prose, sections, directives and predicates.
%  A predicate collects its consecutive clauses and the notes between
%  them; a PlDoc comment just before it is its documentation.
entries([], []).
entries([clause(c(doc(H, Det, Ps), P, L, _))|Es0], [pred(Key, dterm(H, Det, Ps, P, L), Items)|Es]) :- !,
    functor(H, N, A),
    (   Es0 = [clause(c(T, _, _, _))|_], clause_key(T, Key0), ( Key0 = N/A ; Key0 = N//A )
    ->  Key = Key0, pred_items(Key, Es0, Items, Es1)
    ;   Key = N/A, Items = [], Es1 = Es0
    ),
    entries(Es1, Es).
entries([group(doc, L, Ts)|Es0], [pred(Key, Doc, Items)|Es]) :-
    Es0 = [clause(C)|_], C = c(T, _, _, _), clause_key(T, Key), !,
    Doc = doc(group(doc, L, Ts)),
    pred_items(Key, Es0, Items, Es1),
    entries(Es1, Es).
entries([group(note, L, Ts)|Es0], [pred(Key, note(group(note, L, Ts)), Items)|Es]) :-
    Es0 = [clause(C)|_], C = c(T, _, L1, _), clause_key(T, Key),
    length(Ts, N), L1 =:= L + N, !,
    pred_items(Key, Es0, Items, Es1),
    entries(Es1, Es).
entries([group(K, L, Ts)|Es0], [E|Es]) :- !,
    group_entry(K, group(K, L, Ts), E),
    entries(Es0, Es).
entries([clause(C)|Es0], [E|Es]) :-
    C = c(T, _, _, _),
    (   clause_key(T, Key)
    ->  E = pred(Key, none, Items),
        pred_items(Key, [clause(C)|Es0], Items, Es1)
    ;   E = directive(C), Es1 = Es0
    ),
    entries(Es1, Es).

group_entry(section, G, section(Title)) :- G = group(_, _, [_]), !,
    group_text(G, [Title0]),
    split_string(Title0, "", " ", [Title]).
group_entry(_, G, prose(G)).

pred_items(Key, [clause(C)|Es0], [clause(C)|Items], Es) :-
    C = c(T, _, _, _), clause_key(T, Key), !,
    pred_items(Key, Es0, Items, Es).
pred_items(Key, Es0, Items, Es) :-
    append(Notes, [clause(C)|Es1], Es0),
    maplist([group(note, _, _)]>>true, Notes),
    C = c(T, _, _, _), clause_key(T, Key), !,
    append(Notes, [clause(C)|Items1], Items),
    pred_items(Key, Es1, Items1, Es).
pred_items(_, Es, [], Es).

%% HTML

write_page(Path, Body) :-
    phrase(Body, Cs),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
                       format(S, "~s", [Cs]),
                       close(S)).

esc(X) --> { text_codes(X, Cs) }, esc_codes(Cs).

text_codes(X, Cs) :- string(X), !, string_codes(X, Cs).
text_codes(X, Cs) :- atom(X), !, atom_codes(X, Cs).
text_codes(X, Cs) :- is_list(X), !, Cs = X.
text_codes(X, Cs) :- format(codes(Cs), "~w", [X]).

esc_codes([]) --> [].
esc_codes([C|Cs]) --> esc_code(C), esc_codes(Cs).

esc_code(0'<) --> !, "&lt;".
esc_code(0'>) --> !, "&gt;".
esc_code(0'&) --> !, "&amp;".
esc_code(0'") --> !, "&quot;".
esc_code(C) --> [C].

raw(X) --> { text_codes(X, Cs) }, Cs.

%  el(Tag, Class, Body): an element with a class attribute (none for no
%  class).
el(Tag, Class, Body) --> el(Tag, Class, [], Body).
el(Tag, Class, Attrs, Body) -->
    "<", raw(Tag),
    (   { Class == none } -> [] ; " class=\"", raw(Class), "\"" ),
    attrs(Attrs), ">", Body, "</", raw(Tag), ">".

attrs([]) --> [].
attrs([K=V|As]) --> " ", raw(K), "=\"", esc(V), "\"", attrs(As).

seq([], _) --> [].
seq([X|Xs], G) --> call(G, X), seq(Xs, G).

%% Terms

%  term(T, Pos, Prec, Ctx): T at most priority Prec, drawn as data.
%  Ctx is ctx(File, Role), Role head for the defining occurrence.

unparen(P0, P) :- nonvar(P0), P0 = parentheses_term_position(_, _, P1), !, unparen(P1, P).
unparen(P, P).

args_pos(P, N, As) :-
    (   nonvar(P), P = term_position(_, _, _, _, As0) -> As = As0
    ;   length(As, N)
    ).

term(T, P0, Prec, Ctx) --> { unparen(P0, P) }, term_(T, P, Prec, Ctx).

term_('$VAR'(N), _, _, _) --> !, var_(N).
term_(T, P, _, _) --> { number(T) }, !, { source_text(P, T, Src) }, el(span, n, esc(Src)).
term_(T, P, _, _) --> { string(T) }, !, { source_text(P, T, Src) }, el(span, s, esc(Src)).
term_(T, _, _, _) --> { T == [] }, !, el(span, "l empty", "[]").
term_(T, _, Prec, Ctx) --> { atom(T) }, !, atom_(T, Prec, Ctx).
term_(T, P, _, Ctx0) --> { T = [_|_] }, !, { head_args_ctx(Ctx0, Ctx) }, list_(T, P, Ctx).
term_({}(G), P, _, Ctx) --> !,
    { nonvar(P), P = brace_term_position(_, _, GP) -> true ; GP = _ },
    el(span, braces, term(G, GP, 1200, Ctx)).
term_(T, P, Prec, Ctx0) --> { op_form(T, Form) }, !, { head_args_ctx(Ctx0, Ctx) }, op_term(Form, T, P, Prec, Ctx).
term_(T, P, _, Ctx) --> compound_(T, P, Ctx).

source_text(P, T, Src) :-
    (   nonvar(P), P = From-To, nb_getval(dterm_text, Text),
        Len is To - From, sub_string(Text, From, Len, _, Src0)
    ->  Src = Src0
    ;   format(string(Src), "~q", [T])
    ).

var_('_') --> !, el(span, "v anon", "_").
var_(N) -->
    { atom_codes(N, Cs),
      append(Stem0, Digits, Cs), Stem0 \== [],
      maplist([C]>>code_type(C, digit), Digits), !,
      ( Digits \== [], append(Stem, `_`, Stem0), Stem \== [] -> true ; Stem = Stem0 ),
      ( Cs = [0'_|_] -> Class = "v anon" ; Class = v ) },
    el(span, Class, ['data-v'=N],
       ( esc(Stem), ( { Digits == [] } -> [] ; el(sub, none, esc(Digits)) ) )).

atom_(T, Prec, ctx(_, head)) --> !, el(span, "f def", atom_text(T, Prec)).
atom_(T, Prec, _) --> el(span, a, atom_text(T, Prec)).

atom_text(T, Prec) -->
    { format(codes(Cs), "~q", [T]),
      ( current_op(P, _, dterm_syntax:T), P > Prec -> Paren = true ; Paren = false ) },
    ( { Paren == true } -> "(", esc(Cs), ")" ; esc(Cs) ).

compound_(T, P, Ctx) -->
    { compound_name_arguments(T, N, As), length(As, Arity), args_pos(P, Arity, Ps) },
    { head_args_ctx(Ctx, ACtx) },
    el(span, c, ( functor_(N, Arity, Ctx), args(As, Ps, ACtx) )).

head_args_ctx(ctx(F, head), ctx(F, pattern)) :- !.
head_args_ctx(Ctx, Ctx).

functor_(N, _, ctx(_, head)) --> !, el(span, "f def", esc_q(N)).
functor_(N, _, ctx(_, pattern)) --> !, el(span, "f pat", esc_q(N)).
functor_(N, _, _) --> el(span, f, esc_q(N)).

esc_q(N) --> { format(codes(Cs), "~q", [N]) }, esc(Cs).

args(As, Ps, Ctx) --> el(span, args, arg_list(As, Ps, Ctx)).

arg_list([A], [P], Ctx) --> !, el(span, arg, term(A, P, 999, Ctx)).
arg_list([A|As], [P|Ps], Ctx) -->
    el(span, arg, ( term(A, P, 999, Ctx), el(span, sep, ",") )),
    arg_list(As, Ps, Ctx).

list_(T, P, Ctx) -->
    { list_parts(T, Es, Tail),
      (   nonvar(P), P = list_position(_, _, EPs, TP) -> true
      ;   length(Es, N), length(EPs, N), TP = none ) },
    el(span, l, ( list_elems(Es, EPs, Tail, TP, Ctx) )).

list_parts(L, Es, Tail) :-
    (   nonvar(L), L = [E|L1] -> Es = [E|Es1], list_parts(L1, Es1, Tail)
    ;   L == [] -> Es = [], Tail = []
    ;   Es = [], Tail = L
    ).

list_elems([E], [P], Tail, TP, Ctx) --> !,
    el(span, arg, term(E, P, 999, Ctx)),
    (   { Tail == [] } -> []
    ;   el(span, bar, "|"), el(span, arg, term(Tail, TP, 999, Ctx))
    ).
list_elems([E|Es], [P|Ps], Tail, TP, Ctx) -->
    el(span, arg, ( term(E, P, 999, Ctx), el(span, sep, ",") )),
    list_elems(Es, Ps, Tail, TP, Ctx).

%  Operators. op_form(T, Form): T is written with an operator, Form one of
%  infix(Type, P), prefix(Type, P), postfix(Type, P).
op_form(T, infix(Type, P)) :-
    compound(T), compound_name_arity(T, N, 2),
    current_op(P, Type, dterm_syntax:N), infix_type(Type), !.
op_form(T, prefix(Type, P)) :-
    compound(T), compound_name_arity(T, N, 1),
    current_op(P, Type, dterm_syntax:N), prefix_type(Type),
    arg(1, T, A), \+ number(A), !.

infix_type(xfx). infix_type(xfy). infix_type(yfx).
prefix_type(fy). prefix_type(fx).

op_term(infix(Type, P), T, Pos, Prec, Ctx) -->
    { T =.. [N, L, R], args_pos(Pos, 2, [LP, RP]),
      arg_prec(Type, P, LPrec, RPrec), op_class(N, Class) },
    paren_if(P, Prec,
             el(span, o, ( term(L, LP, LPrec, Ctx), op_(N, Class), term(R, RP, RPrec, Ctx) ))).
op_term(prefix(Type, P), T, Pos, Prec, Ctx) -->
    { T =.. [N, A], args_pos(Pos, 1, [AP]),
      ( Type == fy -> APrec = P ; APrec is P - 1 ) },
    paren_if(P, Prec, el(span, "o pre", ( op_(N, tight), term(A, AP, APrec, Ctx) ))).

arg_prec(xfx, P, L, L) :- L is P - 1.
arg_prec(xfy, P, L, P) :- L is P - 1.
arg_prec(yfx, P, P, R) :- R is P - 1.

paren_if(P, Prec, Body) --> ( { P > Prec } -> el(span, paren, Body) ; Body ).

op_class(N, tight) :- memberchk(N, [/, //, :, -, ^, '**']), !.
op_class(N, comma) :- N == ',', !.
op_class(_, wide).

op_(N, Class) -->
    { op_glyph(N, G) -> true ; format(codes(G), "~w", [N]) },
    { format(atom(Title), "~w", [N]) },
    { atom_concat('op ', Class, C) },
    el(span, C, [title=Title], esc(G)).

op_glyph(=<, "≤").
op_glyph(>=, "≥").
op_glyph(\=, "≠").
op_glyph(==, "≡").
op_glyph(\==, "≢").
op_glyph(=\=, "≠").
op_glyph(#=<, "#≤").
op_glyph(#>=, "#≥").
op_glyph(#\=, "#≠").
op_glyph(->, "→").
op_glyph(\+, "¬").
op_glyph(*, "×").
op_glyph(-, "−").

%% Goals

%  body(G, Pos, Ctx): G in goal position, Ctx ctx(File, goal | dcg).
%  A conjunction is a column of rows, with the comments between them.

body(G, P0, Ctx) -->
    { unparen(P0, P), conj_list(G, P, Gs) },
    el(div, goals, rows(Gs, Ctx)).

conj_list(G, P0, Gs) :-
    unparen(P0, P),
    (   nonvar(G), G = (A, B)
    ->  args_pos(P, 2, [PA, PB]),
        conj_list(A, PA, As), conj_list(B, PB, Bs), append(As, Bs, Gs)
    ;   Gs = [G-P]
    ).

rows([], _) --> [].
rows([G-P|Gs], Ctx) -->
    { pos_from(P, From) }, notes_before(From),
    el(div, goal, ( goal(G, P, Ctx), aside_after(P) )),
    rows(Gs, Ctx).

pos_from(P, From) :- ( nonvar(P), arg(1, P, From), integer(From) -> true ; From = inf ).
pos_to(P, To) :- ( nonvar(P), arg(2, P, To), integer(To) -> true ; To = inf ).

goal(G, P0, Ctx) --> { unparen(P0, P) }, goal_(G, P, Ctx).

goal_('$VAR'(N), _, _) --> !, var_(N).
goal_(!, _, _) --> !, el(span, cut, [title="cut"], "!").
goal_(G, P, Ctx) --> { nonvar(G), G = (_;_) }, !, alternatives(G, P, Ctx).
goal_(G, P, Ctx) --> { nonvar(G), ( G = (_->_) ; G = (_*->_) ) }, !, alternatives(G, P, Ctx).
goal_(G, P, Ctx) --> { nonvar(G), G = (_,_) }, !, el(div, "paren block", body(G, P, Ctx)).
goal_(\+ G, P, Ctx) --> !,
    { args_pos(P, 1, [GP]) },
    el(span, not, ( el(span, "op neg", [title="\\+"], "¬"), negated(G, GP, Ctx) )).
goal_({}(G), P, ctx(F, dcg)) --> !,
    { nonvar(P), P = brace_term_position(_, _, GP) -> true ; GP = _ },
    el(div, "braces block", body(G, GP, ctx(F, goal))).
goal_(G, P, ctx(F, dcg)) --> { is_list(G) ; string(G) ; G = [_|_] }, !,
    el(span, terminals, term(G, P, 999, ctx(F, data))).
goal_(M:G, P, Ctx) --> { atom(M) }, !,
    { args_pos(P, 2, [_, GP]) },
    el(span, qualified, ( el(span, module, esc(M)), el(span, "op tight", ":"), goal(G, GP, Ctx) )).
goal_(G, P, Ctx) --> { callable(G), \+ op_form(G, _) ; meta_args(G, _) }, !, call_(G, P, Ctx).
goal_(G, P, ctx(F, _)) --> term(G, P, 999, ctx(F, goal)).

negated(G, P, Ctx) -->
    (   { nonvar(G), ( G = (_,_) ; G = (_;_) ; G = (_->_) ) }
    ->  el(div, "paren block", body(G, P, Ctx))
    ;   goal(G, P, Ctx)
    ).

%  A call: the functor links to the definition when the corpus has one;
%  arguments the predicate calls are drawn as goals.
call_(G, P, ctx(F, Mode)) -->
    { G =.. [N|As], length(As, A0),
      extra_args(Mode, K), A is A0 + K,
      ( pred_href(F, N/A, Href) -> true ; Href = none ),
      ( meta_args(G, Metas) -> true ; Metas = [] ),
      args_pos(P, A0, Ps) },
    (   { As == [] }
    ->  call_name(N, Href)
    ;   el(span, "c call", ( call_name(N, Href), call_args(As, Ps, 1, Metas, F) ))
    ).

call_name(N, none) --> !, el(span, "f call", esc_q(N)).
call_name(N, Href) --> el(a, "f call", [href=Href], esc_q(N)).

call_args(As, Ps, I, Metas, F) --> el(span, args, call_arg_list(As, Ps, I, Metas, F)).

call_arg_list([A|As], [P|Ps], I, Metas, F) -->
    { ( As == [] -> Sep = [] ; Sep = el(span, sep, ",") ) },
    el(span, arg, ( meta_arg(A, P, I, Metas, F), Sep )),
    { I1 is I + 1 },
    ( { As == [] } -> [] ; call_arg_list(As, Ps, I1, Metas, F) ).

meta_arg(A, P, I, Metas, F) -->
    (   { memberchk(I-Spec, Metas) }
    ->  meta_arg_(Spec, A, P, F)
    ;   term(A, P, 999, ctx(F, data))
    ).

meta_arg_(goal, A, P, F) --> !,
    (   { nonvar(A), ( A = (_,_) ; A = (_;_) ; A = (_->_) ) }
    ->  el(div, "paren block", body(A, P, ctx(F, goal)))
    ;   goal(A, P, ctx(F, goal))
    ).
meta_arg_(dcg, A, P, F) --> !,
    (   { nonvar(A), A = (_,_) }
    ->  el(div, "paren block", body(A, P, ctx(F, dcg)))
    ;   goal(A, P, ctx(F, dcg))
    ).
meta_arg_(closure(K), A, P, F) -->
    { callable(A), A \= '$VAR'(_), \+ op_form(A, _),
      functor(A, N, A0), Ar is A0 + K, pred_href(F, N/Ar, _) }, !,
    goal(A, P, ctx(F, closure(K))).
meta_arg_(_, A, P, F) --> term(A, P, 999, ctx(F, data)).

%  A call in Mode has K more arguments than it is written with: two in
%  a DCG body, K for a closure.
extra_args(dcg, 2) :- !.
extra_args(closure(K), K) :- !.
extra_args(_, 0).

%  The arguments of the meta-predicates the sources use that are goals,
%  DCG bodies or closures.
meta_args(G, Metas) :-
    compound(G), compound_name_arity(G, N, A), meta_spec(N, A, Metas).

meta_spec(findall, 3, [2-goal]).
meta_spec(findall, 4, [2-goal]).
meta_spec(forall, 2, [1-goal, 2-goal]).
meta_spec(aggregate_all, 3, [2-goal]).
meta_spec(once, 1, [1-goal]).
meta_spec(ignore, 1, [1-goal]).
meta_spec(call, 1, [1-goal]).
meta_spec(catch, 3, [1-goal, 3-goal]).
meta_spec(setup_call_cleanup, 3, [1-goal, 2-goal, 3-goal]).
meta_spec(phrase, 2, [1-dcg]).
meta_spec(phrase, 3, [1-dcg]).
meta_spec(N, A, [1-closure(K)]) :-
    memberchk(N, [maplist, foldl, include, exclude, partition, call, foldl_, aggregate_all]),
    closure_extra(N, A, K).

closure_extra(maplist, A, K) :- K is A - 1.
closure_extra(foldl, A, K) :- K is A - 2.
closure_extra(include, 3, 1).
closure_extra(exclude, 3, 1).
closure_extra(partition, 4, 1).
closure_extra(call, A, K) :- A > 1, K is A - 1.

%  Comments inside a clause are queued in dterm_notes in source order;
%  a row first draws the ones before it, and a comment that ends the
%  line of a goal is drawn beside it.
notes_before(From) -->
    { nb_getval(dterm_notes, Q0),
      partition([cm(O, _, _, _)]>>(O @< From), Q0, Now, Q),
      nb_setval(dterm_notes, Q) },
    notes(Now).

notes([]) --> [].
notes([cm(_, _, _, Text)|Cs]) --> el(div, note, inline_comment(Text)), notes(Cs).

aside_after(P) -->
    { pos_to(P, To), integer(To),
      nb_getval(dterm_notes, [cm(O, L, _, Text)|Q]),
      nb_getval(dterm_lines, Lines),
      offset_line(Lines, To, L1), L1 =:= L, O >= To }, !,
    { nb_setval(dterm_notes, Q) },
    el(span, aside, inline_comment(Text)).
aside_after(_) --> [].

inline_comment(Text) -->
    { group_text(group(note, 0, [Text]), Ls0) -> true ; Ls0 = [Text] },
    { ( string_concat("/*", _, Text) -> group_text(group(block, 0, [Text]), Ls0b) ; Ls0b = Ls0 ),
      atomic_list_concat(Ls0b, ' ', S0), split_string(S0, "", " ", [S]) },
    inline(S, []).

%  If-then-else chains and disjunctions: a table of rows, each a
%  condition and its consequence, or a plain alternative.
alternatives(G, P, Ctx) -->
    { alt_list(G, P, Alts) },
    (   { memberchk(if(_, _, _, _, _), Alts) }
    ->  el(div, cases, case_rows(Alts, none, Ctx))
    ;   el(div, alts, alt_rows(Alts, first, Ctx))
    ).

alt_list(G, P0, Alts) :-
    unparen(P0, P),
    (   nonvar(G), G = (A ; B)
    ->  args_pos(P, 2, [PA, PB]),
        alt(A, PA, Alt), alt_list(B, PB, Alts1), Alts = [Alt|Alts1]
    ;   alt(G, P, Alt), Alts = [Alt]
    ).

alt(G, P0, Alt) :-
    unparen(P0, P),
    (   nonvar(G), G = (C -> T) -> args_pos(P, 2, [CP, TP]), Alt = if(->, C, CP, T, TP)
    ;   nonvar(G), G = (C *-> T) -> args_pos(P, 2, [CP, TP]), Alt = if(*->, C, CP, T, TP)
    ;   Alt = plain(G, P)
    ).

case_rows([], _, _) --> [].
case_rows([if(Op, C, CP, T, TP)|As], _, Ctx) -->
    { pos_from(CP, From) }, notes_before(From),
    { ( Op == (->) -> Arrow = "→" ; Arrow = "*→" ), format(atom(Title), "~w", [Op]) },
    el(div, case, ( el(div, cond, body(C, CP, Ctx)),
                    el(div, arrow, [title=Title], raw(Arrow)),
                    el(div, then, body(T, TP, Ctx)) )),
    case_rows(As, if, Ctx).
case_rows([plain(G, P)|As], Prev, Ctx) -->
    { pos_from(P, From), ( Prev == if -> Label = "else" ; Prev == none -> Label = "" ; Label = "or" ) },
    notes_before(From),
    el(div, "case plain", ( el(div, cond, el(span, kw, [title=";"], raw(Label))),
                            el(div, arrow, []),
                            el(div, then, body(G, P, Ctx)) )),
    case_rows(As, plain, Ctx).

alt_rows([], _, _) --> [].
alt_rows([plain(G, P)|As], First, Ctx) -->
    { pos_from(P, From) }, notes_before(From),
    ( { First == first } -> [] ; el(div, or, [title=";"], "or") ),
    el(div, alt, body(G, P, Ctx)),
    alt_rows(As, rest, Ctx).

%% Clauses

clause_(c(T, P, L, Inner), F) -->
    { nb_setval(dterm_notes, Inner), unparen(P, P1) },
    clause_body(T, P1, L, F),
    { nb_getval(dterm_notes, Left), nb_setval(dterm_notes, []) },
    ( { Left == [] } -> [] ; el(div, "notes trailing", notes(Left)) ).

clause_body((H :- B), P, L, F) --> !,
    { args_pos(P, 2, [HP, BP]) },
    el(div, "clause rule", ['data-line'=L],
       ( el(div, head, ( line_link(L, F), term(H, HP, 1199, ctx(F, head)),
                         el(span, neck, [title=":-"], "←") )),
         body(B, BP, ctx(F, goal)) )).
clause_body((H --> B), P, L, F) --> !,
    { args_pos(P, 2, [HP0, BP]), unparen(HP0, HP) },
    el(div, "clause dcg", ['data-line'=L],
       ( el(div, head, ( line_link(L, F), dcg_head(H, HP, F),
                         el(span, neck, [title="-->"], "⟶") )),
         body(B, BP, ctx(F, dcg)) )).
clause_body(H, P, L, F) -->
    el(div, "clause fact", ['data-line'=L],
       el(div, head, ( line_link(L, F), term(H, P, 1199, ctx(F, head)) ))).

dcg_head((H, PB), P, F) --> !,
    { args_pos(P, 2, [HP, PBP]) },
    term(H, HP, 999, ctx(F, head)), el(span, pushback, ( el(span, sep, ","), term(PB, PBP, 999, ctx(F, data)) )).
dcg_head(H, P, F) --> term(H, P, 999, ctx(F, head)).

line_link(L, F) -->
    { github(G), format(atom(Href), "~wsrc/~w.pl#L~w", [G, F, L]) },
    el(a, ln, [href=Href, title="source line"], esc(L)).

%  Directives: the module header, imports, and the rest as terms.
directive_(c((:- module(M, Exports)), _, _, _), F) --> !,
    el(div, "module-decl",
       ( el(span, kw, "module"), el(span, "f def", esc(M)),
         el(div, exports, ( el(span, label, "exports"), seq(Exports, export_(F)) )) )).
directive_(c((:- use_module(Spec)), _, _, _), F) --> !,
    el(div, uses, ( el(span, kw, "uses"), use_(Spec, F) )).
directive_(c((:- use_module(Spec, Imports)), P, _, _), F) --> !,
    { args_pos(P, 1, [DP]), args_pos(DP, 2, [_, IP]) },
    el(div, uses, ( el(span, kw, "uses"), use_(Spec, F), term(Imports, IP, 999, ctx(F, data)) )).
directive_(c((:- G), P, L, Inner), F) --> !,
    { nb_setval(dterm_notes, Inner), args_pos(P, 1, [GP]) },
    el(div, "clause directive", ['data-line'=L],
       el(div, head, ( line_link(L, F), el(span, neck, [title=":-"], ":-"), goal(G, GP, ctx(F, goal)) ))).
directive_(C, F) --> clause_(C, F).

export_(F, E) -->
    { export_key(E, PI), ( pred_href(F, PI, Href) -> true ; Href = '#' ),
      format(codes(Cs), "~q", [E]) },
    el(a, export, [href=Href], esc(Cs)).

use_(library(L), _) --> !, el(span, lib, esc(L)).
use_(M, _) --> { atom(M), defined(_, M, _) }, !,
    { format(atom(Href), "~w.html", [M]) },
    el(a, lib, [href=Href], esc(M)).
use_(M, _) --> el(span, lib, esc_q(M)).

%% Predicates

pred_(Key, Doc, Items, F) -->
    { key_id(Key, Id), key_pred(Key, PI),
      include([clause(_)]>>true, Items, Cs), length(Cs, NC),
      ( NC > 1 -> Class = "pred multi" ; Class = pred ),
      xrefs(F, PI, Callees, Callers) },
    el(section, Class, [id=Id],
       ( el(div, "pred-main",
            ( doc_(Doc, Key, F),
              (   { fact_table(Items, Key) }
              ->  facts_table(Items, Key, F)
              ;   seq(Items, item_(F))
              ) )),
         xref_aside(Callees, Callers) )).

%  The predicates in the corpus that PI in File calls, and those that call
%  it, as Def-Id pairs.
xrefs(F, PI, Callees, Callers) :-
    findall(D-Id, ( calls(F, PI, To), resolve(F, To, D, Id) ), Callees0),
    sort(Callees0, Callees),
    findall(F2-Id, ( calls(F2, From, PI), resolve(F2, PI, F, _),
                     defined(From, F2, Id) ), Callers0),
    sort(Callers0, Callers).

xref_aside([], []) --> !, [].
xref_aside(Callees, Callers) -->
    el(aside, xref,
       ( xref_list("calls", Callees), xref_list("called by", Callers) )).

xref_list(_, []) --> !, [].
xref_list(Title, Refs) -->
    { length(Refs, N), nb_getval(dterm_file, F) },
    el(div, "xref-group",
       ( el(div, "xref-title", ( esc(Title), " ", el(span, count, esc(N)) )),
         el(ul, none, seq(Refs, xref_item(F))) )).

xref_item(F, D-Id) -->
    { uri_encoded(fragment, Id, Frag),
      ( D == F -> format(atom(Href), "#~w", [Frag]) ; format(atom(Href), "~w.html#~w", [D, Frag]) ) },
    el(li, none, el(a, none, [href=Href],
                    ( esc(Id), ( { D == F } -> [] ; el(span, file, ( " ", esc(D) )) ) ))).

item_(F, clause(C)) --> clause_(C, F).
item_(F, G) --> { G = group(_, _, _) }, el(div, "prose between", prose_group(G, [], F)).

%  A predicate of at least three short facts is a table of its tuples.
fact_table(Items, N/A) :-
    A > 0,
    include([clause(_)]>>true, Items, Cs), length(Cs, Len), Len >= 3,
    forall(member(clause(c(T, _, _, _)), Cs),
           ( T \= (_ :- _), T \= (_ --> _), functor(T, N, A),
             format(atom(S), "~q", [T]), atom_length(S, SL), SL =< 110 )).

facts_table(Items, N/1, F) --> { maplist([clause(_)]>>true, Items) }, !,
    el(div, "facts set",
       ( el(span, "f def", esc_q(N)), el(span, args, seq(Items, fact_value(F))) )).
facts_table(Items, N/A, F) -->
    el(table, facts,
       ( el(caption, none, el(span, "f def", esc_q(N))),
         el(tbody, none, seq(Items, fact_row(A, F))) )).

fact_row(_, F, clause(c(T, P, L, Inner))) --> !,
    { nb_setval(dterm_notes, Inner), T =.. [_|As], length(As, Ar), args_pos(P, Ar, Ps) },
    el(tr, none, ['data-line'=L],
       ( el(td, ln, line_link(L, F)), seq_pairs(As, Ps, F) )),
    { nb_setval(dterm_notes, []) }.
fact_row(A, F, G) -->
    { Span is A + 1 },
    el(tr, note, el(td, none, [colspan=Span], prose_group(G, [], F))).

fact_value(F, clause(c(T, P, L, _))) -->
    { arg(1, T, X), args_pos(P, 1, [XP]) },
    el(span, arg, ['data-line'=L], term(X, XP, 999, ctx(F, data))).

seq_pairs([], [], _) --> [].
seq_pairs([A|As], [P|Ps], F) --> el(td, none, term(A, P, 999, ctx(F, data))), seq_pairs(As, Ps, F).

%  PlDoc: the signatures, then the prose with the argument names marked.
doc_(none, _, _) --> [].
doc_(dterm(H, Det, Ps, _, L), Key, F) -->
    { findall(N, sub_term('$VAR'(N), H), Vars0), sort(Vars0, Vars),
      ( Key = _//_ -> Dcg = true ; Dcg = false ),
      include([P]>>(P = also(_, _)), Ps, Alsos),
      include([P]>>(P = ('$VAR'(_): _)), Ps, Args),
      include([P]>>(P = cites(_)), Ps, Cites),
      doc_paragraphs(Ps, Paras),
      include(example_form, Ps, _) },
    el(div, "doc dterm-doc",
       ( signature_(F, sig(H is Det, Dcg)),
         seq(Alsos, also_(F, Dcg)),
         ( { Args == [] } -> [] ; el(table, modes, el(tbody, none, seq(Args, mode_row(H, Vars, F)))) ),
         seq(Paras, para_(Vars, F)),
         ( { Cites == [] } -> [] ; el(div, cites, seq(Cites, cite_)) ),
         examples_(Ps, H, L, F) )).
doc_(note(G), Key, F) -->
    { group_text(G, Lines0), dedent(Lines0, Lines),
      atomic_list_concat(Lines, '\n', Joined0), atom_string(Joined0, Joined),
      key_name(Key, Name), sig_prefix(Joined, Name, SigText, Rest),
      sig_term(SigText, Sig), Sig = sig(_, _), !,
      sig_vars(Sig, [], Vars),
      split_string(Rest, "\n", "", RestLines) },
    el(div, doc, ( signature_(F, Sig), el(div, prose, prose_lines(RestLines, Vars, F)) )).
doc_(note(G), _, F) --> el(div, "doc plain", prose_group(G, [], F)).
doc_(doc(G), _, F) -->
    { group(_, _, Texts) = G,
      partition([T]>>string_concat("%!", _, T), Texts, SigTexts, ProseTexts),
      maplist(sig_parse, SigTexts, Sigs),
      foldl(sig_vars, Sigs, [], Vars) },
    el(div, doc,
       ( seq(Sigs, signature_(F)),
         prose_group(group(note, 0, ProseTexts), Vars, F) )).


key_name(N/_, N).
key_name(N//_, N).

%  A note that starts with the predicate's own head, as name(+A, -B): or
%  name(+A)//: before its prose, is a signature too.
sig_prefix(Text, Name, Sig, Rest) :-
    atom_length(Name, NL),
    sub_string(Text, 0, NL, _, Name),
    sub_string(Text, NL, 1, _, "("),
    string_codes(Text, Cs),
    length(Pre, NL), append(Pre, [0'(|Cs1], Cs),
    close_paren(Cs1, 1, After0, Inside),
    (   After0 = [0'/, 0'/|After1] -> Slashes = `//` ; After1 = After0, Slashes = [] ),
    (   append(Det, [0':|After2], After1), \+ memberchk(0'\n, Det), \+ memberchk(0'(, Det)
    ->  true
    ;   append(Det, [0'.|After2], After1), \+ memberchk(0'\n, Det)
    ->  true
    ;   Det = [], After2 = After1
    ),
    append([Pre, `(`, Inside, Slashes, Det], SigCs),
    string_codes(Sig0, SigCs), split_string(Sig0, "", " ", [Sig]),
    string_codes(Rest0, After2), split_string(Rest0, "", " ", [Rest]).

%  close_paren(Cs, Depth, After, Inside): Inside ends with the parenthesis
%  that closes depth Depth.
close_paren([0')|Cs], 1, Cs, [0')]) :- !.
close_paren([C|Cs], D0, After, [C|Inside]) :-
    (   C == 0'( -> D is D0 + 1
    ;   C == 0') -> D is D0 - 1
    ;   D = D0
    ),
    close_paren(Cs, D, After, Inside).
sig_parse(Text, Sig) :-
    sub_string(Text, 2, _, 0, S0),
    sig_term(S0, Sig).

sig_term(S0, Sig) :-
    split_string(S0, "", " .", [S1]),
    (   sub_string(S1, B, _, A, "//"), sub_string(S1, 0, B, _, H), A0 is A,
        sub_string(S1, _, A0, 0, After), \+ sub_string(H, _, _, _, " is "),
        ( After == "" ; string_concat(" ", _, After) )
    ->  string_concat(H, After, S2), Dcg = true
    ;   S2 = S1, Dcg = false
    ),
    (   catch(term_string(T, S2, [module(dterm_sig), variable_names(Vs)]), _, fail)
    ->  name_variables(T, Vs), Sig = sig(T, Dcg)
    ;   Sig = raw(S1)
    ).

sig_vars(raw(_), Vs, Vs).
sig_vars(sig(T, _), Vs0, Vs) :-
    findall(N, sub_term('$VAR'(N), T), Ns),
    append(Vs0, Ns, Vs).

signature_(_, raw(S)) --> el(div, sig, el(code, none, esc(S))).
signature_(F, sig(T, Dcg)) -->
    { ( T = (H is Det) -> true ; H = T, Det = none ) },
    el(div, sig,
       ( sig_head(H, F),
         ( { Dcg == true } -> el(span, "kw dcg", "//") ; [] ),
         ( { Det == none } -> [] ; el(span, det, esc(Det)) ) )).

sig_head(H, F) -->
    { compound(H) -> compound_name_arguments(H, N, As) ; N = H, As = [] },
    el(span, c,
       ( el(span, "f def", esc_q(N)),
         ( { As == [] } -> [] ; el(span, args, sig_args(As, F)) ) )).

sig_args([A|As], F) -->
    { ( As == [] -> Sep = [] ; Sep = el(span, sep, ",") ) },
    el(span, arg, ( sig_arg(A, F), Sep )),
    ( { As == [] } -> [] ; sig_args(As, F) ).

sig_arg(A, F) -->
    { compound(A), A =.. [M, X], memberchk(M, [+, -, ?, @, :, !]) }, !,
    { mode_title(M, Title) },
    el(span, mode, [title=Title], esc(M)), term(X, _, 999, ctx(F, data)).
sig_arg(A, F) --> term(A, _, 999, ctx(F, data)).

mode_title(+, "input: bound on entry").
mode_title(-, "output: unbound on entry").
mode_title(?, "bound or unbound").
mode_title(@, "not further instantiated").
mode_title(:, "meta argument").
mode_title(!, "mutable").

also_(F, Dcg, also(H, Det)) --> signature_(F, sig(H is Det, Dcg)).

%  Consecutive strings among the properties are one paragraph.
doc_paragraphs([], []).
doc_paragraphs([S|Ps0], [T|Ts]) :- string(S), !,
    take_strings(Ps0, Ss, Ps),
    atomic_list_concat([S|Ss], ' ', A), atom_string(A, T),
    doc_paragraphs(Ps, Ts).
doc_paragraphs([_|Ps], Ts) :- doc_paragraphs(Ps, Ts).

take_strings([S|Ps0], [S|Ss], Ps) :- string(S), !, take_strings(Ps0, Ss, Ps).
take_strings(Ps, [], Ps).

para_(Vars, F, T) --> el(div, prose, el(p, none, inline(T, Vars, F))).

%  An argument row: its name, which way it goes, what it is.
mode_row(H, Vars, F, '$VAR'(N): Desc) -->
    { ( sub_term(MA, H), compound(MA), MA =.. [M, V], V == '$VAR'(N),
        mode_word(M, W) -> true ; W = "" ) },
    el(tr, none, ( el(td, name, var_(N)), el(td, dir, esc(W)),
                   el(td, desc, inline(Desc, Vars, F)) )).

mode_word(+, "in").
mode_word(-, "out").
mode_word(?, "in/out").
mode_word(@, "in").
mode_word(:, "meta").

%  A citation of the C standard links to its paragraph in N1570.
cite_(cites(C)) -->
    { atom_concat('C11 ', Par, C) }, !,
    { format(atom(Href), "https://port70.net/~~nsz/c/c11/n1570.html#~w", [Par]) },
    el(a, cite, [href=Href, title="C11 (N1570)"], ( el(span, std, "C11"), " ", esc(Par) )).
cite_(cites(C)) --> el(span, cite, esc(C)).

%  The examples, each with the result it gave when the page was built.
examples_(Ps, H, _, F) -->
    { findall(I-E, ( nth1(I, Ps, E), example_form(E) ), Es) },
    (   { Es == [] } -> []
    ;   { functor(H, HN, HA), length(Es, N),
          aggregate_all(count, ( member(I-_, Es), ran(F, HN/HA, I, pass) ), NP) },
        el(div, examples,
           ( el(div, "examples-title", ( "examples ", el(span, count, ( esc(NP), "/", esc(N), " hold" )) )),
             el(table, none, el(tbody, none, seq(Es, example_row(HN/HA, F)))) ))
    ).

example_row(PI, F, I-E) -->
    { ( ran(F, PI, I, R) -> true ; R = unknown ),
      result_mark(R, Mark, Title), atom_concat('ex ', R, Class) },
    el(tr, Class,
       ( el(td, mark, [title=Title], raw(Mark)),
         example_cells(E, F) )).

result_mark(pass, "✓", "held when this page was built").
result_mark(fail, "✗", "did not hold when this page was built").
result_mark(unknown, "·", "not run").

example_cells(example(G), F) -->
    el(td, goal, goal(G, _, ctx(F, goal))), el(td, none, []), el(td, none, []).
example_cells(example(G, C), F) -->
    el(td, goal, goal(G, _, ctx(F, goal))),
    el(td, then, "⟹"),
    el(td, check, term(C, _, 1200, ctx(F, data))).
example_cells(fails(G), F) -->
    el(td, goal, goal(G, _, ctx(F, goal))),
    el(td, then, "⟹"),
    el(td, check, el(span, "kw fails", "fails")).

%% Prose

%  A comment group as blocks: paragraphs, - lists and indented
%  preformatted text. Vars are the names to mark as variables.
prose_group(G, Vars, F) -->
    { group_text(G, Lines) },
    el(div, prose, prose_lines(Lines, Vars, F)).

prose_lines(Lines0, Vars, F) -->
    { dedent(Lines0, Lines), blocks(Lines, Blocks) },
    seq(Blocks, block_(Vars, F)).

dedent(Ls0, Ls) :-
    exclude(blank, Ls0, NonBlank),
    maplist(indent, NonBlank, Is),
    ( min_list(Is, Min) -> true ; Min = 0 ),
    maplist(drop(Min), Ls0, Ls).

indent(S, I) :-
    string_codes(S, Cs), phrase(spaces(I), Cs, _).

spaces(I) --> " ", !, spaces(I0), { I is I0 + 1 }.
spaces(0) --> [].

drop(N, S0, S) :- ( blank(S0) -> S = "" ; sub_string(S0, N, _, 0, S) ).

%  blocks(Lines, Blocks): p(Text), ul(Items), pre(Lines).
blocks([], []).
blocks([L|Ls], Bs) :- blank(L), !, blocks(Ls, Bs).
blocks([L|Ls0], [ul(Items)|Bs]) :- item_start(L, _), !,
    list_items([L|Ls0], Items, Ls), blocks(Ls, Bs).
blocks([L|Ls0], [pre([L|Pre])|Bs]) :- indent(L, I), I > 0, !,
    take_indented(Ls0, Pre0, Ls), trim_blank_ends(Pre0, Pre1), append(Pre1, [], Pre),
    blocks(Ls, Bs).
blocks([L|Ls0], [p(Text)|Bs]) :-
    take_para(Ls0, Para, Ls),
    atomic_list_concat([L|Para], ' ', Text0), atom_string(Text0, Text),
    blocks(Ls, Bs).

item_start(L, Rest) :-
    ( string_concat("- ", Rest, L) ; string_concat("* ", Rest, L) ), !.

list_items([L|Ls0], [Text|Items], Ls) :-
    item_start(L, First),
    take_cont(Ls0, Cont, Ls1),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), Cont, Cont1),
    atomic_list_concat([First|Cont1], ' ', T), atom_string(T, Text),
    (   Ls1 = [L1|_], item_start(L1, _) -> list_items(Ls1, Items, Ls)
    ;   Ls1 = [B, L1|_], blank(B), item_start(L1, _) -> Ls1 = [_|Ls2], list_items(Ls2, Items, Ls)
    ;   Items = [], Ls = Ls1
    ).

take_cont([L|Ls0], [L|Cs], Ls) :- \+ blank(L), indent(L, I), I > 0, !, take_cont(Ls0, Cs, Ls).
take_cont(Ls, [], Ls).

take_indented([L|Ls0], [L|Cs], Ls) :- ( blank(L) ; indent(L, I), I > 0 ), !, take_indented(Ls0, Cs, Ls).
take_indented(Ls, [], Ls).

take_para([L|Ls0], [L|Ps], Ls) :-
    \+ blank(L), \+ item_start(L, _), indent(L, 0), !, take_para(Ls0, Ps, Ls).
take_para(Ls, [], Ls).

block_(Vars, F, p(Text)) --> el(p, none, inline(Text, Vars, F)).
block_(Vars, F, ul(Items)) --> el(ul, none, seq(Items, li_(Vars, F))).
block_(_, _, pre(Lines)) -->
    { dedent(Lines, Ls), atomic_list_concat(Ls, '\n', T) },
    el(pre, none, esc(T)).

li_(Vars, F, Text) --> el(li, none, inline(Text, Vars, F)).

inline(Text, Vars) --> { nb_getval(dterm_file, F) }, inline(Text, Vars, F).

%  Inline prose: `code`, name/N references, argument names, docs links.
inline(Text, Vars, F) --> { string_codes(Text, Cs) }, inl(Cs, Vars, F).

inl([], _, _) --> !, [].
inl([0'`|Cs0], Vars, F) --> { append(Code, [0'`|Cs], Cs0) }, !,
    el(code, none, esc(Code)), inl(Cs, Vars, F).
inl(Cs0, Vars, F) --> { word(Cs0, W, Cs1), W \== [] }, !, word_(W, Cs1, Vars, F).
inl([C|Cs], Vars, F) --> esc_code(C), inl(Cs, Vars, F).

word(Cs0, W, Cs) :- span(word_char, Cs0, W, Cs).

span(P, [C|Cs0], [C|W], Cs) :- call(P, C), !, span(P, Cs0, W, Cs).
span(_, Cs, [], Cs).

word_char(C) :- code_type(C, csym).

word_(W, Cs0, Vars, F) -->
    { pred_ref(W, Cs0, Ref, PI, Cs), pred_href(F, PI, Href) }, !,
    el(a, ref, [href=Href], el(code, none, esc(Ref))), inl(Cs, Vars, F).
word_(W, Cs0, Vars, F) -->
    { atom_codes(N, W), memberchk(N, Vars) }, !,
    var_(N), inl(Cs0, Vars, F).
word_(`docs`, [0'/|Cs0], Vars, F) -->
    { span([C]>>(word_char(C) ; C == 0'- ; C == 0'.), Cs0, P0, Cs),
      append(P, `.md`, P0) }, !,
    { github(G), format(atom(Href), "~wdocs/~s.md", [G, P]) },
    el(a, none, [href=Href], ( "docs/", esc(P0) )), inl(Cs, Vars, F).
word_(W, Cs, Vars, F) --> esc(W), inl(Cs, Vars, F).

pred_ref(W, Cs0, Ref, PI, Cs) :-
    atom_codes(N, W),
    (   Cs0 = [0'/, 0'/|Cs1] -> Slash = `//` ; Cs0 = [0'/|Cs1], Slash = `/` ),
    span([C]>>code_type(C, digit), Cs1, Ds, Cs), Ds \== [],
    number_codes(A0, Ds),
    ( Slash == `//` -> A is A0 + 2 ; A = A0 ),
    PI = N/A,
    append([W, Slash, Ds], Ref).

%% Pages

write_source_page(Out, Sources, Src) :-
    Src = src(Base, Text, Lines, _),
    nb_setval(dterm_text, Text),
    nb_setval(dterm_lines, Lines),
    nb_setval(dterm_file, Base),
    nb_setval(dterm_notes, []),
    file_name_extension(Base, html, Name),
    directory_file_path(Out, Name, Path),
    write_page(Path, source_page(Sources, Src)).

source_page(Sources, src(Base, _, _, Events)) -->
    { entries(Events, Entries), format(atom(Title), "~w.pl", [Base]) },
    shell(Title, crumbs_source(Title),
          ( el(nav, "toc dterm-nav", ( el(div, "toc-title", "nanofil/src"),
                                        el(ul, none, seq(Sources, nav_file(Base, Entries))) )),
            el(article, dterm, ( el(h1, "source-title", esc(Title)),
                                 seq(Entries, entry_(Base)) )) )).

crumbs_source(Title) -->
    el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="index.html"], "nanofil"), el(span, "crumb-sep", "›"),
    el(span, "crumb current", esc(Title)).

nav_file(Current, Entries, src(Base, _, _, _)) -->
    { format(atom(Href), "~w.html", [Base]) },
    (   { Base == Current }
    ->  el(li, current, ( el(a, none, [href=Href], ( esc(Base), ".pl" )),
                          el(ul, none, seq(Entries, nav_entry)) ))
    ;   el(li, none, el(a, none, [href=Href], ( esc(Base), ".pl" )))
    ).

nav_entry(section(T)) --> !,
    { section_id(T, Id) },
    { atom_concat('#', Id, Href) },
    el(li, "nav-section", el(a, none, [href=Href], esc(T))).
nav_entry(pred(Key, _, _)) --> !,
    { key_id(Key, Id), uri_encoded(fragment, Id, Frag), atom_concat('#', Frag, Href) },
    el(li, "nav-pred", el(a, none, [href=Href], esc(Id))).
nav_entry(_) --> [].

section_id(T, Id) :-
    string_lower(T, L),
    split_string(L, " ", " ():,.'`", Ws0), exclude(==(""), Ws0, Ws),
    atomic_list_concat(Ws, '-', Id0),
    atom_concat('s-', Id0, Id).

entry_(_, section(T)) --> { section_id(T, Id) }, el(h2, none, [id=Id], esc(T)).
entry_(F, prose(G)) -->
    { G = group(K, _, _), ( K == block -> C = "prose lede" ; C = "prose-block" ) },
    el(div, C, prose_group(G, [], F)).
entry_(F, directive(C)) --> directive_(C, F).
entry_(F, pred(Key, Doc, Items)) --> pred_(Key, Doc, Items, F).

shell(Title, Crumbs, Main) -->
    "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>", esc(Title), " · nanofil · Filnix wiki</title>\n",
    "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n",
    "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"../style.css\">\n",
    "<link rel=\"stylesheet\" href=\"dterm.css\">\n",
    "</head>\n<body>\n",
    "<header class=\"library\"><div class=\"page-frame library-frame\">\n",
    "  <div class=\"library-heading\"><p class=\"eyebrow\">Fil-C on Nix</p><h1><a href=\"../index.html\">Filnix wiki</a></h1></div>\n",
    "  <nav class=\"doors\">\n",
    "    <a class=\"door\" href=\"../docs/\">Docs</a>\n",
    "    <a class=\"door\" href=\"../index.html#explainers\">Explainers</a>\n",
    "    <a class=\"door selected\" href=\"index.html\">nanofil</a>\n",
    "    <a class=\"door\" href=\"https://nix.swa.sh/\">Campaigns</a>\n",
    "    <a class=\"door\" href=\"https://github.com/mbrock/filnix\">Source</a>\n",
    "  </nav>\n</div></header>\n",
    "<div class=\"status\"><div class=\"page-frame status-frame\">\n",
    el(nav, crumbs, ['aria-label'="Breadcrumb"], Crumbs),
    el(span, "status-right", el(a, none, [href="https://github.com/mbrock/filnix/tree/main/nanofil"], "mbrock/filnix/nanofil")),
    "\n</div></div>\n",
    el(main, "page-frame dterm-page", Main),
    "\n<script src=\"dterm.js\"></script>\n</body>\n</html>\n".

%  The index: every module with the first paragraph of its header.
index_page(Sources) -->
    shell("nanofil", ( el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                       el(span, "crumb current", "nanofil") ),
          ( el(nav, "toc dterm-nav", ( el(div, "toc-title", "nanofil/src"),
                                        el(ul, none, seq(Sources, nav_file(none, []))) )),
            el(article, "dterm index",
               ( el(h1, "source-title", "nanofil, read as Prolog"),
                 el(div, "prose lede",
                    ( el(p, none, ( "nanofil is a C compiler written in Prolog that emits Fil-C ABI assembly. ",
                                    "It aims to read like the standards it implements: each fact about C, the IR ",
                                    "or Fil-C stated once, as a relation everything else reads (",
                                    el(a, none, [href="https://github.com/mbrock/filnix/blob/main/nanofil/docs/campaign.md"], "the campaign"),
                                    "). These pages draw its source as terms: clause heads over their goals, ",
                                    "conditionals as tables, fact tables as tables, PlDoc as signatures." )) )),
                 el(div, modules, seq(Sources, module_card)) )) )).

module_card(src(Base, Text, _, Events)) -->
    { format(atom(Href), "~w.html", [Base]),
      split_string(Text, "\n", "", Ls), length(Ls, NL),
      aggregate_all(count, ( member(clause(c(T, _, _, _)), Events), clause_key(T, _) ), NC),
      nb_setval(dterm_file, Base),
      ( member(group(block, L, Ts), Events) -> summary(group(block, L, Ts), Sum) ; Sum = "" ) },
    el(a, "card-link module-card", [href=Href],
       ( el(strong, none, ( esc(Base), ".pl" )),
         el(span, meta, ( esc(NL), " lines · ", esc(NC), " clauses" )),
         el(span, summary, esc(Sum)) )).

summary(G, Sum) :-
    group_text(G, Lines0), dedent(Lines0, Lines), blocks(Lines, Bs),
    (   Bs = [p(T)|_] -> Sum = T
    ;   Bs = [pre(Ls)|_] -> atomic_list_concat(Ls, ' ', A), atom_string(A, Sum)
    ;   Sum = ""
    ).
