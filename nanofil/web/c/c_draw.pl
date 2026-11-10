:- encoding(utf8).
/*  c_draw: C drawn by what the frontend reads it as.

    c_read.pl gives a file's items as c_parse reads them, with their
    lines, the comments and directives the lexer skips, and how each
    integer was spelled. This module draws them, for the pages of
    dterm_c.pl and for ```` ```c ```` fences in nanofil's documents
    (dterm_guide.pl):

    - a function is its signature over its body; a body is a column of
      statements, a compound statement its keyword line over its own
      column, set in from a hairline, so the nesting is the drawing and
      braces and semicolons are not needed;
    - `if` and its `else if` chain are one construct, `switch` a table of
      its case labels and the statements under each;
    - a struct or union is a table of its fields, aligned as careful C is
      written, an enum a table of its constants and values;
    - inline, an expression is set as dterm sets a term: a call is its
      function and arguments in bows, dterm.js breaks it at the width it
      gets (data-d=args, data-d=op), and the parser's tree decides the
      parentheses, so only the needed ones are drawn. Assignment is `←`,
      equality `=`, and `≠ ≤ ≥ ∧ ∨ ¬ × →` replace their ASCII spellings
      (each keeps its spelling as its title);
    - a local is a variable (hovering it lights up its other uses); a
      name the file defines links to its definition, a field to its
      struct when only one struct has it, a goto to its label;
    - comments are where they were written: before an item they are its
      prose, inside a body notes, after code on its line asides;
      directives are drawn among the items, a #define with its body read
      as an expression when it is one;
    - what the grammar refused stays as its tokens, marked with the
      parser's reason.
*/
:- module(c_draw, [c_fence//1, c_inline//1, c_inline_auto//1, c_ready/0]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(uri)).
:- use_module(library(base64)).
:- use_module(c_read).

:- include('../dterm_html').

%  c_global(Name, Kind, Href): a name the file defines at file scope;
%  Kind is fn, var, type, macro or const. c_tag(Kind, Tag, Href): a
%  struct, union or enum tag. c_field(Name, Href): a field only one of
%  the file's structs has. c_label(Name, Href): a label of the function
%  being drawn.
:- dynamic c_global/3, c_tag/3, c_field/3, c_label/2, c_spelling/2.

%% State

%  c_set_page(+Unit, +Mode, +Github, +Play): draw Unit next; Mode is page
%  (anchors and links) or fence (neither). Github is the URL of the
%  file's source, for line links, or none; Play the playground URL for
%  the file, or none.
c_set_page(Unit, Mode, Github, Play) :-
    retractall(c_global(_, _, _)), retractall(c_tag(_, _, _)), retractall(c_field(_, _, _)),
    retractall(c_label(_, _)), retractall(c_spelling(_, _)),
    Unit = unit(Items, Cms, Dirs, Sp, Lines), nb_setval(c_lines, Lines),
    forall(member(V-S-Spelling, Sp), assertz(c_spelling(V-S, Spelling))),
    nb_setval(c_mode, Mode), nb_setval(c_github, Github), nb_setval(c_play, Play),
    (   Mode == page -> index_unit(Items, Dirs) ; true ),
    events(Cms, Dirs, Evs), nb_setval(c_events, Evs).

index_unit(Items, Dirs) :-
    forall(( member(I, Items), item_defines(I, Kind, Name, Anchor) ),
           ( c_global(Name, _, _) -> true ; pre(Anchor, A), atom_concat('#', A, H), assertz(c_global(Name, Kind, H)) )),
    forall(( member(dir(_, _, T), Dirs), define_name(T, N) ),
           ( c_global(N, _, _) -> true ; pre(N, A), atom_concat('#', A, H), assertz(c_global(N, macro, H)) )),
    forall(( member(I, Items), item_specs(I, Specs), member(Sp, Specs), tag_defined(Sp, K, Tag, Fs) ),
           ( tag_anchor(K, Tag, A), atom_concat('#', A, H),
             ( c_tag(K, Tag, _) -> true ; assertz(c_tag(K, Tag, H)) ),
             forall(member(F, Fs), assertz(c_field(F, A, H))) )),
    findall(F, ( c_field(F, A1, _), c_field(F, A2, _), A1 \== A2 ), Dup0), sort(Dup0, Dup),
    forall(member(F, Dup), retractall(c_field(F, _, _))).

%  What an item defines: functions (the definition, else the first
%  prototype), variables, typedefs and enumeration constants.
item_defines(item(_, _, fundef(_, _, dcl(some(N), _, _), _)), fn, N, N).
item_defines(fun(_, _, _, dcl(some(N), _, _), _), fn, N, N).
item_defines(item(_, _, decl(_, Specs, Inits)), Kind, N, N) :-
    member(init(dcl(some(N), T, _), _), Inits),
    (   memberchk(storage(typedef), Specs) -> Kind = type
    ;   T = func(_, _) -> Kind = fn
    ;   Kind = var
    ).
item_defines(I, const, N, N) :-
    item_specs(I, Specs), sub_specs(Specs, enum(_, Es)), ( Es = packed(Es1) -> true ; Es1 = Es ),
    is_list(Es1), member(enumerator(N, _), Es1).

item_specs(item(_, _, decl(_, Specs, _)), Specs).
item_specs(item(_, _, fundef(_, Specs, _, _)), Specs).

%  Specifiers, and those of struct members, recursively.
sub_specs(Specs, S) :- member(S0, Specs), ( S = S0 ; S0 = su(_, _, Ms, _), is_list(Ms), member(field(Sp1, _, _), Ms), sub_specs(Sp1, S) ).

tag_defined(su(K, some(Tag), Ms, _), K, Tag, Fs) :- is_list(Ms),
    findall(F, ( member(field(_, dcl(some(F), _, _), _), Ms) ), Fs).
tag_defined(enum(some(Tag), Es), enum, Tag, []) :- Es \== none.
tag_defined(su(_, _, Ms, _), K, Tag, Fs) :- is_list(Ms), member(field(Sp, _, _), Ms), member(S, Sp), tag_defined(S, K, Tag, Fs).

tag_anchor(K, Tag, A) :- atomic_list_concat([K, '-', Tag], A0), pre(A0, A).

%  pre(+Anchor0, -Anchor): an anchor of the fence being drawn, which its
%  prefix keeps apart from the page's and the other fences' anchors.
pre(A0, A) :- ( nb_current(c_prefix, P) -> true ; P = '' ), atom_concat(P, A0, A).

define_name(T, N) :-
    split_string(T, " \t", " \t", [H|Rest0]), exclude(==(""), Rest0, Rest),
    (   H == "#define" -> Rest = [W|_] ; H == "#", Rest = ["define", W|_] ),
    string_codes(W, Cs), ident_codes(Cs, Is), Is \== [], atom_codes(N, Is).

ident_codes([C|Cs], [C|Is]) :- ( code_type(C, csym) ), !, ident_codes(Cs, Is).
ident_codes(_, []).

%% Events: comments and directives, in line order

events(Cms, Dirs, Evs) :-
    merge_line_comments(Cms, Cms1),
    findall(F-ev(F, T, cm(Text, Trail)), member(cm(F, T, Text, Trail), Cms1), E1),
    findall(F-ev(F, T, dir(Text)), member(dir(F, T, Text), Dirs), E2),
    append(E1, E2, E0), keysort(E0, E3), pairs_values(E3, Evs).

%  Consecutive // comments on lines of their own are one comment.
merge_line_comments([cm(F, F, A, no), cm(G, G, B, no)|Cs], Out) :-
    G =:= F + 1, line_comment(A), line_comment(B), !,
    string_concat(A, "\n", A1), string_concat(A1, B, AB),
    merge_line_comments([cm(F, G, AB, no)|Cs], Out).
merge_line_comments([cm(F, T, A, no), cm(G, G, B, no)|Cs], Out) :-
    T > F, G =:= T + 1, line_comment(B), \+ sub_string(A, _, _, _, "*/"), merged(A), !,
    string_concat(A, "\n", A1), string_concat(A1, B, AB),
    merge_line_comments([cm(F, G, AB, no)|Cs], Out).
merge_line_comments([C|Cs], [C|Out]) :- !, merge_line_comments(Cs, Out).
merge_line_comments([], []).

%  A // comment's text has no newline; merged ones do, and are marked by
%  being made only of line comments (block comments keep their own).
line_comment(T) :- \+ sub_string(T, _, _, _, "\n").
merged(T) :- \+ sub_string(T, _, _, _, "\n\n").

%  Take the events before line L (own-line comments and directives).
take_before(L, Evs) :-
    nb_getval(c_events, All),
    partition([ev(F, _, _)]>>(F < L), All, Evs, Rest),
    nb_setval(c_events, Rest).

%  Take the comments that end line L after code.
take_trailing(L, Evs) :-
    nb_getval(c_events, All),
    partition([ev(F, _, K)]>>(F =:= L, K = cm(_, yes)), All, Evs, Rest),
    nb_setval(c_events, Rest).

notes_before(L) --> { take_before(L, Evs) }, seq(Evs, note_ev).
notes_rest --> { nb_getval(c_events, Evs), nb_setval(c_events, []) }, seq(Evs, note_ev).

note_ev(ev(_, _, cm(Text, _))) --> { comment_lines(Text, Ls) }, comment_block(Ls, note).
note_ev(ev(F, _, dir(Text))) --> directive(F, Text).

aside_ev(ev(_, _, cm(Text, _))) --> { comment_lines(Text, Ls), atomic_list_concat(Ls, ' ', T) }, el(span, aside, inline(T)).

%  Before an item the comments are prose, at the level of the page.
prose_before(L) --> { take_before(L, Evs) }, seq(Evs, prose_ev).

prose_ev(ev(_, _, cm(Text, _))) --> { comment_lines(Text, Ls) }, comment_block(Ls, prose).
prose_ev(ev(F, _, dir(Text))) --> directive(F, Text).

%% Comments

%  comment_lines(+Text, -Lines): a comment's lines without the *s that
%  start them and the indentation they share.
comment_lines(Text, Lines) :-
    split_string(Text, "\n", "", Ls0),
    (   Ls0 = [First|More], More \== [],
        forall(( member(L, More), \+ blank(L) ), ( split_string(L, "", " \t", [S]), string_concat("*", _, S) ))
    ->  maplist(unstar, More, More1), Ls1 = [First|More1]
    ;   Ls1 = Ls0
    ),
    maplist([L0, L]>>( split_string(L0, "", "\r", [L1]), L = L1 ), Ls1, Ls2),
    (   Ls2 = [F0|R] -> split_string(F0, "", " \t*", [F1]), dedent(R, R1), Ls3 = [F1|R1] ; Ls3 = Ls2 ),
    trim_blank_ends(Ls3, Lines).

unstar(L0, L) :-
    (   split_string(L0, "", " \t", [S]), string_concat("*", R, S)
    ->  ( string_concat(" ", L, R) -> true ; L = R )
    ;   L = L0
    ).

%  A comment of key: value lines (a test's `run:` lines) is a list of
%  them; any other is prose in dterm's little Markdown.
comment_block(Ls, _) --> { Ls \== [], maplist(key_line, Ls) }, !,
    el(div, "c-meta", seq(Ls, meta_line)).
comment_block(Ls, Kind) -->
    { blocks(Ls, Bs), ( Kind == prose -> C = "prose c-prose" ; C = "note c-note" ) },
    el(div, C, seq(Bs, pblock)).

key_line(L) :- string_codes(L, Cs), phrase(( key_word, ":", rest_codes ), Cs).
key_word --> [C], { code_type(C, alpha) }, key_word_rest.
key_word_rest --> [C], { code_type(C, csym) ; C == 0'- }, !, key_word_rest.
key_word_rest --> [].
rest_codes --> [_], !, rest_codes.
rest_codes --> [].

meta_line(L) -->
    { sub_string(L, B, _, A, ":"), !, sub_string(L, 0, B, _, K), sub_string(L, _, A, 0, V0), split_string(V0, "", " ", [V]) },
    el(div, "c-meta-line", ( el(span, "c-meta-key", esc(K)), " ", el(code, none, esc(V)) )).

pblock(p(T)) --> el(p, none, inline(T)).
pblock(ul(Items)) --> el(ul, none, seq(Items, [T]>>el(li, none, inline(T)))).
pblock(pre(Ls)) --> { atomic_list_concat(Ls, '\n', T) }, el(pre, none, esc(T)).
pblock(h(_, T)) --> el(h4, "prose-h", inline(T)).
pblock(fence(_, Ls)) --> { atomic_list_concat(Ls, '\n', T) }, el(pre, none, esc(T)).
pblock(embed(N)) --> el(p, none, ( "![[", esc(N), "]]" )).
pblock(table(H, Rows)) -->
    el(table, "prose-table", ( el(thead, none, el(tr, none, seq(H, [C]>>el(th, none, inline(C))))),
                               el(tbody, none, seq(Rows, [R]>>el(tr, none, seq(R, [C]>>el(td, none, inline(C)))))) )).

%  Inline Markdown: `code`, [text](url), and the rest as text.
inline(T) --> { text_codes(T, Cs) }, inl(Cs).

inl([]) --> !.
inl([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0), Code \== [] }, !, el(code, none, esc(Code)), inl(Cs).
inl([0'[|Cs0]) --> { append(Txt, [0'], 0'(|Cs1], Cs0), \+ memberchk(0'], Txt), append(Url, [0')|Cs], Cs1),
                     \+ memberchk(0' , Url), Url \== [] }, !,
    { atom_codes(U, Url) }, el(a, none, [href=U], esc(Txt)), inl(Cs).
inl(Cs0) --> { span_plain(Cs0, P, Cs), P \== [] }, !, esc(P), inl(Cs).
inl([C|Cs]) --> esc([C]), inl(Cs).

span_plain([C|Cs0], [C|P], Cs) :- \+ memberchk(C, `\`[`), !, span_plain(Cs0, P, Cs).
span_plain(Cs, [], Cs).

%% Directives

directive(F, Text) -->
    { split_string(Text, "", " \t", [T0]), string_concat("#", T1, T0), split_string(T1, "", " \t", [T2]),
      ( sub_string(T2, B, _, A, " ") -> sub_string(T2, 0, B, _, W), sub_string(T2, _, A, 0, R0), split_string(R0, "", " \t", [R])
      ; W = T2, R = "" ) },
    directive(W, R, F).

directive("include", R, F) --> !,
    el(div, "c-dir c-include", ( line_link(F), dkw("include"), " ", el(span, "c-path", esc(R)) )).
directive("define", R, F) --> { define_parts(R, N, Ps, Body) }, !,
    { ( nb_getval(c_mode, page) -> pre(N, A), As = [id=A] ; As = [] ) },
    el(div, "clause c-dir c-define", As,
       el(div, "head", ( line_link(F), dkw("define"), " ", el(span, "f def c-mac", esc(N)),
                         ( { Ps == none } -> [] ; el(span, "c c-params", ['data-d'=args], el(span, args, macro_params(Ps))) ),
                         ( { Body == "" } -> [] ; " ", macro_body(Body, Ps) ) ))).
directive(W, R, F) -->
    el(div, "c-dir", ( line_link(F), dkw(W), ( { R == "" } -> [] ; " ", el(span, "c-dir-text", tokens_text(R)) ) )).

dkw(W) --> el(span, "kw c-hash", ( "#", esc(W) )).

%  define_parts(+Rest, -Name, -Params, -Body): #define Name(Params) Body,
%  Params none for an object macro.
define_parts(R, N, Ps, Body) :-
    string_codes(R, Cs), ident_codes(Cs, Is), Is \== [], atom_codes(N, Is), append(Is, Cs1, Cs),
    (   Cs1 = [0'(|Cs2], append(P, [0')|Cs3], Cs2), \+ memberchk(0'), P)
    ->  string_codes(PS, P), split_string(PS, ",", " \t", Ps0), exclude(==(""), Ps0, Ps), string_codes(B0, Cs3)
    ;   Ps = none, string_codes(B0, Cs1)
    ),
    split_string(B0, "", " \t", [Body]).

macro_params([]) --> [].
macro_params([P]) --> !, el(span, arg, el(span, v, ['data-v'=P], esc(P))).
macro_params([P|Ps]) --> el(span, arg, ( el(span, v, ['data-v'=P], esc(P)), el(span, sep, ",") )), " ", macro_params(Ps).

%  A macro's body is drawn as an expression when it reads as one, its
%  parameters as variables; otherwise as its tokens.
macro_body(Body, Ps) -->
    { string_chars(Body, Cs), catch(c_lex:c_tokens(Cs, macro, Ts), _, fail),
      catch(c_parse:c_constant_expression(Ts, E), _, fail),
      ( Ps == none -> Locals = [] ; maplist([S, A]>>atom_string(A, S), Ps, Locals) ) }, !,
    el(span, "c-mbody", term(E, Locals)).
macro_body(Body, Ps) -->
    { ( Ps == none -> Locals = [] ; maplist([S, A]>>atom_string(A, S), Ps, Locals) ) },
    el(span, "c-mbody c-tokens", tokens_text(Body, Locals)).

tokens_text(Text) --> tokens_text(Text, []).
tokens_text(Text, Locals) -->
    { string_chars(Text, Cs), catch(c_lex:c_tokens(Cs, text, Ts), _, fail) }, !, tokens(Ts, Locals).
tokens_text(Text, _) --> el(code, none, esc(Text)).

%% Items

%  c_unit(+Unit): the items of the unit c_set_page/4 set, with the
%  comments and directives among them.
c_unit(unit(Items, _, _, _, _)) --> seq(Items, top_item), notes_rest.

top_item(I) -->
    { item_lines(I, F, T) },
    prose_before(F),
    top_item_(I),
    notes_within(T), html_flush.

item_lines(item(F, T, _), F, T).
item_lines(fun(F, T, _, _, _), F, T).
item_lines(raw(F, T, _, _), F, T).

%  Comments still inside an item's lines after it is drawn.
notes_within(T) --> { T1 is T + 1, take_before(T1, Evs) }, seq(Evs, note_ev).

top_item_(item(F, _, fundef(_, Specs, Dcl, Body))) --> !, function(F, Specs, Dcl, Body).
top_item_(fun(F, _, Specs, Dcl, Body)) --> !, function(F, Specs, Dcl, Body).
top_item_(raw(F, T, Toks, Why)) --> !, raw_item(F, T, Toks, Why).
top_item_(item(F, _, decl(_, Specs, Inits))) --> !, top_decl(F, Specs, Inits).
top_item_(item(F, _, static_assert(_, E, Msg))) --> !,
    el(div, "clause c-item c-assert", el(div, head, ( line_link(F), kw("static_assert"), " ", term(E, []),
                                                       ( { Msg == [] } -> [] ; ", ", str_lit(Msg) ) ))).
top_item_(item(F, _, pragma_weak(_, N, Target))) --> !,
    el(div, "c-dir", ( line_link(F), dkw("pragma"), " weak ", name_ref(N, []),
                       ( { Target == none } -> [] ; " = ", name_ref(Target, []) ) )).
top_item_(item(F, _, toplevel_asm(_, Template))) --> !,
    el(div, "clause c-item", el(div, head, ( line_link(F), kw("asm"), " ", str_lit(Template) ))).
top_item_(item(F, _, X)) --> el(div, "clause c-item", el(div, head, ( line_link(F), el(code, none, esc(X)) ))).

%  A function: its signature, the comments on its line beside it, its
%  body under it.
function(F, Specs, Dcl, Body) -->
    { Dcl = dcl(some(N), _, _), fn_locals(Dcl, Body, Locals), anchor_attrs(fn, N, As),
      retractall(c_label(_, _)), forall(sub_term(label(L, _), Body), ( atom(L), label_anchor(N, L, H), assertz(c_label(L, H)) )),
      nb_setval(c_fn, N) },
    el(section, "clause c-item c-fn", As,
       ( el(div, head, ( line_link(F), specs_dcl(Specs, Dcl, def, Locals), ir_link(N), head_asides(F) )),
         body(Body, Locals) )).

label_anchor(Fn, L, H) :- atomic_list_concat([Fn, '--', L], A0), pre(A0, A), atom_concat('#', A, H).

anchor_attrs(Kind, N, As) :-
    (   nb_getval(c_mode, page), c_global(N, Kind, H), pre(N, A), atom_concat('#', A, H) -> As = [id=A]
    ;   As = []
    ).

ir_link(N) -->
    { nb_getval(c_play, Play) },
    (   { Play == none } -> []
    ;   { uri_encoded(query_value, N, Q), format(atom(H), "~w&ir=~w", [Play, Q]) },
        " ", el(a, "c-ir", [href=H, title="This function's IR, compiled by nanofil in the playground"], "IR")
    ).

%  The names a function binds: its parameters and every declaration in
%  its body. Scopes are not told apart: a name is a local if any block
%  declares it.
fn_locals(dcl(_, T, _), Body, Locals) :-
    findall(N, ( param_names(T, N) ; sub_term(decl(_, _, Inits), Body), member(init(dcl(some(N), _, _), _), Inits) ), Ns0),
    sort(Ns0, Locals).

param_names(func(_, params(Ps, _)), N) :- member(param(_, dcl(some(N), _, _)), Ps).
param_names(func(_, knr(Ns)), N) :- member(N, Ns).
param_names(func(_, knr(Ns, _)), N) :- member(N, Ns).
param_names(ptr(T, _), N) :- param_names(T, N).

body(at(_, block(Items)), Locals) --> !, el(div, "c-body", stmts(Items, Locals)).
body(S, Locals) --> el(div, "c-body", stmts([S], Locals)).

%  A declaration at file scope: a struct, union or enum it defines is a
%  table; a typedef, prototype or variable is one line.
top_decl(F, Specs, Inits) -->
    { partition([S]>>defines_tag(S), Specs, Tags, Plain) },
    (   { Tags == [] } -> []
    ;   seq(Tags, tag_def(F, Specs, Inits))
    ),
    (   { Inits == [] } -> ( { Tags == [] } -> el(div, "clause c-item", el(div, head, ( line_link(F), specs(Specs, []) ))) ; [] )
    ;   { Tags \== [], memberchk(storage(typedef), Specs) } -> []
    ;   { Inits = [init(dcl(some(N), T, _), _)|_], decl_kind(Specs, T, K), anchor_attrs(K, N, As) },
        el(div, "clause c-item c-decl", As,
           el(div, head, ( line_link(F), specs_inits(Plain, Specs, Inits, [], def), head_asides(F) )))
    ).

decl_kind(Specs, _, type) :- memberchk(storage(typedef), Specs), !.
decl_kind(_, func(_, _), fn) :- !.
decl_kind(_, _, var).

defines_tag(su(_, _, Ms, _)) :- is_list(Ms).
defines_tag(enum(_, Es)) :- Es \== none.

%  A struct, union or enum definition, with the typedef or variables
%  its declaration names.
tag_def(F, Specs, Inits, S) -->
    { S = su(K, Tag, Ms, Attrs) -> true ; S = enum(Tag, Es), K = enum, Attrs = [] },
    { Tag = some(T), nb_getval(c_mode, page) -> tag_anchor(K, T, A), As = [id=A] ; As = [] },
    { memberchk(storage(typedef), Specs), Inits = [init(dcl(some(TN), base, _), _)|_] -> Typedef = TN ; Typedef = none },
    el(section, "clause c-item c-tag", As,
       ( el(div, head, ( line_link(F),
                         ( { Typedef \== none } -> typedef_head(Typedef) ; [] ),
                         kw(K), ( { Tag = some(T) } -> " ", el(span, "ty def", esc(T)) ; [] ),
                         ( { Attrs == [] } -> [] ; " ", c_attrs(Attrs) ), head_asides(F) )),
         ( { K == enum } -> enum_table(Es) ; fields_table(Ms) ),
         ( { Typedef == none, Inits \== [] } -> el(div, "goal c-tag-decls", declarators(Inits, [], def)) ; [] ) )).

%  typedef struct {...} name: the name first, as what the table defines.
typedef_head(N) -->
    { anchor_attrs(type, N, As) },
    kw("typedef"), " ", el(span, "ty def", As, esc(N)), " ", el(span, "op wide", [title="typedef"], "="), " ".

fields_table(Ms) --> el(div, "c-fields", seq(Ms, field_row)).

field_row(field(Specs, Dcl, Width)) -->
    { field_name(Dcl, N), ( N \== none, c_field(N, A, _), nb_getval(c_mode, page) -> atomic_list_concat([A, '.', N], Id), As = [id=Id] ; As = [] ) },
    (   { partition([S]>>defines_tag(S), Specs, [Tag], Rest) }
    ->  el(div, "c-field c-field-nested", As,
           ( el(div, "c-ftype", ( specs(Rest, []), ( { Rest == [] } -> [] ; " " ), nested_tag(Tag) )),
             el(div, "c-fname goal", ( declarator(Dcl, [], field), width(Width) )) ))
    ;   el(div, "c-field", As,
           ( el(div, "c-ftype goal", specs(Specs, [])),
             el(div, "c-fname goal", ( declarator(Dcl, [], field), width(Width) )) ))
    ).
field_row(static_assert(_, E, _)) --> el(div, "c-field", ( el(div, "c-ftype", kw("static_assert")), el(div, "c-fname goal", term(E, [])) )).
field_row(X) --> el(div, "c-field", el(code, none, esc(X))).

field_name(dcl(some(N), _, _), N) :- !.
field_name(_, none).

nested_tag(su(K, Tag, Ms, _)) -->
    kw(K), ( { Tag = some(T) } -> " ", el(span, "ty def", esc(T)) ; [] ), fields_table(Ms).
nested_tag(enum(Tag, Es)) --> kw(enum), ( { Tag = some(T) } -> " ", el(span, "ty def", esc(T)) ; [] ), enum_table(Es).

width(none) --> !.
width(E) --> "\u00A0", el(span, "op wide", [title=":"], ":"), " ", term(E, []).

enum_table(packed(Es)) --> !, enum_table(Es).
enum_table(Es) --> el(div, "c-fields c-enum", seq(Es, enum_row)).

enum_row(enumerator(N, V)) -->
    { anchor_attrs(const, N, As) },
    el(div, "c-field", As, ( el(div, "c-fname goal", el(span, "a def", esc(N))),
                             el(div, "c-fval goal", ( { V == none } -> [] ; defeq, " ", term(V, []) )) )).

%% Statements

stmts([], _) --> [].
stmts([S|Ss], Locals) --> { stmt_line(S, L) }, notes_before(L), { nb_setval(c_line, L) }, stmt(S, Locals), stmts(Ss, Locals).

%  row(+Class, :Content): a statement's line, or a compound statement's
%  first, with the comments that end its source line beside it.
row(Class, Content) -->
    { nb_getval(c_line, L), ( L > 0 -> take_trailing(L, Evs) ; Evs = [] ), nb_setval(c_line, 0) },
    (   { Evs == [] } -> el(div, Class, Content)
    ;   el(div, "c-row", ( el(div, Class, Content), seq(Evs, aside_ev) ))
    ).

%  The comments that end line L, inside a head.
head_asides(L) --> { take_trailing(L, Evs) }, seq(Evs, spaced_aside).

spaced_aside(E) --> " ", aside_ev(E).

stmt_line(at(_:L, _), L) :- !.
stmt_line(decl(_:L, _, _), L) :- !.
stmt_line(static_assert(_:L, _, _), L) :- !.
stmt_line(raw(L, _, _, _), L) :- !.
stmt_line(_, 0).

stmt(decl(_, Specs, Inits), Ls) --> !,
    (   { Inits == [] } -> row("goal c-stmt", specs(Specs, Ls))
    ;   el(div, "goal c-stmt c-local", specs_inits(Specs, Specs, Inits, Ls, local))
    ).
stmt(static_assert(_, E, _), Ls) --> !, row("goal c-stmt", ( kw("static_assert"), " ", term(E, Ls) )).
stmt(raw(F, T, Toks, Why), Ls) --> !, raw_stmt(F, T, Toks, Why, Ls).
stmt(at(_, S), Ls) --> stmt_(S, Ls).

stmt_(expr(E), Ls) --> !, row("goal c-stmt", term(E, Ls)).
stmt_(null, _) --> !, el(div, "goal c-stmt c-null", el(span, sep, ";")).
stmt_(block(Items), Ls) --> !, el(div, "c-block", stmts(Items, Ls)).
stmt_(return(none), _) --> !, row("goal c-stmt", kw("return")).
stmt_(return(E), Ls) --> !, row("goal c-stmt", ( kw("return"), " ", term(E, Ls) )).
stmt_(break, _) --> !, row("goal c-stmt", kw("break")).
stmt_(continue, _) --> !, row("goal c-stmt", kw("continue")).
stmt_(goto(L), _) --> !, row("goal c-stmt", ( kw("goto"), " ", label_ref(L) )).
stmt_(computed_goto(E), Ls) --> !, row("goal c-stmt", ( kw("goto"), " ", el(span, "o pre", ( el(span, op, "*"), term(E, Ls) )) )).
stmt_(label(L, S), Ls) --> !,
    { nb_getval(c_mode, Mode), ( Mode == page, c_label(L, H) -> atom_concat('#', Id, H), As = [id=Id] ; As = [] ) },
    el(div, "c-labelled", ( el(div, "c-label", As, ( el(span, "c-lname", esc(L)), el(span, sep, ":") )), stmt(S, Ls) )).
stmt_(if(C, T, E), Ls) --> !, { if_chain(if(C, T, E), Arms) }, el(div, "c-cmp c-if", seq(Arms, if_arm(Ls))).
stmt_(while(C, S), Ls) --> !,
    el(div, "c-cmp c-while", ( row("goal c-head", ( kw("while"), " ", term(C, Ls) )), body(S, Ls) )).
stmt_(do(S, C), Ls) --> !,
    el(div, "c-cmp c-do", ( row("goal c-head", kw("do")), body(S, Ls),
                            el(div, "goal c-head", ( kw("while"), " ", term(C, Ls) )) )).
stmt_(for(I, C, St, S), Ls) --> !,
    el(div, "c-cmp c-for", ( row("goal c-head", ( kw("for"), " ",
                                                     el(span, "c c-forparts", ['data-d'=args],
                                                        el(span, args, ( for_part(I, Ls, ";"), " ", for_part(C, Ls, ";"), " ", for_part(St, Ls, "") ))) )),
                             body(S, Ls) )).
stmt_(switch(E, S), Ls) --> !,
    { S = at(_, block(Items)) -> true ; Items = [S] },
    { switch_rows(Items, Rows) },
    el(div, "c-cmp c-switch", ( row("goal c-head", ( kw("switch"), " ", term(E, Ls) )),
                                el(div, "c-cases", seq(Rows, case_row(Ls))) )).
stmt_(case(E, S), Ls) --> !, el(div, "c-labelled", ( el(div, "c-label", ( kw("case"), " ", case_value(E, Ls), el(span, sep, ":") )), stmt(S, Ls) )).
stmt_(default(S), Ls) --> !, el(div, "c-labelled", ( el(div, "c-label", ( kw("default"), el(span, sep, ":") )), stmt(S, Ls) )).
stmt_(asm(T, Outs, Ins, Cl, _), Ls) --> !, asm_stmt(T, Outs, Ins, Cl, Ls).
stmt_(asm_empty(Outs, Ins, Cl, _), Ls) --> !, asm_stmt([], Outs, Ins, Cl, Ls).
%  The parser keeps only what kind of asm this is; its text is the source's.
stmt_(unsupported_asm(_), _) --> !,
    { nb_getval(c_line, L), nb_getval(c_lines, Lines), ( nth1(L, Lines, T0) -> split_string(T0, "", " \t", [T]) ; T = "asm" ) },
    row("goal c-stmt c-rawstmt", el(span, none, [title="nanofil cannot check this asm's instructions, so it refuses a function that runs it"], el(code, "c-asm-text", esc(T)))).
stmt_(S, _) --> row("goal c-stmt", el(code, none, esc(S))).

asm_stmt(T, Outs, Ins, Cl, Ls) -->
    row("goal c-stmt", ( kw("asm"), " ",
        el(span, "c c-asm", ['data-d'=args],
           el(span, args, ( el(span, arg, str_lit(T)), asm_ops(Outs, Ls), asm_ops(Ins, Ls), asm_clobbers(Cl) ))) )).

asm_ops([], _) --> !, " ", el(span, arg, el(span, sep, ":")).
asm_ops(Ops, Ls) --> " ", el(span, arg, el(span, sep, ":")), asm_ops_(Ops, Ls).
asm_ops_([], _) --> [].
asm_ops_([op(C, E)|Ops], Ls) --> { atom_codes(C, Cs) },
    " ", el(span, arg, ( str_lit(Cs), el(span, paren, term(E, Ls)), ( { Ops == [] } -> [] ; el(span, sep, ",") ) )), asm_ops_(Ops, Ls).

asm_clobbers([]) --> !.
asm_clobbers(Cl) --> " ", el(span, arg, el(span, sep, ":")), asm_clobbers_(Cl).
asm_clobbers_([]) --> [].
asm_clobbers_([labels(Ls)|Cs]) --> !, " ", el(span, arg, el(span, sep, ":")), seq(Ls, spaced_label), asm_clobbers_(Cs).
asm_clobbers_([C|Cs]) --> { atom_codes(C, Bs) }, " ", el(span, arg, str_lit(Bs)), asm_clobbers_(Cs).

spaced_label(L) --> " ", label_ref(L).

for_part(none, _, Sep) --> !, el(span, arg, ( { Sep == "" } -> [] ; el(span, sep, esc(Sep)) )).
for_part(expr(E), Ls, Sep) --> !, for_part(E, Ls, Sep).
for_part(decl(_, Specs, Inits), Ls, Sep) --> !, el(span, arg, ( specs_inits(Specs, Specs, Inits, Ls, local), sep_(Sep) )).
for_part(E, Ls, Sep) --> el(span, arg, ( term(E, Ls), sep_(Sep) )).

sep_("") --> !.
sep_(S) --> el(span, sep, esc(S)).

if_chain(if(C, T, E), [if(C, T)|Arms]) :- else_chain(E, Arms).

else_chain(none, []) :- !.
else_chain(at(_, if(C, T, E)), [elif(C, T)|Arms]) :- !, else_chain(E, Arms).
else_chain(E, [else(E)]).

if_arm(Ls, if(C, T)) --> row("goal c-head", ( kw("if"), " ", term(C, Ls) )), body(T, Ls).
if_arm(Ls, elif(C, T)) --> el(div, "goal c-head", ( kw("else if"), " ", term(C, Ls) )), body(T, Ls).
if_arm(Ls, else(E)) --> el(div, "goal c-head", kw("else")), body(E, Ls).

%  A switch's rows: each case and default with the labels that fall into
%  it, and the statements up to the next label.
switch_rows([], []).
switch_rows([I|Is], [row(Labels, [S|Body])|Rows]) :-
    case_labels(I, Labels, S), !,
    take_unlabelled(Is, Body, Rest), switch_rows(Rest, Rows).
switch_rows([I|Is], [row([], [I|Body])|Rows]) :- take_unlabelled(Is, Body, Rest), switch_rows(Rest, Rows).

case_labels(at(_, case(E, S0)), [case(E)|Ls], S) :- !, ( case_labels(S0, Ls, S) -> true ; Ls = [], S = S0 ).
case_labels(at(_, default(S0)), [default|Ls], S) :- !, ( case_labels(S0, Ls, S) -> true ; Ls = [], S = S0 ).

take_unlabelled([I|Is], [I|Body], Rest) :- \+ case_labels(I, _, _), !, take_unlabelled(Is, Body, Rest).
take_unlabelled(Is, [], Is).

case_row(Ls, row(Labels, Body)) -->
    { Body = [S|_], stmt_line(S, L) },
    notes_before(L),
    el(div, "c-case", ( el(div, "c-case-labels", case_labels_(Labels, Ls)),
                        el(div, "c-case-body", stmts(Body, Ls)) )).

%  The labels of one row, as one: case 2, 3 or case 3, default.
case_labels_(Labels, Ls) -->
    { partition([L]>>(L = case(_)), Labels, Cases, Defaults) },
    el(span, "c-case-label",
       ( ( { Cases == [] } -> [] ; kw("case"), " ", case_values(Cases, Ls) ),
         ( { Defaults == [] } -> [] ; ( { Cases == [] } -> [] ; el(span, sep, ","), " " ), kw("default") ) )).

case_values([case(E)], Ls) --> !, case_value(E, Ls).
case_values([case(E)|Cs], Ls) --> case_value(E, Ls), el(span, sep, ","), " ", case_values(Cs, Ls).

case_value(range(Lo, Hi), Ls) --> !, term(Lo, Ls), " … ", term(Hi, Ls).
case_value(E, Ls) --> term(E, Ls).

label_ref(L) -->
    (   { nb_getval(c_mode, page), c_label(L, H) } -> el(a, "c-lname", [href=H], esc(L))
    ;   el(span, "c-lname", esc(L))
    ).

%% What the grammar refused

raw_item(F, T, Toks, Why) -->
    { lines_tokens(Toks, Rows) },
    el(div, "clause c-item c-raw", ( el(div, "c-raw-why", ( line_link(F), refused(Why, F, T) )),
                                     el(div, "c-raw-lines", seq(Rows, raw_row([]))) )).

raw_stmt(_, _, Toks, Why, Ls) -->
    { why_title(Why, Title) },
    row("goal c-stmt c-rawstmt", el(span, none, [title=Title], tokens(Toks, Ls))).

refused(Why, F, T) -->
    { ( F == T -> format(string(Where), "line ~w", [F]) ; format(string(Where), "lines ~w–~w", [F, T]) ) },
    el(span, "c-refused", ( "nanofil's parser does not read ", esc(Where), ( { Why == "" } -> [] ; ": ", esc(Why) ) )).

why_title("", "nanofil's parser does not read this statement; drawn as its tokens") :- !.
why_title(W, T) :- format(string(T), "nanofil's parser does not read this statement (~w); drawn as its tokens", [W]).

lines_tokens([], []).
lines_tokens([tok(T, _:L)|Ts0], [[tok(T, _:L)|Line]|Rows]) :-
    take_line(Ts0, L, Line, Ts), lines_tokens(Ts, Rows).

take_line([tok(T, F:L)|Ts0], L, [tok(T, F:L)|Line], Ts) :- !, take_line(Ts0, L, Line, Ts).
take_line(Ts, _, [], Ts).

raw_row(Ls, Toks) --> el(div, "c-raw-line", tokens(Toks, Ls)).

%  tokens(+Tokens, +Locals): c_lex tokens as text, spaced as C is.
tokens([], _) --> [].
tokens([tok(T, _)|Ts], Ls) --> token(T, Ls), ( { Ts = [tok(N, _)|_], \+ tight(T, N) } -> " " ; [] ), tokens(Ts, Ls).

tight(p(P), _) :- memberchk(P, ['(', '[', '.', '->', '!', '~', '#', '##']), !.
tight(_, p(P)) :- memberchk(P, [')', ']', ',', ';', '.', '->', '++', '--', ':']), !.
tight(id(_), p('(')) :- !.
tight(kw(K), p('(')) :- memberchk(K, [sizeof, alignof, attribute, typeof, asm]), !.

token(id(N), Ls) --> !, name_ref(N, Ls).
token(kw(K), _) --> !, { kw_spelling(K, W) }, el(span, "c-kw", esc(W)).
token(p(P), _) --> !, el(span, "c-p", esc(P)).
token(int(V, S), _) --> !, num(V, S).
token(float(Cs), _) --> !, { atom_chars(A, Cs) }, el(span, n, esc(A)).
token(imag(float(Cs)), _) --> !, { atom_chars(A, Cs) }, el(span, n, ( esc(A), "i" )).
token(chr(V), _) --> !, chr_lit(V).
token(str(Bs), _) --> !, str_lit(Bs).
token(wstr(_, Vs), _) --> !, "L", str_lit(Vs).
token(T, _) --> el(code, none, esc(T)).

%  c_lex folds GNU's spellings into keywords; a token is drawn as C writes it.
kw_spelling(attribute, '__attribute__') :- !.
kw_spelling(extension, '__extension__') :- !.
kw_spelling(K, K).

%% Specifiers and declarators

%  specs_dcl(+Specs, +Dcl, +Role, +Locals): a declaration of one name.
specs_dcl(Specs, Dcl, Role, Ls) --> specs(Specs, Ls), dcl_space(Dcl), declarator(Dcl, Ls, Role).

dcl_space(dcl(none, base, _)) --> !.
dcl_space(_) --> " ".

%  specs_inits(+Shown, +Specs, +Inits, +Locals, +Role): specifiers and
%  their declarators with initializers, broken as arguments are.
specs_inits(Shown, _Specs, [init(D, I)], Ls, Role) --> !,
    specs(Shown, Ls), dcl_space(D), init_dcl(D, I, Ls, Role).
specs_inits(Shown, _Specs, Inits, Ls, Role) -->
    specs(Shown, Ls), " ",
    el(span, "c c-dcls", ['data-d'=args], el(span, "args c-plain", init_dcls(Inits, Ls, Role))).

init_dcls([init(D, I)], Ls, Role) --> !, el(span, arg, init_dcl(D, I, Ls, Role)).
init_dcls([init(D, I)|Is], Ls, Role) --> el(span, arg, ( init_dcl(D, I, Ls, Role), el(span, sep, ",") )), " ", init_dcls(Is, Ls, Role).

init_dcl(D, none, Ls, Role) --> !, declarator(D, Ls, Role).
init_dcl(D, I, Ls, Role) --> el(span, o, ['data-d'=op], ( declarator(D, Ls, Role), "\u00A0", defeq, " ", init(I, Ls) )).

%  An initializer is ≔, so that = is only ever equality and ← assignment.
defeq --> el(span, "op wide c-defeq", [title="="], "≔").

declarators(Inits, Ls, Role) --> init_dcls(Inits, Ls, Role).

init(list(Es), Ls) --> !, braces(Es, Ls).
init(E, Ls) --> term(E, Ls).

braces([], _) --> !, el(span, "c-brace empty", "{ }").
braces(Es, Ls) --> el(span, "c c-init", ['data-d'=args], el(span, "args c-brace", entries(Es, Ls))).

entries([E], Ls) --> !, el(span, arg, entry(E, Ls)).
entries([E|Es], Ls) --> el(span, arg, ( entry(E, Ls), el(span, sep, ",") )), " ", entries(Es, Ls).

entry(entry([], I), Ls) --> !, init(I, Ls).
entry(entry(Ds, I), Ls) --> el(span, o, ['data-d'=op], ( designators(Ds, Ls), "\u00A0", defeq, " ", init(I, Ls) )).
entry(E, Ls) --> init(E, Ls).

designators([], _) --> [].
designators([field(F)|Ds], Ls) --> el(span, "c-p", "."), field_ref(F), designators(Ds, Ls).
designators([index(E)|Ds], Ls) --> subscript(E, Ls), designators(Ds, Ls).
designators([index(A, B)|Ds], Ls) --> el(span, "args c-sub", ( term(A, Ls), " … ", term(B, Ls) )), designators(Ds, Ls).

%  specs(+Specs, +Locals): declaration specifiers as written; a struct
%  or enum defined here is drawn by its tag (its table is drawn apart).
specs([], _) --> [].
specs([S], Ls) --> !, spec(S, Ls).
specs([shared_base|Ss], Ls) --> !, specs(Ss, Ls).
specs([S|Ss], Ls) --> spec(S, Ls), ( { Ss == [shared_base] } -> [] ; " " ), specs(Ss, Ls).

spec(storage(S), _) --> !, el(span, "c-kw", esc(S)).
spec(qual(Q), _) --> !, { qual_spelling(Q, W) }, el(span, "c-kw", esc(W)).
spec(fspec(F), _) --> !, { fspec_spelling(F, W) }, el(span, "c-kw", esc(W)).
spec(tspec(K), _) --> !, { tspec_spelling(K, W) }, el(span, ty, esc(W)).
spec(tname(N), _) --> !, type_ref(N).
spec(su(K, Tag, Ms, _), Ls) --> { is_list(Ms) }, !,
    el(span, "c-kw", esc(K)), ( { Tag = some(T) } -> " ", el(span, "ty def", esc(T)) ; [] ), " ", inline_members(Ms, Ls).
spec(su(K, Tag, Ms, _), _) --> !, el(span, "c-kw", esc(K)), " ", tag_ref(K, Tag, Ms).
spec(enum(Tag, Es), _) --> !, el(span, "c-kw", "enum"), " ", tag_ref(enum, Tag, Es).
spec(attr(A), _) --> !, attr(A).
spec(alignas(type(T)), Ls) --> !, call_like("_Alignas", type_name(T, Ls)).
spec(alignas(expr(E)), Ls) --> !, call_like("_Alignas", term(E, Ls)).
spec(typeof(type(T)), Ls) --> !, call_like("typeof", type_name(T, Ls)).
spec(typeof(expr(comma(num(0, none-dec), E))), Ls) --> !, el(span, "c-kw", "__auto_type"), { _ = E, _ = Ls }.
spec(typeof(expr(E)), Ls) --> !, call_like("typeof", term(E, Ls)).
spec(atomic(T), Ls) --> !, call_like("_Atomic", type_name(T, Ls)).
spec(auto_type, _) --> !, el(span, "c-kw", "__auto_type").
spec(shared_base, _) --> !.
spec(S, _) --> el(code, none, esc(S)).

call_like(Name, Arg) --> el(span, c, ['data-d'=args], ( el(span, "c-kw", esc(Name)), el(span, args, el(span, arg, Arg)) )).

qual_spelling(atomic, '_Atomic') :- !.
qual_spelling(Q, Q).
fspec_spelling(noreturn, '_Noreturn') :- !.
fspec_spelling(F, F).
tspec_spelling(complex, '_Complex') :- !.
tspec_spelling(int128, '__int128') :- !.
tspec_spelling(float16, '_Float16') :- !.
tspec_spelling(bf16, '__bf16') :- !.
tspec_spelling(K, K).

c_attrs([]) --> [].
c_attrs([A|As]) --> attr(A), ( { As == [] } -> [] ; " " ), c_attrs(As).

attr(extension) --> !, el(span, "c-kw c-attr", "__extension__").
attr(nullability) --> !.
attr(c23) --> !, el(span, "c-attr", "[[…]]").
attr(A) --> { is_list(A) }, !, el(span, "c-attr", [title="__attribute__"], ( el(span, "c-attr-mark", "⟪"), attr_tokens(A), el(span, "c-attr-mark", "⟫") )).
attr(A) --> el(span, "c-attr", esc(A)).

%  An attribute's balanced tokens: group(Ts) is a parenthesized run.
attr_tokens([group(Ts)]) --> !, attr_toks(Ts).
attr_tokens(Ts) --> attr_toks(Ts).

attr_toks([]) --> [].
attr_toks([T|Ts]) --> attr_tok(T), ( { Ts = [N|_], \+ attr_tight(T, N) } -> " " ; [] ), attr_toks(Ts).

attr_tight(_, p(',')) :- !.
attr_tight(_, group(_)) :- !.
attr_tight(p(P), _) :- memberchk(P, ['(']).

attr_tok(group(Ts)) --> !, el(span, paren, attr_toks(Ts)).
attr_tok(id(N)) --> !, esc(N).
attr_tok(kw(K)) --> !, esc(K).
attr_tok(p(P)) --> !, el(span, sep, esc(P)).
attr_tok(int(V, S)) --> !, num(V, S).
attr_tok(str(Bs)) --> !, str_lit(Bs).
attr_tok(T) --> esc(T).

%  declarator(+Dcl, +Locals, +Role): a declarator around its name, set
%  as C writes it (* before, [] and () after, parentheses where a
%  pointer is to an array or function). Role is def (a file-scope
%  name), local, param or field.
declarator(dcl(Name, Type, Asm), Ls, Role) -->
    { dcl_doc(Type, name(Name, Role), Doc) }, dcl_draw(Doc, Ls),
    ( { Asm = asm(Sym) } -> " ", call_like("asm", ( "\"", esc(Sym), "\"" )) ; [] ).

dcl_doc(base, D, D) :- !.
dcl_doc(ptr(T, Qs), D, Out) :- !,
    (   ( T = array(_, _) ; T = func(_, _) ) -> dcl_doc(T, paren(star(Qs, D)), Out)
    ;   dcl_doc(T, star(Qs, D), Out)
    ).
dcl_doc(array(T, S), D, Out) :- !, dcl_doc(T, arr(D, S), Out).
dcl_doc(func(T, Ps), D, Out) :- !, dcl_doc(T, fn(D, Ps), Out).
dcl_doc(T, D, other(T, D)).

dcl_draw(name(none, _), _) --> !.
dcl_draw(name(some(N), Role), _) --> !, name_def(N, Role).
dcl_draw(star(Qs, D), Ls) --> !, el(span, "op c-star", "*"), quals(Qs), dcl_draw(D, Ls).
dcl_draw(paren(D), Ls) --> !, el(span, paren, dcl_draw(D, Ls)).
dcl_draw(arr(D, S), Ls) --> !, dcl_draw(D, Ls), array_size(S, Ls).
dcl_draw(fn(D, Ps), Ls) --> !, el(span, "c c-sig", ['data-d'=args], ( dcl_draw(D, Ls), el(span, args, params(Ps, Ls)) )).
dcl_draw(other(T, D), Ls) --> dcl_draw(D, Ls), el(code, none, esc(T)).

quals([]) --> [].
quals([Q|Qs]) --> { qual_spelling(Q, W) }, el(span, "c-kw", esc(W)), " ", quals(Qs).

array_size(none, _) --> !, el(span, "args c-sub empty", "").
array_size(star, _) --> !, el(span, "args c-sub", "*").
array_size(E, Ls) --> subscript(E, Ls).

params(unspecified, _) --> !, el(span, "c-noparams", []).
params(params(Ps, V), Ls) --> !, param_list(Ps, V, Ls).
params(knr(Ns), _) --> !, knr_names(Ns).
params(knr(Ns, _), _) --> !, knr_names(Ns).
params(P, _) --> el(code, none, esc(P)).

param_list([], variadic, _) --> !, el(span, arg, el(span, "c-p", "…")).
param_list([], fixed, _) --> !, el(span, arg, el(span, ty, "void")).
param_list([P], fixed, Ls) --> !, el(span, arg, param(P, Ls)).
param_list([P|Ps], V, Ls) --> el(span, arg, ( param(P, Ls), el(span, sep, ",") )), " ", param_list(Ps, V, Ls).

param(param(Specs, Dcl), Ls) --> specs(Specs, Ls), dcl_space(Dcl), declarator(Dcl, Ls, param).
param(P, _) --> el(code, none, esc(P)).

knr_names([]) --> [].
knr_names([N]) --> !, el(span, arg, name_def(N, param)).
knr_names([N|Ns]) --> el(span, arg, ( name_def(N, param), el(span, sep, ",") )), " ", knr_names(Ns).

%  A name where it is declared.
name_def(N, def) --> !,
    { c_global(N, K, _) -> def_class(K, C) ; C = "f def" },
    el(span, C, esc(N)).
name_def(N, field) --> !, el(span, "c-field-name def", esc(N)).
name_def(N, _) --> el(span, "v def", ['data-v'=N], esc(N)).

def_class(fn, "f def").
def_class(var, "g def").
def_class(type, "ty def").
def_class(const, "a def").
def_class(macro, "f def c-mac").

type_name(type(Specs, T), Ls) --> specs(Specs, Ls), ( { T == base } -> [] ; " ", declarator(dcl(none, T, none), Ls, local) ).

type_ref(N) -->
    (   { c_global(N, type, H) } -> el(a, ty, [href=H], esc(N))
    ;   el(span, ty, esc(N))
    ).

tag_ref(K, some(T), _) --> !,
    (   { c_tag(K, T, H) } -> el(a, ty, [href=H], esc(T))
    ;   el(span, ty, esc(T))
    ).
tag_ref(_, none, _) --> el(span, "ty anon", "{…}").

%% Expressions

%  term(+E, +Locals): an expression inline, its parentheses those its
%  tree needs.
term(E, Ls) --> expr(E, 0, Ls).

%  expr(+E, +Context, +Locals): E where an operand of precedence at
%  least Context stands; lower binds looser.
expr(E, Ctx, Ls) --> { prec(E, P) }, ( { P < Ctx } -> el(span, paren, expr_(E, Ls)) ; expr_(E, Ls) ).

%  Precedence: 1 comma, 2 assignment, 3 conditional, 4-13 the binary
%  levels of c_operator/4 (1-10) plus 3, 14 cast and prefix, 15 postfix
%  and primary.
prec(comma(_, _), 1) :- !.
prec(assign(_, _, _), 2) :- !.
prec(cond(_, _, _), 3) :- !.
prec(gcond(_, _), 3) :- !.
prec(bin(Op, _, _), P) :- c_parse:c_operator(_, L, Op, _), !, P is L + 3.
prec(cast(type([tspec(bool)], base), num(_, none-dec)), 16) :- !.
prec(cast(_, _), 14) :- !.
prec(un(Op, _), 15) :- memberchk(Op, [postinc, postdec]), !.
prec(un(_, _), 14) :- !.
prec(sizeof_expr(_), 14) :- !.
prec(alignof_expr(_), 14) :- !.
prec(real_part(_), 14) :- !.
prec(imag_part(_), 14) :- !.
prec(label_addr(_), 14) :- !.
prec(_, 16).

expr_(id(N), Ls) --> !, name_ref(N, Ls).
expr_(num(V, S), _) --> !, num(V, S).
expr_(float(Cs), _) --> !, { atom_chars(A, Cs) }, el(span, n, esc(A)).
expr_(imag(float(Cs)), _) --> !, { atom_chars(A, Cs) }, el(span, n, ( esc(A), "i" )).
expr_(chr(V), _) --> !, chr_lit(V).
expr_(str(Bs), _) --> !, str_lit(Bs).
expr_(wstr(T, Vs), _) --> !, { wide_prefix(T, P) }, el(span, s, ( esc(P), str_body(Vs) )).
expr_(bin(Op, A, B), Ls) --> !,
    { c_parse:c_operator(Sp, L, Op, _), P is L + 3, P1 is P + 1, op_glyph(Sp, G) },
    el(span, o, ['data-d'=op], ( expr(A, P, Ls), "\u00A0", el(span, "op wide", [title=Sp], esc(G)), " ", expr(B, P1, Ls) )).
expr_(assign(Op, A, B), Ls) --> !,
    { assign_glyph(Op, Sp, G) },
    el(span, o, ['data-d'=op], ( expr(A, 14, Ls), "\u00A0", el(span, "op wide c-assign", [title=Sp], esc(G)), " ", expr(B, 2, Ls) )).
expr_(comma(A, B), Ls) --> !, el(span, o, ['data-d'=op], ( expr(A, 1, Ls), el(span, "op tight-comma", [title=","], ","), " ", expr(B, 2, Ls) )).
expr_(cond(C, A, B), Ls) --> !,
    el(span, o, ['data-d'=op], ( expr(C, 4, Ls), "\u00A0", el(span, "op wide", [title="?"], "?"), " ",
                                 el(span, o, ['data-d'=op], ( expr(A, 1, Ls), "\u00A0", el(span, "op wide", [title=":"], ":"), " ", expr(B, 3, Ls) )) )).
expr_(gcond(C, B), Ls) --> !,
    el(span, o, ['data-d'=op], ( expr(C, 4, Ls), "\u00A0", el(span, "op wide", [title="?:"], "?:"), " ", expr(B, 3, Ls) )).
expr_(un(Op, A), Ls) --> !, unary(Op, A, Ls).
expr_(call(F, As), Ls) --> !,
    el(span, c, ['data-d'=args], ( callee(F, Ls), el(span, args, args(As, Ls)) )).
expr_(index(A, I), Ls) --> !, el(span, "c c-index", ['data-d'=args], ( expr(A, 15, Ls), el(span, "args c-sub", el(span, arg, term(I, Ls))) )).
expr_(member(A, F), Ls) --> !, el(span, "c-mem", ( expr(A, 15, Ls), el(span, "op tight", [title="."], "."), field_ref(F) )).
expr_(arrow(A, F), Ls) --> !, el(span, "c-mem", ( expr(A, 15, Ls), el(span, "op tight c-arrow", [title="->"], "→"), field_ref(F) )).
expr_(cast(type([tspec(bool)], base), num(1, none-dec)), _) --> !, el(span, a, "true").
expr_(cast(type([tspec(bool)], base), num(0, none-dec)), _) --> !, el(span, a, "false").
expr_(cast(T, E), Ls) --> !, el(span, "o c-cast", ( el(span, "paren c-casttype", type_name(T, Ls)), expr(E, 14, Ls) )).
expr_(sizeof_type(T), Ls) --> !, call_like("sizeof", type_name(T, Ls)).
expr_(sizeof_expr(E), Ls) --> !, el(span, "o pre", ( el(span, "c-kw", "sizeof"), " ", expr(E, 14, Ls) )).
expr_(alignof(T), Ls) --> !, call_like("_Alignof", type_name(T, Ls)).
expr_(alignof_expr(E), Ls) --> !, el(span, "o pre", ( el(span, "c-kw", "_Alignof"), " ", expr(E, 14, Ls) )).
expr_(complit(T, Init), Ls) --> !, el(span, "o c-cast", ( el(span, "paren c-casttype", type_name(T, Ls)), init(Init, Ls) )).
expr_(offsetof(T, Path), Ls) --> !,
    el(span, c, ['data-d'=args], ( el(span, "f c-builtin", "offsetof"),
                                   el(span, args, ( el(span, arg, ( type_name(T, Ls), el(span, sep, ",") )), " ",
                                                    el(span, arg, offset_path(Path, Ls)) )) )).
expr_(va_arg(A, T), Ls) --> !,
    el(span, c, ['data-d'=args], ( el(span, "f c-builtin", "va_arg"),
                                   el(span, args, ( el(span, arg, ( term(A, Ls), el(span, sep, ",") )), " ", el(span, arg, type_name(T, Ls)) )) )).
expr_(bit_cast(T, E), Ls) --> !,
    el(span, c, ['data-d'=args], ( el(span, "f c-builtin", "__builtin_bit_cast"),
                                   el(span, args, ( el(span, arg, ( type_name(T, Ls), el(span, sep, ",") )), " ", el(span, arg, term(E, Ls)) )) )).
expr_(types_compatible(A, B), Ls) --> !,
    el(span, c, ['data-d'=args], ( el(span, "f c-builtin", "__builtin_types_compatible_p"),
                                   el(span, args, ( el(span, arg, ( type_name(A, Ls), el(span, sep, ",") )), " ", el(span, arg, type_name(B, Ls)) )) )).
expr_(label_addr(L), _) --> !, el(span, "o pre", ( el(span, op, [title="&&"], "&&"), label_ref(L) )).
expr_(real_part(E), Ls) --> !, el(span, "o pre", ( el(span, "c-kw", "__real__"), " ", expr(E, 14, Ls) )).
expr_(imag_part(E), Ls) --> !, el(span, "o pre", ( el(span, "c-kw", "__imag__"), " ", expr(E, 14, Ls) )).
expr_(stmtexpr(at(_, block(Items))), Ls) --> !, el(span, "c-stmtexpr", ( el(span, "c-p", "({"), el(div, "c-block", stmts(Items, Ls)), el(span, "c-p", "})") )).
expr_(generic(C, As), Ls) --> !,
    el(span, c, ['data-d'=args], ( el(span, "c-kw", "_Generic"),
                                   el(span, args, ( el(span, arg, ( term(C, Ls), el(span, sep, ",") )), " ", generic_assocs(As, Ls) )) )).
expr_(E, _) --> el(code, none, esc(E)).

wide_prefix(int, "L") :- !.
wide_prefix(ushort, "u") :- !.
wide_prefix(uint, "U") :- !.
wide_prefix(_, "L").

generic_assocs([A], Ls) --> !, el(span, arg, generic_assoc(A, Ls)).
generic_assocs([A|As], Ls) --> el(span, arg, ( generic_assoc(A, Ls), el(span, sep, ",") )), " ", generic_assocs(As, Ls).

generic_assoc(assoc(default, E), Ls) --> !, el(span, o, ( el(span, "c-kw", "default"), el(span, sep, ":"), " ", term(E, Ls) )).
generic_assoc(assoc(T, E), Ls) --> el(span, o, ( type_name(T, Ls), el(span, sep, ":"), " ", term(E, Ls) )).

offset_path([field(F)|Ps], Ls) --> field_ref(F), offset_steps(Ps, Ls).
offset_steps([], _) --> [].
offset_steps([field(F)|Ps], Ls) --> el(span, "op tight", "."), field_ref(F), offset_steps(Ps, Ls).
offset_steps([index(E)|Ps], Ls) --> subscript(E, Ls), offset_steps(Ps, Ls).

subscript(E, Ls) --> el(span, "args c-sub", el(span, arg, term(E, Ls))).

callee(id(N), Ls) --> !, name_ref(N, Ls, call).
callee(F, Ls) --> expr(F, 15, Ls).

args([], _) --> [].
args([A], Ls) --> !, el(span, arg, expr(A, 2, Ls)).
args([A|As], Ls) --> el(span, arg, ( expr(A, 2, Ls), el(span, sep, ",") )), " ", args(As, Ls).

unary(Op, A, Ls) --> { memberchk(Op-Sp, [postinc-'++', postdec-'--']) }, !,
    el(span, "o post", ( expr(A, 15, Ls), el(span, op, [title=Sp], esc(Sp)) )).
unary(Op, A, Ls) -->
    { unary_glyph(Op, Sp, G) },
    el(span, "o pre", ( el(span, "op", [title=Sp], esc(G)), expr(A, 14, Ls) )).

unary_glyph(neg, '-', "−").
unary_glyph(plus, '+', "+").
unary_glyph(bnot, '~', "~").
unary_glyph(not, '!', "¬").
unary_glyph(deref, '*', "*").
unary_glyph(addr, '&', "&").
unary_glyph(preinc, '++', "++").
unary_glyph(predec, '--', "--").

op_glyph('||', "∨") :- !.
op_glyph('&&', "∧") :- !.
op_glyph('==', "=") :- !.
op_glyph('!=', "≠") :- !.
op_glyph('<=', "≤") :- !.
op_glyph('>=', "≥") :- !.
op_glyph('*', "×") :- !.
op_glyph('-', "−") :- !.
op_glyph('<<', "≪") :- !.
op_glyph('>>', "≫") :- !.
op_glyph(Sp, G) :- atom_string(Sp, G).

%  An assignment's Op is its spelling, = or a compound such as *=.
assign_glyph((=), '=', "←") :- !.
assign_glyph(Sp, Sp, G) :-
    (   atom_concat(B, '=', Sp), op_glyph(B, G1) -> string_concat(G1, "=", G) ; atom_string(Sp, G) ).

%  name_ref(+Name, +Locals): a name where it is used.
name_ref(N, Ls) --> name_ref(N, Ls, use).

name_ref(N, Ls, _) --> { memberchk(N, Ls) }, !, el(span, v, ['data-v'=N], esc(N)).
name_ref(N, _, Role) --> { c_global(N, K, H) }, !, { use_class(K, Role, C) }, el(a, C, [href=H], esc(N)).
name_ref(N, _, call) --> !, el(span, "f", esc(N)).
name_ref(N, _, _) --> el(span, "g", esc(N)).

use_class(fn, _, "f call").
use_class(var, _, "g").
use_class(type, _, "ty").
use_class(const, _, "a").
use_class(macro, call, "f call c-mac").
use_class(macro, _, "a c-mac").

field_ref(F) -->
    (   { nb_getval(c_mode, page), c_field(F, A, _) } -> { atomic_list_concat(['#', A, '.', F], H) }, el(a, "c-field-name", [href=H], esc(F))
    ;   el(span, "c-field-name", esc(F))
    ).

%  Constants as the file spelled them.
num(V, S) --> { c_spelling(V-S, Sp) -> true ; num_spelling(V, S, Sp) }, el(span, n, esc(Sp)).

num_spelling(V, Suffix-Radix, Sp) :-
    (   Radix == other, V >= 8 -> format(atom(D), "0x~16r", [V]) ; format(atom(D), "~d", [V]) ),
    ( Suffix == none -> Sp = D ; upcase_atom(Suffix, U), atom_concat(D, U, Sp) ).

chr_lit(V) --> { char_escape(V, Cs) }, el(span, s, ( "'", esc(Cs), "'" )).

str_lit(Bs) --> el(span, "s c-str", ( "\"", str_body(Bs), "\"" )).

str_body(Bs) --> { utf8_or_bytes(Bs, Cs), foldl([C, A0, A]>>( str_escape(C, E), append(A0, E, A) ), Cs, [], Esc) }, esc(Esc).

%  A string's bytes as characters where they are UTF-8, else as bytes.
utf8_or_bytes(Bs, Cs) :- catch(( phrase(utf8_codes(Cs), Bs) ), _, fail), !.
utf8_or_bytes(Bs, Bs).

utf8_codes([]) --> [].
utf8_codes([C|Cs]) --> [B], { B < 0x80 }, !, { C = B }, utf8_codes(Cs).
utf8_codes([C|Cs]) --> [B1, B2], { B1 >= 0xC2, B1 =< 0xDF, cont(B2) }, !, { C is (B1 /\ 0x1F) << 6 \/ (B2 /\ 0x3F) }, utf8_codes(Cs).
utf8_codes([C|Cs]) --> [B1, B2, B3], { B1 >= 0xE0, B1 =< 0xEF, cont(B2), cont(B3) }, !,
    { C is (B1 /\ 0x0F) << 12 \/ (B2 /\ 0x3F) << 6 \/ (B3 /\ 0x3F), C >= 0x800 }, utf8_codes(Cs).
utf8_codes([C|Cs]) --> [B1, B2, B3, B4], { B1 >= 0xF0, B1 =< 0xF4, cont(B2), cont(B3), cont(B4) }, !,
    { C is (B1 /\ 0x07) << 18 \/ (B2 /\ 0x3F) << 12 \/ (B3 /\ 0x3F) << 6 \/ (B4 /\ 0x3F) }, utf8_codes(Cs).

cont(B) :- B /\ 0xC0 =:= 0x80.

str_escape(0'\n, `\\n`) :- !.
str_escape(0'\t, `\\t`) :- !.
str_escape(0'\r, `\\r`) :- !.
str_escape(0'", `\\"`) :- !.
str_escape(0'\\, `\\\\`) :- !.
str_escape(0, `\\0`) :- !.
str_escape(C, E) :- C < 32, !, format(codes(E), "\\x~|~`0t~16r~2+", [C]).
str_escape(127, `\\x7f`) :- !.
str_escape(C, [C]).

char_escape(0'', `\\'`) :- !.
char_escape(0'", `"`) :- !.
char_escape(V, E) :- V < 0, !, V1 is V + 256, char_escape(V1, E).
char_escape(V, E) :- V > 127, V < 256, !, format(codes(E), "\\x~16r", [V]).
char_escape(V, E) :- str_escape(V, E).

%% Lines and keywords

kw(W) --> el(span, kw, esc(W)).

line_link(L) -->
    { nb_getval(c_github, G) },
    (   { G == none ; L == 0 } -> []
    ;   { format(atom(H), "~w#L~w", [G, L]) }, el(a, ln, [href=H, title="line on GitHub"], esc(L))
    ).

%% Pages and fences

%  c_fence(+Lines): a ```c fence of a document, drawn as a file is:
%  its names link to their definitions in the fence, under anchors only
%  it uses (c1-sum), and each function links to its IR in the
%  playground when the fence compiles there by itself.
c_fence(Lines) -->
    { c_ready, atomic_list_concat(Lines, '\n', T), atom_string(T, Text),
      catch(c_read_text(Text, fence, Unit), _, fail),
      flag(c_fence, N0, N0 + 1), N is N0 + 1, format(atom(P), "c~d-", [N]), nb_setval(c_prefix, P),
      fence_play(Text, Unit, Play),
      c_set_page(Unit, page, none, Play) }, !,
    el(div, "dterm-c c-fence", c_unit(Unit)),
    { nb_setval(c_prefix, '') }.

%  The playground can compile a fence that includes headers, or whose
%  calls are all to its own functions.
fence_play(Text, unit(Items, _, Dirs, _, _), Href) :-
    findall(N, ( member(I, Items), ( I = item(_, _, fundef(_, _, dcl(some(N), _, _), _)) ; I = fun(_, _, _, dcl(some(N), _, _), _) ) ), Defined),
    (   Defined \== [], \+ member(raw(_, _, _, _), Items),
        (   member(dir(_, _, D), Dirs), sub_string(D, _, _, _, "include") -> true
        ;   forall(( sub_term(call(id(F), _), Items) ), memberchk(F, Defined))
        ),
        string_length(Text, L), L =< 24000
    ->  ( nb_current(c_play_root, Root) -> true ; Root = 'play/' ),
        base64url(Text, B), format(atom(Href), "~w#src=~w&name=example.c", [Root, B])
    ;   Href = none
    ).

%% C in running text

%  c_ready: nanofil's lexer and parser are loaded, from the source
%  directory the drawer names in c_src_dir (dterm.pl, dterm_rocq.pl's
%  --prolog), the first time C is drawn. Fails without one.
c_ready :- nb_current(c_frontend, Done), !, Done == true.
c_ready :-
    (   nb_current(c_src_dir, Dir), directory_file_path(Dir, 'c_parse.pl', P), exists_file(P)
    ->  c_read_load(Dir), nb_setval(c_frontend, true)
    ;   nb_setval(c_frontend, false), fail
    ).

%  c_inline(+Codes): `c: EXPR` in prose, the code after `c:` drawn as
%  C. Whatever does not parse is drawn as its tokens.
c_inline(Codes) --> { c_marked(Codes, Rest) }, !,
    (   { c_ready, string_codes(T, Rest), c_snippet(T, Snip) } -> snippet(Snip)
    ;   el(code, none, esc(Rest))
    ).

c_marked([0'c, 0':|Cs0], Cs) :- ( Cs0 = [0' |Cs] -> true ; Cs = Cs0 ), Cs \== [].

%  c_inline_auto(+Codes): unmarked inline code that is C beyond doubt:
%  it reads whole as C, has a C keyword (not true, false or bool, which
%  Rocq writes too) among at least two tokens, and is a type, an
%  expression, a statement that starts with its keyword or ends with its
%  ; or }, or a declaration with a space in it. int(ptr) and const(N)
%  stay Prolog.
c_inline_auto(Codes) -->
    { c_ready, string_codes(T, Codes), c_snippet(T, Snip), Snip = snip(Form, Semi, _, _),
      Form \= tokens(_), auto_tokens(T, Ts), length(Ts, NT), NT >= 2,
      once(( member(tok(kw(K), _), Ts), \+ memberchk(K, [true, false, bool, nullptr]) )),
      auto_form(Form, Semi, Ts, Codes), \+ prolog_shaped(Codes), \+ prolog_compound(Codes) }, !,
    snippet(Snip).

%  Code that reads as a Prolog compound (typeof(type(TypeName)), the
%  parser's own terms) is Prolog, as dterm draws it.
prolog_compound(Codes) :-
    catch(term_string(T, Codes, [syntax_errors(quiet)]), _, fail), compound(T).

%  A keyword written against its parenthesis, as const(N), int(ptr) and
%  void(void) are, is a Prolog term about C; sizeof(x) and the like are C.
prolog_shaped(Codes) :-
    append(Pre, [0'(|_], Codes), append(Before, W, Pre), W \== [],
    ( Before == [] -> true ; last(Before, C), \+ code_type(C, csym) ),
    atom_codes(K, W), c_lex:keyword(K, _),
    \+ memberchk(K, [sizeof, '_Alignof', alignof, '__alignof__', typeof, '__typeof__', '__attribute__', asm, '__asm__',
                      '_Alignas', '_Generic', '_Static_assert', static_assert, '__builtin_offsetof']), !.

auto_tokens(T, Ts) :- string_chars(T, Cs), catch(c_lex:c_tokens(Cs, inline, Ts), _, fail).

auto_form(expr(_), _, _, _).
auto_form(type(_), _, _, _).
auto_form(decl(_), _, _, Codes) :- memberchk(0' , Codes).
auto_form(stmt(decl(_, _, _)), _, _, Codes) :- !, memberchk(0' , Codes).
auto_form(stmt(_), yes, _, _) :- !.
auto_form(stmt(_), _, _, Codes) :- last(Codes, 0'}), !.
auto_form(stmt(_), _, [tok(kw(K), _)|_], _) :-
    memberchk(K, [return, while, if, for, do, switch, goto, break, continue]).

%  snippet(+Snip): C inline, as a term is drawn in prose: in the
%  colours of the code, broken by dterm.js. A name is a variable unless
%  it is called or in capitals.
snippet(snip(Form, Semi, Sp, Ts)) -->
    { retractall(c_global(_, _, _)), retractall(c_tag(_, _, _)), retractall(c_field(_, _, _)),
      retractall(c_label(_, _)), retractall(c_spelling(_, _)),
      forall(member(V-S-Spelling, Sp), assertz(c_spelling(V-S, Spelling))),
      nb_setval(c_mode, inline), nb_setval(c_github, none), nb_setval(c_play, none),
      nb_setval(c_events, []), nb_setval(c_lines, []), nb_setval(c_line, 0), nb_setval(c_snippet_tokens, Ts),
      snippet_locals(Form, Ls) },
    el(code, "term cx", ( inline_form(Form, Ls), ( { Semi == yes } -> el(span, sep, ";") ; [] ) )).

snippet_locals(Form, Ls) :-
    findall(N, ( sub_term(id(N), Form), atom(N), \+ sub_term(call(id(N), _), Form), \+ upcase_atom(N, N) ), Ns0),
    findall(N, ( sub_term(dcl(some(N), _, _), Form) ), Ns1),
    append(Ns0, Ns1, Ns2), sort(Ns2, Ls).

inline_form(expr(E), Ls) --> term(E, Ls).
inline_form(type(T), Ls) --> type_name(T, Ls).
inline_form(stmt(at(_, null)), Ls) --> !, { nb_getval(c_snippet_tokens, Ts), append(Ts1, [tok(p(';'), _)], Ts) -> true ; nb_getval(c_snippet_tokens, Ts1) }, tokens(Ts1, Ls).
inline_form(stmt(S), Ls) --> inline_stmt(S, Ls).
inline_form(decl(D), Ls) --> inline_decl(D, Ls).
inline_form(tokens(Ts), Ls) --> tokens(Ts, Ls).

inline_decl(fundef(_, Specs, Dcl, Body), Ls) --> !, specs_dcl(Specs, Dcl, def, Ls), " ", inline_stmt(Body, Ls).
inline_decl(decl(_, Specs, []), Ls) --> !, specs(Specs, Ls).
inline_decl(decl(_, Specs, Inits), Ls) --> !, specs_inits(Specs, Specs, Inits, Ls, local).
inline_decl(D, _) --> el(code, none, esc(D)).

%  A statement on one line: a block is its statements in braces, each
%  with its ;.
inline_stmt(decl(_, Specs, []), Ls) --> !, specs(Specs, Ls).
inline_stmt(decl(_, Specs, Inits), Ls) --> !, specs_inits(Specs, Specs, Inits, Ls, local).
inline_stmt(at(_, S), Ls) --> inline_stmt_(S, Ls), !.
inline_stmt(S, _) --> el(code, none, esc(S)).

inline_stmt_(expr(E), Ls) --> term(E, Ls).
inline_stmt_(null, _) --> [].
inline_stmt_(return(none), _) --> ikw(return).
inline_stmt_(return(E), Ls) --> ikw(return), " ", term(E, Ls).
inline_stmt_(break, _) --> ikw(break).
inline_stmt_(continue, _) --> ikw(continue).
inline_stmt_(goto(L), _) --> ikw(goto), " ", el(span, "c-lname", esc(L)).
inline_stmt_(computed_goto(E), Ls) --> ikw(goto), " ", el(span, "o pre", ( el(span, op, "*"), expr(E, 14, Ls) )).
inline_stmt_(label(L, S), Ls) --> el(span, "c-lname", esc(L)), el(span, sep, ":"), inline_body(S, Ls).
inline_stmt_(while(C, S), Ls) --> ikw(while), " ", el(span, paren, term(C, Ls)), inline_body(S, Ls).
inline_stmt_(if(C, T, E), Ls) --> ikw(if), " ", el(span, paren, term(C, Ls)), inline_body(T, Ls),
    ( { E == none } -> [] ; " ", ikw(else), inline_body(E, Ls) ).
inline_stmt_(block(Items), Ls) --> inline_block(Items, Ls).

inline_body(at(_, null), _) --> !.
inline_body(S, Ls) --> " ", inline_stmt(S, Ls).

inline_block([], _) --> !, el(span, "c-brace empty", "{ }").
inline_block(Items, Ls) --> el(span, "c c-init", ['data-d'=args], el(span, "args c-brace", block_items_(Items, Ls))).

block_items_([I], Ls) --> !, el(span, arg, ( inline_stmt(I, Ls), item_semi(I) )).
block_items_([I|Is], Ls) --> el(span, arg, ( inline_stmt(I, Ls), item_semi(I) )), " ", block_items_(Is, Ls).

item_semi(at(_, block(_))) --> !.
item_semi(at(_, while(_, at(_, block(_))))) --> !.
item_semi(at(_, if(_, _, _))) --> !.
item_semi(_) --> el(span, sep, ";").

%  A struct's or union's members inline, in braces, each with its ;.
inline_members([], _) --> !, el(span, "c-brace empty", "{ }").
inline_members(Ms, Ls) --> el(span, "c c-init", ['data-d'=args], el(span, "args c-brace", members_(Ms, Ls))).

members_([M], Ls) --> !, el(span, arg, ( member_(M, Ls), el(span, sep, ";") )).
members_([M|Ms], Ls) --> el(span, arg, ( member_(M, Ls), el(span, sep, ";") )), " ", members_(Ms, Ls).

member_(field(Specs, Dcl, W), Ls) --> !, specs(Specs, Ls), dcl_space(Dcl), declarator(Dcl, Ls, field), width(W).
member_(M, _) --> el(code, none, esc(M)).

ikw(W) --> el(span, "c-kw", esc(W)).
