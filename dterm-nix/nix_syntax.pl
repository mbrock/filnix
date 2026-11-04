:- encoding(utf8).
/*  nix_syntax: Nix source as Prolog terms, with positions and comments.

    A lexer and a DCG for the Nix language, written so that dterm-nix can
    draw Nix the way dterm draws Prolog. Unlike `nix-instantiate --parse`,
    nothing is desugared or dropped: every node keeps the character span
    it came from, strings keep their source spelling, and comments are
    returned beside the tree, so the drawing can put each one where it
    was written.

    Every node's first argument is its span From-To (character offsets,
    To exclusive):

    | Term | Nix |
    |---|---|
    | `var(P, Name)` | an identifier |
    | `int(P, N)`, `float(P, F)` | numbers |
    | `str(P, Parts)`, `istr(P, Parts)` | `"…"` and `''…''`; parts are `lit(Text)` and `interp(P, E)` |
    | `path(P, Parts)`, `spath(P, Text)`, `uri(P, Text)` | `./a/b`, `<nixpkgs>`, `https://…` |
    | `paren(P, E)` | `( E )` |
    | `list(P, Es)` | `[ … ]` |
    | `attrs(P, Rec, Bs)` | `{ … }` or `rec { … }`; Rec is `plain` or `rec` |
    | `bind(P, Path, E)` | `a.b = E;` in an attrset or `let` |
    | `inherit(P, From, Names)` | `inherit (From) a b;`, From `none` without parentheses |
    | `select(P, E, Path, Default)` | `E.a.b` or `E.a.b or D`; Default `none` without `or` |
    | `app(P, F, Args)` | `F A B`, the arguments of one application in a list |
    | `lam(P, Param, Body)` | `x: Body` or `{ a, b ? d, ... } @ x: Body` |
    | `let(P, Bs, Body)` | `let … in Body` |
    | `with(P, E, Body)`, `assert(P, C, Body)` | `with E; Body`, `assert C; Body` |
    | `if(P, C, T, E)` | `if C then T else E` |
    | `bin(P, Op, L, R)` | binary operators, Op the operator's atom (`'//'`, `'++'`, …) |
    | `has(P, E, Path)` | `E ? a.b` |
    | `not(P, E)`, `neg(P, E)` | `!E`, `-E` |

    A parameter is `pid(Name)` or `pset(Formals, Ellipsis, At)`, with
    `formal(P, Name, Default)` (Default `none` when there is none),
    Ellipsis `true` or `false`, and At `none`, `before(Name)` or
    `after(Name)`. An attribute path is a list of `aid(P, Name)`,
    `astr(P, Parts)` and `ainterp(P, E)`.

    Comments are `cm(From, To, Text)`, Text with its markers.
*/
:- module(nix_syntax, [nix_read_file/3, nix_parse_codes/3, node_pos/2]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

%  nix_read_file(+File, -Text, -Nix): Nix is nix(Expr, Comments) for File.
nix_read_file(File, Text, nix(E, Cms)) :-
    read_file_to_string(File, Text, [encoding(utf8)]),
    string_codes(Text, Cs),
    (   nix_parse_codes(Cs, E, Cms) -> true
    ;   nb_getval(nix_far, Far),
        offset_line_col(Cs, Far, L, C),
        format(user_error, "~w:~w:~w: Nix syntax error~n", [File, L, C]),
        fail
    ).

%  nix_parse_codes(+Codes, -Expr, -Comments)
nix_parse_codes(Cs, E, Cms) :-
    nb_setval(nix_far, 0),
    lex(Cs, 0, top, Toks, Cms, [], Rest, _),
    Rest == [],
    phrase(expr(E), Toks), !.

node_pos(N, P) :- arg(1, N, P).

offset_line_col(Cs, O, L, C) :-
    length(Pre, O), append(Pre, _, Cs), !,
    include(==(0'\n), Pre, NLs), length(NLs, L0), L is L0 + 1,
    (   append(_, [0'\n|Last], Pre), \+ memberchk(0'\n, Last) -> length(Last, C0) ; length(Pre, C0) ),
    C is C0 + 1.
offset_line_col(_, _, 0, 0).

%% Lexing

%  lex(Cs0, O0, Mode, Toks, Cms0, Cms, Cs, O): the tokens t(Kind, From, To)
%  at offset O0 of Cs0, to the end (Mode top) or to the } that closes an
%  interpolation (Mode interp(Depth)).
lex(Cs0, O0, Mode, Toks, Cms0, Cms, Cs, O) :-
    skip(Cs0, O0, Cs1, O1, Cms0, Cms1),
    (   Cs1 == []
    ->  Mode == top, Toks = [], Cs = [], O = O1, Cms = Cms1
    ;   Mode = interp(0), Cs1 = [0'}|Cs2]
    ->  Toks = [], Cs = Cs2, O is O1 + 1, Cms = Cms1
    ;   token(Cs1, O1, Kind, Cs2, O2, Cms1, Cms2)
    ->  Toks = [t(Kind, O1, O2)|Toks1],
        depth(Mode, Kind, Mode1),
        lex(Cs2, O2, Mode1, Toks1, Cms2, Cms, Cs, O)
    ;   nb_setval(nix_far, O1), fail
    ).

depth(interp(D), p('{'), interp(D1)) :- !, D1 is D + 1.
depth(interp(D), p('}'), interp(D1)) :- !, D1 is D - 1.
depth(M, _, M).

%  Whitespace and comments.
skip([C|Cs0], O0, Cs, O, Cms0, Cms) :- white(C), !, O1 is O0 + 1, skip(Cs0, O1, Cs, O, Cms0, Cms).
skip([0'#|Cs0], O0, Cs, O, [cm(O0, O1, Text)|Cms0], Cms) :- !,
    take_line(Cs0, Line, Cs1), length(Line, N), O1 is O0 + 1 + N,
    string_codes(Text, [0'#|Line]),
    skip(Cs1, O1, Cs, O, Cms0, Cms).
skip([0'/, 0'*|Cs0], O0, Cs, O, [cm(O0, O1, Text)|Cms0], Cms) :- !,
    append(Body, [0'*, 0'/|Cs1], Cs0), !,
    length(Body, N), O1 is O0 + 4 + N,
    append([`/*`, Body, `*/`], T), string_codes(Text, T),
    skip(Cs1, O1, Cs, O, Cms0, Cms).
skip(Cs, O, Cs, O, Cms, Cms).

white(0' ). white(0'\t). white(0'\n). white(0'\r).

take_line([], [], []).
take_line([0'\n|Cs], [], [0'\n|Cs]) :- !.
take_line([C|Cs0], [C|L], Cs) :- take_line(Cs0, L, Cs).

%  token(Cs0, O0, Kind, Cs, O, Cms0, Cms)
token([0'$, 0'{|Cs0], O0, interp(Toks), Cs, O, Cms0, Cms) :- !,
    O1 is O0 + 2, lex(Cs0, O1, interp(0), Toks, Cms0, Cms, Cs, O).
token([0'"|Cs0], O0, str(Parts), Cs, O, Cms0, Cms) :- !,
    O1 is O0 + 1, dq(Cs0, O1, Parts, Cs, O, Cms0, Cms).
token([0'', 0''|Cs0], O0, istr(Parts), Cs, O, Cms0, Cms) :- !,
    O1 is O0 + 2, ind(Cs0, O1, Parts, Cs, O, Cms0, Cms).
token(Cs0, O0, spath(S), Cs, O, Cms, Cms) :-
    Cs0 = [0'<|Cs1], span(spath_char, Cs1, P, [0'>|Cs]), P \== [], !,
    string_codes(S, P), length(P, N), O is O0 + N + 2.
token(Cs0, O0, path(Parts), Cs, O, Cms0, Cms) :-
    path_start(Cs0, Pre, Cs1), !,
    path_rest(Cs1, Rest, Cs2), append(Pre, Rest, P), length(P, N), O1 is O0 + N,
    string_codes(S, P),
    path_interps(Cs2, O1, Parts1, Cs, O, Cms0, Cms),
    Parts = [lit(S)|Parts1].
token(Cs0, O0, uri(S), Cs, O, Cms, Cms) :-
    Cs0 = [C|_], alpha(C), span(scheme_char, Cs0, Sch, [0':|Cs1]),
    span(uri_char, Cs1, U, Cs), U \== [], !,
    append(Sch, [0':|U], All), string_codes(S, All), length(All, N), O is O0 + N.
token(Cs0, O0, Kind, Cs, O, Cms, Cms) :-
    Cs0 = [C|_], ( alpha(C) ; C == 0'_ ), !,
    span(id_char, Cs0, I, Cs), atom_codes(A, I), length(I, N), O is O0 + N,
    ( keyword(A) -> Kind = kw(A) ; Kind = id(A) ).
token(Cs0, O0, Kind, Cs, O, Cms, Cms) :-
    number_token(Cs0, Kind, Len, Cs), !, O is O0 + Len.
token(Cs0, O0, p(Op), Cs, O, Cms, Cms) :-
    member(S, ["...", "++", "//", "==", "!=", "<=", ">=", "&&", "||", "->", "|>", "<|",
               "{", "}", "[", "]", "(", ")", ";", ":", ",", ".", "=", "?", "@",
               "+", "-", "*", "/", "!", "<", ">"]),
    string_codes(S, SC), append(SC, Cs, Cs0), !,
    atom_codes(Op, SC), length(SC, N), O is O0 + N.

keyword(if). keyword(then). keyword(else). keyword(assert). keyword(with).
keyword(let). keyword(in). keyword(rec). keyword(inherit).

alpha(C) :- between(0'a, 0'z, C) ; between(0'A, 0'Z, C).
digit(C) :- between(0'0, 0'9, C).
id_char(C) :- alpha(C) ; digit(C) ; C == 0'_ ; C == 0'' ; C == 0'-.
path_char(C) :- alpha(C) ; digit(C) ; memberchk(C, `._-+`).
spath_char(C) :- path_char(C) ; C == 0'/.
scheme_char(C) :- alpha(C) ; digit(C) ; memberchk(C, `+-.`).
uri_char(C) :- alpha(C) ; digit(C) ; memberchk(C, `%/?:@&=+$,-_.!~*'`).

span(P, [C|Cs0], [C|W], Cs) :- call(P, C), !, span(P, Cs0, W, Cs).
span(_, Cs, [], Cs).

%  A path is path characters, then / and more, at least one slash
%  followed by a path character (or an interpolation); ~/ starts one too.
path_start([0'~, 0'/|Cs0], [0'~, 0'/|P], Cs) :- !, span(path_char, Cs0, P, Cs).
path_start(Cs0, Pre, Cs) :-
    span(path_char, Cs0, P0, [0'/|Cs1]),
    (   Cs1 = [C|_], path_char(C) -> true ; Cs1 = [0'$, 0'{|_] ),
    span(path_char, Cs1, P1, Cs),
    append(P0, [0'/|P1], Pre).

path_rest([0'/, C|Cs0], P, Cs) :- path_char(C), !,
    span(path_char, [C|Cs0], P1, Cs1), path_rest(Cs1, P2, Cs),
    append([0'/|P1], P2, P).
path_rest(Cs, [], Cs).

path_interps([0'$, 0'{|Cs0], O0, [interp(Toks, O0, O1)|Parts], Cs, O, Cms0, Cms) :- !,
    O2 is O0 + 2, lex(Cs0, O2, interp(0), Toks, Cms0, Cms1, Cs1, O1),
    span(spath_char, Cs1, P, Cs2), length(P, N), O3 is O1 + N,
    ( P == [] -> Parts = Parts1 ; string_codes(S, P), Parts = [lit(S)|Parts1] ),
    path_interps(Cs2, O3, Parts1, Cs, O, Cms1, Cms).
path_interps(Cs, O, [], Cs, O, Cms, Cms).

number_token(Cs0, float(F), Len, Cs) :-
    (   span(digit, Cs0, I, [0'.|Cs1]), I \== [] -> true
    ;   Cs0 = [0'.|Cs1], I = [0'0]
    ),
    span(digit, Cs1, Fr, Cs2), ( I == [0'0], Cs0 = [0'.|_] -> Fr \== [] ; true ),
    (   Cs2 = [E|Cs3], memberchk(E, `eE`),
        ( Cs3 = [S|Cs4], memberchk(S, `+-`) -> Sg = [S] ; Cs4 = Cs3, Sg = [] ),
        span(digit, Cs4, Ex, Cs), Ex \== []
    ->  append([[E], Sg, Ex], Exp)
    ;   Exp = [], Cs = Cs2
    ),
    append([I, `.`, Fr, `0`, Exp], FCs), number_codes(F, FCs),
    length(Cs0, L0), length(Cs, L1), Len is L0 - L1.
number_token(Cs0, int(N), Len, Cs) :-
    span(digit, Cs0, D, Cs), D \== [], number_codes(N, D), length(D, Len).

%  A "…" string: lit(Text) parts in their source spelling, and
%  interp(Toks, From, To) for each ${…}.
dq(Cs0, O0, Parts, Cs, O, Cms0, Cms) :-
    dq_lit(Cs0, L, Cs1), length(L, N), O1 is O0 + N,
    ( L == [] -> Parts = Parts1 ; string_codes(S, L), Parts = [lit(S)|Parts1] ),
    (   Cs1 = [0'"|Cs] -> O is O1 + 1, Parts1 = [], Cms = Cms0
    ;   Cs1 = [0'$, 0'{|Cs2]
    ->  O2 is O1 + 2, lex(Cs2, O2, interp(0), Toks, Cms0, Cms1, Cs3, O3),
        Parts1 = [interp(Toks, O1, O3)|Parts2],
        dq(Cs3, O3, Parts2, Cs, O, Cms1, Cms)
    ).

dq_lit([0'\\, C|Cs0], [0'\\, C|L], Cs) :- !, dq_lit(Cs0, L, Cs).
dq_lit([0'$, 0'$|Cs0], [0'$, 0'$|L], Cs) :- !, dq_lit(Cs0, L, Cs).
dq_lit([0'$, 0'{|Cs], [], [0'$, 0'{|Cs]) :- !.
dq_lit([0'"|Cs], [], [0'"|Cs]) :- !.
dq_lit([C|Cs0], [C|L], Cs) :- !, dq_lit(Cs0, L, Cs).
dq_lit([], [], []).

%  An ''…'' string, likewise.
ind(Cs0, O0, Parts, Cs, O, Cms0, Cms) :-
    ind_lit(Cs0, L, Cs1), length(L, N), O1 is O0 + N,
    ( L == [] -> Parts = Parts1 ; string_codes(S, L), Parts = [lit(S)|Parts1] ),
    (   Cs1 = [0'', 0''|Cs] -> O is O1 + 2, Parts1 = [], Cms = Cms0
    ;   Cs1 = [0'$, 0'{|Cs2]
    ->  O2 is O1 + 2, lex(Cs2, O2, interp(0), Toks, Cms0, Cms1, Cs3, O3),
        Parts1 = [interp(Toks, O1, O3)|Parts2],
        ind(Cs3, O3, Parts2, Cs, O, Cms1, Cms)
    ).

ind_lit([0'', 0'', 0''|Cs0], [0'', 0'', 0''|L], Cs) :- !, ind_lit(Cs0, L, Cs).
ind_lit([0'', 0'', 0'$|Cs0], [0'', 0'', 0'$|L], Cs) :- !, ind_lit(Cs0, L, Cs).
ind_lit([0'', 0'', 0'\\, C|Cs0], [0'', 0'', 0'\\, C|L], Cs) :- !, ind_lit(Cs0, L, Cs).
ind_lit([0'', 0''|Cs], [], [0'', 0''|Cs]) :- !.
ind_lit([0'$, 0'$|Cs0], [0'$, 0'$|L], Cs) :- !, ind_lit(Cs0, L, Cs).
ind_lit([0'$, 0'{|Cs], [], [0'$, 0'{|Cs]) :- !.
ind_lit([C|Cs0], [C|L], Cs) :- !, ind_lit(Cs0, L, Cs).
ind_lit([], [], []).

%% Parsing

tk(K, F, T) --> [t(K, F, T)], { far(F) }.
tk(K) --> tk(K, _, _).

far(F) :- nb_getval(nix_far, F0), ( F > F0 -> nb_setval(nix_far, F) ; true ).

peek(K), [t(K, F, T)] --> [t(K, F, T)].

expr(E) --> expr_function(E).

expr_function(E) --> lambda(E), !.
expr_function(assert(F-T, C, B)) --> tk(kw(assert), F, _), !, expr(C), tk(p(;)), expr_function(B), { end(B, T) }.
expr_function(with(F-T, W, B)) --> tk(kw(with), F, _), !, expr(W), tk(p(;)), expr_function(B), { end(B, T) }.
expr_function(let(F-T, Bs, B)) --> tk(kw(let), F, _), \+ peek(p('{')), !, binds(Bs), tk(kw(in)), expr_function(B), { end(B, T) }.
expr_function(E) --> expr_if(E).

lambda(lam(F-T, pid(X), B)) --> tk(id(X), F, _), tk(p(:)), !, expr_function(B), { end(B, T) }.
lambda(lam(F-T, pset(Fs, Ell, before(X)), B)) -->
    tk(id(X), F, _), tk(p(@)), !, formals(Fs, Ell, _), tk(p(:)), expr_function(B), { end(B, T) }.
lambda(lam(F-T, pset(Fs, Ell, At), B)) -->
    formals(Fs, Ell, F),
    ( tk(p(@)) -> tk(id(X)), { At = after(X) } ; { At = none } ),
    tk(p(:)), !, expr_function(B), { end(B, T) }.

formals(Fs, Ell, F) --> tk(p('{'), F, _), formal_list(Fs, Ell), tk(p('}')).

formal_list([], true) --> tk(p('...')), !.
formal_list([formal(F-T, X, D)|Fs], Ell) -->
    tk(id(X), F, T0),
    ( tk(p(?)) -> expr(D), { end(D, T) } ; { D = none, T = T0 } ),
    ( tk(p(',')) -> formal_list(Fs, Ell) ; { Fs = [], Ell = false } ).
formal_list([], false) --> [].

expr_if(if(F-T, C, Th, El)) --> tk(kw(if), F, _), !, expr(C), tk(kw(then)), expr(Th), tk(kw(else)), expr(El), { end(El, T) }.
expr_if(E) --> expr_op(0, E).

%  Operators by precedence climbing. binop(Op, Level, Assoc): a higher
%  level binds tighter; ! (8) and unary - (13) are prefixes, ? (12) takes
%  an attribute path, application is 14 and selection 15.
binop('|>', 1, left).
binop('<|', 1, right).
binop('->', 2, right).
binop('||', 3, left).
binop('&&', 4, left).
binop('==', 5, none).
binop('!=', 5, none).
binop('<', 6, none).
binop('<=', 6, none).
binop('>', 6, none).
binop('>=', 6, none).
binop('//', 7, right).
binop('+', 9, left).
binop('-', 9, left).
binop('*', 10, left).
binop('/', 10, left).
binop('++', 11, right).
binop('?', 12, none).

expr_op(Min, E) --> unary(L), op_rest(Min, L, E).

unary(not(F-T, A)) --> tk(p(!), F, _), !, expr_op(9, A), { end(A, T) }.
unary(neg(F-T, A)) --> tk(p(-), F, _), !, expr_op(13, A), { end(A, T) }.
unary(E) --> expr_app(E).

op_rest(Min, L, E) -->
    (   peek(p(Op)), { binop(Op, Lv, As), Lv >= Min }
    ->  tk(p(Op)),
        (   { Op == (?) }
        ->  attrpath(Path), { start(L, F), last(Path, A), end(A, T), N = has(F-T, L, Path) }
        ;   { As == right -> RMin = Lv ; RMin is Lv + 1 },
            expr_op(RMin, R), { start(L, F), end(R, T), N = bin(F-T, Op, L, R) }
        ),
        op_rest(Min, N, E)
    ;   { E = L }
    ).

expr_app(E) --> expr_select(F), app_args(As), { As == [] -> E = F ; start(F, S), last(As, A), end(A, T), E = app(S-T, F, As) }.

app_args([A|As]) --> starts_simple, !, expr_select(A), app_args(As).
app_args([]) --> [].

starts_simple --> peek(K), { simple_start(K) }.

simple_start(id(X)) :- X \== or.
simple_start(int(_)). simple_start(float(_)).
simple_start(str(_)). simple_start(istr(_)).
simple_start(path(_)). simple_start(spath(_)). simple_start(uri(_)).
simple_start(p('(')). simple_start(p('{')). simple_start(p('[')).
simple_start(kw(rec)).

expr_select(E) -->
    expr_simple(S),
    (   tk(p('.')), attrpath(Path)
    ->  (   tk(id(or)) -> expr_select(D), { end(D, T) }
        ;   { D = none, last(Path, A), end(A, T) }
        ),
        { start(S, F), E = select(F-T, S, Path, D) }
    ;   { E = S }
    ).

expr_simple(var(F-T, X)) --> tk(id(X), F, T), !.
expr_simple(int(F-T, N)) --> tk(int(N), F, T), !.
expr_simple(float(F-T, N)) --> tk(float(N), F, T), !.
expr_simple(str(F-T, Ps)) --> tk(str(Ps0), F, T), !, { parts(Ps0, Ps) }.
expr_simple(istr(F-T, Ps)) --> tk(istr(Ps0), F, T), !, { parts(Ps0, Ps) }.
expr_simple(path(F-T, Ps)) --> tk(path(Ps0), F, T), !, { parts(Ps0, Ps) }.
expr_simple(spath(F-T, S)) --> tk(spath(S), F, T), !.
expr_simple(uri(F-T, S)) --> tk(uri(S), F, T), !.
expr_simple(paren(F-T, E)) --> tk(p('('), F, _), !, expr(E), tk(p(')'), _, T).
expr_simple(attrs(F-T, rec, Bs)) --> tk(kw(rec), F, _), !, tk(p('{')), binds(Bs), tk(p('}'), _, T).
expr_simple(attrs(F-T, plain, Bs)) --> tk(p('{'), F, _), !, binds(Bs), tk(p('}'), _, T).
expr_simple(list(F-T, Es)) --> tk(p('['), F, _), !, list_elems(Es), tk(p(']'), _, T).

list_elems([E|Es]) --> starts_simple, !, expr_select(E), list_elems(Es).
list_elems([]) --> [].

parts([], []).
parts([lit(S)|Ps0], [lit(S)|Ps]) :- parts(Ps0, Ps).
parts([interp(Toks, F, T)|Ps0], [interp(F-T, E)|Ps]) :-
    phrase(expr(E), Toks), parts(Ps0, Ps).

binds([B|Bs]) --> bind(B), !, binds(Bs).
binds([]) --> [].

bind(inherit(F-T, From, Names)) -->
    tk(kw(inherit), F, _), !,
    ( tk(p('(')) -> expr(From), tk(p(')')) ; { From = none } ),
    inherit_names(Names), tk(p(;), _, T).
bind(bind(F-T, Path, E)) --> attrpath(Path), { Path = [A|_], start(A, F) }, tk(p(=)), expr(E), tk(p(;), _, T).

inherit_names([N|Ns]) --> attr(N), !, inherit_names(Ns).
inherit_names([]) --> [].

attrpath([A|As]) --> attr(A), ( tk(p('.')) -> attrpath(As) ; { As = [] } ).

attr(aid(F-T, X)) --> tk(id(X), F, T), !.
attr(astr(F-T, Ps)) --> tk(str(Ps0), F, T), !, { parts(Ps0, Ps) }.
attr(ainterp(F-T, E)) --> tk(interp(Toks), F, T), { phrase(expr(E), Toks) }.

start(N, F) :- arg(1, N, F-_).
end(N, T) :- arg(1, N, _-T).
