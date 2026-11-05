:- encoding(utf8).
/*  dterm-nix: Nix source as web pages, drawn the way dterm draws Prolog.

    nix_syntax.pl reads each file into terms with positions and comments;
    this file draws them by what they are:

    - an attribute set is a table of its bindings, name over value when
      the value is itself a block;
    - `let … in` is its bindings over its body;
    - a function's argument set is a signature with a table of its
      arguments and their defaults;
    - `if` chains and `mkIf` are tables of condition and consequence;
    - `inherit (x) a b` is a row of the names it binds;
    - a `mkOption` call is drawn as its type, default and example, with
      its description as prose;
    - `for pkgs.x [ steps ]`, a port, is a table of its steps
      (dterm_ports.pl);
    - paths link to the files they name, a drawn .nix file to its page;
    - each `let` binding lists the bindings that use it and those it
      uses, and a name links to the binding it refers to.

    Comments are drawn where they were written: a file's header is the
    page's lede, comments between bindings are notes, a section comment
    (# ━━━ Title ━━━) is a heading, and a comment at the end of a line
    sits beside it. The sidebar is the page's contents, the names bound
    at the file's top grouped by its sections (outline/3), over the
    files by directory. Inline terms are set as dterm sets
    Prolog: dterm.js (nanofil/web) breaks their lines at the width they
    get, reading the same data-d=args and data-d=op markup.

    Usage: swipl dterm_nix.pl OUT ROOT [--files=LIST] FILE... draws
    ROOT/FILE as OUT/PAGE.html for each FILE (a path under ROOT, such as
    nixos/filc.nix), and OUT/index.html. A path in the code or a comment
    links to the repository's file when there is one: in ROOT, or with
    --files, in LIST, one repository path per line. The pages expect dterm.css and
    dterm.js at ../nanofil/ and dterm-nix.css and dterm-nix.js beside
    them, as on the Filnix wiki.
*/
:- module(dterm_nix, []).

:- use_module(library(lists)).
:- use_module(library(ordsets)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(uri)).
:- use_module(nix_syntax).

:- initialization(main, main).

github('https://github.com/mbrock/filnix/blob/main/').

:- include('../nanofil/web/dterm_html').

main :-
    current_prolog_flag(argv, [Out, Root|Args0]),
    (   option_arg('--files=', Args0, List, Args1)
    ->  read_file_to_string(List, S, []), split_string(S, "\n", "", Ls),
        exclude(==(""), Ls, Ls1), maplist(atom_string, Repo, Ls1), list_to_ord_set(Repo, Set),
        nb_setval(nix_repo, Set)
    ;   Args1 = Args0, nb_setval(nix_repo, none)
    ),
    ( option_arg('--options=', Args1, Json, Args2) -> true ; Json = none, Args2 = Args1 ),
    ( option_arg('--nixpkgs=', Args2, Nixpkgs, Files) -> true ; Nixpkgs = none, Files = Args2 ),
    nb_setval(nix_root, Root),
    nb_setval(nix_pages, Files),
    check_page_names(Files),
    maplist(read_or_report(Root), Files, Read),
    (   memberchk(failed, Read)
    ->  format(user_error, "dterm-nix: a file above does not parse~n", []), halt(1)
    ;   Pages = Read
    ),
    (   Json == none -> Index = none
    ;   read_options(Json, Index)
    ),
    nb_setval(nix_options, Index),
    dsl_ids(Pages, Dsl), nb_setval(nix_dsl, Dsl),
    port_sites(Pages),
    maplist(write_source_page(Out, Pages), Pages),
    (   Index == none -> true
    ;   option_readers(Root, Nixpkgs, Files, Index),
        directory_file_path(Out, 'options.html', OPath),
        write_page(OPath, options_page(Pages, Index))
    ),
    directory_file_path(Out, 'index.html', IPath),
    write_page(IPath, index_page).

option_arg(Prefix, Args0, Value, Args) :-
    select(A, Args0, Args), atom_concat(Prefix, Value, A), !.

%% Reading

%  Every file is drawn, or the build fails: one that does not parse is
%  reported, and so are two whose pages would have the same name.
read_or_report(Root, File, Page) :-
    (   catch(read_page(Root, File, Page0), E, ( print_message(error, E), fail ))
    ->  Page = Page0
    ;   format(user_error, "dterm-nix: cannot read ~w~n", [File]), Page = failed
    ).

check_page_names(Files) :-
    maplist(page_name, Files, Names), msort(['index.html', 'options.html'|Names], Sorted),
    (   append(_, [X, X|_], Sorted)
    ->  format(user_error, "dterm-nix: two pages would be ~w~n", [X]), halt(1)
    ;   true
    ).

%  page(File, Text, Lines, Expr, Comments)
read_page(Root, File, page(File, Text, Lines, E, Cms)) :-
    directory_file_path(Root, File, Path),
    nix_read_file(Path, Text, nix(E, Cms0)),
    line_starts(Text, Lines),
    maplist(comment_kind(Text, Lines), Cms0, Cms).

%  A comment is own (alone on its line) or trailing (after code).
comment_kind(Text, ls(Starts), cm(F, T, S), cm(F, T, S, Kind)) :-
    functor(Starts, _, N), bsearch(Starts, F, 1, N, L), arg(L, Starts, Start),
    Len is F - Start, sub_string(Text, Start, Len, _, Pre),
    ( split_string(Pre, "", " \t", [""]) -> Kind = own ; Kind = trailing ).

line_starts(Text, ls(Starts)) :-
    string_codes(Text, Cs),
    findall(O, (O = 0 ; nth0(O0, Cs, 0'\n), O is O0 + 1), Os),
    Starts =.. [l|Os].

offset_line(O, Line) :- nb_getval(nix_lines, ls(Starts)), functor(Starts, _, N), bsearch(Starts, O, 1, N, Line).

bsearch(_, _, L, L, L) :- !.
bsearch(S, O, L, H, Line) :-
    M is (L + H + 1) // 2, arg(M, S, X),
    (   X =< O -> bsearch(S, O, M, H, Line) ; M1 is M - 1, bsearch(S, O, L, M1, Line) ).

src_text(F-T, S) :- nb_getval(nix_text, Text), L is T - F, sub_string(Text, F, L, _, S).

one_line(F-T) :- offset_line(F, L), T1 is max(F, T - 1), offset_line(T1, L1), L1 =:= L.

%% Names: what each identifier refers to

:- dynamic binder/4, ref/2, uses/2, binder_value/2, with_ref/2.

%  binder(Id, Name, Kind, Owner): a name bound in the file at anchor Id,
%  by Kind let, rec, param or inherit; Owner is the let binding it was
%  bound inside, or none. ref(Pos, Id): the identifier at Pos means Id.
%  uses(Owner, Id): the let binding Owner uses the one at Id.
resolve(E) :-
    retractall(binder(_, _, _, _)), retractall(ref(_, _)), retractall(uses(_, _)),
    retractall(binder_value(_, _)), retractall(with_ref(_, _)),
    res(E, [], none).

bid(F, Id) :- format(atom(Id), "b~w", [F]).

res(var(P, X), Env, Own) :- !,
    (   memberchk(X-Id, Env), Id \== none
    ->  assertz(ref(P, Id)),
        (   Own \== none, Own \== Id, binder(Id, _, let, IdOwn), IdOwn \== Own, \+ uses(Own, Id)
        ->  assertz(uses(Own, Id))
        ;   true
        )
    ;   member(with(W), Env)
    ->  assertz(with_ref(P, W))
    ;   true
    ).
res(with(_, W, B), Env, Own) :- !, res(W, Env, Own), res(B, [with(W)|Env], Own).
res(let(_, Bs, B), Env0, Own) :- !,
    binds_env(Bs, let, Own, Env0, Env),
    res_binds(Bs, Env, Own, let),
    res(B, Env, Own).
res(attrs(_, rec, Bs), Env0, Own) :- !,
    binds_env(Bs, rec, Own, Env0, Env),
    res_binds(Bs, Env, Own, rec).
res(attrs(P, plain, Bs), Env, Own) :- nb_getval(nix_top, P), !,
    forall(member(bind(_, Path, _), Bs), ( Path = [aid(F-_, _)|_] -> bid(F, Id), path_name(Path, N), assertz(binder(Id, N, top, none)) ; true )),
    res_binds(Bs, Env, Own, top).
res(attrs(_, plain, Bs), Env, Own) :- !, res_binds(Bs, Env, Own, plain).
res(lam(F-_, Param, B), Env0, Own) :- !,
    param_env(Param, F, Own, Env0, Env),
    ( Param = pset(Fs, _, _) -> forall(member(formal(_, _, D), Fs), ( D == none -> true ; res(D, Env, Own) )) ; true ),
    res(B, Env, Own).
res(N, Env, Own) :- compound(N), !,
    N =.. [_, _|As], forall(member(A, As), res_sub(A, Env, Own)).
res(_, _, _).

res_sub(A, Env, Own) :- is_list(A), !, forall(member(X, A), res_sub(X, Env, Own)).
res_sub(interp(_, E), Env, Own) :- !, res(E, Env, Own).
res_sub(lit(_), _, _) :- !.
res_sub(ainterp(_, E), Env, Own) :- !, res(E, Env, Own).
res_sub(astr(_, Ps), Env, Own) :- !, res_sub(Ps, Env, Own).
res_sub(aid(_, _), _, _) :- !.
res_sub(A, Env, Own) :- compound(A), functor(A, _, N), N > 0, arg(1, A, _-_), !, res(A, Env, Own).
res_sub(_, _, _).

binds_env(Bs, Kind, Own, Env0, Env) :-
    foldl(bind_env(Kind, Own), Bs, Env0, Env).

bind_env(Kind, Own, bind(_, [aid(F-_, X)|Path], V), Env0, [X-Id|Env0]) :- !,
    bid(F, Id), assertz(binder(Id, X, Kind, Own)),
    ( Path == [] -> assertz(binder_value(Id, V)) ; true ).
bind_env(Kind, Own, inherit(_, _, Ns), Env0, Env) :- !,
    foldl([N, E0, E]>>( N = aid(F-_, X) -> bid(F, Id), assertz(binder(Id, X, Kind, Own)), E = [X-Id|E0] ; E = E0 ),
          Ns, Env0, Env).
bind_env(_, _, _, Env, Env).

%  The values of bindings; each value of a let is owned by its binding.
res_binds(Bs, Env, Own, Kind) :- forall(member(B, Bs), res_bind(B, Env, Own, Kind)).

res_bind(bind(_, Path, E), Env, Own0, Kind) :-
    res_sub(Path, Env, Own0),
    (   Kind == let, Path = [aid(F-_, _)] -> bid(F, Own)
    ;   Kind == top, Path = [aid(F-_, _)|_] -> bid(F, Own)
    ;   Own = Own0
    ),
    res(E, Env, Own).
res_bind(inherit(_, From, Ns), Env, Own, _) :-
    (   From == none
    ->  forall(member(aid(P, X), Ns), ( memberchk(X-Id, Env) -> assertz(ref(P, Id)) ; true ))
    ;   res(From, Env, Own)
    ).

%  A plain parameter, or one named before its set, is anchored where
%  the function starts; one named after its set is not anchored.
param_env(pid(X), F, Own, Env, [X-Id|Env]) :- !, bid(F, Id), assertz(binder(Id, X, param, Own)).
param_env(pset(Fs, _, At), F0, Own, Env0, Env) :-
    foldl([formal(F-_, X, _), E0, [X-Id|E0]]>>( bid(F, Id), assertz(binder(Id, X, param, Own)) ), Fs, Env0, Env1),
    (   At = before(X) -> bid(F0, Id), assertz(binder(Id, X, param, Own)), Env = [X-Id|Env1]
    ;   At = after(X) -> Env = [X-none|Env1]
    ;   Env = Env1
    ).

%% Block or inline

%  block(E): E is drawn as a block of rows rather than as a line of text.
block(let(_, _, _)) :- !.
block(attrs(P, _, Bs)) :- !, \+ inline_attrs(P, Bs).
block(list(P, Es)) :- !, ( member(E, Es), block(E) -> true ; comments_inside(P) ).
block(lam(_, Param, B)) :- !, ( block(B) -> true ; Param = pset(Fs, _, _), member(formal(_, _, D), Fs), D \== none ).
block(with(_, _, B)) :- !, block(B).
block(assert(_, _, B)) :- !, block(B).
block(app(_, var(_, for), [_, _])) :- !.
block(app(_, _, As)) :- !, member(A, As), block(A), !.
block(paren(_, E)) :- !, block(E).
block(bin(_, _, L, R)) :- !, ( block(L) -> true ; block(R) ).
block(if(P, C, T, E)) :- !, ( \+ one_line(P) -> true ; block(C) ; block(T) ; block(E) ).
block(istr(_, Ps)) :- !, member(lit(S), Ps), sub_string(S, _, _, _, "\n"), !.

inline_attrs(P, Bs) :-
    \+ comments_inside(P),
    forall(member(bind(_, _, V), Bs), \+ block(V)),
    length(Bs, N),
    ( N =< 1 -> true ; one_line(P), N =< 3 ).

comments_inside(F-T) :- nb_getval(nix_notes_all, Cms), member(cm(O, _, _, _), Cms), O > F, O < T, !.

%% Notes: comments drawn where they were written

notes_before(From) -->
    { nb_getval(nix_notes, Q0), partition([cm(O, _, _, _)]>>(O < From), Q0, Now, Q), nb_setval(nix_notes, Q),
      note_groups(Now, Gs) },
    seq(Gs, note_).

%  Consecutive line comments form one group; a section comment starts
%  one.
note_groups([], []).
note_groups([C|Cs0], [[C|G]|Gs]) :-
    group_more(C, Cs0, G, Cs), note_groups(Cs, Gs).

group_more(cm(O, _, T, own), [cm(O1, To1, T1, own)|Cs0], [cm(O1, To1, T1, own)|G], Cs) :-
    \+ string_concat("/*", _, T), \+ string_concat("/*", _, T1),
    \+ section_title(cm(O1, To1, T1, own), _),
    offset_line(O, L), offset_line(O1, L1), L1 =:= L + 1, !,
    group_more(cm(O1, To1, T1, own), Cs0, G, Cs).
group_more(_, Cs, [], Cs).

%  A section comment, # ━━━ Title ━━━, is the heading of the section
%  that follows it, and of its names in the page's contents.
note_([C|G]) --> { section_title(C, T) }, !,
    { sec_id(T, Id) }, el(h2, "nix-sec", [id=Id], esc(T)),
    ( { G == [] } -> [] ; note_(G) ).
note_(G) --> { group_lines(G, Lines0), line_breaks(Lines0, Lines) }, el(div, note, prose_lines(Lines)).

section_title(cm(_, _, Text, own), Title) :-
    string_concat("#", R0, Text), split_string(R0, "", " ", [R]),
    member(Fr-Cs, ["━━━"-" ━", "───"-" ─", "==="-" =", "---"-" -"]),
    string_concat(Fr, _, R), string_concat(_, Fr, R), !,
    split_string(R, "", Cs, [T]), T \== "", atom_string(Title, T).

%  Its words, lower-case and joined by dashes: sec-core-libraries.
sec_id(Title, Id) :-
    downcase_atom(Title, D), atom_codes(D, Cs),
    maplist([C, W]>>( code_type(C, alnum) -> W = C ; W = 0'  ), Cs, Ws),
    atom_codes(A, Ws), atomic_list_concat(Parts, ' ', A), exclude(==(''), Parts, Ps),
    atomic_list_concat([sec|Ps], '-', Id).

%  Comments are read as dterm's little Markdown: consecutive lines are
%  one paragraph, a blank line ends it, and list items, indented blocks,
%  headings and tables are blocks of their own (blocks/2). A line that
%  was written as a line stays one, a line break within its paragraph:
%  a numbered line (1. …), each line of a run of label lines (Each
%  port: …, Usage: …), and a short line without end punctuation before
%  one that starts a sentence, such as a title over its explanation.
line_breaks(Ls0, Ls) :-
    maplist(label_line, Ls0, Labels),
    run_marks(Labels, none, Marks),
    pairs_keys_values(Ps, Ls0, Marks),
    break_pairs(Ps, Ls).

break_pairs([A-MA, B-MB|Ps], [A1|Ls]) :-
    \+ blank(A), \+ blank(B), indent(A, 0), indent(B, 0),
    (   numbered(B) -> true
    ;   MA == run, MB == run -> true
    ;   unended(A), string_code(1, B, C), C >= 0'A, C =< 0'Z
    ), !,
    soft_break(A, A1),
    break_pairs([B-MB|Ps], Ls).
break_pairs([A-_|Ps], [A|Ls]) :- !, break_pairs(Ps, Ls).
break_pairs([], []).

%  A line break within a paragraph, which block_//1 draws as <br>.
soft_break(A, A1) :- string_concat(A, "\u001E", A1).

%  A short line without punctuation at its end or a comma in it, as a
%  title is; "…, which omits" is a sentence that goes on.
unended(A) :-
    split_string(A, "", " ", [A1]), string_length(A1, N), N < 56, \+ sub_string(A1, _, _, _, ","),
    sub_string(A1, _, 1, 0, E), \+ sub_string(".,:;!?(", _, _, _, E).

%  run for a label line next to another label line.
run_marks([], _, []).
run_marks([L|Ls], Prev, [M|Ms]) :-
    ( Ls = [Next|_] -> true ; Next = none ),
    ( L == label, ( Prev == label ; Next == label ) -> M = run ; M = none ),
    run_marks(Ls, L, Ms).

%  A label line: up to three words, the first capitalized, then ": ".
label_line(L, Kind) :-
    (   indent(L, 0), once(sub_string(L, B, _, _, ": ")), B > 0,
        sub_string(L, 0, B, _, Pre), split_string(Pre, " ", "", Ws), length(Ws, N), N =< 3,
        string_code(1, Pre, C), C >= 0'A, C =< 0'Z,
        forall(member(W, Ws), ( W \== "", string_codes(W, Cs), forall(member(X, Cs), ( code_type(X, alpha) ; X == 0'- )) ))
    ->  Kind = label
    ;   Kind = none
    ).

numbered(B) :- string_codes(B, Cs), phrase((digits, ". "), Cs, _).
digits --> [C], { C >= 0'0, C =< 0'9 }, ( digits -> [] ; [] ).

group_lines(G, Lines) :- foldl([cm(_, _, T, _), L0, L]>>( comment_lines(T, Ls), append(L0, Ls, L) ), G, [], Lines).

comment_lines(T, Lines) :-
    (   string_concat("/*", Rest, T)
    ->  sub_string(Rest, 0, _, 2, Body), split_string(Body, "\n", "", Ls0),
        maplist([L0, L]>>( string_concat(" *", L1, L0) -> L = L1 ; L = L0 ), Ls0, Ls1),
        trim_blank_ends(Ls1, Lines0), dedent(Lines0, Lines)
    ;   string_concat("#", R0, T),
        ( string_concat(" ", R, R0) -> true ; R = R0 ),
        Lines = [R]
    ).

%  A comment at the end of the line where a row ends sits beside it.
aside_after(To) -->
    { nb_getval(nix_notes, [cm(O, _, Text, trailing)|Q]), T1 is max(0, To - 1),
      offset_line(T1, L), offset_line(O, L1), L1 =:= L, O >= T1 }, !,
    { nb_setval(nix_notes, Q), comment_lines(Text, Ls), atomic_list_concat(Ls, ' ', S) },
    el(span, aside, inline(S)), aside_after(To).
aside_after(_) --> [].

%% Blocks

%  blk(E): E drawn as a block.
blk(E) --> { block(E) }, !, blk_(E).
blk(str(P, [lit(S)])) --> { nb_getval(nix_prose, true) }, !,
    { node_pos(str(P, []), _-T) }, el(div, "prose described", prose_lines([S])), aside_after(T).
blk(E) --> { node_pos(E, _-T) }, el(div, goal, term(E)), aside_after(T).

blk_(let(_, Bs, B)) -->
    el(div, "let",
       ( el(div, "kw-row", el(span, kw, "let")),
         binds(Bs, let),
         el(div, "kw-row", el(span, kw, "in")),
         el(div, "let-body", blk(B)) )).
blk_(attrs(P, Rec, Bs)) -->
    { nb_getval(nix_top, P) -> Kind = top ; Kind = Rec },
    el(div, "attrs", ( ( { Rec == rec } -> el(span, "kw rec", "rec") ; [] ), binds(Bs, Kind) )).
%  The list a file makes, such as ports.nix's, is its page's body.
blk_(list(P, Es)) --> { nb_getval(nix_top, P) }, !, el(div, "list-block top", seq(Es, list_row)).
blk_(list(_, Es)) --> el(div, "list-block", seq(Es, list_row)).
blk_(lam(F-_, pid(X), B0)) --> !,
    { curried(B0, Ps, B) },
    el(div, "lam", ( el(div, "goal sig", ( el(span, lambda, "λ"), seq([F-X|Ps], param_def) )), el(div, "lam-body", blk(B)) )).
blk_(lam(F-_, Param, B)) --> el(div, "lam", ( signature(Param, F), el(div, "lam-body", blk(B)) )).

blk_(with(_, W, B)) -->
    el(div, "with", ( el(div, "goal kw-line", ( el(span, kw, "with"), " ", term(W) )), blk(B) )).
blk_(assert(_, C, B)) -->
    el(div, "assert", ( el(div, "goal kw-line", ( el(span, kw, "assert"), " ", term(C) )), blk(B) )).
blk_(paren(_, E)) --> { for_app(E, _, _) }, !, blk(E).
blk_(paren(_, E)) --> el(div, "paren block", blk(E)).
blk_(if(P, C, T, E)) --> { if_chain(if(P, C, T, E), Cases) }, cases(Cases, "").
blk_(app(P, var(_, for), [Pkg, S])) --> !, port_block(P, Pkg, S).
blk_(app(_, F, [C, X])) --> { is_fn(F, mkIf) }, !, cases([if(C, X)], "mkif").
blk_(app(_, F, As)) -->
    { append(Inline, [B|Rest], As), block(B), !, nb_getval(nix_option, Opt0),
      ( is_fn(F, mkOption) -> nb_setval(nix_option, true) ; nb_setval(nix_option, false) ) },
    el(div, "app-block",
       ( el(div, "goal app-head", fn_head(F, Inline)),
         el(div, "app-args", seq([B|Rest], app_row)) )),
    { nb_setval(nix_option, Opt0) }.
blk_(bin(P, Op, L, R)) -->
    { op_chain(Op, bin(P, Op, L, R), Es) },
    el(div, "op-stack", op_rows(Es, Op, first)).
blk_(istr(_, Ps)) --> istr_block(Ps).

%  x: y: B, as the parameters x and y of B.
curried(lam(F-_, pid(X), B0), [F-X|Ps], B) :- !, curried(B0, Ps, B).
curried(B, [], B).

param_def(F-X) --> { bid(F, Id) }, el(span, "v def", [id=Id, 'data-b'=Id], esc(X)), " ".

app_row(A) --> { node_pos(A, F-_) }, notes_before(F), el(div, "app-arg", blk(A)).

list_row(E) --> { node_pos(E, F-_) }, notes_before(F), el(div, "item", blk(E)).

op_rows([], _, _) --> [].
op_rows([E|Es], Op, First) -->
    { node_pos(E, F-_) }, notes_before(F),
    el(div, "op-row", ( ( { First == first } -> el(span, "op-lead", []) ; el(span, "op-lead", op_glyph(Op)) ),
                        el(div, operand, blk(E)) )),
    op_rows(Es, Op, rest).

%  The operands of a chain of one operator.
op_chain(Op, bin(_, Op, L, R), Es) :- !, op_chain(Op, L, Ls), op_chain(Op, R, Rs), append(Ls, Rs, Es).
op_chain(_, E, [E]).

if_chain(if(_, C, T, E), [if(C, T)|Cs]) :- !, if_chain(E, Cs).
if_chain(E, [else(E)]).

%  Conditionals: dterm's case table (dterm.css), a row per condition.
cases(Cs, Extra) -->
    { atomic_list_concat([cases, stack, Extra], ' ', Class0), atom_string(Class0, Class) },
    el(div, Class, case_rows(Cs, Extra)).

case_rows([], _) --> [].
case_rows([if(C, T)|Cs], Extra) -->
    { node_pos(C, F-_) }, notes_before(F),
    el(div, case, ( el(div, cond, el(div, goals, blk(C))),
                    el(div, arrow, "→"),
                    el(div, then, el(div, goals, blk(T))) )),
    case_rows(Cs, Extra).
case_rows([else(E)|Cs], Extra) -->
    { node_pos(E, F-_) }, notes_before(F),
    el(div, "case plain", ( el(div, cond, el(span, kw, "else")), el(div, arrow, []),
                            el(div, then, el(div, goals, blk(E))) )),
    case_rows(Cs, Extra).

%  An indented string as the text it means, a block of code marked as a
%  string rather than set between its quotes: its common indentation
%  gone, interpolations drawn as terms. A description is prose.
istr_block(Ps) -->
    { nb_getval(nix_prose, true), \+ member(interp(_, _), Ps), istr_text(Ps, Lines) }, !,
    el(div, "prose described", prose_lines(Lines)).
istr_block(Ps) -->
    { istr_lines(Ps, Lines) },
    el(div, "istr", [title="an indented string, ''…''"], el(div, "istr-text", seq(Lines, istr_line))).

istr_text(Ps, Lines) :-
    findall(S, member(lit(S), Ps), Ss), atomic_list_concat(Ss, A), split_string(A, "\n", "", Ls0),
    trim_blank_ends(Ls0, Ls1), dedent(Ls1, Lines).

%  The lines of an indented string as lists of lit(Text) and interp(P, E).
istr_lines(Ps, Lines) :-
    foldl(split_part, Ps, [[]], Rev0), reverse(Rev0, Lines0), maplist(reverse, Lines0, Lines1),
    exclude(blank_line, Lines1, NonBlank),
    maplist(line_indent, NonBlank, Is), ( min_list(Is, Min) -> true ; Min = 0 ),
    trim_blank_lines(Lines1, Lines2),
    maplist(drop_indent(Min), Lines2, Lines).

split_part(lit(S), [Cur|Done], Acc) :- !,
    split_string(S, "\n", "", [First|More]),
    ( First == "" -> Cur1 = Cur ; Cur1 = [lit(First)|Cur] ),
    foldl([L, [C|D], [C1, C|D]]>>( L == "" -> C1 = [] ; C1 = [lit(L)] ), More, [Cur1|Done], Acc0),
    Acc = Acc0.
split_part(I, [Cur|Done], [[I|Cur]|Done]).

blank_line(L) :- forall(member(P, L), ( P = lit(S), blank(S) )).
line_indent([lit(S)|_], I) :- !, indent(S, I).
line_indent(_, 0).
trim_blank_lines(Ls0, Ls) :-
    ( append([B], Ls1, Ls0), blank_line(B) -> trim_blank_lines(Ls1, Ls) ;
      append(Ls1, [B], Ls0), blank_line(B) -> trim_blank_lines(Ls1, Ls) ; Ls = Ls0 ).
drop_indent(N, [lit(S)|Ps], [lit(S1)|Ps]) :- !, ( blank(S) -> S1 = "" ; string_length(S, L), K is min(N, L), sub_string(S, K, _, 0, S1) ).
drop_indent(_, Ps, Ps).

istr_line(Ps) --> el(div, "istr-line", seq(Ps, istr_part)).
istr_part(lit(S)) --> esc(S).
istr_part(interp(_, E)) --> el(span, interp, ( el(span, dollar, "${"), term(E), el(span, dollar, "}") )).

%% Bindings

%  The bindings in runs, each a table of its own: a comment or a block
%  value ends a run, so a name column is as wide as its run needs.
binds(Bs, Kind) --> { runs(Bs, none, Runs) }, seq(Runs, bind_run(Kind)).

bind_run(Kind, Bs) --> el(div, binds, seq(Bs, bind_row(Kind))).

runs([], _, []).
runs([B|Bs], _, [[B|R]|Rs]) :- runs_cont(Bs, B, R, Rs).

runs_cont([], _, [], []).
runs_cont([B|Bs], Prev, R, Rs) :-
    (   run_break(Prev, B)
    ->  R = [], runs([B|Bs], none, Rs)
    ;   R = [B|R1], runs_cont(Bs, B, R1, Rs)
    ).

run_break(Prev, B) :-
    (   bind_block(Prev) -> true
    ;   bind_block(B) -> true
    ;   node_pos(Prev, _-T), node_pos(B, F-_), comments_between(T, F)
    ).

bind_block(bind(_, _, V)) :- block(V).

comments_between(T, F) :- nb_getval(nix_notes_all, Cms), member(cm(O, _, _, own), Cms), O >= T, O < F, !.

bind_row(Kind, bind(F-T, Path, V)) -->
    notes_before(F),
    { Path = [aid(AF-_, X)|_], bid(AF, Id) -> true ; Id = none, X = none },
    { ( memberchk(X, [description, longDescription]) -> Prose = true ; Prose = false ) },

    { ( block(V) -> Class = "clause bind over" ; wide_name(Path) -> Class = "clause bind wide" ; Class = "clause bind" ), offset_line(F, L),
      ( Id == none -> As = ['data-line'=L] ; As = [id=Id, 'data-line'=L] ),
      ( Id \== none, nb_getval(nix_snippet, false), nb_getval(nix_file, File), \+ line_anchor(File, L, _)
      ->  assertz(line_anchor(File, L, Id))
      ;   true
      ) },
    el(div, Class, As,
       ( el(div, head, ( line_link(L), attrpath(Path, def), el(span, eq, "=") )),
         el(div, value, ( { nb_getval(nix_prose, P0), nb_setval(nix_prose, Prose) },
                          blk(V),
                          { nb_setval(nix_prose, P0) } )),
         ( { memberchk(Kind, [let, top]), Id \== none } -> xrefs(Id) ; [] ),
         declared_options(L) )),
    aside_after(T).
bind_row(_, inherit(F-T, From, Ns)) -->
    notes_before(F),
    { offset_line(F, L) },
    el(div, "clause bind wide inherit", ['data-line'=L],
       ( el(div, head, ( line_link(L), el(span, kw, "inherit"),
                         ( { From == none } -> [] ; " ", el(span, from, term(From)) ) )),
         el(div, "value names", seq(Ns, inherit_name)) )),
    aside_after(T).

%  A name too long for the name column runs into the value's.
wide_name(Path) :- path_name(Path, N), atom_length(N, L), L > 20.

inherit_name(aid(F-_, X)) --> { bid(F, Id), ( binder(Id, _, _, _) -> As = [id=Id] ; As = [] ) },
    el(span, "name def", As, esc(X)), " ".
inherit_name(A) --> attr(A, def), " ".

%  The options of the index declared on this line, linked to it.
declared_options(L) -->
    { nb_getval(nix_snippet, false), nb_getval(nix_options, Index), Index \== none, nb_getval(nix_file, F),
      findall(N, ( index_options(Index, Os), member(O, Os), member(D, O.declarations),
                   D.file == F, D.line == L, N = O.name ), Ns), Ns \== [] }, !,
    el(div, "xrefs", el(span, "xref-group", ( el(span, "xref-title", "options"), " ", seq(Ns, option_ref) ))).
declared_options(_) --> [].

option_ref(N) --> { option_href(N, H) }, el(a, none, [href=H], esc(N)), " ".

%  Who uses a let binding, and what it uses.
xrefs(Id) -->
    { findall(N-U, ( uses(U, Id), binder(U, N, _, _) ), Users0), sort(Users0, Users),
      findall(N-U, ( uses(Id, U), binder(U, N, _, _) ), Used0), sort(Used0, Used) },
    (   { Users == [], Used == [] } -> []
    ;   el(div, "xrefs", ( xref_list("uses", Used), xref_list("used by", Users) ))
    ).

xref_list(_, []) --> !, [].
xref_list(Title, Refs) -->
    el(span, "xref-group", ( el(span, "xref-title", esc(Title)), " ", seq(Refs, xref_item) )).
xref_item(N-Id) --> { atom_concat('#', Id, H) }, el(a, none, [href=H], esc(N)), " ".

attrpath([A], Role) --> !, attr(A, Role).
attrpath([A|As], Role) --> attr(A, Role), el(span, dot, "."), attrpath(As, Role).

attr(aid(_, X), def) --> !, el(span, "name def", esc(X)).
attr(aid(_, X), _) --> el(span, name, esc(X)).
attr(astr(_, Ps), _) --> str_(Ps).
attr(ainterp(_, E), _) --> el(span, interp, ( el(span, dollar, "${"), term(E), el(span, dollar, "}") )).

line_link(L) -->
    { github(G), nb_getval(nix_file, F), format(atom(Href), "~w~w#L~w", [G, F, L]) },
    el(a, ln, [href=Href, title="source line"], esc(L)).

%% Functions: their parameters as a signature

signature(pid(X), F) -->
    { bid(F, Id) },
    el(div, "goal sig", ( el(span, lambda, "λ"), el(span, "v def", [id=Id, 'data-b'=Id], esc(X)) )).
signature(pset(Fs, Ell, At), F) -->
    el(div, "sig-block",
       ( el(div, "goal sig", ( el(span, lambda, "λ"), at_before(At, F), formals_inline(Fs, Ell), at_after(At) )),
         (   { member(formal(_, _, D), Fs), D \== none }
         ->  el(table, formals, el(tbody, none, seq(Fs, formal_row)))
         ;   []
         ) )).

at_before(before(X), F) --> { F \== none }, !, { bid(F, Id) }, el(span, "v def", [id=Id, 'data-b'=Id], esc(X)), el(span, at, "@").
at_before(before(X), _) --> !, el(span, "v def", esc(X)), el(span, at, "@").
at_before(_, _) --> [].
at_after(after(X)) --> !, el(span, at, "@"), el(span, "v def", esc(X)).
at_after(_) --> [].

formals_inline(Fs, Ell) -->
    { length(Fs, N), ( Ell == true -> N1 is N + 1 ; N1 = N ) },
    el(span, "c set", ['data-d'=args], el(span, "args curly", formal_items(Fs, Ell, N1))).

formal_items([], true, _) --> !, el(span, "arg ellipsis", "…").
formal_items([], false, _) --> [].
formal_items([formal(F-_, X, D)|Fs], Ell, _) -->
    { bid(F, Id), ( Fs == [], Ell == false -> Sep = [] ; Sep = el(span, sep, ",") ) },
    el(span, arg, ( el(span, "v def", [id=Id, 'data-b'=Id], esc(X)), ( { D == none } -> [] ; el(span, "opt", "?") ), Sep )),
    ( { Fs == [], Ell == false } -> [] ; " " ),
    formal_items(Fs, Ell, _).

formal_row(formal(F-_, X, D)) -->
    { nb_getval(nix_notes, Q0), partition([cm(O, _, _, _)]>>(O < F), Q0, Now, Q), nb_setval(nix_notes, Q),
      note_groups(Now, Gs) },
    seq(Gs, [G]>>el(tr, note, el(td, none, [colspan=2], note_(G)))),
    el(tr, none, ( el(td, name, el(span, "v", esc(X))),
                   el(td, default, ( { D == none } -> [] ; el(span, "kw", "default"), " ", term(D) )) )).

%% Terms: inline Nix, set as dterm sets Prolog

term(var(P, X)) --> !, var_ref(P, X).
term(int(P, _)) --> !, { src_text(P, S) }, el(span, n, esc(S)).
term(float(P, _)) --> !, { src_text(P, S) }, el(span, n, esc(S)).
term(str(_, Ps)) --> !, str_(Ps).
term(istr(_, Ps)) --> !, el(span, s, ( "''", seq(Ps, str_part), "''" )).
term(path(P, Ps)) --> !, path_(P, Ps).
term(spath(_, S)) --> !, el(span, "spath", ( "<", esc(S), ">" )).
term(uri(_, S)) --> !, el(a, uri, [href=S], esc(S)).
term(paren(_, E)) --> !, el(span, paren, term(E)).
term(list(_, [])) --> !, el(span, "l empty", "[ ]").
term(list(_, Es)) --> !, el(span, l, ['data-d'=args], items(Es)).
term(attrs(_, _, [])) --> !, el(span, "curly-empty", "{ }").
term(attrs(_, Rec, Bs)) --> !,
    el(span, "c set", ['data-d'=args],
       ( ( { Rec == rec } -> el(span, "kw rec", "rec") ; [] ),
         el(span, "args curly", seq_sp(Bs, inline_bind)) )).
term(select(_, E, Path, D)) --> !,
    el(span, sel, ( term(E), el(span, dot, "."), attrpath(Path, use) )),
    ( { D == none } -> [] ; "\u00A0", el(span, "op wide", [title="or"], el(span, kw, "or")), " ", term(D) ).
%  lib.literalExpression "E" shows the expression E, set as Nix.
term(app(_, F, [str(_, [lit(S0)])])) -->
    { is_fn(F, literalExpression), unescape(S0, S), catch(code_expr(S, E), _, fail) }, !,
    el(span, "c app", ( fn_(F), " ",
       el(span, "s lit-expr", [title="a Nix expression, as text"],
          el(code, term, ( el(span, q, "‹"), snippet(S, term(E)), el(span, q, "›") ))) )).
term(app(_, F, As)) --> !,
    el(span, "c app", ['data-d'=args], ( fn_(F), el(span, args, items(As)) )).
term(lam(F-_, pid(X), B0)) --> !,
    { curried(B0, Ps, B) },
    el(span, "o lam", ['data-d'=op], ( el(span, params, seq_colon([F-X|Ps])), el(span, "op wide colon", [title=":"], ":"), " ", term(B) )).
term(lam(F-_, Param, B)) --> !,
    el(span, "o lam", ['data-d'=op], ( param_inline(Param, F), el(span, "op wide colon", [title=":"], ":"), " ", term(B) )).
term(bin(_, Op, L, R)) --> !,
    el(span, o, ['data-d'=op], ( term(L), "\u00A0", el(span, "op wide", [title=Op], op_glyph(Op)), " ", term(R) )).
term(has(_, E, Path)) --> !,
    el(span, o, ( term(E), "\u00A0", el(span, "op", [title="?"], "?"), " ", attrpath(Path, use) )).
term(not(_, E)) --> !, el(span, "o pre", ( el(span, "op neg", [title="!"], "¬"), term(E) )).
term(neg(_, E)) --> !, el(span, "o pre", ( el(span, "op", [title="-"], "−"), term(E) )).
term(if(_, C, T, E)) --> !,
    el(span, "o if", ( el(span, kw, "if"), " ", term(C), " ", el(span, kw, "then"), " ", term(T), " ",
                       el(span, kw, "else"), " ", term(E) )).
term(let(_, Bs, B)) --> !,
    el(span, "o let", ( el(span, kw, "let"), " ", seq_sp(Bs, inline_bind), " ", el(span, kw, "in"), " ", term(B) )).
term(with(_, W, B)) --> !, el(span, "o with", ( el(span, kw, "with"), " ", term(W), "; ", term(B) )).
term(assert(_, C, B)) --> !, el(span, "o assert", ( el(span, kw, "assert"), " ", term(C), "; ", term(B) )).

items([E]) --> !, el(span, arg, term(E)).
items([E|Es]) --> el(span, arg, term(E)), " ", items(Es).

seq_sp([X], G) --> !, el(span, arg, call(G, X)).
seq_sp([X|Xs], G) --> el(span, arg, call(G, X)), " ", seq_sp(Xs, G).

%  A name bound inline is anchored like one bound in a table, so its uses
%  and readers can link to it.
inline_bind(bind(_, Path, V)) -->
    { Path = [aid(F-_, _)|_], nb_getval(nix_snippet, false), bid(F, Id) }, !,
    el(span, "inline-def", [id=Id], attrpath(Path, use)), "\u00A0", el(span, eqi, "="), " ", term(V), el(span, sep, ";").
inline_bind(bind(_, Path, V)) --> attrpath(Path, use), "\u00A0", el(span, eqi, "="), " ", term(V), el(span, sep, ";").
inline_bind(inherit(_, From, Ns)) -->
    el(span, kw, "inherit"), " ", ( { From == none } -> [] ; el(span, paren, term(From)), " " ),
    seq_names(Ns), el(span, sep, ";").

seq_names([N]) --> !, inline_name(N).
seq_names([N|Ns]) --> inline_name(N), " ", seq_names(Ns).

inline_name(aid(F-_, X)) --> { nb_getval(nix_snippet, false), bid(F, Id), binder(Id, _, _, _) }, !,
    el(span, "name inline-def", [id=Id], esc(X)).
inline_name(N) --> attr(N, use).

param_inline(pset(Fs, Ell, At), F) --> at_before(At, F), formals_inline(Fs, Ell), at_after(At).

seq_colon([F-X]) --> !, { bid(F, Id) }, el(span, "v def", [id=Id, 'data-b'=Id], esc(X)).
seq_colon([F-X|Ps]) --> seq_colon([F-X]), el(span, colon, ":"), "\u00A0", seq_colon(Ps).

%  The function of an application, linked when the file defines it.
fn_head(F, []) --> !, fn_(F).
fn_head(F, As) --> el(span, "c app", ['data-d'=args], ( fn_(F), el(span, args, items(As)) )).

fn_(var(P, X)) --> !, var_ref(P, X, "f call").
fn_(select(P, E, Path, none)) --> !, el(span, "f call", term(select(P, E, Path, none))).
fn_(F) --> term(F).

is_fn(var(_, N), N).
is_fn(select(_, _, Path, none), N) :- last(Path, aid(_, N)).

var_ref(P, X) --> var_ref(P, X, v).
var_ref(P, X, Class) -->
    (   { nb_getval(nix_snippet, false), ref(P, Id) }
    ->  { atom_concat('#', Id, H) }, el(a, Class, [href=H, 'data-b'=Id], esc(X))
    ;   { builtin_name(X) } -> el(span, "v builtin", esc(X))
    ;   el(span, Class, esc(X))
    ).

builtin_name(X) :- memberchk(X, [builtins, true, false, null, import, throw, toString, map, abort,
                                  baseNameOf, dirOf, isNull, removeAttrs, derivation, placeholder]).

str_(Ps) --> el(span, s, ( "\"", seq(Ps, str_part), "\"" )).
str_part(lit(S)) --> esc(S).
str_part(interp(_, E)) --> el(span, interp, ( el(span, dollar, "${"), term(E), el(span, dollar, "}") )).

%  A path links to the file or directory it names in the repository.
path_(_, Ps) -->
    { Ps = [lit(S)], path_target(S, Href) }, !,
    el(a, path, [href=Href], esc(S)).
path_(_, Ps) --> el(span, path, seq(Ps, str_part)).

path_target(S, Href) :-
    \+ sub_string(S, 0, _, _, "/"), \+ sub_string(S, 0, _, _, "~"),
    nb_getval(nix_file, F),
    file_directory_name(F, Dir), directory_file_path(Dir, S, Rel0),
    normalize_rel(Rel0, Rel), Rel \== '',
    repo_href(Rel, Href).

%  repo_href(+Path, -Href): Path is a file or directory of the
%  repository; Href is its page, or its place on GitHub.
repo_href(Rel, Href) :-
    nb_getval(nix_pages, Pages), memberchk(Rel, Pages), !, page_name(Rel, Href).
%  A directory imported as Nix is its default.nix.
repo_href(Rel, Href) :-
    nb_getval(nix_pages, Pages), atom_concat(Rel, '/default.nix', D), memberchk(D, Pages), !,
    page_name(D, Href).
repo_href(Rel, Href) :-
    repo_entry(Rel, Kind),
    (   Kind == dir -> atom_concat('https://github.com/mbrock/filnix/tree/main/', Rel, Href)
    ;   github(G), atom_concat(G, Rel, Href)
    ).

repo_entry(Rel, Kind) :-
    nb_getval(nix_repo, Set),
    (   Set == none
    ->  nb_getval(nix_root, Root), directory_file_path(Root, Rel, Abs),
        ( exists_file(Abs) -> Kind = file ; exists_directory(Abs) -> Kind = dir )
    ;   ord_memberchk(Rel, Set) -> Kind = file
    ;   atom_concat(Rel, '/', Pre), member(F, Set), sub_atom(F, 0, _, _, Pre) -> Kind = dir
    ).

normalize_rel(P0, P) :-
    atomic_list_concat(Parts0, '/', P0),
    foldl([X, A0, A]>>( X == '.' -> A = A0 ; X == '' -> A = A0 ; X == '..' -> A0 = [_|A] ; A = [X|A0] ), Parts0, [], Rev),
    reverse(Rev, Parts), atomic_list_concat(Parts, '/', P).

op_glyph(Op) --> { op_glyph(Op, G) -> true ; atom_codes(Op, G) }, esc(G).

op_glyph('==', "≡").
op_glyph('!=', "≢").
op_glyph('<=', "≤").
op_glyph('>=', "≥").
op_glyph('&&', "∧").
op_glyph('||', "∨").
op_glyph('->', "⇒").
op_glyph('*', "×").
op_glyph('-', "−").

%% Prose: comments and descriptions, in dterm's little Markdown

prose_lines(Lines0) --> { dedent(Lines0, Lines), blocks(Lines, Bs) }, el(div, prose, seq(Bs, block_)).

block_(p(T)) --> { split_string(T, "\u001E", " ", Ls) }, el(p, none, soft_lines(Ls)).
block_(ul(Items)) --> el(ul, none, seq(Items, li_)).
block_(pre(Lines)) --> { dedent(Lines, Ls) }, pre_block(Ls).
block_(h(N, T)) --> { format(atom(H), "h~d", [N]) }, el(H, "prose-h", inline(T)).
block_(table(Head, Rows)) -->
    el(table, "prose-table", ( el(thead, none, el(tr, none, seq(Head, cell_(th)))),
                               el(tbody, none, seq(Rows, row_)) )).
block_(fence(_, Lines)) --> { dedent(Lines, Ls), atomic_list_concat(Ls, '\n', T) }, el(pre, fence, esc(T)).

row_(Cells) --> el(tr, none, seq(Cells, cell_(td))).
cell_(Tag, T) --> el(Tag, none, inline(T)).
li_(T) --> { split_string(T, "\u001E", " ", Ls) }, el(li, none, soft_lines(Ls)).

soft_lines([L]) --> !, inline(L).
soft_lines([L|Ls]) --> inline(L), "<br>", soft_lines(Ls).

%  Indented text in a comment, such as an example of the module's use,
%  is drawn as Nix when it reads as bindings or an expression.
pre_block(Ls) -->
    { atomic_list_concat(Ls, '\n', T), string_codes(T, Cs),
      catch(example_binds(Cs, Wrapped, Bs), _, fail) }, !,
    el(div, example, snippet(Wrapped, el(div, binds, seq(Bs, example_row)))).
pre_block(Ls) --> { atomic_list_concat(Ls, '\n', T) }, el(pre, none, esc(T)).

%  Example bindings, each with the comment that ends its line.
example_binds(Cs, Wrapped, Bs) :-
    append([`{`, Cs, `\n}`], WCs), string_codes(Wrapped, WCs),
    nix_parse_codes(WCs, attrs(_, _, Bs0), Cms), Bs0 \== [],
    maplist(example_note(WCs, Cms), Bs0, Bs).

example_note(WCs, Cms, B, B-Note) :-
    node_pos(B, _-T),
    (   member(cm(O, _, Text), Cms), O >= T, length(Pre, O), append(Pre, _, WCs),
        length(Upto, T), append(Upto, Between, Pre), \+ memberchk(0'\n, Between)
    ->  comment_lines(Text, Ls), atomic_list_concat(Ls, ' ', Note)
    ;   Note = none
    ).

example_row(bind(_, Path, V)-Note) -->
    el(div, "clause bind", ( el(div, head, ( attrpath(Path, use), el(span, eq, "=") )),
                             el(div, value, ( blk(V),
                                              ( { Note == none } -> [] ; el(span, aside, inline(Note)) ) )) )).
example_row(inherit(P, F, Ns)-_) --> el(div, "clause bind", el(div, goal, inline_bind(inherit(P, F, Ns)))).

inline(Text) --> { string_codes(Text, Cs) }, inl(Cs).

inl([]) --> !, [].
%  A MyST role in an option's description, such as {manpage}`ssh(1)` or
%  {option}`services.openssh.enable`: its text as code, an option
%  linked to the index.
inl([0'{|Cs0]) --> { append(Role, [0'}, 0'`|Cs1], Cs0), Role \== [], maplist([C]>>code_type(C, alpha), Role),
                     append(Code, [0'`|Cs], Cs1) }, !,
    (   { Role == `option`, atom_codes(Name, Code), option_href(Name, H) }
    ->  el(a, ref, [href=H], el(code, none, esc(Code)))
    ;   el(code, none, esc(Code))
    ),
    inl(Cs).
%  Markdown links: <https://…> and [text](url).
inl([0'<|Cs0]) --> { append(U, [0'>|Cs], Cs0), append(`http`, _, U), \+ memberchk(0' , U) }, !,
    el(a, none, [href=U], esc(U)), inl(Cs).
inl([0'[|Cs0]) --> { append(T, [0'], 0'(|Cs1], Cs0), \+ memberchk(0'], T), append(U, [0')|Cs], Cs1), \+ memberchk(0' , U) }, !,
    { string_codes(TS, T) }, el(a, none, [href=U], inline(TS)), inl(Cs).
inl([0'`|Cs0]) --> { append(Code, [0'`|Cs], Cs0) }, !,
    (   { \+ call_like(Code), catch(code_expr(Code, E), _, fail), E \= var(_, _) }
    ->  { string_codes(CS, Code) }, el(code, term, snippet(CS, term(E)))
    ;   el(code, none, esc(Code))
    ),
    inl(Cs).
inl(Cs0) --> { span(path_word_char, Cs0, W, Cs), W \== [] }, !,
    (   { memberchk(0'/, W), atom_codes(A, W), prose_path(A, Href) }
    ->  el(a, path, [href=Href], esc(A))
    ;   esc(W)
    ),
    inl(Cs).
inl([C|Cs]) --> esc_code(C), inl(Cs).

path_word_char(C) :- code_type(C, csym) ; memberchk(C, `./-`).

%  Code in prose written as f(x), such as sshd_config(5), is not Nix,
%  which writes an application f x.
call_like(Code) :- append(_, [C, 0'(|_], Code), code_type(C, csym), !.

%  A word in prose that names a file of the repository, such as
%  lib/block-rust-go.nix or tests/nixos.
prose_path(A0, Href) :-
    ( sub_atom(A0, B, 1, 0, '.') -> sub_atom(A0, 0, B, _, A1) ; A1 = A0 ),
    sub_atom(A1, 0, 1, _, C), char_type(C, alnum),
    normalize_rel(A1, A), A == A1,
    repo_href(A, Href).

%  Inline code that reads as a Nix expression is drawn as one; its
%  positions are offsets into the code.
code_expr(Code0, E) :-
    ( is_list(Code0) -> Code = Code0 ; text_to_string(Code0, S), string_codes(S, Code) ),
    nix_parse_codes(Code, E, []).

%  snippet(Text, Body): Body drawn with Text as the source its positions
%  are in, and no names resolved: they belong to the snippet, not the file.
snippet(Text, Body) -->
    { maplist(nb_getval, [nix_text, nix_lines, nix_notes, nix_snippet], Saved),
      line_starts(Text, Ls), maplist(nb_setval, [nix_text, nix_lines, nix_notes, nix_snippet], [Text, Ls, [], true]) },
    Body,
    { maplist(nb_setval, [nix_text, nix_lines, nix_notes, nix_snippet], Saved) }.

%  The text a "…" string means, for the escapes a Nix expression in one
%  uses.
unescape(S0, S) :-
    string_codes(S0, Cs0), phrase(unesc(Cs), Cs0), string_codes(S, Cs).
unesc([C|Cs]) --> "\\", [C], !, unesc(Cs).
unesc([C|Cs]) --> [C], !, unesc(Cs).
unesc([]) --> [].

span(P, [C|Cs0], [C|W], Cs) :- call(P, C), !, span(P, Cs0, W, Cs).
span(_, Cs, [], Cs).

%% The option index

:- include(dterm_options).

%% Port lists

:- include(dterm_ports).

%% Pages

%  Every file is one page, drawn the same way: its header comment the
%  lede, its expression the body, and its contents the sections and
%  names of its own source (outline/3) in the sidebar, over the files.

page_name(File, Html) :- atomic_list_concat(Parts, '/', File), atomic_list_concat(Parts, '-', B0),
    file_name_extension(B, _, B0), file_name_extension(B, html, Html).

write_source_page(Out, _, page(File, Text, Lines, E, Cms)) :-
    nb_setval(nix_text, Text), nb_setval(nix_lines, Lines), nb_setval(nix_file, File),
    nb_setval(nix_prose, false), nb_setval(nix_option, false),
    nb_setval(nix_snippet, false),
    ( top_body(E, Top) -> node_pos(Top, TP), nb_setval(nix_top, TP) ; nb_setval(nix_top, none) ),
    resolve(E),
    node_pos(E, From-_),
    partition([cm(O, _, _, _)]>>(O < From), Cms, Head, Body),
    nb_setval(nix_notes_all, Body), nb_setval(nix_notes, Body),
    summarize(File, Text, Head),
    outline(E, Body, Groups),
    page_name(File, Name), directory_file_path(Out, Name, Path),
    write_page(Path, source_page(File, Head, E, Groups)).

source_page(File, Head, E, Groups) -->
    { note_groups(Head, Gs) },
    shell(File, crumbs(File),
          ( sidebar(File, Groups),
            el(article, "dterm nix", ( el(h1, "source-title", esc(File)),
                                       el(div, "prose lede", seq(Gs, lede_group)),
                                       el(div, "clause nix-root", ( blk(E), rest_notes )) )) )).

lede_group(G) --> { group_lines(G, Ls0), line_breaks(Ls0, Ls) }, prose_lines(Ls).

rest_notes --> { nb_getval(nix_notes, Q), nb_setval(nix_notes, []), note_groups(Q, Gs) }, seq(Gs, note_).

crumbs(Title) -->
    el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="index.html"], "Nix"), el(span, "crumb-sep", "›"),
    el(span, "crumb current", esc(Title)).

%  The value a file makes, through its functions and lets.
top_body(lam(_, _, B), T) :- !, top_body(B, T).
top_body(let(_, _, B), T) :- !, top_body(B, T).
top_body(with(_, _, B), T) :- !, top_body(B, T).
top_body(T, T) :- T = attrs(_, plain, _), !.
top_body(T, T) :- T = list(_, _).

%  The first sentence of a file's header, and its length, for the index.
:- dynamic page_summary/3.

summarize(File, Text, Head) :-
    split_string(Text, "\n", "", Ls), length(Ls, NL),
    (   note_groups(Head, [G|_]), group_lines(G, GLs0), line_breaks(GLs0, GLs), dedent(GLs, D),
        blocks(D, [p(P)|_]), split_string(P, "\u001E", " ", [S0|_])
    ->  first_sentence(S0, Sum)
    ;   Sum = ""
    ),
    retractall(page_summary(File, _, _)), assertz(page_summary(File, Sum, NL)).

first_sentence(S0, S) :-
    (   sub_string(S0, B, _, _, ". "), B > 20 -> B1 is B + 1, sub_string(S0, 0, B1, _, S1) ; S1 = S0 ),
    (   string_length(S1, N), N > 160 -> sub_string(S1, 0, 157, _, S2), string_concat(S2, "…", S) ; S = S1 ).

%% Contents: a page's sections and the names in them

%  outline(+E, +Cms, -Groups): g(Title, Href, Entries) in source order.
%  The names are those the file binds at its top, through its functions
%  and lets: let bindings, the attributes of the set it makes, and the
%  ports, bindings and imports of the list it makes. A section comment
%  starts a group of the names after it; before the first, names are
%  grouped by what binds them.
outline(E, Cms, Groups) :-
    top_items(E, Es),
    findall(O-s(T), ( member(C, Cms), C = cm(O, _, _, _), section_title(C, T) ), Ss),
    findall(O-X, ( member(X, Es), X = e(O, _, _, _) ), Ps),
    append(Ps, Ss, Xs0), keysort(Xs0, Xs1), pairs_values(Xs1, Xs),
    outline_groups(Xs, Groups).

outline_groups(Xs, Gs) :-
    (   append(Pre, [s(T)|Post], Xs), \+ memberchk(s(_), Pre)
    ->  kind_groups(Pre, G1), section_groups([s(T)|Post], G2), append(G1, G2, Gs)
    ;   kind_groups(Xs, Gs)
    ).

kind_groups([], []).
kind_groups([e(O, K, N, H)|Xs], [g(k(K), none, [e(O, K, N, H)|Same])|Gs]) :-
    same_kind(K, Xs, Same, Rest), kind_groups(Rest, Gs).

same_kind(K, [e(O, K, N, H)|Xs], [e(O, K, N, H)|S], R) :- !, same_kind(K, Xs, S, R).
same_kind(_, Xs, [], Xs).

section_groups([], []).
section_groups([s(T)|Xs], [g(T, H, Es)|Gs]) :-
    sec_id(T, Id), atom_concat('#', Id, H),
    (   append(Es, [s(T1)|Rest], Xs), \+ memberchk(s(_), Es)
    ->  section_groups([s(T1)|Rest], Gs)
    ;   Es = Xs, Gs = []
    ).

%  e(Offset, Kind, Name, Href)
top_items(lam(_, _, B), Es) :- !, top_items(B, Es).
top_items(with(_, _, B), Es) :- !, top_items(B, Es).
top_items(assert(_, _, B), Es) :- !, top_items(B, Es).
top_items(paren(_, B), Es) :- !, top_items(B, Es).
top_items(let(_, Bs, B), Es) :- !, bind_items(let, Bs, E1), top_items(B, E2), append(E1, E2, Es).
top_items(attrs(_, _, Bs), Es) :- !, bind_items(returns, Bs, Es).
top_items(bin(_, '//', L, R), Es) :- !, top_items(L, E1), top_items(R, E2), append(E1, E2, Es).
top_items(list(_, Is), Es) :- !, foldl([I, A0, A]>>( list_items(I, E), append(A0, E, A) ), Is, [], Es).
top_items(_, []).

list_items(paren(_, E), Es) :- !, list_items(E, Es).
list_items(app(F-_, var(_, for), [Pkg, _]), [e(F, item, N, H)]) :- !,
    pkg_name(Pkg, N), nb_getval(nix_file, File),
    ( port_site(File, F, Id) -> atom_concat('#', Id, H) ; H = none ).
list_items(let(_, Bs, B), Es) :- !, bind_items(item, Bs, E1), list_items(B, E2), append(E1, E2, Es).
list_items(attrs(_, _, Bs), Es) :- !, bind_items(item, Bs, Es).
list_items(app(F-_, var(_, import), [path(_, [lit(S)])|_]), [e(F, import, N, H)]) :-
    path_target(S, H), !, ( atom_concat('./', N, S) -> true ; atom_string(N, S) ).
list_items(_, []).

bind_items(Kind, Bs, Es) :-
    findall(e(F, Kind, Name, H), ( member(bind(_, Path, _), Bs), Path = [aid(F-_, _)|_], bid(F, Id),
                                   atom_concat('#', Id, H), path_name(Path, Name) ), Es).

path_name(Path, Name) :-
    maplist([A, N]>>( A = aid(_, N) -> true ; N = '…' ), Path, Ns), atomic_list_concat(Ns, '.', Name).

%% The sidebar: this page's contents, then the files

sidebar(Current, Groups) -->
    el(nav, "toc dterm-nav nix-nav", ['aria-label'="Contents"],
       ( ( { Groups == [] } -> []
         ; el(details, "nav-block contents", [open=open], ( el(summary, "toc-title", "Contents"), seq(Groups, nav_group) )) ),
         ( { Current == index } -> [] ; files_nav(Current) ) )).

nav_group(g(T, H, [])) --> !, el(div, "nav-group", nav_title(T, H)).
%  Short names are set in two columns, long ones in one.
nav_group(g(T, H, Es)) -->
    { ( member(e(_, _, N, _), Es), atom_length(N, L), L > 13 -> C = "nav-names long" ; C = "nav-names" ) },
    el(details, "nav-group", [open=open], ( el(summary, none, nav_title(T, H)), el(ul, C, seq(Es, nav_name)) )).

nav_title(T, H) --> { group_title(T, S) },
    ( { H == none } -> el(span, "nav-group-title", esc(S)) ; el(a, "nav-group-title", [href=H], esc(S)) ).

group_title(k(let), "let") :- !.
group_title(k(returns), "returns") :- !.
group_title(k(item), "list") :- !.
group_title(k(import), "imports") :- !.
group_title(T, T).

nav_name(e(_, _, N, none)) --> !, el(li, none, esc(N)).
nav_name(e(_, _, N, H)) --> el(li, none, el(a, none, [href=H], esc(N))).

files_nav(Current) -->
    { nb_getval(nix_pages, Files), dir_groups(Files, Ds), ( Current == options -> OC = current ; OC = none ) },
    el(details, "nav-block files", [open=open],
       ( el(summary, "toc-title", "Files"),
         el(ul, "nav-top", ( el(li, none, el(a, none, [href="index.html"], "Index")),
                             ( { nb_getval(nix_options, I), I \== none }
                             -> el(li, OC, el(a, none, [href="options.html"], "Options"))
                             ;  [] ) )),
         seq(Ds, dir_nav(Current)) )).

dir_nav(Current, D-Fs) -->
    { dir_title(D, T), ( memberchk(Current, Fs) -> As = [open=open] ; As = [] ) },
    el(details, "nav-dir", As, ( el(summary, none, esc(T)), el(ul, none, seq(Fs, file_nav(D, Current))) )).

file_nav(D, Current, F) --> { page_name(F, H), rel_to(D, F, R), ( F == Current -> C = current ; C = none ) },
    el(li, C, el(a, none, [href=H], esc(R))).

%  The files by the directory they are in at the top of the repository,
%  the files at the top first.
dir_groups(Files, Ds) :-
    maplist([F, D-F]>>( once(sub_atom(F, B, _, _, '/')) -> sub_atom(F, 0, B, _, D) ; D = '' ), Files, Ps0),
    keysort(Ps0, Ps), group_pairs_by_key(Ps, Ds).

dir_title('', "top level") :- !.
dir_title(D, T) :- atom_concat(D, '/', T).

dir_id('', 'dir-top') :- !.
dir_id(D, Id) :- atom_concat('dir-', D, Id).

rel_to('', F, F) :- !.
rel_to(D, F, R) :- atom_concat(D, '/', P), atom_concat(P, R, F).

shell(Title, Crumbs, Main) -->
    "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>", esc(Title), " · Nix · Filnix wiki</title>\n",
    "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n",
    "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"../style.css\">\n",
    "<link rel=\"stylesheet\" href=\"../nanofil/dterm.css\">\n",
    "<link rel=\"stylesheet\" href=\"dterm-nix.css\">\n",
    "</head>\n<body>\n",
    "<header class=\"library\"><div class=\"page-frame library-frame\">\n",
    "  <div class=\"library-heading\"><p class=\"eyebrow\">Fil-C on Nix</p><h1><a href=\"../index.html\">Filnix wiki</a></h1></div>\n",
    "  <nav class=\"doors\">\n",
    "    <a class=\"door\" href=\"../docs/\">Docs</a>\n",
    "    <a class=\"door\" href=\"../index.html#explainers\">Explainers</a>\n",
    "    <a class=\"door selected\" href=\"index.html\">Nix</a>\n",
    "    <a class=\"door\" href=\"../nanofil/\">nanofil</a>\n",
    "    <a class=\"door\" href=\"https://nix.swa.sh/\">Campaigns</a>\n",
    "    <a class=\"door\" href=\"https://github.com/mbrock/filnix\">Source</a>\n",
    "  </nav>\n</div></header>\n",
    "<div class=\"status\"><div class=\"page-frame status-frame\">\n",
    el(nav, crumbs, ['aria-label'="Breadcrumb"], Crumbs),
    el(span, "status-right", el(a, none, [href="https://github.com/mbrock/filnix"], "mbrock/filnix")),
    "\n</div></div>\n",
    el(main, "page-frame dterm-page", Main),
    "\n<script src=\"../nanofil/dterm.js\"></script>\n<script src=\"dterm-nix.js\"></script>\n</body>\n</html>\n".


%% The index: every page, by directory

index_page -->
    { nb_getval(nix_pages, Files), dir_groups(Files, Ds),
      findall(g(T, H, []), ( member(D-_, Ds), dir_title(D, T), dir_id(D, Id), atom_concat('#', Id, H) ), Gs0),
      ( nb_getval(nix_options, I), I \== none -> Gs = [g("Evaluated", '#evaluated', [])|Gs0] ; Gs = Gs0 ) },
    shell("Nix", ( el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                   el(span, "crumb current", "Nix") ),
          ( sidebar(index, Gs),
            el(article, "dterm nix index",
               ( el(h1, "source-title", "filnix, read as Nix"),
                 el(div, "prose lede",
                    el(p, none, ( "Every Nix file of filnix, drawn by what it is rather than how it was typed: attribute sets as ",
                                  "tables of bindings, ", el(code, none, "let"), " as bindings over a body, function ",
                                  "arguments as signatures, ", el(code, none, "if"), " and ", el(code, none, "mkIf"),
                                  " as tables of conditions, ports as tables of their steps, options with their descriptions as prose. Each name ",
                                  "links to where it is bound, and each ", el(code, none, "let"), " binding lists what ",
                                  "uses it. Drawn by ", el(a, none, [href="https://github.com/mbrock/filnix/tree/main/dterm-nix"], "dterm-nix"),
                                  ", after ", el(a, none, [href="../nanofil/"], "nanofil's dterm"), "." ))),
                 options_entry,
                 seq(Ds, dir_section) )) )).

options_entry --> { nb_getval(nix_options, I), I \== none }, !,
    el(section, "dir",
       ( el(h2, "nix-sec", [id=evaluated], "Evaluated"),
         el(table, "files", el(tbody, none,
            el(tr, none, ( el(td, "file-name", el(a, none, [href="options.html"], "Options")),
                           el(td, "file-sum", "Every option the exported NixOS and finix modules declare or set: type, default, description, where it is declared and defined, its value and the port that builds it, and which modules read it."),
                           el(td, "file-lines", []) )))) )).
options_entry --> [].

dir_section(D-Fs) -->
    { dir_title(D, T), dir_id(D, Id) },
    el(section, "dir", ( el(h2, "nix-sec", [id=Id], esc(T)),
                         el(table, "files", el(tbody, none, seq(Fs, file_row(D)))) )).

file_row(D, F) -->
    { page_name(F, H), rel_to(D, F, R), ( page_summary(F, S, N) -> true ; S = "", N = 0 ) },
    el(tr, none, ( el(td, "file-name", el(a, none, [href=H], esc(R))),
                   el(td, "file-sum", inline(S)),
                   el(td, "file-lines", ( esc(N), " lines" )) )).
