:- encoding(utf8).
/*  Concept nodes: one page per concept of nanofil, shared by its Prolog,
    its Rocq and its documents (docs/dterm.md, "Concept nodes").

    A concept is a file docs/concepts/ID.md: a `# Title / alias / ...`
    line, then Markdown whose first paragraph is its summary. Any text
    links to it with `[[name]]` or `[[name|shown text]]`, and a line that
    is only `![[name]]` embeds its whole text (dterm_html.pl's
    embed_line/2). A name is the ID or any of
    the title's alternatives, compared without case, with -, _ and space
    the same, and a plural -s or -es is its singular.

    This module reads the concepts and resolves names. Drawing them is
    each renderer's own: dterm.pl for the Prolog pages and documents,
    rocq_draw.pl for the Rocq, each with its own Markdown. The concept
    pages, with what links to each, are dterm_guide.pl's.
*/
:- module(concepts, [concepts_load/1, concept/3, concept_kind/3, concept_resolve/2, concept_title/2,
                     concept_summary/2, concept_plain/2, concept_url/3, concept_link_codes/4,
                     concept_page/2, concepts_loaded/0]).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).

%  concept(Id, Names, Body): the concept docs/concepts/Id.md, its title's
%  alternatives (the first is its title) and the lines of its text.
%  concept_key(Key, Id): a normalized name of Id.
%  concept_kind(Id, Kind, Rest): Id is a general Fil-C concept (Kind
%  'Fil-C'), nanofil's own ('nanofil'), or one of Iris and the program
%  logics before it ('Iris'), from its first line after the title,
%  **Fil-C**, **nanofil** or **Iris**; Rest is the Markdown after it on
%  that line, after a ·: the upstream documentation and source, the
%  nearest Fil-C concept, or the papers.
:- dynamic concept/3, concept_key/2, concept_kind/3.

concepts_loaded :- concept(_, _, _), !.

%  concepts_load(+Dir): read every Dir/*.md as a concept. Two concepts
%  with one name is an error.
concepts_load(Dir) :-
    directory_files(Dir, Es0), msort(Es0, Es),
    forall(( member(E, Es), file_name_extension(Id0, md, E), Id0 \== 'README' ),
           ( atom_string(Id0, IdS), atom_string(Id, IdS),
             directory_file_path(Dir, E, Path), load_concept(Id, Path) )).

load_concept(Id, Path) :-
    read_file_to_string(Path, Text, [encoding(utf8)]),
    split_string(Text, "\n", "", [First|Lines0]),
    (   string_concat("# ", Title, First) -> true
    ;   format(string(M), "~w: a concept starts with a # Title line", [Path]), throw(concept_error(M))
    ),
    split_string(Title, "/", " ", Names0), exclude(==(""), Names0, Names),
    drop_blank(Lines0, Lines1), reverse(Lines1, R0), drop_blank(R0, R1), reverse(R1, Lines2),
    (   Lines2 = [K|Lines3], kind_line(K, Kind, Rest)
    ->  assertz(concept_kind(Id, Kind, Rest)), drop_blank(Lines3, Lines)
    ;   Lines = Lines2
    ),
    assertz(concept(Id, Names, Lines)),
    atom_string(Id, IdS),
    forall(member(N, [IdS|Names]), add_key(N, Id, Path)).

%  kind_line(+Line, -Kind, -Rest): **Fil-C**, **nanofil** or **Iris**,
%  then optionally a · and Rest.
kind_line(L, Kind, Rest) :-
    member(Mark-Kind, ["**Fil-C**"-'Fil-C', "**nanofil**"-nanofil, "**Iris**"-'Iris']),
    string_concat(Mark, R0, L), !,
    split_string(R0, "", " ", [R1]),
    (   R1 == "" -> Rest = ""
    ;   string_concat("·", R2, R1) -> split_string(R2, "", " ", [Rest])
    ).

drop_blank([L|Ls0], Ls) :- split_string(L, "", " \t", [""]), !, drop_blank(Ls0, Ls).
drop_blank(Ls, Ls).

add_key(Name, Id, Path) :-
    key(Name, K),
    (   concept_key(K, Id) -> true
    ;   concept_key(K, Other)
    ->  format(string(M), "~w: the name ~w is also concept ~w's", [Path, Name, Other]), throw(concept_error(M))
    ;   assertz(concept_key(K, Id))
    ).

%  key(+Name, -Key): Name in lower case, with - and _ as spaces and runs
%  of spaces as one.
key(Name, Key) :-
    string_lower(Name, L), string_codes(L, Cs0),
    maplist([C0, C]>>( memberchk(C0, `-_`) -> C = 0'  ; C = C0 ), Cs0, Cs),
    string_codes(S, Cs), split_string(S, " ", " ", Ws0), exclude(==(""), Ws0, Ws),
    atomic_list_concat(Ws, ' ', Key0), atom_string(Key0, Key).

%  concept_resolve(+Name, -Id): Name names concept Id.
concept_resolve(Name, Id) :-
    key(Name, K),
    (   concept_key(K, Id) -> true
    ;   string_concat(K1, "es", K), concept_key(K1, Id) -> true
    ;   string_concat(K1, "s", K), concept_key(K1, Id)
    ).

concept_title(Id, Title) :- concept(Id, [Title|_], _).

%  concept_summary(+Id, -Text): the first paragraph, as one line.
concept_summary(Id, Text) :-
    concept(Id, _, Lines),
    take_para(Lines, Para),
    maplist([S0, S]>>split_string(S0, "", " ", [S]), Para, Ws),
    atomic_list_concat(Ws, ' ', A), atom_string(A, Text).

take_para([L|Ls], [L|Ps]) :- \+ split_string(L, "", " \t", [""]), !, take_para(Ls, Ps).
take_para(_, []).

%  concept_page(+Id, -Page): the page of concept Id, concept-Id.html,
%  beside the module pages.
concept_page(Id, Page) :- format(atom(Page), "concept-~w.html", [Id]).

%  concept_link_codes(+Codes, -Name, -Shown, -Rest): Codes, after a [[,
%  are name]] or name|shown]] on one line. A C23 attribute,
%  [[gnu::packed]] or [[gnu::cleanup(f)]], is not a link.
concept_link_codes(Cs0, Name, Shown, Rest) :-
    append(Inner, [0'], 0']|Rest], Cs0),
    \+ memberchk(0'\n, Inner), \+ memberchk(0'[, Inner), \+ memberchk(0'], Inner), !,
    Inner \== [], \+ memberchk(0':, Inner), \+ memberchk(0'(, Inner),
    (   append(N, [0'||S], Inner) -> true ; N = Inner, S = Inner ),
    string_codes(Name, N), string_codes(Shown, S).

%  concept_plain(+Text, -Plain): Text without its links, for a card:
%  [[a|b]] is b, [[a]] a, [text](url) text, and [name] name.
concept_plain(Text, Plain) :-
    string_codes(Text, Cs0), plain(Cs0, Cs), string_codes(Plain, Cs).

plain([], []).
plain([0'`|Cs0], [0'`|Cs]) :- append(Code, [0'`|Rest], Cs0), !,
    append(Code, [0'`|Cs1], Cs), plain(Rest, Cs1).
plain([0'[, 0'[|Cs0], Cs) :- concept_link_codes(Cs0, _, Shown, Rest), !,
    string_codes(Shown, S), append(S, Cs1, Cs), plain(Rest, Cs1).
plain([0'[|Cs0], Cs) :- append(T, [0'], 0'(|Rest0], Cs0), \+ memberchk(0'], T),
    append(U, [0')|Rest], Rest0), \+ memberchk(0' , U), !,
    append(T, Cs1, Cs), plain(Rest, Cs1).
plain([0'[|Cs0], Cs) :- append(T, [0']|Rest], Cs0), \+ memberchk(0'[, T), \+ memberchk(0'\n, T), !,
    append([0'`|T], [0'`|Cs1], Cs), plain(Rest, Cs1).
plain([C|Cs0], [C|Cs]) :- plain(Cs0, Cs).

%  concept_url(+Url, +Prefix, -Href): a link in a concept, relative to
%  docs/concepts, as the site has it from a page Prefix below nanofil/
%  ('' or '../'): another concept, a document, a Rocq or a Prolog page,
%  or else the file on GitHub.
concept_url(Url, _, Url) :- ( sub_atom(Url, B, _, _, ':'), B > 0 ; sub_atom(Url, 0, _, _, '#') ), !.
concept_url(Url, Pre, Href) :-
    ( sub_atom(Url, B, _, _, '#') -> sub_atom(Url, 0, B, _, Path), sub_atom(Url, B, _, 0, Frag) ; Path = Url, Frag = '' ),
    concept_path(Path, Pre, Href0), atom_concat(Href0, Frag, Href).

concept_path(Path, Pre, Href) :- file_name_extension(Id, md, Path), \+ sub_atom(Id, _, _, _, '/'), !,
    concept_page(Id, P), atom_concat(Pre, P, Href).
concept_path(Path, Pre, Href) :- atom_concat('../', F, Path), file_name_extension(D, md, F), \+ sub_atom(D, _, _, _, '/'), !,
    (   nb_current(guide_docs, Ds), memberchk(D, Ds) -> format(atom(Href), "~w~w.html", [Pre, D])
    ;   format(atom(Href), "~wdocs/~w.html", [Pre, D])
    ).
concept_path(Path, Pre, Href) :- atom_concat('../../rocq/', F, Path), file_name_extension(B, v, F), !,
    atomic_list_concat(Ps, '/', B), atomic_list_concat(['rocq'|Ps], '-', Page),
    format(atom(Href), "~wrocq/~w.html", [Pre, Page]).
concept_path(Path, Pre, Href) :- atom_concat('../../src/', F, Path), file_name_extension(M, pl, F), !,
    format(atom(Href), "~w~w.html", [Pre, M]).
concept_path(Path, _, Href) :-
    atomic_list_concat(Parts0, '/', Path),
    foldl([P, A0, A]>>( P == '..' -> A0 = [_|A] ; A = [P|A0] ), Parts0, [concepts, docs, nanofil], R),
    reverse(R, Parts), atomic_list_concat(Parts, '/', Rel),
    atom_concat('https://github.com/mbrock/filnix/blob/main/', Rel, Href).
