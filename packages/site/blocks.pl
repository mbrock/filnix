/*  blocks.pl: the stream, drawn from the XML files in blocks/.

    swipl packages/site/blocks.pl SITE REPO FILES
    swipl packages/site/blocks.pl --check REPO FILES

    A block is one small authored, identified entry: a finding, a
    milestone, a measurement, a question, a reply or a note, written by
    mbrock or an Amp thread, in one XML file (blocks/README.md has the
    format). This program reads every block, checks that each reference
    resolves at this revision (a file a block is <about>, a concept, a
    block it replies to or cites), and fails the build if one does not.
    It then draws, under SITE/stream/:

    - index.html, every block newest first, and kind-K.html, tag-T.html;
    - B.html, one block with the replies to it;
    - feed.xml (Atom) and outbox.json (an ActivityStreams collection);
    - about.tsv: PAGE, ID and TITLE for each block about a file the site
      draws, which packages/site/chrome.py sets in that page's margin;
    - SITE/docs/C.html for a collection C: the blocks a document became
      (<origin path="docs/C.md" anchor="..."/>), in their old order and
      at their old anchors, after the document's own lede.

    FILES lists the repository's paths, for <about> and links.
*/
:- module(blocks, []).
% The Nix sandbox has no locale: without this, SWI-Prolog reads this
% file's non-ASCII text (the bylines' middle dots) as U+FFFD.
:- encoding(utf8).
:- use_module(library(sgml)).
:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(filesex)).
:- use_module(library(json)).
:- initialization(main, main).

:- dynamic block/1, repo_file/1, concept/1, site_root/1.

%% HTML, as DCGs over codes (after nanofil/web/dterm_html.pl)

write_page(Path, Body) :-
    phrase(Body, Cs),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
                       format(S, "~s", [Cs]), close(S)).

esc(X) --> { text_codes(X, Cs) }, esc_codes(Cs).
text_codes(X, Cs) :- string(X), !, string_codes(X, Cs).
text_codes(X, Cs) :- atom(X), !, atom_codes(X, Cs).
text_codes(X, Cs) :- format(codes(Cs), "~w", [X]).
esc_codes([]) --> [].
esc_codes([C|Cs]) --> esc_code(C), esc_codes(Cs).
esc_code(0'<) --> !, "&lt;".
esc_code(0'>) --> !, "&gt;".
esc_code(0'&) --> !, "&amp;".
esc_code(0'") --> !, "&quot;".
esc_code(C) --> [C].
raw(X) --> { text_codes(X, Cs) }, Cs.

el(Tag, Class, Body) --> el(Tag, Class, [], Body).
el(Tag, Class, Attrs, Body) -->
    "<", raw(Tag),
    ( { Class == none } -> [] ; " class=\"", raw(Class), "\"" ),
    attrs(Attrs), ">", Body, "</", raw(Tag), ">".
attrs([]) --> [].
attrs([K=V|As]) --> " ", raw(K), "=\"", esc(V), "\"", attrs(As).

seq([], _) --> [].
seq([X|Xs], G) --> call(G, X), seq(Xs, G).

cls(Fmt, Args, C) :- format(atom(C), Fmt, Args).

github('https://github.com/mbrock/filnix/blob/main/').
thread_url('https://ampcode.com/threads/').

kind(finding,   "Finding",   "Findings").
kind(milestone, "Milestone", "Milestones").
kind(bench,     "Measurement", "Measurements").
kind(question,  "Question",  "Questions").
kind(reply,     "Reply",     "Replies").
kind(note,      "Note",      "Notes").

main :-
    current_prolog_flag(argv, Argv),
    (   Argv = ['--check', Repo, Files]
    ->  load(Repo, Files, Bs), length(Bs, N),
        format(user_error, "blocks: ~d blocks check~n", [N])
    ;   Argv = [Site, Repo, Files]
    ->  load(Repo, Files, Bs), draw(Site, Bs)
    ;   format(user_error, "usage: blocks.pl SITE REPO FILES | --check REPO FILES~n", []),
        halt(2)
    ).

%% Reading and checking

load(Repo, FilesList, Bs) :-
    read_file_to_string(FilesList, S, []),
    split_string(S, "\n", "", Ls), exclude(==(""), Ls, Paths),
    forall(member(P, Paths), (atom_string(A, P), assertz(repo_file(A)))),
    directory_file_path(Repo, 'nanofil/docs/concepts', CDir),
    (   exists_directory(CDir)
    ->  directory_files(CDir, Fs),
        forall(( member(F, Fs), file_name_extension(C, md, F) ), assertz(concept(C)))
    ;   true ),
    directory_file_path(Repo, blocks, Dir),
    (   exists_directory(Dir)
    ->  findall(F, directory_member(Dir, F, [extensions([xml]), recursive(true)]), Files0)
    ;   Files0 = [] ),
    msort(Files0, Files),
    maplist(read_block(Repo), Files, Bs0),
    forall(member(B, Bs0), assertz(block(B))),
    findall(E, ( member(B, Bs0), problem(B, E) ), Es),
    (   Es == [] -> true
    ;   forall(member(E, Es), format(user_error, "~w~n", [E])),
        length(Es, N), format(user_error, "blocks: ~d problems~n", [N]), halt(1) ),
    predsort(newest_first, Bs0, Bs).

newest_first(O, A, B) :-
    get_dict(created, A, CA), get_dict(created, B, CB),
    compare(O0, CB-B.id, CA-A.id), ( O0 == (=) -> O = (<) ; O = O0 ).

read_block(Repo, File, B) :-
    load_xml(File, DOM, [space(sgml), dialect(xml)]),
    (   DOM = [element(block, As, Cs)] -> true
    ;   include(is_element, DOM, [element(block, As, Cs)]) -> true
    ;   format(user_error, "~w: the root must be one <block>~n", [File]), halt(1) ),
    relative_file_name(File, Repo, Rel0),
    atom_string(Rel, Rel0),
    attr(id, As, Id, ''), attr(kind, As, Kind, ''), attr(actor, As, Actor, ''),
    attr(created, As, Created, ''), attr(model, As, Model, ''),
    attr(thread, As, Thread0, ''), attr('in-reply-to', As, Reply, ''),
    attr(supersedes, As, Supersedes, ''),
    (   Thread0 == '', sub_atom(Actor, 0, _, _, 'T-') -> Thread = Actor ; Thread = Thread0 ),
    partition(meta, Cs, Meta, Body0),
    exclude(blank_text, Body0, Body),
    (   member(element(title, _, T), Meta) -> text_of(T, Title) ; Title = "" ),
    findall(about(P, Sym), ( member(element(about, A2, _), Meta), attr(path, A2, P, ''), attr(symbol, A2, Sym, '') ), Abouts),
    findall(Tg, ( member(element(tag, A3, _), Meta), attr(name, A3, Tg, '') ), Tags),
    findall(origin(OP, OA), ( member(element(origin, A4, _), Meta), attr(path, A4, OP, ''), attr(anchor, A4, OA, '') ), Origins),
    B = block{id:Id, kind:Kind, actor:Actor, created:Created, model:Model, thread:Thread,
              reply:Reply, supersedes:Supersedes, title:Title, abouts:Abouts, tags:Tags,
              origins:Origins, body:Body, file:Rel}.

is_element(element(_, _, _)).
blank_text(T) :- atomic(T), split_string(T, "", " \t\n\r", [""]).
meta(element(T, _, _)) :- memberchk(T, [title, about, tag, origin]).

attr(K, As, V, D) :- ( memberchk(K=V0, As) -> V = V0 ; V = D ).

text_of(Cs, S) :- phrase(texts(Cs), Codes), string_codes(S0, Codes), normalize_space(string(S), S0).
texts([]) --> [].
texts([C|Cs]) --> text(C), texts(Cs).
text(element(_, _, Cs)) --> !, texts(Cs).
text(A) --> { atom_codes(A, Cs) }, Cs.

problem(B, E) :-
    file_base_name(B.file, Base), file_name_extension(Stem, xml, Base),
    (   B.id \== Stem -> format(string(E), "~w: id ~w is not the file's name", [B.file, B.id])
    ;   \+ kind(B.kind, _, _) -> format(string(E), "~w: no kind ~w (finding, milestone, bench, question, reply, note)", [B.file, B.kind])
    ;   \+ iso_time(B.created) -> format(string(E), "~w: created must be an ISO time, such as 2026-11-11T05:48:12Z", [B.file])
    ;   B.title == "" -> format(string(E), "~w: no <title>", [B.file])
    ;   B.actor == '' -> format(string(E), "~w: no actor (mbrock or the thread's T-... id)", [B.file])
    ).
problem(B, E) :-
    member(about(P, _), B.abouts), \+ repo_file(P), \+ repo_dir(P),
    format(string(E), "~w: <about path=\"~w\"> is not a file of the repository", [B.file, P]).
problem(B, E) :-
    member(R, [B.reply, B.supersedes]), R \== '', \+ block_id(R),
    format(string(E), "~w: no block ~w", [B.file, R]).
problem(B, E) :-
    refs(B.body, Rs), member(R, Rs), bad_ref(R, Why),
    format(string(E), "~w: ~w", [B.file, Why]).
problem(B, E) :-
    findall(F2, ( block(B2), B2.id == B.id, get_dict(file, B2, F2) ), [_, _|_]),
    format(string(E), "~w: another block has the id ~w", [B.file, B.id]).

block_id(Id) :- block(B), B.id == Id, !.
repo_dir(P) :- atom_concat(P, '/', Prefix), repo_file(F), sub_atom(F, 0, _, _, Prefix), !.
iso_time(T) :- atom(T), catch(parse_time(T, iso_8601, _), _, fail).

refs(Cs, Rs) :- phrase(refs_(Cs), Rs).
refs_([]) --> [].
refs_([element(T, As, Cs)|Es]) --> !, ref(T, As), refs_(Cs), refs_(Es).
refs_([_|Es]) --> refs_(Es).
ref(concept, As) --> !, { attr(ref, As, R, '') }, [concept(R)].
ref(ref, As) --> !, { attr(block, As, R, '') }, [block(R)].
ref(_, As) --> { memberchk(path=P, As) }, !, [path(P)].
ref(T, _) --> { body_tag(T) }, !.
ref(T, _) --> [tag(T)].

bad_ref(concept(C), Why) :- \+ concept(C), format(string(Why), "no concept ~w in nanofil/docs/concepts", [C]).
bad_ref(block(R), Why) :- \+ block_id(R), format(string(Why), "<ref block=\"~w\"/>: no such block", [R]).
bad_ref(path(P), Why) :- \+ repo_file(P), \+ repo_dir(P), format(string(Why), "path ~w is not a file of the repository", [P]).
bad_ref(tag(T), Why) :- format(string(Why), "<~w> is not a block element (blocks/README.md lists them)", [T]).

% Elements a body may hold beside the semantic ones drawn below.
body_tag(T) :- memberchk(T, [p, ul, ol, li, em, strong, b, i, blockquote, pre, code, br,
                             table, thead, tbody, tr, th, td, h3, h4, sup, sub, a, del,
                             c, ir, prolog, rocq, nix, sh, claim, metrics, metric, figure, figcaption]).

%% Drawing

draw(Site, Bs) :-
    retractall(site_root(_)), assertz(site_root(Site)),
    directory_file_path(Site, stream, Out), make_directory_path(Out),
    page(Out, 'index.html', "Stream", all, Bs),
    forall(( kind(K, _, Plural), include(of_kind(K), Bs, KBs), KBs \== [] ),
           ( atom_concat('kind-', K, P0), atom_concat(P0, '.html', P),
             page(Out, P, Plural, kind(K), KBs) )),
    findall(T, ( member(B, Bs), member(T, B.tags) ), Ts0), sort(Ts0, Ts),
    forall(member(T, Ts),
           ( include(tagged(T), Bs, TBs), atom_concat('tag-', T, P0), atom_concat(P0, '.html', P),
             format(string(Title), "#~w", [T]), page(Out, P, Title, tag(T), TBs) )),
    forall(member(B, Bs), one(Out, B)),
    feed(Out, Bs), outbox(Out, Bs), about_tsv(Site, Out, Bs), latest(Out, Bs),
    collections(Site, Bs),
    length(Bs, N), format(user_error, "blocks: drew ~d blocks~n", [N]).

of_kind(K, B) :- B.kind == K.
tagged(T, B) :- memberchk(T, B.tags).

head(Title, Root) -->
    "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>", esc(Title), " · Filnix</title>\n",
    "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n",
    "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=DM+Mono:ital,wght@0,300;0,400;0,500;1,400&amp;family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"", raw(Root), "style.css\">\n",
    "<link rel=\"alternate\" type=\"application/atom+xml\" title=\"Filnix stream\" href=\"", raw(Root), "stream/feed.xml\">\n",
    "</head>\n<body>\n",
    "<header class=\"library\"><!-- the site's band: packages/site/chrome.py --></header>\n".

status(Crumbs, Right) -->
    "<div class=\"status\"><div class=\"page-frame status-frame\">\n  ",
    el(nav, crumbs, ['aria-label'="Breadcrumb"], Crumbs), "\n  ",
    el(span, "status-right", Right), "\n</div></div>\n".

crumb(Href, Label) --> el(a, crumb, [href=Href], esc(Label)), el(span, "crumb-sep", "›").
here(Label) --> el(span, "crumb current", esc(Label)).

page(Out, File, Title, Which, Bs) :-
    directory_file_path(Out, File, Path),
    length(Bs, N),
    write_page(Path, (
        head(Title, '../'),
        status(( { Which == all } -> here("Stream") ; crumb('index.html', "Stream"), here(Title) ),
               el(a, none, [href='feed.xml'], "Atom feed")),
        "<main class=\"page-frame reading wide stream\">\n",
        el(h1, none, esc(Title)),
        intro(Which, N),
        filters(Which),
        el(ol, "stream-list", seq(Bs, card('../', ''))),
        "</main>\n</body>\n</html>\n" )).

intro(all, N) --> !,
    el(p, none, ( "The stream is a list of short dated entries, newest first. mbrock and the Amp threads ",
                  "working in this repository write them to record findings, milestones, measurements and questions. ",
                  "Each entry names its author and the files it is about, and those files' pages link back to it. ",
                  "There are ", esc(N), " so far; ",
                  el(a, none, [href='https://github.com/mbrock/filnix/blob/main/blocks/README.md'], "blocks/README.md"),
                  " explains how to write one." )).
intro(_, N) --> el(p, small, ( esc(N), " ", ( { N =:= 1 } -> "entry" ; "entries" ), ", newest first." )).

filters(Which) -->
    { findall(K-L, ( kind(K, _, L), block(B), B.kind == K ), KLs0), sort(KLs0, KLs) },
    "<nav class=\"stream-filters\" aria-label=\"Kinds\">",
    filter(Which == all, 'index.html', "All"),
    seq(KLs, kind_filter(Which)),
    "</nav>\n".
kind_filter(Which, K-L) --> { atom_concat('kind-', K, P0), atom_concat(P0, '.html', P) }, filter(Which == kind(K), P, L).
filter(Sel, Href, Label) --> { ( call(Sel) -> C = "on" ; C = none ) }, el(a, C, [href=Href], esc(Label)).

% A block in a list: its header, its body, what it is about.
card(Root, Self, B) -->
    { kind(B.kind, Label, _), atomic_list_concat([Root, 'stream/', B.id, '.html'], Href),
      cls("block kind-~w", [B.kind], C) },
    el(li, C, [id=B.id], (
        "<div class=\"block-head\">",
        el(span, "block-kind", esc(Label)),
        ( { Self == self } -> el(h1, "block-title", esc(B.title))
        ; el(a, "block-title", [href=Href], esc(B.title)) ),
        "</div>\n",
        byline(Root, B),
        el(div, "block-body", body(Root, B.body)),
        footline(Root, B) )).

byline(Root, B) -->
    { day(B.created, Day) },
    "<p class=\"block-by\">", actor(Root, B), " · ", el(time, none, [datetime=B.created], esc(Day)),
    ( { B.model \== '' } -> " · ", esc(B.model) ; [] ),
    ( { B.reply \== '', block_title(B.reply, RT), block_href(Root, B.reply, RHref) }
    -> " · in reply to ", el(a, none, [href=RHref], esc(RT)) ; [] ),
    ( { B.supersedes \== '', block_title(B.supersedes, ST), block_href(Root, B.supersedes, SHref) }
    -> " · supersedes ", el(a, none, [href=SHref], esc(ST)) ; [] ),
    "</p>\n".

actor(_, B) -->
    { B.thread \== '', thread_url(U), atom_concat(U, B.thread, Href), sub_atom(B.thread, 0, 10, _, Short) },
    !,
    ( { B.actor == B.thread } -> "Amp" ; esc(B.actor) ),
    " in ", el(a, none, [href=Href, title=B.thread], ( "thread ", esc(Short) )).
actor(_, B) --> esc(B.actor).

footline(Root, B) -->
    { B.abouts \== [] ; B.tags \== [] }, !,
    "<p class=\"block-about\">",
    ( { B.abouts \== [] } -> "About ", seq_sep(B.abouts, about_link(Root)) ; [] ),
    ( { B.abouts \== [], B.tags \== [] } -> " · " ; [] ),
    seq_sep(B.tags, tag_link(Root)),
    "</p>\n".
footline(_, _) --> [].

about_link(Root, about(P, Sym)) -->
    { path_href(Root, P, '', Href) },
    el(a, "path", [href=Href], ( esc(P), ( { Sym \== '' } -> ": ", esc(Sym) ; [] ) )).
tag_link(Root, T) --> { atomic_list_concat([Root, 'stream/tag-', T, '.html'], Href) }, el(a, tag, [href=Href], ( "#", esc(T) )).

seq_sep([], _) --> [].
seq_sep([X], G) --> !, call(G, X).
seq_sep([X|Xs], G) --> call(G, X), ", ", seq_sep(Xs, G).

block_title(Id, T) :- block(B), B.id == Id, !, T = B.title.
block_href(Root, Id, Href) :- atomic_list_concat([Root, 'stream/', Id, '.html'], Href).

day(Iso, Day) :-
    parse_time(Iso, iso_8601, Stamp),
    stamp_date_time(Stamp, date(Y, M, D, _, _, _, _, _, _), 'UTC'),
    nth1(M, ["Jan","Feb","Mar","Apr","May","Jun","Jul","Aug","Sep","Oct","Nov","Dec"], Mon),
    format(string(Day), "~d ~w ~d", [D, Mon, Y]).

one(Out, B) :-
    atom_concat(B.id, '.html', File), directory_file_path(Out, File, Path),
    findall(R, ( block(R), R.reply == B.id ), Rs0), predsort(oldest_first, Rs0, Rs),
    write_page(Path, (
        head(B.title, '../'),
        status(( crumb('index.html', "Stream"), here(B.title) ),
               el(a, none, [href=Src], esc(B.file))),
        "<main class=\"page-frame reading stream one\">\n",
        el(ol, "stream-list", card('../', self, B)),
        ( { Rs == [] } -> [] ; el(h2, none, "Replies"), el(ol, "stream-list replies", seq(Rs, card('../', ''))) ),
        "</main>\n</body>\n</html>\n" )),
    github(G), atom_concat(G, B.file, Src).

oldest_first(O, A, B) :- newest_first(O0, A, B), ( O0 == (<) -> O = (>) ; O = (<) ).

%% The body

body(Root, Cs) --> seq(Cs, node(Root)).

node(_, A) --> { atomic(A) }, !, esc(A).
node(Root, element(T, As, Cs)) --> draw_el(T, As, Cs, Root).

draw_el(c, _, Cs, R) --> !, el(code, "lang-c", body(R, Cs)).
draw_el(ir, _, Cs, R) --> !, el(code, "lang-ir", body(R, Cs)).
draw_el(prolog, _, Cs, R) --> !, el(code, "lang-prolog", body(R, Cs)).
draw_el(sh, _, Cs, R) --> !, el(code, "lang-sh", body(R, Cs)).
draw_el(rocq, As, Cs, R) --> !, maybe_link(R, As, el(code, "lang-rocq", body(R, Cs))).
draw_el(nix, As, Cs, R) --> !, maybe_link(R, As, el(code, "lang-nix", ( { Cs == [] } -> path_text(As) ; body(R, Cs) ))).
draw_el(concept, As, Cs, R) --> !,
    { attr(ref, As, C, ''), atomic_list_concat([R, 'nanofil/concept-', C, '.html'], Href) },
    el(a, concept, [href=Href], ( { Cs == [] } -> esc(C) ; body(R, Cs) )).
draw_el(ref, As, Cs, R) --> !,
    { attr(block, As, Id, ''), block_href(R, Id, Href), block_title(Id, T) },
    el(a, "block-ref", [href=Href], ( { Cs == [] } -> esc(T) ; body(R, Cs) )).
draw_el(a, As, Cs, R) --> !,
    (   { attr(path, As, P, ''), P \== '' }
    ->  { attr(anchor, As, F, ''), path_href(R, P, F, Href) }, el(a, none, [href=Href], ( { Cs == [] } -> esc(P) ; body(R, Cs) ))
    ;   { attr(href, As, H, '#') }, el(a, none, [href=H], body(R, Cs)) ).
draw_el(claim, As, Cs, R) --> !,
    { attr(status, As, S, stated), attr(check, As, Chk, ''), cls("claim claim-~w", [S], C) },
    el(div, C, (
        el(span, "claim-status", esc(S)),
        body(R, Cs),
        ( { Chk \== '' } -> el(p, "claim-check", ( "Checked by ", el(code, none, esc(Chk)) )) ; [] ) )).
draw_el(metrics, As, Cs, R) --> !,
    { attr(baseline, As, Base, ''), include(is_metric, Cs, Ms) },
    el(table, metrics, (
        ( { Base \== '' } -> el(caption, none, ( "Against ", esc(Base) )) ; [] ),
        seq(Ms, metric(R)) )).
draw_el(pre, As, Cs, R) --> !, { attr(lang, As, L, '') },
    ( { L == '' } -> el(pre, none, body(R, Cs)) ; { cls("lang-~w", [L], C) }, el(pre, C, body(R, Cs)) ).
draw_el(T, _, [], _) --> { memberchk(T, [br]) }, !, "<br>".
draw_el(T, _, Cs, R) --> el(T, none, body(R, Cs)).

is_metric(element(metric, _, _)).
metric(_, element(metric, As, _)) -->
    { attr(label, As, L, ''), attr(value, As, V, ''), attr(unit, As, U, ''), attr(delta, As, D, '') },
    el(tr, none, ( el(th, none, esc(L)), el(td, num, esc(V)), el(td, none, esc(U)),
                   el(td, delta, esc(D)) )).

maybe_link(R, As, Inner) -->
    ( { attr(path, As, P, ''), P \== '' } -> { path_href(R, P, '', Href) }, el(a, none, [href=Href], Inner) ; Inner ).
path_text(As) --> { attr(path, As, P, ''), attr(attr, As, A, '') }, esc(P), ( { A \== '' } -> ": ", esc(A) ; [] ).

%  path_href(Root, Path, Anchor, Href): the site's page for a file of the
%  repository, as packages/site/pages.lua finds it, or else GitHub.
path_href(Root, P, F, Href) :-
    (   page_of(P, Page), site_has(Page) -> atom_concat(Root, Page, H0)
    ;   github(G), atom_concat(G, P, H0) ),
    ( F == '' -> Href = H0 ; atomic_list_concat([H0, '#', F], Href) ).

site_has(Page) :- ( site_root(S) -> directory_file_path(S, Page, Path), exists_file(Path) ; true ).

page_of(P, Page) :- atom_concat('nanofil/src/', F, P), file_name_extension(M, pl, F), \+ sub_atom(M, _, _, _, '/'), !,
    atomic_list_concat(['nanofil/', M, '.html'], Page).
page_of(P, Page) :- file_name_extension(B, v, P), atom_concat('nanofil/', R, B), !,
    atomic_list_concat(Parts, '/', R), atomic_list_concat(Parts, '-', D),
    atomic_list_concat(['nanofil/rocq/rocq-', D, '.html'], Page).
page_of(P, Page) :- file_name_extension(B, nix, P), !,
    atomic_list_concat(Parts, '/', B), atomic_list_concat(Parts, '-', D),
    atomic_list_concat(['nix/', D, '.html'], Page).
page_of(P, Page) :- atom_concat('docs/archive/', F, P), file_name_extension(N, md, F), !, atomic_list_concat(['docs/', N, '.html'], Page).
page_of(P, Page) :- atom_concat('docs/', F, P), file_name_extension(N, md, F), \+ sub_atom(N, _, _, _, '/'), !,
    ( N == 'README' -> Page = 'docs/index.html' ; atomic_list_concat(['docs/', N, '.html'], Page) ).
page_of(P, Page) :- atom_concat('nanofil/docs/archive/', F, P), file_name_extension(N, md, F), !, atomic_list_concat(['nanofil/docs/', N, '.html'], Page).
page_of(P, Page) :- atom_concat('nanofil/docs/', F, P), file_name_extension(N, md, F), \+ sub_atom(N, _, _, _, '/'), !,
    atomic_list_concat(['nanofil/docs/', N, '.html'], Page).
page_of(P, Page) :- atom_concat('pages/', R, P), atom_concat(Dir, '/index.html', R), !, atom_concat(Dir, '/', Page0), atom_concat(Page0, 'index.html', Page).

% The newest blocks, for the home page (chrome.py sets this file into
% its <div data-stream="latest">, and deletes it).
latest(Out, Bs) :-
    directory_file_path(Out, 'latest.html', Path),
    length(Bs, N), ( N > 6 -> length(Top, 6), append(Top, _, Bs) ; Top = Bs ),
    write_page(Path, el(ol, "stream-list compact", seq(Top, brief))).

brief(B) -->
    { kind(B.kind, Label, _), atomic_list_concat(['stream/', B.id, '.html'], Href), day(B.created, Day),
      cls("block kind-~w", [B.kind], C) },
    el(li, C, (
        "<div class=\"block-head\">", el(span, "block-kind", esc(Label)),
        el(a, "block-title", [href=Href], esc(B.title)), "</div>\n",
        "<p class=\"block-by\">", actor('', B), " · ", esc(Day), "</p>" )).

%% Feeds

feed(Out, Bs) :-
    directory_file_path(Out, 'feed.xml', Path),
    ( Bs = [B0|_] -> Updated = B0.created ; Updated = '1970-01-01T00:00:00Z' ),
    length(Bs, N), ( N > 50 -> length(Top, 50), append(Top, _, Bs) ; Top = Bs ),
    write_page(Path, (
        "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<feed xmlns=\"http://www.w3.org/2005/Atom\">\n",
        "<title>Filnix stream</title>\n<id>https://filnix.org/stream/</id>\n",
        "<link href=\"https://filnix.org/stream/\"/>\n<link rel=\"self\" href=\"https://filnix.org/stream/feed.xml\"/>\n",
        "<updated>", esc(Updated), "</updated>\n",
        seq(Top, entry), "</feed>\n" )).

entry(B) -->
    { atomic_list_concat(['https://filnix.org/stream/', B.id, '.html'], U), phrase(body('https://filnix.org/', B.body), Cs), string_codes(H, Cs) },
    "<entry>\n<title>", esc(B.title), "</title>\n<id>", esc(U), "</id>\n<link href=\"", esc(U), "\"/>\n",
    "<updated>", esc(B.created), "</updated>\n<author><name>", esc(B.actor), "</name></author>\n",
    "<category term=\"", esc(B.kind), "\"/>\n",
    "<content type=\"html\">", esc(H), "</content>\n</entry>\n".

outbox(Out, Bs) :-
    directory_file_path(Out, 'outbox.json', Path),
    maplist(activity, Bs, Items), length(Items, N),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
        json_write_dict(S, _{'@context':"https://www.w3.org/ns/activitystreams",
                             id:"https://filnix.org/stream/outbox.json",
                             type:"OrderedCollection", totalItems:N, orderedItems:Items}, [width(0)]),
        close(S)).

activity(B, A) :-
    atomic_list_concat(['https://filnix.org/stream/', B.id, '.html'], U),
    phrase(body('https://filnix.org/', B.body), Cs), string_codes(H, Cs),
    Note0 = _{type:"Note", id:U, url:U, name:B.title, published:B.created, attributedTo:B.actor,
              content:H, tag:Tags},
    findall(_{type:"Hashtag", name:T2}, ( member(T, [B.kind|B.tags]), atom_concat('#', T, T2) ), Tags),
    (   B.reply \== '' -> atomic_list_concat(['https://filnix.org/stream/', B.reply, '.html'], R), Note = Note0.put(inReplyTo, R)
    ;   Note = Note0 ),
    A = _{type:"Create", actor:B.actor, published:B.created, object:Note}.

%% Margins and collections

about_tsv(_, Out, Bs) :-
    directory_file_path(Out, 'about.tsv', Path),
    setup_call_cleanup(open(Path, write, S, [encoding(utf8)]),
        forall(( member(B, Bs), member(about(P, _), B.abouts), page_of(P, Page), site_has(Page) ),
               format(S, "~w\t~w\t~w\t~w\t~w~n", [Page, B.id, B.kind, B.created, B.title])),
        close(S)).

% A document that became blocks keeps its page and its anchors: the
% blocks are drawn into it, oldest first by their origin's order.
collections(Site, Bs) :-
    findall(P, ( member(B, Bs), member(origin(P, _), B.origins) ), Ps0), sort(Ps0, Ps),
    forall(member(P, Ps), collection(Site, P, Bs)).

collection(Site, P, Bs) :-
    page_of(P, Page), directory_file_path(Site, Page, Path),
    findall(B, ( member(B, Bs), memberchk(origin(P, _), B.origins) ), Cs0),
    sort(created, @=<, Cs0, Cs),
    phrase(( "<section class=\"collection\">\n",
             seq(Cs, collected(P)), "</section>\n" ), Codes),
    string_codes(Html, Codes),
    read_file_to_string(Path, Text, []),
    (   sub_string(Text, Before, _, After, "<!-- collection -->")
    ->  sub_string(Text, 0, Before, _, A), sub_string(Text, _, After, 0, Z),
        atomics_to_string([A, Html, Z], New),
        setup_call_cleanup(open(Path, write, S, [encoding(utf8)]), write(S, New), close(S))
    ;   format(user_error, "~w has no <!-- collection --> for its blocks~n", [P]), halt(1) ).

collected(P, B) -->
    { memberchk(origin(P, Anchor), B.origins), cls("block collected kind-~w", [B.kind], C),
      block_href('../', B.id, Href) },
    el(article, C, [id=Anchor], (
        el(h2, none, ( esc(B.title), " ", el(a, "block-link", [href=Href, title="This finding in the stream"], "¶") )),
        byline('../', B),
        el(div, "block-body", body('../', B.body)),
        footline('../', B) )).
