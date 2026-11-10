:- encoding(utf8).
/*  dterm-c: C source as web pages, drawn the way dterm draws Prolog.

    c_read.pl reads each file with nanofil's own lexer and parser;
    c_draw.pl draws what they read. This file makes the pages: one per
    file, its first comment the lede, a sidebar of the names it defines,
    and an index of the files by directory.

    Usage: swipl dterm_c.pl OUT ROOT [--src=DIR] FILE... draws ROOT/FILE
    as OUT/PAGE.html and OUT/index.html, and copies dterm-c.css and
    dterm-c.js into OUT. FILE is its path in the repository:
    nanofil/tests/c/basic.c is tests-c-basic.html, a header x.h is
    x-h.html. DIR is nanofil's src, whose lexer and parser read the
    files (default ROOT/nanofil/src). The pages expect dterm.css and
    dterm.js one directory up, the wiki's style.css two up and the
    playground at ../play/, as on the Filnix wiki (nanofil/c/).
*/
:- module(dterm_c, []).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(base64)).
:- use_module(library(uri)).
:- use_module(library(aggregate)).
:- use_module(library(filesex)).
:- use_module(c_read).
:- use_module(c_draw).

:- include('../dterm_html').

:- initialization(main, main).

github('https://github.com/mbrock/filnix/blob/main/').

main :-
    current_prolog_flag(argv, [Out, Root|Args0]),
    (   select(A, Args0, Files), atom_concat('--src=', Src, A) -> true
    ;   Files = Args0, directory_file_path(Root, 'nanofil/src', Src)
    ),
    c_read_load(Src),
    make_directory_path(Out),
    module_property(dterm_c, file(Self)), file_directory_name(Self, Here),
    forall(member(F, ['dterm-c.css', 'dterm-c.js']),
           ( directory_file_path(Here, F, From), directory_file_path(Out, F, To), copy_file(From, To) )),
    msort(Files, Sorted),
    nb_setval(c_files, Sorted),
    foldl(draw_or_report(Out, Root), Sorted, [], Summaries0),
    reverse(Summaries0, Summaries),
    directory_file_path(Out, 'index.html', IPath),
    write_page(IPath, index_page(Summaries)),
    length(Summaries, N),
    format(user_error, "dterm-c: ~d pages~n", [N]),
    (   nb_current(c_failed, true) -> halt(1) ; true ).

draw_or_report(Out, Root, File, S0, S) :-
    (   catch(draw_file(Out, Root, File, Sum), E, ( print_message(error, E), fail ))
    ->  S = [Sum|S0]
    ;   format(user_error, "dterm-c: ~w: not drawn~n", [File]), nb_setval(c_failed, true), S = S0
    ).

%  nanofil/tests/c/basic.c is tests-c-basic.html; a header keeps its
%  kind, x.h is x-h.html.
page_name(File0, Page) :-
    ( atom_concat('nanofil/', File, File0) -> true ; File = File0 ),
    file_name_extension(B0, Ext, File),
    ( Ext == c -> B1 = B0 ; atomic_list_concat([B0, '-', Ext], B1) ),
    atomic_list_concat(Parts, '/', B1), atomic_list_concat(Parts, '-', B),
    file_name_extension(B, html, Page).

draw_file(Out, Root, File, sum(File, Page, NL, NFns, Raw, Summary)) :-
    directory_file_path(Root, File, Path),
    c_read_file(Path, Text, Unit0),
    c_unit_lede(Unit0, Lede, Unit),
    page_name(File, Page),
    github(G), atom_concat(G, File, Src),
    file_base_name(File, Base), play_href(Text, Base, Play),
    c_set_page(Unit, page, Src, Play),
    c_unit_names(Unit, Groups),
    Unit = unit(Items, _, _, _, Lines),
    length(Lines, NL),
    ( member(g("Functions", Fs), Groups) -> length(Fs, NFns) ; NFns = 0 ),
    aggregate_all(count, ( member(I, Items), raw_in(I) ), Raw),
    summary(Lede, Summary),
    directory_file_path(Out, Page, OPath),
    write_streamed_page(OPath, source_page(File, Src, Play, Lede, Unit, Groups, NL), true).

raw_in(raw(_, _, _, _)).
raw_in(fun(_, _, _, _, B)) :- sub_term(raw(_, _, _, _), B).

%  The playground compiles the file from the link (play.js reads #src=
%  and &name=, and dterm-c.js adds &ir=).
%  A long file would make a link browsers refuse.
play_href(Text, Base, Href) :-
    string_length(Text, N),
    (   N =< 24000
    ->  base64url(Text, B), uri_encoded(query_value, Base, Q), format(atom(Href), "../play/#src=~w&name=~w", [B, Q])
    ;   Href = none
    ).

%  The first sentence of the lede, for the index.
summary([], "") :- !.
summary(Lede, S) :-
    blocks(Lede, Bs), ( Bs = [p(P)|_] -> true ; P = "" ),
    (   sub_string(P, B, _, _, ". "), B > 20 -> B1 is B + 1, sub_string(P, 0, B1, _, S) ; S = P ).

%% Pages

source_page(File, Src, Play, Lede, Unit, Groups, NL) -->
    { short(File, Title) },
    shell(Title, crumbs(Title),
          ( sidebar(File, Groups),
            el(article, "dterm dterm-c",
               ( el(h1, "source-title", esc(Title)),
                 el(p, "c-meta-bar", ( esc(NL), " lines · ", el(a, none, [href=Src], "source on GitHub"),
                                       ( { Play == none } -> []
                                       ; " · ", el(a, "c-play", [href=Play], "compile it in the playground") ) )),
                 ( { Lede == [] } -> [] ; el(div, "prose lede", c_prose(Lede)) ),
                 el(div, "c-root", c_unit(Unit)) )) )).

short(File, Short) :- ( atom_concat('nanofil/', Short, File) -> true ; Short = File ).

crumbs(Title) -->
    el(a, crumb, [href="../../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="../index.html"], "nanofil"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="index.html"], "C"), el(span, "crumb-sep", "›"),
    el(span, "crumb current", esc(Title)).

sidebar(File, Groups) -->
    el(nav, "toc dterm-nav c-nav", ['aria-label'="Contents"],
       ( ( { Groups == [] } -> []
         ; el(details, "nav-block contents", [open=open], ( el(summary, "toc-title", "Contents"), seq(Groups, nav_group) )) ),
         neighbours(File) )).

nav_group(g(T, Ns)) -->
    el(details, "nav-group", [open=open],
       ( el(summary, none, el(span, "nav-group-title", esc(T))), el(ul, "nav-names", seq(Ns, nav_name)) )).

nav_name(n(N, A, K)) --> { atom_concat('#', A, H) }, el(li, K, el(a, none, [href=H], esc(N))).

%  The files beside this one: its directory's, around it.
neighbours(File) -->
    { nb_getval(c_files, Fs), file_directory_name(File, D),
      include([F]>>file_directory_name(F, D), Fs, Here), nth0(I, Here, File),
      length(Here, N), From is max(0, I - 6), To is min(N - 1, I + 6),
      findall(F, ( between(From, To, J), nth0(J, Here, F) ), Near), short(D, SD) },
    el(details, "nav-block files", [open=open],
       ( el(summary, "toc-title", ( esc(SD), "/" )),
         el(ul, "nav-top", ( el(li, none, el(a, none, [href="index.html"], "All files")),
                             seq(Near, file_nav(File)) )) )).

file_nav(Current, F) -->
    { page_name(F, H), file_base_name(F, B), ( F == Current -> C = current ; C = none ) },
    el(li, C, el(a, none, [href=H], esc(B))).

shell(Title, Crumbs, Main) -->
    "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>", esc(Title), " · C · nanofil · Filnix wiki</title>\n",
    "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n",
    "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"../../style.css\">\n",
    "<link rel=\"stylesheet\" href=\"../dterm.css\">\n",
    "<link rel=\"stylesheet\" href=\"dterm-c.css\">\n",
    "</head>\n<body>\n",
    site_header('../../', nanofil, Crumbs, el(a, none, [href="../guide.html"], "the compiler's guide")),
    el(main, "page-frame dterm-page", Main),
    "\n<script src=\"../dterm.js\"></script>\n<script src=\"dterm-c.js\"></script>\n</body>\n</html>\n".

%% The index

index_page(Sums) -->
    shell("C", ( el(a, crumb, [href="../../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                 el(a, crumb, [href="../index.html"], "nanofil"), el(span, "crumb-sep", "›"),
                 el(span, "crumb current", "C") ),
          el(article, "dterm dterm-c c-index",
             ( el(h1, "source-title", "nanofil's C, read by nanofil"),
               el(div, "prose lede",
                  el(p, none, ( "The C programs nanofil is tested on, drawn from what its own frontend reads: ",
                                el(a, none, [href="../c_lex.html"], "c_lex.pl"), " lexes each file and ",
                                el(a, none, [href="../c_parse.html"], "c_parse.pl"), " parses it, unpreprocessed, so macros stay as written. ",
                                "A body is a column of statements, a struct a table of its fields, and each name links to its definition. ",
                                "Each page can open its file in the playground, which compiles it to IR in the browser. Drawn by ",
                                el(a, none, [href="https://github.com/mbrock/filnix/tree/main/nanofil/web/c"], "dterm-c"), "." ))),
               { findall(D, ( member(sum(F, _, _, _, _, _), Sums), file_directory_name(F, D) ), Ds0), sort(Ds0, Ds) },
               seq(Ds, file_dir(Sums)) ))).

file_dir(Sums, Dir) -->
    { short(Dir, R), github(G), atomic_list_concat(Parts, '/blob/', G), Parts = [Repo, Main],
      atomic_list_concat([Repo, '/tree/', Main, Dir], Src) },
    el(h2, "c-dir-title", el(a, none, [href=Src], ( esc(R), "/" ))),
    el(dl, "c-files", seq(Sums, file_row(Dir))).

file_row(Dir, sum(F, P, NL, NF, Raw, S)) --> { file_directory_name(F, Dir) }, !,
    { file_base_name(F, B) },
    el(dt, none, ( el(a, none, [href=P], esc(B)),
                   el(span, "c-file-meta", ( esc(NL), "\u00A0lines", count_(NF, "function"), raw_(Raw) )) )),
    el(dd, none, inline_text(S)).
file_row(_, _) --> [].

count_(0, _) --> !, [].
count_(1, W) --> !, " · 1\u00A0", esc(W).
count_(N, W) --> " · ", esc(N), "\u00A0", esc(W), "s".

raw_(0) --> !, [].
raw_(N) --> " · ", el(span, "c-refused", ( esc(N), "\u00A0not read" )).

inline_text(S) --> { split_string(S, "`", "", Parts) }, code_parts(Parts, text).

code_parts([], _) --> [].
code_parts([P|Ps], text) --> esc(P), code_parts(Ps, code).
code_parts([P|Ps], code) --> ( { Ps == [] } -> esc(P) ; el(code, none, esc(P)) ), code_parts(Ps, text).
