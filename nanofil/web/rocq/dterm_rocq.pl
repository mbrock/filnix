:- encoding(utf8).
/*  dterm-rocq: Rocq source as web pages, drawn the way dterm draws Prolog.

    rocq_syntax.pl reads each .v file into terms with positions and
    comments; rocq_draw.pl draws them by what they are (inductive types as
    tables of constructors, relations as inference rules, theorems as
    rules over their folded proofs, match as a table). This file makes the
    pages: one per file, its first coqdoc comment the lede, and a sidebar
    of the names it defines, by the sections its (** * Title *) comments
    make, over the files.

    Usage: swipl dterm_rocq.pl OUT ROOT [--prolog=DIR] [--concepts=DIR] FILE.v... draws
    ROOT/FILE.v as OUT/PAGE.html and OUT/index.html, ROOT the repository
    and FILE its path there (nanofil/rocq/Core.v is rocq-Core.html). With --prolog,
    name/N and module.pl in comments link to nanofil's Prolog pages, one
    directory up (../MODULE.html), for the predicates DIR's .pl files
    define. With --concepts=DIR, [[name]] in comments links to a concept
    of DIR (docs/concepts, web/concepts.pl), whose page is one directory
    up, and ![[name]] embeds it. The pages expect dterm.css and dterm.js one directory up and
    dterm-rocq.css and dterm-rocq.js beside them, as on the Filnix wiki
    (nanofil/rocq/).
*/
:- module(dterm_rocq, []).

:- use_module(library(lists)).
:- use_module(library(apply)).
:- use_module(library(readutil)).
:- use_module(library(uri)).
:- use_module(library(http/json)).
:- use_module(library(crypto)).
:- use_module(library(time)).
:- use_module(library(aggregate)).
:- use_module(rocq_syntax).
:- use_module(rocq_draw).
:- use_module('../concepts').

:- include('../dterm_html').

:- initialization(main, main).

main :-
    current_prolog_flag(argv, [Out, Root|Args0]),
    %  --states=FILE, once per capture (the theories', the spikes'): the
    %  files of all of them.
    partition([C]>>atom_concat('--states=', _, C), Args0, StateArgs, Args1),
    (   StateArgs == [] -> nb_setval(rq_capture, none)
    ;   foldl(read_states, StateArgs, _{files:_{}}, States), nb_setval(rq_capture, States)
    ),
    %  --concepts=DIR: [[name]] in comments links to DIR's concepts.
    (   select(K, Args1, Args), atom_concat('--concepts=', CDir, K)
    ->  concepts_load(CDir), nb_setval(rq_concepts, '../')
    ;   Args = Args1
    ),
    (   select(A, Args, Files), atom_concat('--prolog=', Dir, A)
    ->  index_prolog(Dir), nb_setval(rq_prolog, '../')
    ;   Files = Args, nb_setval(rq_prolog, none)
    ),
    maplist(read_or_report(Root), Files, Read),
    (   memberchk(failed, Read) -> format(user_error, "dterm-rocq: a file above does not read~n", []), halt(1)
    ;   true
    ),
    nb_setval(rq_files, Files),
    forall(member(page(F, _, Items, _), Read), ( page_name(F, P), rocq_index_items(P, F, Items) )),
    maplist(write_source_page(Out), Read),
    directory_file_path(Out, 'index.html', IPath),
    write_page(IPath, index_page(Read)).

%% Reading

read_states(Arg, S0, S) :-
    atom_concat('--states=', File, Arg),
    % UTF-8 whatever the locale: a Nix build has none.
    setup_call_cleanup(open(File, read, In, [encoding(utf8)]), json_read_dict(In, D), close(In)),
    S = S0.put(files, S0.files.put(D.files)).

:- dynamic page_notations/2.

read_or_report(Root, File, Page) :-
    directory_file_path(Root, File, Path),
    (   catch(rocq_read_file(Path, Text, rocq(Items, Cms0)), E, ( print_message(error, E), fail ))
    ->  maplist(note_kind(Text), Cms0, Cms),
        rocq_notations(Ns), assertz(page_notations(File, Ns)),
        Page = page(File, Text, Items, Cms),
        forall(( raw_item(Items, raw(F-_, Kw)), \+ shown_as_text(Kw) ),
               ( sub_string(Text, 0, F, _, Pre), split_string(Pre, "\n", "", Ls), length(Ls, L),
                 format(user_error, "~w:~w: dterm-rocq draws this ~w as text~n", [File, L, Kw]) ))
    ;   format(user_error, "dterm-rocq: cannot read ~w~n", [File]), Page = failed
    ).

%  Commands drawn as their text on purpose.
shown_as_text(K) :- memberchk(K, ['Extraction', 'Extract', 'Check', 'Compute', 'Print', 'Eval', 'Search']).

raw_item(Items, I) :- member(I0, Items), ( I0 = raw(_, _), I = I0 ; I0 = block(_, B, _), raw_item(B, I) ).

%  nanofil/rocq/Core.v is rocq-Core.html, in the site's nanofil/rocq/.
page_name(File0, Page) :-
    ( atom_concat('nanofil/', File, File0) -> true ; File = File0 ),
    file_name_extension(B0, _, File), atomic_list_concat(Parts, '/', B0), atomic_list_concat(Parts, '-', Page).

%  The predicates nanofil's Prolog defines, by module: the names of the
%  clause heads that start a line of DIR/*.pl.
index_prolog(Dir) :-
    directory_files(Dir, Es),
    forall(( member(E, Es), file_name_extension(M, pl, E) ),
           ( directory_file_path(Dir, E, P), read_file_to_string(P, S, [encoding(utf8)]),
             split_string(S, "\n", "", Ls),
             forall(( member(L, Ls), head_name(L, N) ),
                    ( rocq_prolog_pred(N, M) -> true ; assertz(rocq_draw:rocq_prolog_pred(N, M)) )) )).

head_name(L, N) :-
    string_codes(L, [C|Cs]), C >= 0'a, C =< 0'z,
    span_csym(Cs, W, [D|_]), memberchk(D, `( :`),
    atom_codes(N, [C|W]).

span_csym([C|Cs0], [C|W], Cs) :- code_type(C, csym), !, span_csym(Cs0, W, Cs).
span_csym(Cs, [], Cs).

%% Pages

write_source_page(Out, page(File, Text, Items, Cms)) :-
    get_time(T0),
    page_name(File, Page), nb_setval(rq_page, Page), nb_setval(rq_file, File),
    % Its own notations and its imports', not those of the file read last.
    page_notations(File, Ns), rocq_set_notations(Ns),
    (   Items = [I|_], first_offset(I, From) -> true ; string_length(Text, From) ),
    partition([cm(O, _, _, _)]>>(O < From), Cms, Head, Body),
    rocq_set_source(Text, Body),
    source_states(File, Text),
    contents(Items, Body, Groups),
    summarize(File, Text, Head),
    file_name_extension(Page, html, Name), directory_file_path(Out, Name, Path),
    setup_call_cleanup(start_stack_watch(Alarm),
      once(write_streamed_page(Path, source_page(File, Head, Items, Groups), sample_render_stack)),
      remove_alarm(Alarm)),
    % Keep the next page independent of this one's disposable fragments.
    statistics(globalused, Before), garbage_collect, statistics(globalused, Live),
    get_time(T1), Elapsed is T1 - T0, MB is Before / 1048576, LiveMB is Live / 1048576,
    nb_getval(rq_stack_peak, Peak), PeakMB is Peak / 1048576,
    current_prolog_flag(stack_limit, Limit), LimitMB is Limit / 1048576,
    utc_stamp(T1, Stamp),
    format(user_error, '~w rocq render: ~w ~2fs, sampled stack max ~1f/~1f MiB, global ~1f MiB -> ~1f MiB after GC~n',
           [Stamp, File, Elapsed, PeakMB, LimitMB, MB, LiveMB]).

% Sample at fragment boundaries and every 50ms during a large term, not
% just after the page returns. This is not an exact high-water mark.
start_stack_watch(Alarm) :-
    nb_setval(rq_stack_peak, 0), nb_setval(rq_stack_warned, false),
    sample_render_stack,
    alarm(0.05, watch_render_stack, Alarm, [install(false), remove(false)]),
    nb_setval(rq_stack_alarm, Alarm), install_alarm(Alarm, 0.05).

watch_render_stack :-
    sample_render_stack,
    nb_getval(rq_stack_alarm, Alarm), uninstall_alarm(Alarm), install_alarm(Alarm, 0.05).

sample_render_stack :-
    statistics(globalused, G), statistics(localused, L), statistics(trailused, T), Used is G + L + T,
    nb_getval(rq_stack_peak, Old), Peak is max(Old, Used), nb_setval(rq_stack_peak, Peak),
    current_prolog_flag(stack_limit, Limit),
    (   Used * 5 >= Limit * 3, nb_getval(rq_stack_warned, false)
    ->  nb_setval(rq_stack_warned, true), nb_getval(rq_file, File),
        get_time(Now), utc_stamp(Now, Stamp), MB is Used / 1048576, LimitMB is Limit / 1048576,
        format(user_error, '~w rocq render WARNING: ~w crossed 60% of stack limit (~1f/~1f MiB sampled)~n',
               [Stamp, File, MB, LimitMB])
    ;   true
    ).

utc_stamp(Time, Stamp) :-
    stamp_date_time(Time, Date, 'UTC'), format_time(atom(Stamp), '%FT%TZ', Date).

% Captures belong to the exact source, never a nearby revision's offsets.
source_states(File, Text) :-
    nb_getval(rq_capture, Capture),
    (   Capture \== none, atom_concat('nanofil/rocq/', Rel, File)
    ->  get_dict(Rel, Capture.files, Entry),
        crypto_data_hash(Text, Hash, [algorithm(sha256), encoding(utf8)]),
        ( atom_string(Hash, Entry.sha256) -> rocq_set_states(Entry.states)
        ; throw(error(stale_proof_capture(File), _)) )
    ;   rocq_set_states(none)
    ).

first_offset(I, F) :- ( I = proved(S, _) ; I = block(S, _, _) ; S = I ), !, arg(1, S, F-_).

source_page(File0, Head, Items, Groups) -->
    { ( atom_concat('nanofil/', File, File0) -> true ; File = File0 ) },
    shell(File, crumbs(File),
          ( sidebar(File0, Groups),
            el(article, "dterm dterm-rocq", ( el(h1, "source-title", esc(File)),
                                              el(div, "prose lede", seq(Head, lede_)),
                                              rocq_layout,
                                              el(div, "rq-root", rocq_items(Items)) )) )).

%  The header: its first coqdoc comment's title is the page's subtitle,
%  its text the lede.
lede_(cm(_, _, Text, _)) -->
    { comment_prose_lines(Text, Lines0),
      ( comment_heading(Text, _, Title), Lines0 = [_|Lines] -> true ; Title = none, Lines = Lines0 ) },
    ( { Title == none } -> [] ; el(p, "rq-subtitle", esc(Title)) ),
    rocq_prose(Lines).

crumbs(Title) -->
    el(a, crumb, [href="../../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="../index.html"], "nanofil"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="index.html"], "Rocq"), el(span, "crumb-sep", "›"),
    el(span, "crumb current", esc(Title)).

%  The first sentence of a file's header, for the index.
:- dynamic page_summary/3.

summarize(File, Text, Head) :-
    split_string(Text, "\n", "", Ls), length(Ls, NL),
    (   Head = [cm(_, _, T, _)|_], comment_prose_lines(T, Lines0),
        ( comment_heading(T, _, _), Lines0 = [_|Lines] -> true ; Lines = Lines0 ),
        blocks(Lines, [p(P)|_])
    ->  ( sub_string(P, B, _, _, ". "), B > 20 -> B1 is B + 1, sub_string(P, 0, B1, _, Sum) ; Sum = P )
    ;   Sum = ""
    ),
    assertz(page_summary(File, Sum, NL)).

%% Contents

%  contents(+Items, +Cms, -Groups): g(Title, Href, Names), the names the
%  file defines under the (** * Title *) comment before them.
contents(Items, Cms, Groups) :-
    rocq_items_names(Items, Ns),
    findall(O-s(T), ( member(cm(O, _, Text, _), Cms), comment_heading(Text, L, T), L =< 3 ), Ss),
    findall(O-N, ( member(N, Ns), N = n(O, _, _, _) ), Ps),
    append(Ss, Ps, Xs0), keysort(Xs0, Xs1), pairs_values(Xs1, Xs),
    groups(Xs, none, Groups).

groups([], _, []).
groups([s(T)|Xs], _, Gs) :- !, groups(Xs, T, Gs).
groups(Xs, T, [g(T, Ns)|Gs]) :- take_names(Xs, Ns, Rest), groups(Rest, T, Gs).

take_names([n(_, N, Q, K)|Xs], [n(N, Q, K)|Ns], Rest) :- !, take_names(Xs, Ns, Rest).
take_names(Xs, [], Xs).

sidebar(Current, Groups) -->
    el(nav, "toc dterm-nav nix-nav rq-nav", ['aria-label'="Contents"],
       ( ( { Groups == [] } -> []
         ; el(details, "nav-block contents", [open=open], ( el(summary, "toc-title", "Contents"), seq(Groups, nav_group) )) ),
         files_nav(Current) )).

nav_group(g(T, Ns)) -->
    { ( T == none -> Title = "top" ; Title = T ) },
    el(details, "nav-group", [open=open],
       ( el(summary, none, el(span, "nav-group-title", esc(Title))), el(ul, "nav-names long", seq(Ns, nav_name)) )).

nav_name(n(N, Q, K)) --> { uri_encoded(fragment, Q, F), atom_concat('#', F, H) },
    el(li, K, el(a, none, [href=H], esc(N))).

files_nav(Current) -->
    { nb_getval(rq_files, Files) },
    el(details, "nav-block files", [open=open],
       ( el(summary, "toc-title", "Files"),
         el(ul, "nav-top", ( el(li, none, el(a, none, [href="index.html"], "Index")),
                             seq(Files, file_nav(Current)) )) )).

file_nav(Current, F) --> { page_name(F, P), file_name_extension(P, html, H), ( F == Current -> C = current ; C = none ),
                           ( atom_concat('nanofil/', R, F) -> true ; R = F ) },
    el(li, C, el(a, none, [href=H], esc(R))).

shell(Title, Crumbs, Main) -->
    "<!doctype html>\n<html lang=\"en\">\n<head>\n<meta charset=\"utf-8\">\n",
    "<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\">\n",
    "<title>", esc(Title), " · Rocq · nanofil · Filnix wiki</title>\n",
    "<link rel=\"preconnect\" href=\"https://fonts.googleapis.com\">\n",
    "<link rel=\"preconnect\" href=\"https://fonts.gstatic.com\" crossorigin>\n",
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
    "<link rel=\"stylesheet\" href=\"../../style.css\">\n",
    "<link rel=\"stylesheet\" href=\"../dterm.css\">\n",
    "<link rel=\"stylesheet\" href=\"dterm-rocq.css\">\n",
    "</head>\n<body>\n",
    site_header('../../', nanofil, Crumbs, el(a, none, [href="../formal.html"], "the formal campaign")),
    el(main, "page-frame dterm-page", Main),
    "\n<script src=\"../dterm.js\"></script>\n<script src=\"dterm-rocq.js\"></script>\n</body>\n</html>\n".

%% The index

index_page(Pages) -->
    shell("Rocq", ( el(a, crumb, [href="../../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                    el(a, crumb, [href="../index.html"], "nanofil"), el(span, "crumb-sep", "›"),
                    el(span, "crumb current", "Rocq") ),
          el(article, "dterm dterm-rocq rq-index",
             ( el(h1, "source-title", "nanofil's formal model, read as Rocq"),
               el(div, "prose lede",
                  el(p, none, ( "The Rocq side of ", el(a, none, [href="../formal.html"], "the formal campaign"),
                                ", drawn by what it is rather than how it was typed: inductive types as tables of their ",
                                "constructors, relations as inference rules, theorems as their statement over a ",
                                "folded proof, ", el(code, none, "match"), " as a table of patterns. Each name links to its ",
                                "definition, and the Prolog a definition transcribes links to its page. Drawn by ",
                                el(a, none, [href="https://github.com/mbrock/filnix/tree/main/nanofil/web/rocq"], "dterm-rocq"),
                                ", after ", el(a, none, [href="../"], "nanofil's dterm"), "." ))),
               { findall(D, ( member(page(F, _, _, _), Pages), file_directory_name(F, D) ), Ds0), sort(Ds0, Ds) },
               seq(Ds, file_dir(Pages)) ))).

%  A directory's files, each its name, its size and its header's first
%  sentence, the sentence drawn as the page draws it.
file_dir(Pages, Dir) -->
    { ( atom_concat('nanofil/', R, Dir) -> true ; R = Dir ),
      atom_concat('https://github.com/mbrock/filnix/tree/main/', Dir, Src) },
    el(h2, "rq-dir", el(a, none, [href=Src], ( esc(R), "/" ))),
    el(dl, "rq-files", seq(Pages, file_row(Dir))).

file_row(Dir, page(F, _, Items, _)) --> { file_directory_name(F, Dir) }, !,
    { page_name(F, P), file_name_extension(P, html, H), ( page_summary(F, S, N) -> true ; S = "", N = 0 ),
      file_base_name(F, Base), rocq_items_names(Items, Ns),
      aggregate_all(count, member(n(_, _, _, lemma), Ns), NL),
      aggregate_all(count, member(n(_, _, _, axiom), Ns), NA),
      nb_setval(rq_file, F), nb_setval(rq_page, P) },
    el(dt, none, ( el(a, none, [href=H], esc(Base)),
                   el(span, "rq-file-meta", ( esc(N), "\u00A0lines", count_(NL, lemma), count_(NA, axiom) )) )),
    el(dd, none, rocq_prose_inline(S)).
file_row(_, _) --> [].

count_(0, _) --> !, [].
count_(1, W) --> !, " · 1\u00A0", esc(W).
count_(N, W) --> " · ", esc(N), "\u00A0", esc(W), "s".
