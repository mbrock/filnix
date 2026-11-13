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
:- use_module(library(unix)).
:- use_module(library(filesex)).
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
    ->  index_prolog(Dir), nb_setval(rq_prolog, '../'),
        % C in comments is drawn from nanofil's parse (c/c_draw.pl).
        nb_setval(c_src_dir, Dir), nb_setval(c_play_root, '../play/')
    ;   Files = Args, nb_setval(rq_prolog, none)
    ),
    maplist(read_or_report(Root), Files, Read),
    (   memberchk(failed, Read) -> format(user_error, "dterm-rocq: a file above does not read~n", []), halt(1)
    ;   true
    ),
    nb_setval(rq_files, Files),
    forall(member(page(F, _, Items, _), Read), ( page_name(F, P), rocq_index_items(P, F, Items) )),
    forall(member(page(F, Text, Items, Cms), Read), ( page_head(Items, Text, Cms, Head, _), summarize(F, Text, Head) )),
    write_source_pages(Out, Read),
    % The index draws only prose, outside any page's source.
    rocq_set_source("", []),
    directory_file_path(Out, 'index.html', IPath),
    write_page(IPath, index_page(Read)).

%  Once every file is read and indexed, the pages are independent: forked
%  workers, one per core up to 8, draw them. Each claims the next page,
%  longest source first, by making its claim directory, which only one
%  worker can do.
write_source_pages(Out, Read) :-
    (   getenv('NIX_BUILD_CORES', C0), atom_number(C0, C), C > 0 -> true
    ;   current_prolog_flag(cpu_count, C)
    ),
    length(Read, NPages), N is min(8, min(C, NPages)),
    (   N =< 1
    ->  nb_setval(rq_failed, false),
        forall(member(Page, Read), draw_or_report(Out, Page)),
        nb_getval(rq_failed, false)
    ;   map_list_to_pairs([page(_, Text, _, _), L]>>string_length(Text, L), Read, Sized),
        keysort(Sized, Ascending), reverse(Ascending, Longest), pairs_values(Longest, Pages),
        directory_file_path(Out, '.claims', Claims), make_directory(Claims),
        flush_output(user_output), flush_output(user_error),
        numlist(1, N, Ws), maplist(page_worker(Out, Claims, Pages), Ws, Pids),
        maplist([Pid, S]>>wait(Pid, S), Pids, Statuses),
        delete_directory_and_contents(Claims),
        (   forall(member(S, Statuses), S == exited(0)) -> true
        ;   format(user_error, "dterm-rocq: the pages named above were not drawn~n", []), halt(1)
        )
    ).

page_worker(Out, Claims, Pages, _, Pid) :-
    fork(Pid0),
    (   Pid0 == child
    ->  set_stream(user_error, buffer(line)), nb_setval(rq_failed, false),
        forall(( member(Page, Pages), claim(Claims, Page) ), draw_or_report(Out, Page)),
        (   nb_getval(rq_failed, false) -> halt(0) ; halt(1) )
    ;   Pid = Pid0
    ).

%  Draw one page; if it fails, throws or loops, name it and its error,
%  mark the run failed, and go on to the next page. The longest page
%  takes seconds, so two minutes is a drawing that never ends.
draw_or_report(Out, Page) :-
    Page = page(File, _, _, _),
    (   catch(call_with_time_limit(120, write_source_page(Out, Page)), E, true)
    ->  (   var(E) -> true
        ;   print_message(error, E),
            format(user_error, "dterm-rocq: ~w: not drawn, it raised the error above~n", [File]),
            nb_setval(rq_failed, true)
        )
    ;   format(user_error, "dterm-rocq: ~w: not drawn, drawing it failed~n", [File]),
        nb_setval(rq_failed, true)
    ).

claim(Claims, page(File, _, _, _)) :-
    page_name(File, P), directory_file_path(Claims, P, Dir),
    catch(make_directory(Dir), error(existence_error(_, _), _), fail).

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
    page_head(Items, Text, Cms, Head, Body),
    rocq_set_source(Text, Body),
    source_states(File, Text),
    contents(Items, Body, Groups),
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
% A file of a directory no capture replayed (rocq/backend) is drawn
% without states; one missing from a captured directory is an error.
source_states(File, Text) :-
    nb_getval(rq_capture, Capture),
    (   Capture \== none, atom_concat('nanofil/rocq/', Rel, File), get_dict(Rel, Capture.files, Entry)
    ->  crypto_data_hash(Text, Hash, [algorithm(sha256), encoding(utf8)]),
        ( atom_string(Hash, Entry.sha256) -> rocq_set_states(Entry.states)
        ; throw(error(stale_proof_capture(File), _)) )
    ;   Capture \== none, atom_concat('nanofil/rocq/', Rel, File), file_directory_name(Rel, Dir),
        get_dict(Other, Capture.files, _), file_directory_name(Other, Dir)
    ->  throw(error(missing_proof_capture(File), _))
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
      header_title(Text, Lines0, Title, Lines) },
    ( { Title == none } -> [] ; el(p, "rq-subtitle", esc(Title)) ),
    rocq_prose(Lines).

header_title(Text, [_|Lines], Title, Lines) :- comment_heading(Text, _, Title), !.
header_title(_, [First|Lines], Title, Lines) :- string_concat("# ", Title0, First), !, split_string(Title0, "", " ", [Title]).
header_title(_, Lines, none, Lines).

crumbs(Title) -->
    el(a, crumb, [href="../../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="../index.html"], "nanofil"), el(span, "crumb-sep", "›"),
    el(a, crumb, [href="index.html"], "Rocq"), el(span, "crumb-sep", "›"),
    el(span, "crumb current", esc(Title)).

%  The comments before a file's first item are its header.
page_head(Items, Text, Cms, Head, Body) :-
    (   Items = [I|_], first_offset(I, From) -> true ; string_length(Text, From) ),
    partition([cm(O, _, _, _)]>>(O < From), Cms, Head, Body).

%  The index blurb of a file, or the first sentence of its header when
%  a new file has no explicit blurb yet.
:- dynamic page_summary/3.

summarize(File, Text, Head) :-
    split_string(Text, "\n", "", Ls), length(Ls, NL),
    (   file_blurb(File, Sum) -> true
    ;   Head = [cm(_, _, T, _)|_], comment_prose_lines(T, Lines0),
        header_title(T, Lines0, _, Lines),
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
    "<link rel=\"stylesheet\" href=\"https://fonts.googleapis.com/css2?family=DM+Mono:ital,wght@0,300;0,400;0,500;1,400&amp;family=Public+Sans:ital,wght@0,100..900;1,100..900&amp;display=swap\">\n",
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
             ( el(h1, "source-title", "nanofil's Rocq model and proofs"),
               el(div, "prose lede",
                  ( el(p, none,
                       ( "This directory contains the Rocq formalization and proofs for ",
                         el(a, none, [href="../index.html"], "nanofil"), " (",
                         el(a, none, [href="../formal.html"], "the formal campaign"),
                         "). It defines an executable small-step semantics and validator for nanofil's checked capability IR (",
                         el(code, none, "rocq/theories/core/"),
                         "), proves that a module the validator accepts never makes an unchecked memory access under the Fil-C runtime axioms (",
                         el(a, none, [href="rocq-theories-soundness-Soundness.html"], "Soundness.v"),
                         "), and builds an Iris separation logic for proving that compiled C programs never panic (",
                         el(code, none, "rocq/theories/logic/"),
                         "). It also includes a Gallina x86-64 compiler backend and NFB bytecode round-trip proofs (",
                         el(code, none, "rocq/backend/"), ") and a λANF-to-IR lowering pass (",
                         el(code, none, "anf/lower/"), ")." )),
                    el(p, none,
                       ( "The active whole-program campaign (", el(code, none, "rocq/glibc/"), ", ",
                         el(a, none, [href="../docs/glibc-ir.html"], "glibc-ir.md"),
                         ") links C programs against userland glibc compiled to nanofil IR and pushes trusted contracts down to libpizlo's ",
                         el(code, none, "zsys_*"), " syscall and runtime boundary (",
                         el(a, none, [href="../docs/zsys.html"], "zsys.md"),
                         "). Earlier whole-program work proved GNU Hello against per-function libc contracts (",
                         el(code, none, "rocq/theories/hello_contracts/"),
                         ", kept as a compiled reference proof) and proved ",
                         el(code, none, "listsum.c"), " through the program logic as a worked example (", el(code, none, "rocq/spikes/"),
                         "). Generated IR fixture files (", el(code, none, "*Code.v"), ", written by ",
                         el(code, none, "rocq/scripts/gallina.pl"), ") are omitted from this index." )),
                    el(h2, "prose-h", "Start here"),
                    el(ul, none,
                       ( el(li, none,
                            ( el(strong, none, "Live GNU Hello over userland glibc ("), el(code, none, "rocq/glibc/"), el(strong, none, "): "),
                              "Start with ", el(a, none, [href="rocq-glibc-zsys-OsWorld.html"], "OsWorld.v"), " and ",
                              el(a, none, [href="rocq-glibc-zsys-OsRegistry.html"], "OsRegistry.v"), " for the audited ",
                              el(code, none, "zsys_*"), " syscall boundary and ", el(code, none, "errno"), " lending, ",
                              el(a, none, [href="rocq-glibc-string-WordString.html"], "WordString.v"), ", ",
                              el(a, none, [href="rocq-glibc-string-StrlenWord.html"], "StrlenWord.v"), ", and ",
                              el(a, none, [href="rocq-glibc-string-StrcmpLogic.html"], "StrcmpLogic.v"),
                              " for fractional word-aligned string ownership, ", el(code, none, "strlen"), ", and ", el(code, none, "strcmp"), ", and ",
                              el(a, none, [href="rocq-glibc-stdlib-AllocLogic.html"], "AllocLogic.v"), ", ",
                              el(a, none, [href="rocq-glibc-stdlib-AtexitLogic.html"], "AtexitLogic.v"), ", and ",
                              el(a, none, [href="rocq-glibc-stdlib-LeavesLogic.html"], "LeavesLogic.v"), " for ",
                              el(code, none, "malloc"), ", ", el(code, none, "free"), ", ", el(code, none, "atexit"),
                              ", and TLS/locale leaf triples. ",
                              el(a, none, [href="rocq-glibc-LenLogic.html"], "LenLogic.v"), " (", el(code, none, "len.c"), ") and ",
                              el(a, none, [href="rocq-glibc-SayLogic.html"], "SayLogic.v"), " (", el(code, none, "say.c"), ", ",
                              el(code, none, "write(1, msg, strlen(msg))"),
                              ") are small end-to-end worked proofs over compiled glibc IR." )),
                         el(li, none,
                            ( el(strong, none, "Core IR model and validator soundness ("),
                              el(code, none, "rocq/theories/core/"), el(strong, none, ", "),
                              el(code, none, "rocq/theories/soundness/"), el(strong, none, "): "),
                              "Read ", el(a, none, [href="rocq-theories-core-Syntax.html"], "Syntax.v"), ", ",
                              el(a, none, [href="rocq-theories-core-Semantics.html"], "Semantics.v"), ", ",
                              el(a, none, [href="rocq-theories-core-Runtime.html"], "Runtime.v"), ", and ",
                              el(a, none, [href="rocq-theories-core-Validate.html"], "Validate.v"),
                              " for the checked IR and validator, then ",
                              el(a, none, [href="rocq-theories-soundness-Machine.html"], "Machine.v"), " and ",
                              el(a, none, [href="rocq-theories-soundness-Soundness.html"], "Soundness.v"), " (",
                              el(code, none, "valid_no_unchecked"),
                              ") for the proof that validated IR never steps to ", el(code, none, "unchecked"), "." )),
                         el(li, none,
                            ( el(strong, none, "Iris program logic ("),
                              el(code, none, "rocq/theories/logic/"), el(strong, none, ", "),
                              el(code, none, "rocq/theories/external/"), el(strong, none, "): "),
                              "Read ", el(a, none, [href="rocq-theories-logic-Panics.html"], "Panics.v"), ", ",
                              el(a, none, [href="rocq-theories-logic-Pieces.html"], "Pieces.v"), ", ",
                              el(a, none, [href="rocq-theories-logic-Heap.html"], "Heap.v"), ", ",
                              el(a, none, [href="rocq-theories-logic-Language.html"], "Language.v"), ", and ",
                              el(a, none, [href="rocq-theories-logic-Logic.html"], "Logic.v"), " (",
                              el(a, none, [href="../logic.html"], "the program logic"), "), with ",
                              el(a, none, [href="rocq-theories-external-ExternalCalls.html"], "ExternalCalls.v"), " and ",
                              el(a, none, [href="rocq-theories-logic-ContractFrame.html"], "ContractFrame.v"),
                              " for external-call contracts and framing." )),
                         el(li, none,
                            ( el(strong, none, "Worked examples, reference Hello proof, and compiler backend: "),
                              "Standalone C program proofs are in ", el(code, none, "rocq/theories/programs/"), " (",
                              el(a, none, [href="rocq-theories-programs-Sum.html"], "Sum.v"), ", ",
                              el(a, none, [href="rocq-theories-programs-BufferLogic.html"], "BufferLogic.v"), ", ",
                              el(a, none, [href="rocq-theories-programs-CountLogic.html"], "CountLogic.v"), ", ",
                              el(a, none, [href="rocq-theories-programs-SlotLogic.html"], "SlotLogic.v"),
                              "), the contract-based GNU Hello reference proof is in ",
                              el(code, none, "rocq/theories/hello_contracts/"), " (",
                              el(a, none, [href="rocq-theories-hello_contracts-HelloMain.html"], "HelloMain.v"), ", ",
                              el(a, none, [href="rocq-theories-hello_contracts-HelloJoin.html"], "HelloJoin.v"),
                              "), and the Gallina compiler backend and NFB bytecode proofs are in ",
                              el(code, none, "rocq/backend/"), " (",
                              el(a, none, [href="rocq-backend-Compile.html"], "Compile.v"), ", ",
                              el(a, none, [href="rocq-backend-Regs.html"], "Regs.v"), ", ",
                              el(a, none, [href="rocq-backend-RegsProof.html"], "RegsProof.v"), ", ",
                              el(a, none, [href="rocq-backend-NfbProof.html"], "NfbProof.v"), ")." )) )) )),
               { findall(D, ( member(page(F, _, _, _), Pages), file_directory_name(F, D) ), Ds0), sort(Ds0, Ds),
                 findall(G, role_group(G), Groups),
                 findall(GD, ( member(group(_, _, GDs), Groups), member(GD, GDs) ), Known0), sort(Known0, Known),
                 subtract(Ds, Known, Extra) },
               seq(Groups, index_group(Pages, Ds)),
               seq(Extra, file_dir(Pages)) ))).

role_group(group(
    "Live campaign: GNU Hello over userland glibc",
    ( "Active proof campaign (", el(code, none, "nanofil-glibc"), ", ",
      el(a, none, [href="../docs/glibc-ir.html"], "glibc-ir.md"),
      ") proving userland glibc compiled to nanofil IR over audited libpizlo ",
      el(code, none, "zsys_*"), " syscall contracts (",
      el(a, none, [href="../docs/zsys.html"], "zsys.md"), ")." ),
    [ 'nanofil/rocq/glibc/zsys',
      'nanofil/rocq/glibc/string',
      'nanofil/rocq/glibc/stdlib',
      'nanofil/rocq/glibc/libio',
      'nanofil/rocq/glibc/hello',
      'nanofil/rocq/glibc' ])).
role_group(group(
    "Core framework: IR model, validator soundness, external calls, and Iris program logic",
    ( "Shared foundation (", el(code, none, "nanofil-rocq"), ", ",
      el(a, none, [href="../formal.html"], "formal.md"), ", ",
      el(a, none, [href="../logic.html"], "logic.md"),
      "): the checked-IR semantics and validator, the ", el(code, none, "valid_no_unchecked"),
      " soundness theorem, the external-call boundary, and the Iris separation logic used by all program proofs." ),
    [ 'nanofil/rocq/theories/core',
      'nanofil/rocq/theories/soundness',
      'nanofil/rocq/theories/external',
      'nanofil/rocq/theories/logic' ])).
role_group(group(
    "Worked example programs",
    "Standalone C program proofs demonstrating invariants, loops, heap allocation, helper specifications, persistent callee state, and contract-era hi.c lifecycle composition.",
    [ 'nanofil/rocq/theories/programs' ])).
role_group(group(
    "Legacy libc contracts and reference Hello proof",
    ( "This layer keeps the earlier libc contracts, their fixtures and calling rules, and the reference proof of GNU Hello 2.12.3 (",
      el(a, none, [href="../docs/libc-contracts.html"], "libc-contracts.md"),
      "). They remain compiled and gated while the ", el(code, none, "rocq/glibc/"),
      " campaign proves compiled userland glibc IR." ),
    [ 'nanofil/rocq/hello_contracts',
      'nanofil/rocq/theories/hello_contracts' ])).
role_group(group(
    "Program-logic worked example and constant-time spikes",
    ( "Worked examples (", el(code, none, "listsum.c"),
      ") proved through the production ", el(code, none, "Logic.v"), " framework (",
      el(code, none, "nanofil-logic-spikes"), ", ", el(a, none, [href="../logic.html"], "logic.md"),
      ") and constant-time poison taint semantics." ),
    [ 'nanofil/rocq/spikes' ])).
role_group(group(
    "Gallina compiler backend and λANF lowering",
    ( "Separate compiler workstreams: the Gallina IR-to-x86-64 compiler backend and NFB bytecode round-trip proofs (",
      el(a, none, [href="../docs/gallina-backend.html"], "gallina-backend.md"), ", ",
      el(a, none, [href="../docs/nfb.html"], "nfb.md"),
      "), its C++ (Crane) and C (CertiRocq) extractions, and the CertiRocq λANF-to-IR lowering pass (",
      el(a, none, [href="../lambda-anf.html"], "lambda-anf.md"), ")." ),
    [ 'nanofil/rocq/backend',
      'nanofil/rocq/backend/crane',
      'nanofil/rocq/backend/certirocq',
      'nanofil/anf/lower',
      'nanofil/anf/lower/tests',
      'nanofil/anf/backend' ])).

index_group(Pages, Ds, group(Title, Note, GroupDirs)) -->
    { include([D]>>memberchk(D, Ds), GroupDirs, Present) },
    (   { Present == [] } -> []
    ;   el(h2, "rq-sec", esc(Title)),
        el(p, "rq-group-note", Note),
        seq(Present, file_dir(Pages))
    ).

%  A directory's files, each its name, its size and its blurb.
file_dir(Pages, Dir) -->
    { ( atom_concat('nanofil/', R, Dir) -> true ; R = Dir ),
      atom_concat('https://github.com/mbrock/filnix/tree/main/', Dir, Src) },
    el(h3, "rq-dir", el(a, none, [href=Src], ( esc(R), "/" ))),
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

%% Per-file index blurbs

%  Live campaign: rocq/glibc/zsys/
file_blurb('nanofil/rocq/glibc/zsys/OsBlocks.v',
    "This module tracks borrowed buffers and errno storage so syscall contracts can return ownership to their callers.").
file_blurb('nanofil/rocq/glibc/zsys/OsClose.v',
    "This module specifies how libpizlo closes file descriptors and proves the call rule used by glibc.").
file_blurb('nanofil/rocq/glibc/zsys/OsExit.v',
    "These contracts describe libpizlo's soft and hard process exits, neither of which returns to the caller.").
file_blurb('nanofil/rocq/glibc/zsys/OsFstat.v',
    "This contract describes how libpizlo reads file metadata into a borrowed stat buffer and updates errno.").
file_blurb('nanofil/rocq/glibc/zsys/OsIoctl.v',
    "This contract bounds the buffer changes made by libpizlo's guarded ioctl wrapper for supported requests.").
file_blurb('nanofil/rocq/glibc/zsys/OsLseek.v',
    "This module specifies file-offset changes through libpizlo's seek wrapper, including return values and errno updates.").
file_blurb('nanofil/rocq/glibc/zsys/OsRegistry.v',
    "This registry combines syscall, thread-cookie, and void-returning memory contracts at the boundary between glibc and libpizlo.").
file_blurb('nanofil/rocq/glibc/zsys/OsThread.v',
    "This contract returns the current thread's descriptor pointer without changing memory or emitting trace events.").
file_blurb('nanofil/rocq/glibc/zsys/OsWorld.v',
    "This module tracks errno, thread state, and descriptors across program steps and calls into libpizlo.").
file_blurb('nanofil/rocq/glibc/zsys/OsWrite.v',
    "This contract describes writes from a readable caller buffer, including partial output and errno changes.").
file_blurb('nanofil/rocq/glibc/zsys/OsWritev.v',
    "This contract describes how libpizlo gathers readable buffers for a vectored write and reports errors.").

%  Live campaign: rocq/glibc/string/
file_blurb('nanofil/rocq/glibc/string/MallocCode.v',
    "This generated module supplies the checked IR of glibc's allocator and deallocator to implementation proofs.").
file_blurb('nanofil/rocq/glibc/string/MemFwdCode.v',
    "This generated module supplies checked IR for glibc's memory-copying routines and supporting locale and character functions.").
file_blurb('nanofil/rocq/glibc/string/MemcmpCode.v',
    "This generated module supplies the checked IR of glibc's memcmp implementation to the comparison proof.").
file_blurb('nanofil/rocq/glibc/string/MemcmpLogic.v',
    "This proof covers glibc's memcmp below sixteen bytes, before its capability-less word reads can trap.").
file_blurb('nanofil/rocq/glibc/string/MemrchrBits.v',
    "These arithmetic lemmas explain how glibc's reverse byte search finds the last matching byte within a word.").
file_blurb('nanofil/rocq/glibc/string/MemrchrCode.v',
    "This generated module supplies checked IR for glibc's reverse byte search to the memrchr proofs.").
file_blurb('nanofil/rocq/glibc/string/MemrchrLogic.v',
    "This proof verifies glibc's reverse byte search over readable word windows and supplies its caller-facing specification.").
file_blurb('nanofil/rocq/glibc/string/MemrchrLoop.v',
    "This proof follows glibc's reverse byte search as its loop walks backward through readable eight-byte words.").
file_blurb('nanofil/rocq/glibc/string/MemrchrMask.v',
    "This proof handles the last partially searched word before memrchr returns a match or continues backward.").
file_blurb('nanofil/rocq/glibc/string/StrchrCode.v',
    "This generated module supplies checked IR for glibc's character searches and bounded string-length routine to their proofs.").
file_blurb('nanofil/rocq/glibc/string/StrcmpBits.v',
    "These arithmetic lemmas relate glibc's word comparisons and cross-word merges to the first differing string byte.").
file_blurb('nanofil/rocq/glibc/string/StrcmpCode.v',
    "This generated module supplies the checked IR of glibc's strcmp implementation to the string comparison proofs.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLogic.v',
    "This proof verifies glibc's strcmp for readable word-aligned strings, including aliased inputs with fractional ownership.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLoop.v',
    "These proofs follow the aligned and unaligned word loops used by glibc's string comparison routine.").
file_blurb('nanofil/rocq/glibc/string/StrlenLoop.v',
    "This proof follows glibc's string-length loop through readable words until it finds the terminating zero byte.").
file_blurb('nanofil/rocq/glibc/string/StrlenWord.v',
    "This proof verifies glibc's strlen over word-aligned strings with fractional or permanently read-only ownership.").
file_blurb('nanofil/rocq/glibc/string/StrchrnulLogic.v',
    "These proofs verify glibc's forward character searches over word-aligned strings while preserving the caller's read permission.").
file_blurb('nanofil/rocq/glibc/string/StrncmpBits.v',
    "These arithmetic lemmas relate bounded word comparisons to the byte difference that glibc's strncmp returns.").
file_blurb('nanofil/rocq/glibc/string/StrncmpCode.v',
    "This generated module supplies the checked IR of glibc's strncmp implementation to the bounded comparison proofs.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLogic.v',
    "This proof verifies glibc's bounded string comparison over two word-aligned strings with arbitrary read shares.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLoop.v',
    "These proofs verify the four-word loop steps that glibc's strncmp uses for aligned and unaligned inputs.").
file_blurb('nanofil/rocq/glibc/string/StrncmpWords.v',
    "These invariants track the remaining bytes and readable word windows through glibc's bounded string comparison loops.").
file_blurb('nanofil/rocq/glibc/string/StrnlenLogic.v',
    "This proof verifies glibc's bounded string-length routine by using its compiled byte search on a readable string.").
file_blurb('nanofil/rocq/glibc/string/StrrchrLogic.v',
    "This proof verifies glibc's last-character search while preserving the caller's fractional ownership of the string.").
file_blurb('nanofil/rocq/glibc/string/WordString.v',
    "This ownership assertion describes C strings whose surrounding eight-byte words are readable by glibc's word-at-a-time routines.").

%  Live campaign: rocq/glibc/hello/
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLeaf.v',
    "These proofs verify GNU Hello's small string and memory helpers against the compiled glibc implementations they call.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgCells.v',
    "This module describes the global pointer cells and path tests used when GNU Hello sets its program name.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgClosed.v',
    "This proof closes GNU Hello's program-name specification by supplying the compiled glibc search and comparison proofs.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgLibs.v',
    "This proof verifies how GNU Hello removes libtool directory and filename prefixes from its program name.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgName.v',
    "This proof verifies GNU Hello's program-name setup using the compiled glibc string routines that inspect its path.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcXmalloc.v',
    "GNU Hello's xmalloc uses the concrete glibc allocation proof.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainStreams.v',
    "Concrete exit-stream predicates remain visible without exporting the flush proof modules.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainAlloc.v',
    "The idle allocator predicate remains visible without exporting the allocation proofs.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcDebts.v',
    "GNU Hello's remaining M4 and M6 obligations use concrete stream, string and OS resources.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsT.v',
    "Link and object-layout facts connect GNU Hello to the proved glibc implementations.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsStr.v',
    "Concrete glibc proofs discharge Hello's string, zeroing and errno calls.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainNameSearch.v',
    "Sealed reverse-search and byte-comparison proofs support program-name selection.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsName.v',
    "Hello's program-name call stores the selected suffixes in its global cells.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsSys.v',
    "Concrete allocation, deallocation and exit-registration proofs discharge Hello's system calls.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsCleanup.v',
    "The concrete stream-cleanup proof consumes the state left by Hello's close callback.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLibsExit.v',
    "The concrete exit proof invokes Hello's registered callback and cleans up the streams.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainLibs.v',
    "The completed library record combines concrete proofs, leaving only the explicit HelloDebts.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainLibsCalls.v',
    "The sealed string and program-name call group keeps library composition within its compile budget.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainWitness.v',
    "A concrete finite heap supplies three empty streams and the idle allocator without overlapping ownership.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainWitnessIO.v',
    "The stream list, thread fields, errno and read-only stream resources coexist with the concrete stream and allocator fixture.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainSteps.v',
    "Shared call and memory rules support the proof of Hello's main function.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainStart.v',
    "Hello initializes its name, locale, greeting state and exit callback before the option loop.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainDispatch.v',
    "The option-loop invariant supplies the resources required by each dispatch branch.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainLoop.v',
    "Hello's option loop preserves its resources and safely dispatches to the proved branches.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainVersion.v',
    "Hello's version branch prints its version and exits through the registered callback.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainHelpEnd.v',
    "The help branch finishes its output and exits without returning to main.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainHelp.v',
    "Hello's help branch uses the explicit output obligations and concrete library proofs.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainOperands.v',
    "Hello checks remaining operands and either exits or proceeds to the greeting.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainTail.v',
    "The greeting's final branches release their buffers and exit safely.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainGreet.v',
    "Hello selects narrow or wide output and composes it with the final branches.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcMainFull.v',
    "The complete main triple joins initialization, option parsing and every exit branch.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcJoin.v',
    "Heap adequacy gives hello_never_panics under the concrete initial resources and explicit M4 and M6 obligations.").

%  Live campaign: rocq/glibc/stdlib/
file_blurb('nanofil/rocq/glibc/stdlib/AllocLogic.v',
    "These proofs verify glibc's compiled malloc and free wrappers over the runtime's allocation and deallocation contracts.").
file_blurb('nanofil/rocq/glibc/stdlib/AtexitLogic.v',
    "These proofs verify how glibc registers exit handlers while maintaining ownership of its callback table.").
file_blurb('nanofil/rocq/glibc/stdlib/LeavesLogic.v',
    "These proofs verify glibc's small functions for thread-local errno, character tables, and multibyte conversion state.").
file_blurb('nanofil/rocq/glibc/stdlib/StdlibCode.v',
    "This generated module supplies checked IR for glibc's allocation, exit-handler registration, and supporting locale functions.").

%  Live campaign: rocq/glibc/libio/
file_blurb('nanofil/rocq/glibc/libio/ExitRun.v',
    "This proof verifies glibc's exit sequence through registered handlers, stream cleanup, and the final runtime exit.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunCode.v',
    "This generated module supplies the checked IR of glibc's exit-handler runner and exit entry point.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunLoop.v',
    "This proof follows glibc's exit loop as it invokes registered handlers in reverse registration order.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunTail.v',
    "This proof verifies the end of glibc's exit sequence after the callback list has been exhausted.").
file_blurb('nanofil/rocq/glibc/libio/FileInv.v',
    "These invariants describe glibc's stream fields, buffer ownership, locks, jump tables, and linked list of open streams.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanup.v',
    "This proof verifies glibc's stream cleanup loop as it visits open streams and disables their buffering state.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupCode.v',
    "This generated module supplies the checked IR of glibc's stream cleanup routine to its implementation proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupExit.v',
    "This proof supplies the stream-cleanup rule needed at process exit, including the thread cleanup-buffer calls.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpLock.v',
    "This proof verifies how one cleanup iteration records the current stream and acquires its single-threaded lock.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpUnlock.v',
    "This proof verifies how cleanup releases the stream lock and advances to the next open stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupLock.v',
    "These proofs verify how stream cleanup acquires and releases the list lock around its traversal.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupMode.v',
    "This proof follows cleanup's buffering tests along the path that disables the stream without replacing its buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupPass.v',
    "This proof combines the steps of one stream-cleanup iteration into the rule used by the loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupStart.v',
    "This proof verifies cleanup's initial flush and thread cleanup-buffer setup before it traverses the stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseIt.v',
    "This proof verifies glibc's stream-close helper as it flushes pending output and closes the file descriptor.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItCode.v',
    "This generated module supplies checked IR for glibc's file-stream closing helpers to the close proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItEnd.v',
    "This proof verifies how the stream-close helper clears buffer pointers and marks the stream as closed.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItMid.v',
    "This proof follows the stream-close helper through its indirect close call and removal of the stream buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseSteps.v',
    "These shared rules support instruction steps and temporary cleanup frames in glibc's stream lifecycle proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputn.v',
    "This proof verifies glibc's default string-output loop using the stream jump table's overflow specification.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBuf.v',
    "These assertions describe a stream's writable buffer space and the overflow behavior required by string output.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBytes.v',
    "This proof verifies the short byte-copy loop used by glibc's default string-output routine for small writes.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnCopy.v',
    "This rule verifies copying caller bytes into a stream buffer through libpizlo's memory-move contract.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnRoom.v',
    "This proof verifies the bulk-copy path that fills available stream-buffer space when more than twenty bytes fit.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnSmall.v',
    "This proof verifies the small-copy path that fills at most twenty bytes of available stream-buffer space.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnTail.v',
    "This proof verifies how default string output finishes a round by returning or sending another byte through overflow.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputn.v',
    "This proof verifies glibc's file string-output routine using specifications for buffered overflow and direct byte writes.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnBase.v',
    "This module supplies stream-field ownership, newline scanning, and shared call rules for glibc's file string-output proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCall.v',
    "This proof verifies file string output's indirect write call while preserving the caller's share of the input bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnDo.v',
    "This proof follows file string output's direct-write path when the stream needs neither appending nor seeking.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnEnter.v',
    "These proofs verify how file string output counts the bytes that fit, including the line-buffered case.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFill.v',
    "These proofs verify how file string output copies the fitting input bytes into its stream buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlags.v',
    "This proof verifies how file string output chooses the writable end from line-buffering and unbuffered flags.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlush.v',
    "This proof verifies how file string output either flushes through the overflow entry or returns immediately.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnReset.v',
    "This proof verifies the read-area and write-area pointer resets within file string output's inlined write path.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnSetp.v',
    "This proof verifies the final write-end update before file string output returns or handles remaining bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnWrite.v',
    "This proof verifies how file string output rounds direct writes to whole blocks for sufficiently large buffers.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAlloc.v',
    "This proof verifies glibc's file-buffer allocation routine from the file-status query through installation of the new buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBase.v',
    "This module supplies device-number arithmetic and fresh-buffer ownership rules shared by the stream-allocation proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBuf.v',
    "This proof verifies how a buffered stream requests storage through its jump table's allocation entry.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocMode.v',
    "This proof follows the character-device and terminal tests that decide whether an allocated stream buffer is line-buffered.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocShort.v',
    "This proof verifies how an unbuffered stream uses its built-in one-byte buffer instead of allocating storage.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocTail.v',
    "This proof verifies the final allocation steps that choose a buffer size, allocate storage, and install it.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflow.v',
    "This proof verifies glibc's file overflow routine when the stream is already writing into its buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAlloc.v',
    "This proof verifies glibc's file overflow routine when the stream must first obtain a buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAllocSetg.v',
    "This proof follows overflow's initial allocation call and the subsequent setup of the new buffer's read pointers.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowBase.v',
    "This module describes the write-area state and return values shared by the file overflow proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowCall.v',
    "This proof verifies the call that sends a stream's pending bytes while file overflow flushes its buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFlush.v',
    "This proof verifies overflow's flush after storing a byte and its choice of success or error return.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFull.v',
    "This proof verifies how file overflow flushes a full stream buffer before storing the next byte.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowGen.v',
    "This proof verifies the generic overflow entry that sets byte orientation and dispatches through the stream jump table.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowPut.v',
    "This proof verifies overflow's byte store and the flush required for unbuffered streams or line-ending newlines.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSend.v',
    "This proof verifies how overflow distinguishes a flush request from a request to store another byte.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetp.v',
    "This proof verifies the write-pointer setup when file overflow switches a stream from reading to writing.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpRest.v',
    "This proof verifies the read-pointer resets and flag changes that finish a stream's switch to writing.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpEnd.v',
    "This proof verifies overflow's backup-area test and the write-end adjustment required for a line-buffered stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWrite.v',
    "This proof verifies glibc's buffered write helper while preserving the stream fields and jump-table ownership.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCall.v',
    "This proof verifies the jump-table check and indirect file-write call made by glibc's buffered write helper.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCode.v',
    "This generated module supplies checked IR for glibc's buffered write helper and file overflow routine.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteEnd.v',
    "This proof verifies the final write-end update for line-buffered and block-buffered streams after a buffered write.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteRet.v',
    "This proof verifies the buffered write helper's column-tracking join when the current column field is zero.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteSetp.v',
    "This proof verifies how the buffered write helper resets write pointers and checks the stream's orientation.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteTail.v',
    "This proof verifies how the buffered write helper resets a stream's read pointers after flushing output.").
file_blurb('nanofil/rocq/glibc/libio/LibioFclose.v',
    "This proof verifies glibc's compiled fclose implementation for the standard output stream during program shutdown.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseCode.v',
    "This generated module supplies the checked IR of glibc's fclose implementation to the stream-close proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseLock.v',
    "These proofs verify how glibc's fclose acquires and releases the stream lock in the single-threaded case.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseTail.v',
    "This proof follows fclose's final unlink and finish calls for the statically allocated standard output stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioFinish.v',
    "These proofs verify the default and file-specific finish entries for a stream already closed and unlinked.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlush.v',
    "This proof verifies glibc's flush-all routine by following its traversal of the open-stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushBody.v',
    "This module describes streams open at exit and specifies one iteration of the flush-all loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushClean.v',
    "These proofs verify the flush-all paths that need neither an overflow call nor a synchronization call.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushCode.v',
    "This generated module supplies the checked IR of glibc's flush-all routine to the stream-list proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpLock.v',
    "This proof verifies how a flush iteration records the current stream and acquires its single-threaded lock.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpUnlock.v',
    "This proof verifies how a flush iteration releases its stream lock and advances along the stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOver.v',
    "This proof verifies flush-all iterations over streams with buffered output and combines them with already-clean streams.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOverCall.v',
    "This proof verifies flush-all's checked jump-table dispatch to the overflow entry that flushes a stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushStart.v',
    "This proof verifies flush-all's cleanup-buffer setup and acquisition of the lock protecting the open-stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushTail.v',
    "This proof verifies how flush-all releases the stream-list lock, restores the cleanup buffer, and returns.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenCode.v',
    "This generated module supplies checked IR for generic stream output, marker cleanup, and thread-local destructor calls.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenLeaves.v',
    "These proofs verify glibc's thread-local destructor call and stream-marker cleanup under the assumptions of the exit proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioLogic.v',
    "This module supplies arithmetic facts, pointer checks, and symbolic execution tactics shared by glibc's stream proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsCode.v',
    "This generated module supplies checked IR for glibc's puts and fputs routines to the output proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioRead.v',
    "These proofs verify glibc's stream queries and file close and status helpers over the stream invariant.").
file_blurb('nanofil/rocq/glibc/libio/LibioReadCode.v',
    "This generated module supplies checked IR for glibc's stream queries, buffer allocation, and low-level file operations.").
file_blurb('nanofil/rocq/glibc/libio/LibioSetb.v',
    "This proof verifies how glibc replaces a stream buffer, freeing the old storage when the stream owns it.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlink.v',
    "This proof verifies how glibc removes a stream from the open-stream list while preserving list ownership.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkCode.v',
    "This generated module supplies checked IR for glibc's stream unlinking routine and its file and default finish entries.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkLock.v',
    "This proof verifies the cleanup-buffer setup and stream and list locks acquired before unlinking a stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkMid.v',
    "This proof verifies the pointer updates that splice a stream out of glibc's doubly linked stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkTail.v',
    "This proof verifies the final unlink steps that clear the linked flag, release locks, and restore cleanup state.").
file_blurb('nanofil/rocq/glibc/libio/LibioWrite.v',
    "This proof verifies glibc's low-level file-write loop, including partial writes and the stream's resulting error state.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteCall.v',
    "This proof verifies how the file-write loop calls the syscall wrapper on the remaining byte slice.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteExit.v',
    "These proofs verify file-write loop exits, stream error flags, and updates to the total number of bytes written.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCode.v',
    "This generated module supplies checked IR for glibc's file string-output implementation to the buffered output proofs.").
file_blurb('nanofil/rocq/glibc/libio/SysCleanup.v',
    "This proof verifies how glibc pushes a thread cleanup buffer using the descriptor returned by libpizlo.").
file_blurb('nanofil/rocq/glibc/libio/SysCleanupPop.v',
    "This proof verifies how glibc pops a thread cleanup buffer and restores the previous cleanup state.").
file_blurb('nanofil/rocq/glibc/libio/SysCode.v',
    "This generated module supplies checked IR for glibc's syscall wrappers, terminal query, and thread cleanup-buffer helpers.").
file_blurb('nanofil/rocq/glibc/libio/SysWrappers.v',
    "These proofs verify glibc's compiled syscall wrappers against the contracts for their calls into libpizlo.").

%  Live campaign & worked examples: rocq/glibc/
file_blurb('nanofil/rocq/glibc/GlibcLogic.v',
    "This module supplies shared ownership rules and symbolic execution tactics for proofs of compiled glibc functions.").
file_blurb('nanofil/rocq/glibc/LenCode.v',
    "This generated module supplies checked IR for a string-length example linked with glibc's own strlen implementation.").
file_blurb('nanofil/rocq/glibc/LenLogic.v',
    "This example proves that measuring a fixed greeting with glibc's compiled strlen never panics, without external contracts.").
file_blurb('nanofil/rocq/glibc/SayCode.v',
    "This generated module supplies checked IR for a greeting program linked with glibc's strlen and write implementations.").
file_blurb('nanofil/rocq/glibc/SayLogic.v',
    "This example proves safe greeting output through glibc's compiled strlen and write, using libpizlo's write contract.").
file_blurb('nanofil/rocq/glibc/StrlenBits.v',
    "These arithmetic lemmas support glibc's word-at-a-time string scans by relating byte extraction, masks, and population counts.").
file_blurb('nanofil/rocq/glibc/StrlenLogic.v',
    "This proof verifies glibc's compiled strlen on whole-word objects for use by the greeting examples.").

%  Core framework: rocq/theories/core/
file_blurb('nanofil/rocq/theories/core/Cfg.v',
    "This module builds control-flow graphs and computes dominators so the validator can check where definitions are available.").
file_blurb('nanofil/rocq/theories/core/Extract.v',
    "This module extracts the IR decoder, interpreter, and validator to OCaml for comparison with the Prolog compiler.").
file_blurb('nanofil/rocq/theories/core/Ieee.v',
    "This module computes IEEE floating-point operations on integer bit patterns, including single, double, and extended precision.").
file_blurb('nanofil/rocq/theories/core/Maps.v',
    "These finite maps speed up name lookups on large modules while preserving the behavior of association lists.").
file_blurb('nanofil/rocq/theories/core/Memory.v',
    "This module models data bytes, object regions, and shadow capabilities, together with access checks and memory operations.").
file_blurb('nanofil/rocq/theories/core/Ops.v',
    "This module evaluates checked-IR operations, including integer arithmetic, pointer checks, raw memory accesses, and floating-point conversions.").
file_blurb('nanofil/rocq/theories/core/Run.v',
    "This runner lays out a module's initial memory and executes a function using an arbitrary runtime implementation.").
file_blurb('nanofil/rocq/theories/core/Runtime.v',
    "This module states allocator and collector assumptions and constructs the interpreter runtime that satisfies them.").
file_blurb('nanofil/rocq/theories/core/Semantics.v',
    "This module defines how checked-IR instructions advance execution, including calls, returns, memory accesses, and allocation requests.").
file_blurb('nanofil/rocq/theories/core/Syntax.v',
    "This module defines the instructions, blocks, functions, and data declarations that make up a checked-IR module.").
file_blurb('nanofil/rocq/theories/core/Term.v',
    "This module represents the ground Prolog terms exchanged between the compiler and the formal model.").
file_blurb('nanofil/rocq/theories/core/Transport.v',
    "This module decodes Prolog terms into checked IR and encodes execution outcomes for comparison with Prolog.").
file_blurb('nanofil/rocq/theories/core/ValidFast.v',
    "This faster validator uses finite name maps and is proved equivalent to the original list-based validator.").
file_blurb('nanofil/rocq/theories/core/Validate.v',
    "This validator checks module structure, definition dominance, capability evidence, and the placement of reused or scheduled checks.").
file_blurb('nanofil/rocq/theories/core/Values.v',
    "This module represents runtime words and pointers, keeping a pointer's invisible capability separate from its address.").

%  Core framework: rocq/theories/soundness/
file_blurb('nanofil/rocq/theories/soundness/Ahead.v',
    "This module describes the backward analysis that justifies early capability checks by tracking pending access obligations.").
file_blurb('nanofil/rocq/theories/soundness/Chain.v',
    "This proof connects dominating definitions to the pointer distances and guards that justify reusing capability checks.").
file_blurb('nanofil/rocq/theories/soundness/Coverage.v',
    "This proof shows that a raw memory access covered by a successful check cannot fail as unchecked.").
file_blurb('nanofil/rocq/theories/soundness/Dominance.v',
    "This proof shows that the dominator-tree interval test implies dominance along every control-flow path from entry.").
file_blurb('nanofil/rocq/theories/soundness/Doomed.v',
    "This proof shows that a failed early check eventually traps without allowing an intervening unchecked access.").
file_blurb('nanofil/rocq/theories/soundness/Evidence.v',
    "This proof shows that each validated instruction preserves usable capability evidence and checks its raw accesses.").
file_blurb('nanofil/rocq/theories/soundness/Guard.v',
    "This proof justifies conditional check reuse from earlier span tests, saved bounds, and the guards that connect them.").
file_blurb('nanofil/rocq/theories/soundness/Identity.v',
    "This proof shows that object identities remain registered throughout execution and that freed objects remain freed.").
file_blurb('nanofil/rocq/theories/soundness/Interval.v',
    "This proof shows that the validator's inferred integer intervals contain the offsets computed during execution.").
file_blurb('nanofil/rocq/theories/soundness/Invariant.v',
    "This module states the execution invariant that tracks valid check evidence in active frames and suspended callers.").
file_blurb('nanofil/rocq/theories/soundness/Machine.v',
    "This machine connects instruction execution to an arbitrary runtime and proves that every step preserves runtime readiness.").
file_blurb('nanofil/rocq/theories/soundness/Persistence.v',
    "This proof preserves the evidence invariant across execution so validated frames never perform an unchecked access.").
file_blurb('nanofil/rocq/theories/soundness/Renew.v',
    "This proof justifies reused and partial capability checks from earlier checks that dominate the current instruction.").
file_blurb('nanofil/rocq/theories/soundness/Single.v',
    "This proof shows that dominating single definitions retain the values needed to replay pointer and guard calculations.").
file_blurb('nanofil/rocq/theories/soundness/Sites.v',
    "This proof connects the validator's definition-site checks to dominance at every use of a temporary.").
file_blurb('nanofil/rocq/theories/soundness/Soundness.v',
    "This theorem proves that every module accepted by the validator executes without reaching an unchecked operation.").
file_blurb('nanofil/rocq/theories/soundness/Steps.v',
    "These lemmas recover the instruction and frame changes responsible for a particular step of execution.").
file_blurb('nanofil/rocq/theories/soundness/Walk.v',
    "This proof connects the validator's traversal of each block to the capability facts available during execution.").

%  Core framework: rocq/theories/external/
file_blurb('nanofil/rocq/theories/external/ExternalCalls.v',
    "This framework describes external-call effects and preserves readiness; its fill and copy contracts also support the glibc campaign.").
file_blurb('nanofil/rocq/theories/external/ExternalMachine.v',
    "This machine extends core execution with contract-governed external calls, observable call traces, and external world state.").
file_blurb('nanofil/rocq/theories/external/Startup.v',
    "These predicates describe the capability-backed argument and environment arrays that Fil-C's launcher provides before main begins.").

%  Core framework: rocq/theories/logic/
file_blurb('nanofil/rocq/theories/logic/ContractFrame.v',
    "This proof shows that external calls preserve caller-owned memory outside the buffers and objects they may change.").
file_blurb('nanofil/rocq/theories/logic/Heap.v',
    "This module connects logical ownership of memory pieces to physical memory across stores, allocations, and collection.").
file_blurb('nanofil/rocq/theories/logic/Language.v',
    "This module presents the machine as an Iris language and connects program-logic proofs to execution safety.").
file_blurb('nanofil/rocq/theories/logic/Logic.v',
    "This program logic provides memory ownership assertions and proof rules for checked-IR instructions and external calls.").
file_blurb('nanofil/rocq/theories/logic/MemLogic.v',
    "These assertions own byte and capability buffers, with instruction rules for integer loads, stores, and compare-and-swap.").
file_blurb('nanofil/rocq/theories/logic/Panics.v',
    "This module distinguishes safety failures from ordinary endings and states what it means for a program never to panic.").
file_blurb('nanofil/rocq/theories/logic/Pieces.v',
    "This module divides memory into independently owned pieces keyed by object identity rather than physical address.").
file_blurb('nanofil/rocq/theories/logic/StepRules.v',
    "These rules advance individual checked-IR instructions from local premises without unfolding the whole interpreter or memory state.").
file_blurb('nanofil/rocq/theories/logic/StringLogic.v',
    "These ownership assertions describe C strings and let callers borrow individual bytes or suffixes.").
file_blurb('nanofil/rocq/theories/logic/Symbolic.v',
    "These tactics automate instruction steps while keeping the surrounding environments, memory state, and execution fuel abstract.").
file_blurb('nanofil/rocq/theories/logic/VariadicLogic.v',
    "These rules verify variadic argument snapshots and pointer reads through the cursor stored in a va_list.").
file_blurb('nanofil/rocq/theories/logic/WordBits.v',
    "These arithmetic lemmas relate little-endian bytes, masks, shifts, and carry-free arithmetic for word-at-a-time memory proofs.").

%  Worked example programs: rocq/theories/programs/
file_blurb('nanofil/rocq/theories/programs/Buffer.v',
    "This example proves safe allocation and repeated summation of a four-element heap buffer using a direct execution invariant.").
file_blurb('nanofil/rocq/theories/programs/BufferCode.v',
    "This generated module supplies checked IR for the heap-buffer example to its two alternative safety proofs.").
file_blurb('nanofil/rocq/theories/programs/BufferLogic.v',
    "This example proves the heap-buffer program safe using separation logic, loop induction, and ownership of individual cells.").
file_blurb('nanofil/rocq/theories/programs/Composition.v',
    "This module combines stream state, output obligations, and exit callbacks for the contract-based greeting program.").
file_blurb('nanofil/rocq/theories/programs/CountCode.v',
    "This generated module supplies checked IR for the example that counts character occurrences using a reusable helper.").
file_blurb('nanofil/rocq/theories/programs/CountLogic.v',
    "This example proves a character-counting loop safe by specifying its helper separately and borrowing string suffixes.").
file_blurb('nanofil/rocq/theories/programs/Cycle.v',
    "This example proves safe cyclic reads from a four-element global array for any loop trip count.").
file_blurb('nanofil/rocq/theories/programs/CycleCode.v',
    "This generated module supplies checked IR for the loop that repeatedly sums a small read-only global array.").
file_blurb('nanofil/rocq/theories/programs/Hi.v',
    "This example proves a greeting program safe against a trusted puts contract using a direct machine invariant.").
file_blurb('nanofil/rocq/theories/programs/HiArtifact.v',
    "This proof checks that the compiler-generated greeting module decodes to the exact module used in its safety proof.").
file_blurb('nanofil/rocq/theories/programs/HiCode.v',
    "This generated module supplies checked IR for the small puts greeting used by the example proofs.").
file_blurb('nanofil/rocq/theories/programs/HiLogic.v',
    "This example proves the greeting program safe using separation logic and the library rule for puts.").
file_blurb('nanofil/rocq/theories/programs/Program.v',
    "This proof composes launcher startup, greeting execution, and shutdown into one contract-based program lifecycle.").
file_blurb('nanofil/rocq/theories/programs/ScanCode.v',
    "This generated module supplies checked IR for the string-scanning example that combines length, search, and output calls.").
file_blurb('nanofil/rocq/theories/programs/ScanLogic.v',
    "This example proves safe string scanning and output while retaining permission to read the borrowed suffix afterward.").
file_blurb('nanofil/rocq/theories/programs/SlotCode.v',
    "This generated module supplies checked IR for the example whose helper retains a heap buffer across calls.").
file_blurb('nanofil/rocq/theories/programs/SlotLogic.v',
    "This example verifies a helper that retains, reuses, and grows a heap buffer across repeated calls.").
file_blurb('nanofil/rocq/theories/programs/Sum.v',
    "This example proves that summing a four-element read-only global array never panics, using direct symbolic execution.").
file_blurb('nanofil/rocq/theories/programs/SumCode.v',
    "This generated module supplies checked IR for the small global-array sum used in the first closed-module proof.").

%  Old reference proof: rocq/theories/hello_contracts/
file_blurb('nanofil/rocq/theories/hello_contracts/LibcCalls.v',
    "These retained libc contracts specify string, allocation, errno, and output calls for the earlier Hello proof and examples.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcCallFixtures.v',
    "These interpreter fixtures test admitted calls and rejected boundary cases for the retained libc contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/ExternalMachineFixtures.v',
    "These retained fixtures check external-call dispatch, return channels, rejection, and event order using the libc examples.").
file_blurb('nanofil/rocq/theories/hello_contracts/StartupFixtures.v',
    "These retained fixtures check launcher arguments, environment arrays, and exposed pointer cells using the libc examples.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStringLogic.v',
    "These rules derive string and output call triples from the retained libc contracts and shared string ownership assertions.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcMemLogic.v',
    "These rules derive allocation, copying, and search call triples from the retained libc contracts and shared buffer assertions.").
file_blurb('nanofil/rocq/theories/hello_contracts/Shutdown.v',
    "This retained protocol tracks exit callbacks and output obligations before handing process termination to the host runtime.").
file_blurb('nanofil/rocq/theories/hello_contracts/Stdio.v',
    "This retained protocol tracks required output bytes, delivered prefixes, and stream errors across standard-output calls.").
file_blurb('nanofil/rocq/theories/hello_contracts/CallbackLogic.v',
    "This theorem connects a registered exit callback's program-logic specification to its execution in the shutdown machine.").
file_blurb('nanofil/rocq/theories/hello_contracts/Diagnostics.v',
    "This contract distinguishes diagnostics that return normally from diagnostics that request process exit with a nonzero status.").
file_blurb('nanofil/rocq/theories/hello_contracts/Ending.v',
    "This shutdown model intercepts exit requests and runs registered callbacks before the final host exit.").
file_blurb('nanofil/rocq/theories/hello_contracts/ExitMemory.v',
    "This module describes the capability-backed callback registry used to store exit handlers in the contract-based Hello proof.").
file_blurb('nanofil/rocq/theories/hello_contracts/Formatting.v',
    "These contracts specify GNU Hello's formatted output calls and the format-string checks that make them safe.").
file_blurb('nanofil/rocq/theories/hello_contracts/Getopt.v',
    "This contract specifies option parsing, including argument-string provenance and updates to the option argument and index cells.").
file_blurb('nanofil/rocq/theories/hello_contracts/GetoptLogic.v',
    "These ownership rules let a caller read the option argument and index cells after option parsing.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloClose.v',
    "These proofs verify GNU Hello's stream-closing helper and standard-output exit callback against the retained libc contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloCode.v',
    "This generated module supplies GNU Hello's linked checked IR to the reference proof against per-function libc contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConv.v',
    "These proofs verify the multibyte-to-wide-character conversions used to prepare GNU Hello's greeting for wide output.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConvDefs.v',
    "This module shares memory-span facts and conversion-function definitions between GNU Hello's main and character-conversion proofs.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloDiagnosticChecks.v',
    "These proofs discharge format-string and literal-argument requirements at GNU Hello's particular diagnostic call sites.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloJoin.v',
    "This proof verifies greeting conversion and wide output, then joins them to the rest of Hello's main function.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLeaf.v',
    "These proofs verify GNU Hello's small memory and string wrappers against the retained per-function libc contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLocale.v',
    "These proofs verify the locale-query helpers that GNU Hello uses to choose how to convert its greeting.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloMain.v',
    "This proof follows Hello's main function through naming, locale setup, option parsing, and the help and version exits.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloModule.v',
    "This module decodes and validates GNU Hello's generated IR and identifies the functions used by its reference proof.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloName.v',
    "This proof verifies program-name setup, including path searches, libtool prefix removal, and stores into global pointer cells.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloProgName.v',
    "This proof strengthens program-name setup so the caller retains full ownership of the original and selected name strings.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloReach.v',
    "This check follows global symbols and callback pointers from main to verify that Hello's linked module is closed.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloStdio.v',
    "These proofs establish the output-call specifications needed at Hello's concrete call sites using its owned string literals.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloVersion.v',
    "These proofs verify GNU Hello's help and version output, including its variadic version-formatting helpers.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloWorld.v',
    "This module constructs the initial world and memory that connect Hello's startup, main proof, and exit callback.").
file_blurb('nanofil/rocq/theories/hello_contracts/LentLogic.v',
    "These ownership tokens track strings lent to the program by external library state, including locale category names.").
file_blurb('nanofil/rocq/theories/hello_contracts/Libc.v',
    "This module combines locale, option parsing, streams, errno, character conversion, and shutdown state into one libc world.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcDiagnosticLogic.v',
    "These rules verify diagnostic calls that either return normally or request exit through the composite libc world.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcErrnoLogic.v',
    "These stream-call rules lend the program's errno cell to libc and return ownership after the call.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcExit.v',
    "This contract describes immediate process termination through libc without returning to the program or running further instructions.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamAdapter.v',
    "This adapter transfers stream-handle tokens and errno ownership from the external world into the standard-output exit callback.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamLogic.v',
    "These framing rules keep program-owned memory separate from the private stream storage maintained by libc contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamTokens.v',
    "These tokens track the lifetime of standard-output and standard-error handles while the exit callback closes streams.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreams.v',
    "These stream contracts connect standard output and standard error to the composite world and shutdown's output obligations.").
file_blurb('nanofil/rocq/theories/hello_contracts/Linked.v',
    "This machine runs registered void exit callbacks as they are removed from the callback registry during shutdown.").
file_blurb('nanofil/rocq/theories/hello_contracts/Locale.v',
    "This contract models locale queries and updates while lending category-name strings from library state to the caller.").
file_blurb('nanofil/rocq/theories/hello_contracts/LocaleLogic.v',
    "These rules connect locale queries to the external world and track ownership of the borrowed name strings.").
file_blurb('nanofil/rocq/theories/hello_contracts/Streams.v',
    "These contracts describe stream queries and closing operations through the stream components of the composite libc world.").

%  Program-logic worked example: rocq/spikes/
file_blurb('nanofil/rocq/spikes/ListSum.v',
    "This module decodes the linked-list example and prepares its functions, globals, and initial frames for the safety proof.").
file_blurb('nanofil/rocq/spikes/ListSumCode.v',
    "This generated module supplies checked IR for the example that allocates and sums a linked list.").
file_blurb('nanofil/rocq/spikes/ListSumLogic.v',
    "This example proves a linked-list sum safe using modular function specifications and ownership of list segments.").

%  Gallina compiler backend: rocq/backend/
file_blurb('nanofil/rocq/backend/Abi.v',
    "This pass lowers calls, arguments, returns, and function objects into the actions required by Fil-C's calling conventions.").
file_blurb('nanofil/rocq/backend/Amd64Asm.v',
    "This module reads the backend's assembly lines as typed instructions and refuses every line that the execution model does not describe.").
file_blurb('nanofil/rocq/backend/Amd64Division.v',
    "This theorem shows that the integer division code that the backend emits never faults and leaves the IR's result in the accumulator register.").
file_blurb('nanofil/rocq/backend/Amd64DivisionStep.v',
    "This theorem shows that the code emitted for an IR division instruction loads its operands from the frame, never faults, and stores the result that the IR's step binds.").
file_blurb('nanofil/rocq/backend/Amd64Frame.v',
    "This module relates the stack frame of emitted code to the IR's environment and proves what the emitted operand loads and result stores do to that relation.").
file_blurb('nanofil/rocq/backend/Amd64Layout.v',
    "This proof shows that the frame layout which the backend computes puts every slot inside the frame at a multiple of eight bytes.").
file_blurb('nanofil/rocq/backend/Amd64DivisionCode.v',
    "This module splits the emitted division sequence into four fragments and proves what each fragment computes in the registers.").
file_blurb('nanofil/rocq/backend/Amd64Machine.v',
    "This module defines the registers, arithmetic flags and memory of an x86-64 machine state and the rules for reading and writing a part of a register.").
file_blurb('nanofil/rocq/backend/Amd64Memory.v',
    "This module models memory as a map from addresses to bytes and proves the facts about little-endian reads and writes that the amd64 semantics uses.").
file_blurb('nanofil/rocq/backend/Amd64Step.v',
    "This execution model gives each integer instruction that the backend emits its effect on registers, flags and memory, and it faults on every form that it does not cover.").
file_blurb('nanofil/rocq/backend/Amd64Total.v',
    "These lemmas show that the backend's branch-free operand rewriting makes the processor's divide safe and yields the IR's total quotient and remainder.").
file_blurb('nanofil/rocq/backend/Amd64Word.v',
    "This module reads 8, 16, 32 and 64-bit patterns as unsigned and signed integers and proves the wrapping and sign facts that the amd64 semantics uses.").
file_blurb('nanofil/rocq/backend/Asm.v',
    "This module represents x86-64 assembly lines and prints GNU assembler syntax to match the Prolog printer exactly.").
file_blurb('nanofil/rocq/backend/AsmTerm.v',
    "This decoder turns Prolog assembly terms into typed assembly lines so tests can compare the two printers.").
file_blurb('nanofil/rocq/backend/Compile.v',
    "These compilation pipelines combine optimization, capability-check insertion, validation, calling-convention lowering, and stack-based or register-based assembly emission.").
file_blurb('nanofil/rocq/backend/Copy.v',
    "This pass propagates copies and trivial phi nodes through unchecked SSA modules to match the Prolog optimizer.").
file_blurb('nanofil/rocq/backend/Emit.v',
    "This emitter turns a function's calling-convention plan into complete x86-64 assembly with temporaries stored in stack slots.").
file_blurb('nanofil/rocq/backend/EmitData.v',
    "This emitter produces assembly directives for global data, thread-local storage, constructor entries, and symbol aliases.").
file_blurb('nanofil/rocq/backend/EmitInst.v',
    "This emitter translates individual fused instructions, capability checks, and calling-convention actions into stack-based x86-64 assembly.").
file_blurb('nanofil/rocq/backend/EmitModule.v',
    "This emitter assembles a checked module's functions, data objects, aliases, and weak-symbol thunks into one assembly output.").
file_blurb('nanofil/rocq/backend/EmitObject.v',
    "This emitter produces Fil-C function objects, symbol getters, and entry adapters for generic and variadic calls.").
file_blurb('nanofil/rocq/backend/EmitOps.v',
    "This module selects x86-64 scalar instructions and x87 extended-precision operations for the stack-based assembly emitter.").
file_blurb('nanofil/rocq/backend/EmitThunk.v',
    "This emitter turns weak-symbol resolution plans into the x86-64 thunks needed to resolve optional external functions.").
file_blurb('nanofil/rocq/backend/Escape.v',
    "This analysis finds local allocations whose addresses do not escape and whose accesses use known constant offsets.").
file_blurb('nanofil/rocq/backend/Extract.v',
    "This module extracts the Gallina compiler passes to OCaml so tests can compare them with the Prolog backend.").
file_blurb('nanofil/rocq/backend/FrameSlots.v',
    "This allocator reuses stack slots for temporaries whose live intervals do not overlap and whose storage pools match.").
file_blurb('nanofil/rocq/backend/Fuse.v',
    "This pass combines each capability check with the following raw memory access or call before assembly emission.").
file_blurb('nanofil/rocq/backend/IrTerm.v',
    "These encoders turn typed checked-IR syntax back into the Prolog terms consumed by the compiler passes.").
file_blurb('nanofil/rocq/backend/IrText.v',
    "This parser reads the compiler's textual Prolog-clause IR format, including functions, data declarations, aliases, and context records.").
file_blurb('nanofil/rocq/backend/Layout.v',
    "This module supplies stack-frame offsets, symbol names, and assembly constructors shared by the code emitters.").
file_blurb('nanofil/rocq/backend/Liveness.v',
    "This backward analysis computes which temporaries remain live at the entry and exit of each fused block.").
file_blurb('nanofil/rocq/backend/Nfb.v',
    "This module encodes typed checked-IR modules into NFB bytecode and decodes their canonical binary representation.").
file_blurb('nanofil/rocq/backend/NfbProof.v',
    "These theorems prove that NFB encoding is canonical and that decoding recovers the original checked-IR module.").
file_blurb('nanofil/rocq/backend/NfbRead.v',
    "This proof shows that reading an encoded valid module term recovers exactly the original Prolog term.").
file_blurb('nanofil/rocq/backend/NfbTerm.v',
    "This module encodes and reads NFB binary modules at the Prolog-term level to match the Prolog implementation.").
file_blurb('nanofil/rocq/backend/NfbTotal.v',
    "This proof shows that NFB readers finish within the recursion budget derived from the input's word length.").
file_blurb('nanofil/rocq/backend/NfbTransport.v',
    "This proof shows that decoding the Prolog-term encoding of a typed module recovers its original syntax.").
file_blurb('nanofil/rocq/backend/Order.v',
    "This module implements Prolog's standard term ordering so sorting and ordered sets agree between the two compilers.").
file_blurb('nanofil/rocq/backend/Pizlonate.v',
    "This pass inserts capability checks, pointer flights, and loop-backedge collector polls to turn unchecked IR into checked IR.").
file_blurb('nanofil/rocq/backend/Plan.v',
    "These types describe a function's storage pools, fused checks, and calling-convention actions before registers are assigned.").
file_blurb('nanofil/rocq/backend/PlanTerm.v',
    "These encoders turn calling-convention plans and weak-symbol thunks into Prolog terms for comparison with the Prolog backend.").
file_blurb('nanofil/rocq/backend/Promote.v',
    "This pass replaces non-escaping local memory slots with SSA temporaries and phi nodes to match the Prolog optimizer.").
file_blurb('nanofil/rocq/backend/Regs.v',
    "This module allocates registers, validates the assignment, resolves parallel moves, and emits assembly using the assigned registers.").
file_blurb('nanofil/rocq/backend/RegsProof.v',
    "These proofs justify validated register assignments, parallel-move compilation, and the frame, saved-register, and root-storage invariants.").
file_blurb('nanofil/rocq/backend/TermCfg.v',
    "This module computes control-flow graphs, traversal orders, dominance frontiers, and temporary uses directly from unchecked IR terms.").
file_blurb('nanofil/rocq/backend/Text.v',
    "This string buffer lets the assembly printer build large outputs without repeatedly copying the text already emitted.").

%  Gallina compiler backend extraction: rocq/backend/crane/
file_blurb('nanofil/rocq/backend/crane/CraneExtract.v',
    "This module uses Bloomberg's Crane to extract the Gallina compiler backend and IR parser to C++.").
file_blurb('nanofil/rocq/backend/crane/CraneMap.v',
    "These extraction mappings implement Rocq's integer, character, and string operations through the compiler's C++ runtime library.").
file_blurb('nanofil/rocq/backend/crane/CraneSelfTest.v',
    "These computed reference values test the extracted C++ runtime primitives at integer-width boundaries against Rocq evaluation.").

%  λANF lowering campaign: anf/lower/ & anf/lower/tests/
file_blurb('nanofil/anf/lower/AnfExtract.v',
    "This module extracts the λANF lowering pass and IR text printer to OCaml for the compiler driver.").
file_blurb('nanofil/anf/lower/AnfLower.v',
    "This pass lowers CertiRocq's closure-converted λANF into checked nanofil IR using an arena of tagged 32-bit words.").
file_blurb('nanofil/anf/lower/tests/Programs.v',
    "These gate programs exercise λANF lowering with arithmetic, lists, closures, recursion, and larger computations, alongside printer and ordering tests.").
file_blurb('nanofil/anf/lower/tests/Ref.v',
    "This module extracts gate programs directly to OCaml to provide reference output for the arena-based compiler tests.").
file_blurb('nanofil/anf/lower/tests/Show.v',
    "This module serializes program results as bytes so arena-compiled programs and OCaml references can be compared exactly.").
file_blurb('nanofil/anf/lower/tests/Tap.v',
    "This harness asks CertiRocq to print each gate program's λANF representation for input to the lowering pass.").

% These entries arrived while the prose batch was being verified.
file_blurb('nanofil/anf/backend/Drive.v',
    "This driver runs the Gallina compiler backend through CertiRocq's closure conversion and λANF lowering pipeline.").
file_blurb('nanofil/anf/backend/Tap.v',
    "This harness prints the Gallina backend driver's λANF representation for inspection and subsequent compiler stages.").
file_blurb('nanofil/anf/lower/Prims.v',
    "This module declares the primitive operations that λANF test programs can call through the lowering pass.").
file_blurb('nanofil/rocq/backend/certirocq/CertiExtract.v',
    "This module extracts the Gallina compiler backend and IR text parser to C through CertiRocq.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputs.v',
    "This proof verifies glibc's fputs over readable word-aligned strings while preserving the caller's fractional ownership.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsCall.v',
    "This proof checks stream orientation and the indirect output method call inside glibc's fputs implementation.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsLock.v',
    "This proof follows glibc's fputs as it measures the string and acquires the stream lock.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsUnlock.v',
    "This proof follows glibc's fputs as it releases the stream lock and returns to its caller.").
file_blurb('nanofil/rocq/glibc/libio/LibioPuts.v',
    "This proof verifies glibc's puts over readable word-aligned strings and the standard output stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsBuf.v',
    "This proof checks buffer bounds before puts writes its trailing newline directly into the stream buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsCall.v',
    "This proof checks the stream's method table before puts calls its indirect string output method.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsInv.v',
    "This module describes stream ownership and output method requirements shared by the puts and fputs proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsLock.v',
    "This proof follows puts as it measures the string and acquires the standard output stream's lock.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsMode.v',
    "This proof checks that puts uses the standard output stream with the required narrow character orientation.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsNl.v',
    "This proof follows puts as it emits a trailing newline directly or through the stream's overflow method.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsUnlock.v',
    "This proof follows puts as it releases the standard output stream's lock and returns its result.").
file_blurb('nanofil/rocq/glibc/libio/LibioStdfiles.v',
    "This proof verifies how glibc initializes its standard streams and links them into the global stream list.").
file_blurb('nanofil/rocq/glibc/libio/LibioStdfilesCode.v',
    "This generated module supplies checked IR for glibc's standard stream constructor to its initialization proof.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteCallDq.v',
    "These call rules let glibc write from caller buffers held with shared or permanently read-only ownership.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteDq.v',
    "This proof verifies glibc's file output loop over caller buffers held with any fractional read permission.").
file_blurb('nanofil/rocq/glibc/string/MemFwdLogic.v',
    "These proofs verify glibc's forward memory copying, filling, and string duplication routines through their compiled implementations.").
file_blurb('nanofil/rocq/glibc/string/MemchrFirst.v',
    "This proof checks the first unaligned word examined by glibc's compiled forward byte search routine.").
file_blurb('nanofil/rocq/glibc/string/MemchrLast.v',
    "This proof handles the final partial word and loop exits in glibc's compiled forward byte search.").
file_blurb('nanofil/rocq/glibc/string/MemchrLogic.v',
    "This proof combines the word scanning cases into a caller-facing specification for glibc's compiled memchr.").
file_blurb('nanofil/rocq/glibc/string/MemchrLoop.v',
    "This proof follows glibc's forward byte search loop as it scans readable aligned words for a match.").
file_blurb('nanofil/rocq/spikes/Poison.v',
    "This model tracks secret data through program execution and detects secret-dependent branches and memory address leaks.").
file_blurb('nanofil/rocq/spikes/PoisonSbox.v',
    "This proof checks that an example substitution table lookup avoids secret-dependent branches and memory address leaks.").
