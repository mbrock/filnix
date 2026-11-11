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
    "Reference proof: GNU Hello over per-function libc contracts",
    ( "Retained Campaign 4/7 reference proof of GNU Hello 2.12.3 against per-function libc contracts (",
      el(a, none, [href="../docs/libc-contracts.html"], "libc-contracts.md"),
      "), kept compiled and gated while the ", el(code, none, "rocq/glibc/"),
      " campaign replaces those libc contracts with compiled userland glibc IR." ),
    [ 'nanofil/rocq/hello_contracts',
      'nanofil/rocq/theories/hello_contracts' ])).
role_group(group(
    "Program-logic worked example",
    ( "A heap-allocated linked-list program (", el(code, none, "listsum.c"),
      ") proved through the production ", el(code, none, "Logic.v"), " framework (",
      el(code, none, "nanofil-logic-spikes"), ", ", el(a, none, [href="../logic.html"], "logic.md"),
      "). The design spikes it was compared with are in the git history." ),
    [ 'nanofil/rocq/spikes' ])).
role_group(group(
    "Gallina compiler backend and λANF lowering",
    ( "Separate compiler workstreams: the Gallina IR-to-x86-64 compiler backend and NFB bytecode round-trip proofs (",
      el(a, none, [href="../docs/gallina-backend.html"], "gallina-backend.md"), ", ",
      el(a, none, [href="../docs/nfb.html"], "nfb.md"),
      "), its C++ (Crane) extraction, and the CertiRocq λANF-to-IR lowering pass (",
      el(a, none, [href="../lambda-anf.html"], "lambda-anf.md"), ")." ),
    [ 'nanofil/rocq/backend',
      'nanofil/rocq/backend/crane',
      'nanofil/anf/lower',
      'nanofil/anf/lower/tests' ])).

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
    "Live glibc campaign (reusable separation-logic support): borrowed memory block ranges `(b, o, n)` ([blk_any], [blks]) covering byte and [[aux]] pieces, thread `c: errno` ownership ([errno_own], [errno_any]), and post-call block return lemmas ([blk_return], [blks_return]).").
file_blurb('nanofil/rocq/glibc/zsys/OsClose.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for `c: int zsys_close(int fd)` over [os_world], audited against `c: zsys_close` and probed by [zsys-close.c](zsys-close.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsExit.v',
    "Live glibc campaign (trusted syscall contract): non-returning libpizlo boundary [[external call|contracts]] and WP rules for `c: void zsys_exit_soft(int code)` and `c: void zsys_exit_hard(int code)` over [os_world], probed by [zsys-exit.c](zsys-exit.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsFstat.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for `c: int zsys_fstat(int fd, struct stat *st)` over [os_world], borrowing the 144-byte `c: struct stat` buffer and `c: errno`, probed by [zsys-fstat.c](zsys-fstat.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsIoctl.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for variadic `c: int zsys_ioctl(int fd, int request, ...)` over [os_world], audited against `c: filc_call_syscall_with_guarded_ptr` and probed by [zsys-ioctl.c](zsys-ioctl.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsLseek.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for `c: long zsys_lseek(int fd, long offset, int whence)` over [os_world], probed by [zsys-lseek.c](zsys-lseek.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsRegistry.v',
    "Live glibc campaign (contract registry): combined external-call registry [os_registry] assembling the nine `zsys_*` and `c: zthread_self_cookie` contracts plus void-site `c: zmemmove` and `c: zmemset` contracts ([void_only]), probed by [zsys-mem.c](zsys-mem.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsThread.v',
    "Live glibc campaign (trusted runtime contract): libpizlo boundary [[external call|contract]] and WP rule for `c: void *zthread_self_cookie(void)` returning the thread's `c: struct pthread` pointer [ow_self], probed by [zsys-thread.c](zsys-thread.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsWorld.v',
    "Live glibc campaign (OS boundary framework): the [os_world] state (`c: errno` cell, thread cookie, log descriptor, and allowed descriptors), world interpretation [os_wi], stability lemmas across stores, allocations, frees, and safepoints, and generic WP call rules ([wp_os_call], [wp_os_errno_call], [wp_os_noreturn]).").
file_blurb('nanofil/rocq/glibc/zsys/OsWrite.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for `c: long zsys_write(int fd, const void *buf, size_t size)` over [os_world], audited against `c: filc_native_zsys_write` and probed by [zsys-write.c](../zsys-write.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsWritev.v',
    "Live glibc campaign (trusted syscall contract): libpizlo boundary [[external call|contract]] and WP rule for `c: long zsys_writev(int fd, const struct iovec *iov, int iovcnt)` over [os_world], audited against `c: filc_native_zsys_writev` and probed by [zsys-writev.c](zsys-writev.c).").

%  Live campaign: rocq/glibc/string/
file_blurb('nanofil/rocq/glibc/string/MallocCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([malloc_term]) of userland glibc's `malloc/malloc.os` (`c: malloc` and `c: free`), generated by `rocq/glibc/string/code.sh` as proof input.").
file_blurb('nanofil/rocq/glibc/string/MemFwdCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([memfwd_term]) of userland glibc's `memcpy`, `mempcpy`, `memset`, `strdup`, `errno`, `mbsinit`, `wctype`, and `ctype` units, generated by `rocq/glibc/string/code.sh` as proof input.").
file_blurb('nanofil/rocq/glibc/string/MemcmpCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([memcmp_term]) of userland glibc's `string/memcmp.os`, generated by `rocq/glibc/string/code.sh` as proof input for `c: memcmp`.").
file_blurb('nanofil/rocq/glibc/string/MemcmpLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc_memcmp_small], [glibc_memcmp_small]) for userland glibc's compiled `c: memcmp` on fewer than 16 bytes of two objects at any shares; from 16 bytes on its capability-less word reads trap.").
file_blurb('nanofil/rocq/glibc/string/MemrchrBits.v',
    "Live glibc campaign (reusable arithmetic library): last-match ([last_hit]), leading-zero count ([head_last]), byte-mark, and end-mask ([keep_low]) facts for userland glibc's word-at-a-time `c: memrchr`.").
file_blurb('nanofil/rocq/glibc/string/MemrchrCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([memrchr_term]) of userland glibc's `string/memrchr.os`, generated by `rocq/glibc/string/code.sh` as proof input for `c: memrchr`.").
file_blurb('nanofil/rocq/glibc/string/MemrchrLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples ([memrchr_win], [wp_glibc_memrchr_ws]) for userland glibc's compiled `__memrchr` over a window of words and a [word_string], and [glibc_memrchr_spec] discharging StrrchrLogic.v's premise.").
file_blurb('nanofil/rocq/glibc/string/MemrchrLoop.v',
    "Live glibc campaign (implementation proof): downward word-loop proof ([rloop]) for userland glibc's `__memrchr` over a window of 8-byte words at any share.").
file_blurb('nanofil/rocq/glibc/string/MemrchrMask.v',
    "Live glibc campaign (implementation proof): last-word proof ([memrchr_mask]) for userland glibc's `__memrchr`, from the masked marks of its last word to the answer or the word loop.").
file_blurb('nanofil/rocq/glibc/string/StrchrCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([strchr_term]) of userland glibc's `strchr`, `strchrnul`, `strrchr`, `memchr`, and `strnlen` units, generated by `rocq/glibc/string/code.sh` as proof input.").
file_blurb('nanofil/rocq/glibc/string/StrcmpBits.v',
    "Live glibc campaign (reusable arithmetic library): byte-difference specification ([strcmp_res]), comparison bitmask lemmas ([cmp_mask]), and cross-word [merge] facts for userland glibc's word-at-a-time `c: strcmp`.").
file_blurb('nanofil/rocq/glibc/string/StrcmpCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([strcmp_term]) of userland glibc's `string/strcmp.os`, generated by `rocq/glibc/string/code.sh` as proof input for `c: strcmp`.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLogic.v',
    "Live glibc campaign (implementation proof): general Hoare triple ([wp_glibc_strcmp_ws], [wp_call_glibc_strcmp]) for userland glibc's compiled `c: strcmp` (`__GI_strcmp`) over two [word_string]s at any fractional shares, aliased or not.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLoop.v',
    "Live glibc campaign (implementation proof): loop proofs ([aligned_loop], [unaligned_loop]) for userland glibc's word-at-a-time `c: strcmp` over aligned and unaligned 8-byte word windows at arbitrary fractional shares.").
file_blurb('nanofil/rocq/glibc/string/StrlenLoop.v',
    "Live glibc campaign (implementation proof): induction proof ([loop_spec_dq]) for the inner word-scan loop of userland glibc's `__strlen` at any fractional share `dq`, factoring the 16-step popcount chain ([tail_chain]) for [StrlenWord](StrlenWord.v).").
file_blurb('nanofil/rocq/glibc/string/StrlenWord.v',
    "Live glibc campaign (implementation proof): general Hoare triple ([wp_glibc_strlen_ws], [wp_call_glibc_strlen]) for userland glibc's compiled `__strlen` over a [word_string] at any fractional or persistent read-only share.").
file_blurb('nanofil/rocq/glibc/string/StrchrnulLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc_strchrnul_ws], [wp_glibc_strchr_ws]) for userland glibc's compiled `c: strchrnul` and `c: strchr` over [word_string] at any fractional share.").
file_blurb('nanofil/rocq/glibc/string/StrncmpBits.v',
    "Live glibc campaign (reusable arithmetic library): bounded-length word comparison and byte-difference lemmas ([strncmp_res]) for userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([strncmp_term]) of userland glibc's `string/strncmp.os`, generated by `rocq/glibc/string/code.sh` as proof input for `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc_strncmp_ws], [wp_call_glibc_strncmp]) for userland glibc's compiled `__GI_strncmp` over two [word_string]s at any fractional shares.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLoop.v',
    "Live glibc campaign (implementation proof): unrolled 4-word aligned and unaligned loop steps for userland glibc's `__GI_strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpWords.v',
    "Live glibc campaign (implementation proof): aligned and unaligned word-loop invariants ([aligned_loop], [unaligned_loop]) for userland glibc's `__GI_strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrnlenLogic.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc_strnlen_ws]) for userland glibc's compiled `__strnlen` via `__GI_memchr` over [word_string] at any share.").
file_blurb('nanofil/rocq/glibc/string/StrrchrLogic.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_call_glibc_strrchr]) for userland glibc's compiled `__GI_strrchr` over [word_string] at any share.").
file_blurb('nanofil/rocq/glibc/string/WordString.v',
    "Live glibc campaign (reusable separation-logic predicate): fractional word-aligned C string ownership [word_string] `dq p s` over the 8-byte words read by glibc's word-at-a-time string routines, with splitting, read-only persistence, and suffix-borrowing lemmas.").

%  Live campaign: rocq/glibc/hello/
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLeaf.v',
    "Live glibc campaign (application proof): Hoare triples for GNU Hello's compiled leaf functions (`mbszero`, `strnlen1`, `streq`, `memeq`) linked with userland glibc over [os_wi] with zero capability-token world premises.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgCells.v',
    "Live glibc campaign (application proof): global cell layout and prefix/slash helpers ([name_idx], [short_idx]) for GNU Hello's `set_program_name` over [os_wi] and [pcell] globals.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgClosed.v',
    "Live glibc campaign (application proof): GNU Hello's `set_program_name` and `memeq` linked with userland glibc's own `c: memrchr` and `c: memcmp`, with no premise about either ([set_program_name_closed]).").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgLibs.v',
    "Live glibc campaign (application proof): `\"/.libs/\"` and `\"lt-\"` stripping path proof for GNU Hello's `set_program_name` linked with userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgName.v',
    "Live glibc campaign (application proof): Hoare triple for GNU Hello's compiled `set_program_name` linked with userland glibc's `c: strrchr` and `c: strncmp` over [os_wi].").
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
    "Hello's option loop preserves its resources and reaches a proved exit branch.").
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
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled `c: malloc` ([wp_glibc_malloc]) and `c: free` ([wp_glibc_free], [wp_glibc_free_null]) over [tcache_idle] and the runtime's `c: zgc_alloc` and `c: zgc_free`.").
file_blurb('nanofil/rocq/glibc/stdlib/AtexitLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled exit-handler registration (`__new_exitfn`, `__internal_atexit`, `__cxa_atexit`, and `c: atexit`) over the [exit_funcs_inv] slot-table invariant.").
file_blurb('nanofil/rocq/glibc/stdlib/LeavesLogic.v',
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled TLS, locale, and multibyte leaf functions (`__errno_location`, `__ctype_b_loc`, `__ctype_get_mb_cur_max`, and `c: mbsinit`).").
file_blurb('nanofil/rocq/glibc/stdlib/StdlibCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([stdlib_term]) of userland glibc's `malloc`, `cxa_atexit`, `atexit`, `errno`, `mbsinit`, `wcfuncs`, `ctype/ctype-info.os`, and `mb_cur_max` units, generated by `rocq/glibc/stdlib/code.sh`.").

%  Live campaign: rocq/glibc/libio/
file_blurb('nanofil/rocq/glibc/libio/ExitRun.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc_run_exit_handlers], [wp_glibc_exit]) for userland glibc's compiled `__run_exit_handlers` and `c: exit` over [exit_funcs_inv], `_IO_cleanup`, and `c: zsys_exit_soft`.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([exit_run_term]) of userland glibc's `__run_exit_handlers` and `c: exit`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunLoop.v',
    "Live glibc campaign (implementation proof): LIFO handler-loop proof ([exit_loop]) for userland glibc's `__run_exit_handlers` over [exit_block] by reverse induction on registered exit handlers.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunTail.v',
    "Live glibc campaign (implementation proof): end-of-loop proof ([exit_tail]) for userland glibc's `__run_exit_handlers`, clearing `__exit_funcs`, invoking `_IO_cleanup`, and exiting through `c: zsys_exit_soft`.").
file_blurb('nanofil/rocq/glibc/libio/FileInv.v',
    "Live glibc campaign (reusable separation-logic invariant): 224-byte `_IO_FILE` field layout, [file_inv] stream buffer/lock/vtable invariant, [io_list_inv] `_IO_list_all` chain invariant, [vtables_ro] `__io_vtables` capability check table, and [tcb_cleanup_inv] NPTL cleanup-buffer layout.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanup.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_cleanup]) for userland glibc's compiled `_IO_cleanup` over [io_list_inv], whose inlined `_IO_unbuffer_all` loop ([cleanup_loop]) sets each [exit_stream]'s `_mode` to -1.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_cleanup_term]) of userland glibc's `_IO_cleanup`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupExit.v',
    "Live glibc campaign (implementation proof): `_IO_cleanup` at exit with no callee premise left: ExitRunTail's [cleanup_rule] ([cleanup_rule_io], [cleanup_rule_exit]), discharging the NPTL cleanup push and pop premises ([push_spec_holds], [pop_spec_holds]).").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpLock.v',
    "Live glibc campaign (implementation proof): `run_fp` set and single-threaded stream lock acquire ([wp_cleanup_L82]) in one pass of `_IO_cleanup`'s `_IO_unbuffer_all` loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpUnlock.v',
    "Live glibc campaign (implementation proof): Stream lock release, `run_fp` clear and `_chain` step ([wp_cleanup_L306]) ending one pass of `_IO_cleanup`'s `_IO_unbuffer_all` loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupLock.v',
    "Live glibc campaign (implementation proof): `list_all_lock` acquire and `_IO_list_all` head load ([wp_cleanup_L23]), and lock release, cleanup pop and return ([wp_cleanup_L386]) for userland glibc's `_IO_cleanup`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupMode.v',
    "Live glibc campaign (implementation proof): Backup-area and buffering tests that skip `_IO_SETBUF` and set `_mode` to -1 ([wp_cleanup_L93]) in `_IO_cleanup`'s `_IO_unbuffer_all` loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupPass.v',
    "Live glibc campaign (implementation proof): One pass ([cleanup_pass]) of `_IO_cleanup`'s `_IO_unbuffer_all` loop over an [exit_stream].").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupStart.v',
    "Live glibc campaign (implementation proof): `_IO_flush_all` call, cleanup-buffer push and thread cookie prefix ([wp_cleanup_start]) for userland glibc's `_IO_cleanup`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseIt.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_file_close_maybe_unlink]) for userland glibc's compiled `_IO_file_close_maybe_unlink` flushing pending output and closing the descriptor.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_close_it_term]) of userland glibc's `_IO_file_close_maybe_unlink` and `_IO_new_file_close_it`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItEnd.v',
    "Live glibc campaign (implementation proof): tail block proof for `_IO_file_close_maybe_unlink`, clearing buffer pointers and setting `closed_flags` and `_fileno = -1`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItMid.v',
    "Live glibc campaign (implementation proof): middle block proof for `_IO_file_close_maybe_unlink`, dispatching vtable `__close` and calling `_IO_setb(fp, NULL, NULL, 0)`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseSteps.v',
    "Live glibc campaign (shared proof support): entailment-style step lemmas and fresh 32-byte cleanup-frame helpers for `libio` close, unlink, flush, and cleanup proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputn.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_default_xsputn]) and Löb loop invariant ([wp_dx_loop]) for userland glibc's compiled `_IO_default_xsputn`, over the jump table's overflow ([overflow_spec]).").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBuf.v',
    "Live glibc campaign (reusable separation-logic invariant): a stream's write side ([wbuf], [wroom]) and the jump-table overflow premise ([overflow_spec]) for the string output functions.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBytes.v',
    "Live glibc campaign (implementation proof): Löb proof ([wp_dx_bytes]) of `_IO_default_xsputn`'s byte-by-byte copy of at most 20 bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnCopy.v',
    "Live glibc campaign (shared proof support): `memcpy`/`mempcpy` into a stream buffer at any offset ([wp_call_mempcpy_in]), over libpizlo's `c: zmemmove` contract.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnRoom.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_dx_L44]) for `_IO_default_xsputn` filling the buffer's room, by `__mempcpy` past 20 bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnSmall.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_dx_L50]) for `_IO_default_xsputn` filling at most 20 bytes of the buffer's room by the byte loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnTail.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_dx_L22]) for the end of `_IO_default_xsputn`'s round: the jump table's overflow of the next byte, or the return.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputn.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_file_xsputn]) for userland glibc's compiled `_IO_new_file_xsputn` over the stream's write side, the jump table's overflow ([overflow_spec]) and a write of bytes at a share ([fwq_spec]).").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnBase.v',
    "Live glibc campaign (reusable separation-logic invariant): The stream's fields beside the write side ([xfields], [xos]), the share-taking write premise ([fwq_spec]), the newline scan ([wp_xs_scan]) and the hand-off to `_IO_default_xsputn` ([wp_xs_L178]).").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCall.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L9]) for the jump table's write in `_IO_new_file_xsputn`'s inlined `new_do_write`, on the caller's bytes at their share.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnDo.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L168]) for `_IO_new_file_xsputn`'s direct write: not appending, no seek, then the jump table's write or the rest.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnEnter.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_xs_L18], [wp_xs_L19]) for `_IO_new_file_xsputn`'s count of the bytes that fit, line-buffered or not.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFill.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_xs_L20], [wp_xs_L101]) for `_IO_new_file_xsputn` copying the bytes that fit into the buffer by `__mempcpy`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlags.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L122]) for the write end `new_do_write` chooses from `_IO_LINE_BUF | _IO_UNBUFFERED`, for any buffer ([wroom_cap]).").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlush.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L96]) for `_IO_new_file_xsputn`'s flush through the jump table's overflow of `EOF`, or its return.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnReset.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L70]) for `_IO_setg` and `_IO_setp` in `_IO_new_file_xsputn`'s inlined `new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnSetp.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L117]) for the write end's store after `new_do_write` and the return or the hand-off of the rest.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnWrite.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_xs_L132]) for the direct write's count of `_IO_new_file_xsputn`: whole blocks of the buffer's size when it is at least 128.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAlloc.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_file_doallocate]) for userland glibc's compiled `_IO_file_doallocate`, from its vtable `__stat` call to the installed buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBase.v',
    "Live glibc campaign (shared proof support): the `__gnu_dev_major` arithmetic ([dev_major]), its Hoare triple ([wp_glibc___gnu_dev_major]), and the fresh-buffer continuation ([doalloc_k], [new_buf]) shared by the `_IO_file_doallocate` proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBuf.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_doallocbuf_alloc]) for userland glibc's compiled `_IO_doallocbuf` on a buffered stream, dispatching vtable `__doallocate`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocMode.v',
    "Live glibc campaign (implementation proof): `_IO_file_doallocate`'s character-device test, through `__gnu_dev_major` and `__isatty_nostatus`, that decides whether the stream is line-buffered.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocShort.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_doallocbuf_short]) for `_IO_doallocbuf` on an unbuffered stream, which installs the one-byte `_shortbuf`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocTail.v',
    "Live glibc campaign (implementation proof): `_IO_file_doallocate`'s tail blocks, choosing the buffer size from `st_blksize`, setting `_IO_LINE_BUF`, calling `malloc`, and installing the buffer with `_IO_setb`.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflow.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_file_overflow]) for userland glibc's compiled `_IO_new_file_overflow` on a stream already putting into its buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAlloc.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_file_overflow_alloc]) for userland glibc's compiled `_IO_new_file_overflow` on a stream without a buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAllocSetg.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow`'s first-call allocation ([wp_ovf_L33]) through `_IO_doallocbuf`, then `_IO_setg` of the new buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowBase.v',
    "Live glibc campaign (shared proof support): the put-area state ([ovf_state], [ovf_fixed]) and return relation ([ovf_ret]) of the `_IO_new_file_overflow` proofs, with byte-focus lemmas and step tactics.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowCall.v',
    "Live glibc campaign (implementation proof): `_IO_new_do_write` of the k pending bytes of an [ovf_state] ([wp_ovf_do_write]), as `_IO_new_file_overflow` flushes them.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFlush.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow`'s flush after a stored byte ([wp_ovf_L264]), returning the byte or `EOF`.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFull.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow` on a full buffer ([wp_ovf_L196]), flushing it before storing the byte.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowGen.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc___overflow]) for userland glibc's compiled `__overflow`, orienting the stream narrow and dispatching vtable `__overflow`.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowPut.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow`'s byte store at `_IO_write_ptr` ([wp_ovf_L198]), flushing an unbuffered stream or a line-buffered one at a newline.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSend.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow`'s dispatch on its argument ([wp_ovf_L18]), flushing the buffer for `EOF` and storing a byte otherwise.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetp.v',
    "Live glibc campaign (implementation proof): the first half of `_IO_new_file_overflow`'s switch to putting ([wp_ovf_L113]), setting the write pointers from the read pointer and the buffer's end.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpRest.v',
    "Live glibc campaign (implementation proof): the second half of `_IO_new_file_overflow`'s switch to putting ([wp_ovf_L113_rest]), resetting the read pointers, setting `_IO_CURRENTLY_PUTTING`, and testing `_mode`.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpEnd.v',
    "Live glibc campaign (implementation proof): `_IO_new_file_overflow`'s backup-area test ([wp_ovf_L35]) and line-buffered write-end reset ([wp_ovf_L162]).").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWrite.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_do_write]) for userland glibc's compiled `_IO_new_do_write` over [file_inv] and `__io_vtables`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCall.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_do_write_call]) for `_IO_new_do_write`'s `__io_vtables` check and indirect `slot_write` call into `_IO_new_file_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_do_write_term]) of userland glibc's `_IO_new_do_write` and `_IO_new_file_overflow`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteEnd.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_do_write_end]) for `_IO_new_do_write`'s return block updating `_IO_write_end` for line-buffered vs block-buffered streams.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteRet.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_do_write_ret]) for `_IO_new_do_write`'s column-tracking join block when `_cur_column = 0`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteSetp.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_do_write_setp]) for `_IO_new_do_write`'s `_IO_setp` write-pointer reset and `_mode` check.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteTail.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_do_write_tail]) for `_IO_new_do_write`'s `_IO_setg` read-pointer reset after flushing.").
file_blurb('nanofil/rocq/glibc/libio/LibioFclose.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_fclose_stdout]) for userland glibc's compiled `_IO_new_fclose` on `c: stdout`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_fclose_term]) of userland glibc's `_IO_new_fclose`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseLock.v',
    "Live glibc campaign (implementation proof): single-threaded stream lock acquire and release proofs for userland glibc's `_IO_new_fclose`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseTail.v',
    "Live glibc campaign (implementation proof): `_IO_un_link` and vtable `__finish` epilogue for userland glibc's `_IO_new_fclose` on static `c: stdout`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFinish.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc__IO_default_finish_closed], [wp_glibc__IO_new_file_finish_closed]) for vtable `__finish` on a closed, unlinked stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlush.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_flush_all]) for userland glibc's compiled `_IO_flush_all` by induction over [io_list_inv]'s streams ([flush_loop]), each pass a [flush_body].").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushBody.v',
    "Live glibc campaign (implementation proof): [exit_stream] predicate for the streams open at exit, the [flush_body] contract of one pass of `_IO_flush_all`'s loop, and its instance [flush_body_exit].").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushClean.v',
    "Live glibc campaign (implementation proof): `_IO_flush_all`'s per-stream tests that call neither `_IO_OVERFLOW` nor `_IO_SYNC` ([wp_flush_L94_clean], [wp_flush_L192]).").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_flush_term]) of userland glibc's `_IO_flush_all`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpLock.v',
    "Live glibc campaign (implementation proof): `run_fp` set and single-threaded stream lock acquire ([wp_flush_L83]) in one pass of `_IO_flush_all`'s loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpUnlock.v',
    "Live glibc campaign (implementation proof): Stream lock release, `run_fp` clear and `_chain` step ([wp_flush_L182]) ending one pass of `_IO_flush_all`'s loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOver.v',
    "Live glibc campaign (implementation proof): [flush_body_over] pass of `_IO_flush_all` over a stream with buffered output ([over_stream]), and [flush_body_or] for lists of both kinds of stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOverCall.v',
    "Live glibc campaign (implementation proof): `__io_vtables` check and indirect `__overflow` call `_IO_new_file_overflow (fp, EOF)` ([wp_flush_L240]) in `_IO_flush_all`, over the premise [overflow_spec].").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushStart.v',
    "Live glibc campaign (implementation proof): Cleanup-buffer push and `list_all_lock` acquire prefix ([wp_flush_start]) for userland glibc's `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushTail.v',
    "Live glibc campaign (implementation proof): `list_all_lock` release, cleanup pop and return ([wp_flush_L414]) for userland glibc's `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libiogen_term]) of userland glibc's `__GI___overflow`, `__GI__IO_default_xsputn`, `__GI__IO_unsave_markers`, and `__GI___call_tls_dtors`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenLeaves.v',
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled `__call_tls_dtors` ([dtors_rule_tls]) and `_IO_unsave_markers` ([wp_glibc__IO_unsave_markers], [unsave_spec_holds]).").
file_blurb('nanofil/rocq/glibc/libio/LibioLogic.v',
    "Live glibc campaign (shared proof support): bit/byte arithmetic lemmas, global function-pointer helpers ([ge_fn]), fractional read-check rule ([wp_check_read_dq]), and symbolic step tactics ([LibioStepOn]) for userland glibc's `libio` proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_puts_term]) of userland glibc's `c: puts` and `c: fputs`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioRead.v',
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled `__fpending`, `_IO_ferror`, `_IO_file_close`, and `_IO_file_stat` over [file_inv].").
file_blurb('nanofil/rocq/glibc/libio/LibioReadCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_read_term]) of userland glibc's `__fpending`, `_IO_ferror`, `_IO_file_close`, `_IO_file_stat`, `_IO_setb`, `_IO_doallocbuf`, `_IO_file_doallocate`, and `_IO_new_file_write`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioSetb.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_setb]) for userland glibc's compiled `_IO_setb`, freeing an owned prior buffer when `_IO_USER_BUF` is clear and updating buffer pointers and flags.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlink.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_glibc__IO_un_link_unlinked], [wp_glibc__IO_un_link]) for userland glibc's compiled `_IO_un_link` over [io_list_inv].").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_unlink_term]) of userland glibc's `_IO_un_link`, `_IO_new_file_finish`, and `_IO_default_finish`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkLock.v',
    "Live glibc campaign (implementation proof): cleanup-push and stream/list lock acquisition prefix for userland glibc's `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkMid.v',
    "Live glibc campaign (implementation proof): doubly-linked `_IO_list_all` chain splice proof for userland glibc's `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkTail.v',
    "Live glibc campaign (implementation proof): `_IO_LINKED` flag clear, lock release, and NPTL cleanup-pop epilogue for userland glibc's `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioWrite.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc__IO_new_file_write]) and Löb loop invariant ([wp_file_write_loop]) for userland glibc's compiled `_IO_new_file_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteCall.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_file_write_call]) for `_IO_new_file_write`'s loop body invoking `__GI___write` on the remaining slice.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteExit.v',
    "Live glibc campaign (implementation proof): Hoare triples ([wp_file_write_exit], [wp_file_write_err], [wp_file_write_next]) for `_IO_new_file_write`'s loop exit, `_IO_ERR_SEEN` error path, and `_total_written` advance.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([libio_xsputn_term]) of userland glibc's `_IO_new_file_xsputn`, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/SysCleanup.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc___libc_cleanup_push_defer]) for userland glibc's compiled NPTL `__libc_cleanup_push_defer` over `c: zthread_self_cookie()` and [tcb_cleanup_inv].").
file_blurb('nanofil/rocq/glibc/libio/SysCleanupPop.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc___libc_cleanup_pop_restore]) for userland glibc's compiled NPTL `__libc_cleanup_pop_restore`, restoring [tcb_cleanup_inv] from [tcb_pushed].").
file_blurb('nanofil/rocq/glibc/libio/SysCode.v',
    "Live glibc campaign (generated IR fixture): checked nanofil -O IR ([sys_term]) of userland glibc's `__GI__exit`, `__GI___libc_write`, `__GI___fstat64`, `__lseek64`, `__close_nocancel`, `__isatty_nostatus`, and NPTL cleanup push/pop wrappers, generated by `rocq/glibc/libio/code.sh`.").
file_blurb('nanofil/rocq/glibc/libio/SysWrappers.v',
    "Live glibc campaign (implementation proof): Hoare triples for userland glibc's compiled syscall wrapper functions (`__GI__exit`, `__GI___libc_write`, `__GI___fstat64`, `__lseek64`, `__close_nocancel`, `__close_nocancel_nostatus`, and `__isatty_nostatus`) over `rocq/glibc/zsys/`.").

%  Live campaign & worked examples: rocq/glibc/
file_blurb('nanofil/rocq/glibc/GlibcLogic.v',
    "Live glibc campaign (shared proof support): common separation-logic rules and tactics over [Logic](../theories/logic/Logic.v) for compiled glibc IR proofs, including read-only capability raw word loads ([wp_raw_load_read]), initial-memory piece [[adequacy]], and VM-computed step tactics.").
file_blurb('nanofil/rocq/glibc/LenCode.v',
    "Worked example on userland glibc (generated IR fixture): checked nanofil -O IR ([len_term]) of `rocq/glibc/len.c` linked with userland glibc's `string/strlen.os`, generated by `rocq/glibc/code.sh` and imported by [LenLogic](LenLogic.v) and [StrlenLogic](StrlenLogic.v).").
file_blurb('nanofil/rocq/glibc/LenLogic.v',
    "Worked example on userland glibc (example theorem): proves that `rocq/glibc/len.c` (`c: strlen(\"hello, glibc\")`) linked with userland glibc's compiled `strlen` never panics ([len_never_panics]) with zero external contracts.").
file_blurb('nanofil/rocq/glibc/SayCode.v',
    "Worked example on userland glibc (generated IR fixture): checked nanofil -O IR ([say_term]) of `rocq/glibc/say.c` linked with userland glibc's `string/strlen.os` and `io/write.os`, generated by `rocq/glibc/code.sh`.").
file_blurb('nanofil/rocq/glibc/SayLogic.v',
    "Worked example on userland glibc (example theorem): proves safe execution ([say_logic_safe]) of `rocq/glibc/say.c`, which calls `c: write(1, msg, strlen(msg))` for `\"hello, glibc\\n\"` using compiled userland glibc `strlen` and `write` over [OsWrite](zsys/OsWrite.v).").
file_blurb('nanofil/rocq/glibc/StrlenBits.v',
    "Live glibc campaign (reusable arithmetic library): 64-bit word byte-extraction, bit-masking, and popcount lemmas for userland glibc's word-at-a-time string scans and 16-byte pointer alignment.").
file_blurb('nanofil/rocq/glibc/StrlenLogic.v',
    "Live glibc campaign (implementation proof): Hoare triple ([wp_glibc_strlen]) and loop proof ([loop_spec]) for userland glibc's compiled `__strlen` over whole-word objects, used by [LenLogic](LenLogic.v), [SayLogic](SayLogic.v), and [StrlenLoop](string/StrlenLoop.v).").

%  Core framework: rocq/theories/core/
file_blurb('nanofil/rocq/theories/core/Cfg.v',
    "Core framework: control-flow graphs ([func_cfg]), Cooper–Harvey–Kennedy immediate dominators ([cfg_idoms]), and preorder dominator-tree intervals ([dominates_by_interval]), transcribed from cfg.pl.").
file_blurb('nanofil/rocq/theories/core/Extract.v',
    "Core framework: OCaml [[extraction]] of the IR decoder, [[interpreter]] semantics, and [[validator]] ([judge], [judge_valid], [valid_fast]) for the model and validator test drivers (`rocq/extraction/main.ml`).").
file_blurb('nanofil/rocq/theories/core/Ieee.v',
    "Core framework: pure integer-bit-pattern IEEE 754 floating-point arithmetic (`binary32`, `binary64`, and x87 80-bit extended, round-to-nearest ties-to-even), transcribed from ieee.pl.").
file_blurb('nanofil/rocq/theories/core/Maps.v',
    "Core framework: hash-bucketed finite maps keyed by [name] ([[name-map|name_map]]), providing fast lookups proved equivalent to association-list [lookup] on large IR modules.").
file_blurb('nanofil/rocq/theories/core/Memory.v',
    "Core framework: byte memory, object [[region|regions]], capability shadow space ([[aux]]), Fil-C bounds/alignment/permission checks ([access]), and [[fresh]] allocation predicates, transcribed from interp.pl.").
file_blurb('nanofil/rocq/theories/core/Ops.v',
    "Core framework: integer ALU operations, shifts, divisions, conversions, and pointer arithmetic ([op_res]), transcribed from interp.pl with Fil-C's total division semantics.").
file_blurb('nanofil/rocq/theories/core/Run.v',
    "Core framework: whole-module execution ([Driver]), building a module's initial global and function memory and stepping a function call to an [[outcome]] under any [[runtime]] [Runtime].").
file_blurb('nanofil/rocq/theories/core/Runtime.v',
    "Core framework: the [Runtime] module type axiomatizing the Fil-C allocator, `c: free`, and garbage-collector [[poll|safepoints]], together with [InterpRuntime], its proof-checked instantiation for nanofil's [[interpreter]].").
file_blurb('nanofil/rocq/theories/core/Semantics.v',
    "Core framework: small-step operational semantics ([step], [step_rel]) of the [[core subset]] of [[stage|checked IR]] over explicit call stacks and frames, transcribed from interp.pl.").
file_blurb('nanofil/rocq/theories/core/Syntax.v',
    "Core framework: inductive syntax of the [[core subset]] of [[stage|checked IR]] ([inst], [jump], [block], [func], [module]) and its value [[class|classes]], transcribed from ir.pl.").
file_blurb('nanofil/rocq/theories/core/Term.v',
    "Core framework: ground Prolog terms ([term]: integers, atoms, compounds, and lists) used as IR identifier names and as the serialization format between the Prolog compiler and the Rocq model.").
file_blurb('nanofil/rocq/theories/core/Transport.v',
    "Core framework: [[transport]] decoders ([decode_module]) from Prolog [term]s to [Syntax](Syntax.v) ASTs and encoders of model [[outcome|outcomes]] back to Prolog terms for differential and [[mutant]] testing.").
file_blurb('nanofil/rocq/theories/core/ValidFast.v',
    "Core framework: fast [[validator]] implementation ([valid_fast]) using [[name-map|name_map]] for [[single definition|single-definition]] counting on large functions, proved equivalent ([valid_fast_iff]) to [Validate](Validate.v)'s [valid].").
file_blurb('nanofil/rocq/theories/core/Validate.v',
    "Core framework: the [[stage|checked IR]] [[validator]] ([valid], [valid_func], [valid_data]), transcribed from ir.pl's `valid_module/1` to check SSA dominance, capability checks, [[reuse]] forms, and scheduled checks.").
file_blurb('nanofil/rocq/theories/core/Values.v',
    "Core framework: run-time values ([cap], [ptr], [word]), tracking invisible [[capability|capabilities]] alongside addresses across integer and pointer [[class|classes]] as in interp.pl.").

%  Core framework: rocq/theories/soundness/
file_blurb('nanofil/rocq/theories/soundness/Ahead.v',
    "Core framework (soundness): formalizes the validator's backward dataflow pass ([ahead_justified]) for hoisted [[check_ahead]] instructions and the pending fault obligations ([[need]]) they create.").
file_blurb('nanofil/rocq/theories/soundness/Chain.v',
    "Core framework (soundness): proves that dominant [[single definition|single definitions]] justify the pointer [[offset-interval|offset intervals]], [[guard chain|guard chains]], and pointer distances used by the validator's [[reuse]] rules.").
file_blurb('nanofil/rocq/theories/soundness/Coverage.v',
    "Core framework (soundness): proves the coverage lemma ([covered_access_ok]): any [[raw access]] covered by a passed [[check]] (`covered_access/6`) is in bounds and never produces [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Dominance.v',
    "Core framework (soundness): proves that [Cfg](../core/Cfg.v)'s preorder dominator-tree interval test ([dominates_by_interval]) implies true control-flow path [[dominance]] from function entry.").
file_blurb('nanofil/rocq/theories/soundness/Doomed.v',
    "Core framework (soundness): proves that a [[doomed frame]] created by a failed early [[check_ahead]] executes only [[ahead-transparent]] steps until its own access check traps, never reaching [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Evidence.v',
    "Core framework (soundness): single-instruction soundness of the validator's forward [[evidence pass]] ([checked_inst_rest]), showing that [[live facts]] ([fact_holds]) survive instructions and cover raw accesses.").
file_blurb('nanofil/rocq/theories/soundness/Guard.v',
    "Core framework (soundness): proves soundness of the [[renew_if]] and `check_limit` [[reuse]] forms from dominant [[span test|span tests]] and [[guard chain|guard chains]].").
file_blurb('nanofil/rocq/theories/soundness/Identity.v',
    "Core framework (soundness): proves object-[[identity]] persistence ([persists]) across machine runs—allocated regions are never forgotten or re-allocated at the same base, and freed objects stay [Freed].").
file_blurb('nanofil/rocq/theories/soundness/Interval.v',
    "Core framework (soundness): inductive specification ([iv]) and soundness proof ([offset_interval_iv], [iv_sound]) for the validator's integer [[offset-interval|offset interval]] analysis ([oi]).").
file_blurb('nanofil/rocq/theories/soundness/Invariant.v',
    "Core framework (soundness): states the combined run-level [[evidence]] invariant ([inv]) over active frames and waiting callers, together with the per-step preservation lemmas proved in [Persistence](Persistence.v).").
file_blurb('nanofil/rocq/theories/soundness/Machine.v',
    "Core framework (soundness): couples [Semantics](../core/Semantics.v)'s small-step execution to an arbitrary [Runtime] ([[machine]], [mstep], [run]) and proves that runtime allocation readiness ([[ready]]) is preserved across every step.").
file_blurb('nanofil/rocq/theories/soundness/Persistence.v',
    "Core framework (soundness): proves that the run-level [[evidence]] invariant ([inv]) holds across every machine step of a validated module, so non-doomed frames never perform an [[unchecked]] access ([run_access_not_unchecked]).").
file_blurb('nanofil/rocq/theories/soundness/Renew.v',
    "Core framework (soundness): proves soundness of the [[renew]], [[renew_hull]], and [[half check]] capability-check [[reuse]] forms from dominant earlier checks and pointer distances.").
file_blurb('nanofil/rocq/theories/soundness/Single.v',
    "Core framework (soundness): proves the run-level [[single-definition invariant]] ([sinv]): every replayable single definition whose site dominates the current program point still holds the value its instruction computed.").
file_blurb('nanofil/rocq/theories/soundness/Sites.v',
    "Core framework (soundness): connects [Validate](../core/Validate.v)'s single-definition list ([all_defs]) and strict-[[ssa|SSA]] site check ([temp_sites]) so a single definition's [[site]] dominates every point where its name is read.").
file_blurb('nanofil/rocq/theories/soundness/Soundness.v',
    "Core framework (soundness theorem): assembles Campaign 3's main theorem ([valid_no_unchecked]): if the [[validator]] accepts a module, no [[run]] of it from a [[ready]] state ever steps to [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Steps.v',
    "Core framework (soundness): inversion and frame-preservation lemmas for individual [Semantics](../core/Semantics.v) steps ([step_snapshot], [step_enter], [step_exec_cons], [return_step_next]).").
file_blurb('nanofil/rocq/theories/soundness/Walk.v',
    "Core framework (soundness): connects the validator's block-by-block fold ([evidence_pass]) to the live capability facts holding at each reachable point inside a block ([walks], [relies]).").

%  Core framework: rocq/theories/external/
file_blurb('nanofil/rocq/theories/external/ExternalCalls.v',
    "Core external-call framework: trusted [[external call]] [contract] records (ABI signature, precondition, writable spans, released objects, and postcondition) and finite memory-effect paths ([effects]).").
file_blurb('nanofil/rocq/theories/external/ExternalMachine.v',
    "Core external-call framework: labelled operational [[machine]] ([ExternalMachine]) extending [Machine](../soundness/Machine.v) with external contract invocations, call traces, and world state.").
file_blurb('nanofil/rocq/theories/external/Shutdown.v',
    "Core external-call framework: logical shutdown protocol for registered `c: atexit` / `__cxa_atexit` / `c: on_exit` callbacks, stdout flush obligations, and soft or hard host-exit handoff.").
file_blurb('nanofil/rocq/theories/external/Startup.v',
    "Core external-call framework: entry memory predicates for the Fil-C program launcher (`filc/src/filc_start_program.c`), describing [[capability]]-backed `c: argv` and `c: environ` arrays before `c: main`.").
file_blurb('nanofil/rocq/theories/external/Stdio.v',
    "Core external-call framework: logical stdout protocol tracking ordered output byte obligations, delivery prefixes, and stream error state across external calls.").

%  Core framework: rocq/theories/logic/
file_blurb('nanofil/rocq/theories/logic/ContractFrame.v',
    "Core Iris program logic: framing lemmas ([prefix_agrees_out], [pieces_off]) proving that program-owned memory pieces disjoint from an [[external call]] contract's writable spans and released objects survive the call unchanged.").
file_blurb('nanofil/rocq/theories/logic/Heap.v',
    "Core Iris program logic: instantiates Iris's [gen_heap] over [Pieces](Pieces.v)'s [piece] and [pval], defining the state interpretation [heap_interp] and ghost-heap update lemmas for allocations, stores, and frees.").
file_blurb('nanofil/rocq/theories/logic/Language.v',
    "Core Iris program logic: instantiates Iris's `language` over [ExternalMachine](../external/ExternalMachine.v) with the caller stack as evaluation context ([wp_call_bind]), and proves Iris [[adequacy]] implying [never_panics].").
file_blurb('nanofil/rocq/theories/logic/Logic.v',
    "Core Iris program logic: the main separation-logic functor ([Logic], [LogicSig]), defining points-to assertions ([live], [icell], [pcell], [obj], [bytes], [auxes]) and weakest-precondition rules for every instruction and external call.").
file_blurb('nanofil/rocq/theories/logic/MemLogic.v',
    "Core Iris program logic: byte and [[aux]] block assertions in [Logic](Logic.v) and Hoare triples for contract-based libc memory calls (`c: memset`, `c: memcpy`, `c: memmove`, `c: malloc`, `c: calloc`, `c: free`).").
file_blurb('nanofil/rocq/theories/logic/Panics.v',
    "Core Iris program logic: defines the whole-program safety property [never_panics] (no [[run]] reaches a capability [[trap]], [[unchecked]] access, UB, `unreachable`, or missing contract) and the invariant proof rule [never_panics_by_invariant].").
file_blurb('nanofil/rocq/theories/logic/Pieces.v',
    "Core Iris program logic: the memory resource model ([piece]: object life [PLive], byte [PByte], [[aux]] slot [PAux], and lent-string token [PName]) keyed by object [[identity]], plus memory-agreement lemmas ([agrees]).").
file_blurb('nanofil/rocq/theories/logic/StepRules.v',
    "Core Iris program logic: forward per-instruction symbolic step lemmas for [Semantics](../core/Semantics.v)'s [step], reducing each instruction form from local premises without unfolding the whole module or memory.").
file_blurb('nanofil/rocq/theories/logic/StringLogic.v',
    "Core Iris program logic: C string ownership ([string], [string_suffix], [string_byte]) in [Logic](Logic.v) and Hoare triples for contract-based libc string and output calls (`c: strlen`, `c: strcmp`, `c: strncmp`, `c: strchr`, `c: strrchr`, `c: memchr`, `c: memcmp`, `c: puts`).").
file_blurb('nanofil/rocq/theories/logic/Symbolic.v',
    "Core Iris program logic: Ltac symbolic-execution automation that discharges [StepRules](StepRules.v)'s instruction premises over abstract environments, memories, and [[fuel]].").
file_blurb('nanofil/rocq/theories/logic/VariadicLogic.v',
    "Core Iris program logic: weakest-precondition rules ([wp_snapshot], [wp_va_arg]) for Fil-C's variadic argument [[snapshot]] object ([Snapshot]) and `c: va_arg` pointer reads.").
file_blurb('nanofil/rocq/theories/logic/WordBits.v',
    "Core Iris program logic: general 64-bit little-endian byte extraction ([byte_of]), bitmask, shift, and carry-free addition/subtraction lemmas for word-at-a-time string and memory proofs, promoted from [StrlenBits](../../glibc/StrlenBits.v).").

%  Worked example programs: rocq/theories/programs/
file_blurb('nanofil/rocq/theories/programs/Buffer.v',
    "Worked example program (example theorem): proves [never_panics] for `rocq/theories/programs/buffer.c` (allocating a 4-long heap buffer, filling it, and summing `c: p[i % 4]` up to `n`) by direct 32-point invariant over [Symbolic](../logic/Symbolic.v).").
file_blurb('nanofil/rocq/theories/programs/BufferCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([buffer_term]) of `rocq/theories/programs/buffer.c`, generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/BufferLogic.v',
    "Worked example program (example theorem): proves [buffer_never_panics] for `rocq/theories/programs/buffer.c` in the Iris separation logic of [Logic](../logic/Logic.v) using Löb induction and per-cell heap ownership, contrasting with [Buffer](Buffer.v).").
file_blurb('nanofil/rocq/theories/programs/Composition.v',
    "Worked example program (contract-era lifecycle adapter): couples the capability-backed `stdio_world`, logical stdout protocol, and exit-callback registry into one [program_world] for `tests/c/prog/hi.c`.").
file_blurb('nanofil/rocq/theories/programs/CountCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([count_term]) of `rocq/theories/programs/count.c`, generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/CountLogic.v',
    "Worked example program (example theorem): proves [count_never_panics] for `rocq/theories/programs/count.c` in [Logic](../logic/Logic.v), giving helper `next_l` (`c: strchr` for `'l'`) a reusable Hoare triple and calling it in a loop with suffix borrowing.").
file_blurb('nanofil/rocq/theories/programs/Cycle.v',
    "Worked example program (example theorem): proves [never_panics] for `rocq/theories/programs/cycle.c` (summing `c: xs[i % 4]` from a read-only global array for any trip count `n`) using Floyd inductive assertions and [Symbolic](../logic/Symbolic.v).").
file_blurb('nanofil/rocq/theories/programs/CycleCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([cycle_term]) of `rocq/theories/programs/cycle.c`, generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/Hi.v',
    "Worked example program (contract-era example theorem): proves safety of `tests/c/prog/hi.c` calling `c: puts` against [ExternalCalls](../external/ExternalCalls.v)'s trusted `puts` contract by direct labelled-machine invariant.").
file_blurb('nanofil/rocq/theories/programs/HiArtifact.v',
    "Worked example program (contract-era adapter): proves ([hi_generated_module]) that decoding `rocq/theories/programs/HiCode.v`'s generated `hi_term` yields the exact [hi_module] proved in [Hi](Hi.v).").
file_blurb('nanofil/rocq/theories/programs/HiCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([hi_term]) of `tests/c/prog/hi.c` (`c: puts(\"hi\")`), generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/HiLogic.v',
    "Worked example program (example theorem): proves `tests/c/prog/hi.c` safe in the Iris separation logic of [Logic](../logic/Logic.v) using [StringLogic](../logic/StringLogic.v)'s [wp_puts] triple, contrasting with [Hi](Hi.v).").
file_blurb('nanofil/rocq/theories/programs/Program.v',
    "Worked example program (contract-era lifecycle adapter): composes launcher [Startup](../external/Startup.v), [Hi](Hi.v)'s `c: main` execution, and [Shutdown](../external/Shutdown.v) over the coupled [program_world] of [Composition](Composition.v).").
file_blurb('nanofil/rocq/theories/programs/ScanCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([scan_term]) of `rocq/theories/programs/scan.c`, generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/ScanLogic.v',
    "Worked example program (example theorem): proves [scan_never_panics] for `rocq/theories/programs/scan.c` in [Logic](../logic/Logic.v), chaining contract triples for `c: strlen`, `c: strchr`, and `c: puts` and reading the string suffix after `c: puts` returns.").
file_blurb('nanofil/rocq/theories/programs/SlotCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([slot_term]) of `rocq/theories/programs/slot.c`, generated and checked by `rocq/scripts/programs.sh`.").
file_blurb('nanofil/rocq/theories/programs/SlotLogic.v',
    "Worked example program (example theorem): proves [slot_never_panics] for `rocq/theories/programs/slot.c` in [Logic](../logic/Logic.v), verifying a `quotearg`-style callee (`fill`) that retains, reuses, and reallocates a static heap buffer across calls.").
file_blurb('nanofil/rocq/theories/programs/Sum.v',
    "Worked example program (example theorem): the first closed-module [never_panics] proof, verifying `rocq/theories/programs/sum.c` (summing a 4-element read-only global array) by symbolic execution over [Panics](../logic/Panics.v).").
file_blurb('nanofil/rocq/theories/programs/SumCode.v',
    "Worked example program (generated IR fixture): checked nanofil -O IR ([sum_term]) of `rocq/theories/programs/sum.c`, generated and checked by `rocq/scripts/programs.sh`.").

%  Old reference proof: rocq/theories/hello_contracts/
file_blurb('nanofil/rocq/theories/hello_contracts/CallbackLogic.v',
    "Old Hello reference proof (separation-logic support): Iris [[adequacy]] theorem ([wp_callback_adequate]) bridging a Hoare triple for a registered void exit callback (`close_stdout`) to [Linked](Linked.v)'s callback execution step.").
file_blurb('nanofil/rocq/theories/hello_contracts/Diagnostics.v',
    "Old Hello reference proof (trusted libc contract): contract boundary for gnulib/glibc `c: error` diagnostics, distinguishing status-zero returns from nonzero soft-exit requests.").
file_blurb('nanofil/rocq/theories/hello_contracts/Ending.v',
    "Old Hello reference proof (lifecycle model): intercepts `c: exit` requests at the labelled machine boundary and sequences registered exit callbacks before terminal host exit.").
file_blurb('nanofil/rocq/theories/hello_contracts/ExitMemory.v',
    "Old Hello reference proof (lifecycle model): capability-backed memory layout of userland glibc's `__exit_funcs` callback registry (`c: struct exit_function_list`) for `c: atexit` and `__cxa_atexit`.").
file_blurb('nanofil/rocq/theories/hello_contracts/Formatting.v',
    "Old Hello reference proof (trusted libc contract): contracts for GNU Hello's formatted output calls (`c: printf`, `c: fprintf`, `c: fputs`, `c: putchar`, `c: wprintf`) and format-string validation.").
file_blurb('nanofil/rocq/theories/hello_contracts/Getopt.v',
    "Old Hello reference proof (trusted libc contract): safety contract for `c: getopt_long`, modeling `c: optarg` and `c: optind` updates and argument-string provenance in the composite libc world.").
file_blurb('nanofil/rocq/theories/hello_contracts/GetoptLogic.v',
    "Old Hello reference proof (separation-logic support): ghost-token ownership ([getopt_ps]) and read rules for `c: optarg` and `c: optind` cells updated by [Getopt](Getopt.v)'s `c: getopt_long` contract.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloClose.v',
    "Old Hello reference proof (function proofs): Hoare triples for gnulib's `close_stream` and `close_stdout` exit callback over [LibcStreamAdapter](LibcStreamAdapter.v) and [LibcDiagnosticLogic](LibcDiagnosticLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloCode.v',
    "Old Hello reference proof (generated IR fixture): linked checked nanofil -O IR ([hello_term], 32 reachable functions and data objects) of GNU Hello 2.12.3, generated and checked by `rocq/scripts/hello-fixture.sh`.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConv.v',
    "Old Hello reference proof (function proofs): Hoare triples for `c: mbrtowc` and gnulib's `rpl_mbrtowc` and `rpl_mbsrtowcs` wide-character greeting conversion in [Logic](../logic/Logic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConvDefs.v',
    "Old Hello reference proof (conversion support): pure memory-span lemmas and IR definitions for gnulib's `rpl_mbrtowc` and `rpl_mbsrtowcs`, factored out so [HelloMain](HelloMain.v) and [HelloConv](HelloConv.v) compile in parallel.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloDiagnosticChecks.v',
    "Old Hello reference proof (separation-logic support): discharges the format-string and literal-argument preconditions for GNU Hello's concrete `c: error` diagnostic call sites.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloJoin.v',
    "Old Hello reference proof (main proof, part 2): proves GNU Hello's greeting conversion and `c: wprintf` output path from the greeting join block and combines it with [HelloMain](HelloMain.v) into the full `c: main` triple ([main_spec]).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLeaf.v',
    "Old Hello reference proof (function proofs): Hoare triples for GNU Hello's four gnulib leaf wrappers (`mbszero`, `memeq`, `streq`, and `strnlen1`) in [Logic](../logic/Logic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLocale.v',
    "Old Hello reference proof (function proofs): Hoare triples for gnulib's `setlocale_null_unlocked`, `setlocale_null_r_unlocked`, `setlocale_null_r`, and `hard_locale` over [LocaleLogic](LocaleLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloMain.v',
    "Old Hello reference proof (main proof, part 1): proves GNU Hello's `c: main` from entry through `set_program_name`, `c: setlocale`, `c: getopt_long` option parsing, and `--help` / `--version` exits up to the greeting join block ([main_to_join]).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloModule.v',
    "Old Hello reference proof (module setup): decodes `rocq/theories/hello_contracts/HelloCode.v`'s `hello_term` into [hello_module], checks [valid_fast] ([hello_valid]), and catalogs the module's internal functions and external libc symbols.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloName.v',
    "Old Hello reference proof (function proof): Hoare triple for gnulib's `set_program_name` in [Logic](../logic/Logic.v), covering `c: strrchr`, `\"/.libs/\"` and `\"lt-\"` prefix stripping, and global pointer stores.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloProgName.v',
    "Old Hello reference proof (function proof): strengthens [HelloName](HelloName.v)'s `set_program_name` triple to preserve full C string ownership of `c: argv[0]` and `program_name`.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloReach.v',
    "Old Hello reference proof (reachability check): verifies that `rocq/theories/hello_contracts/HelloCode.v`'s linked `hello_term` is closed under global symbol and callback-pointer references from `c: main`.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloStdio.v',
    "Old Hello reference proof (separation-logic support): Hoare triples for GNU Hello's concrete `c: printf`, `c: fprintf`, `c: fputs`, `c: putchar`, and `c: wprintf` call sites from program-owned string literals.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloVersion.v',
    "Old Hello reference proof (function proofs): Hoare triples for GNU Hello's `print_help` and gnulib's `version_etc_arn`, `version_etc_va`, and `version_etc` using [VariadicLogic](../logic/VariadicLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloWorld.v',
    "Old Hello reference proof (whole-program assembly): constructs a concrete initial [libc_world] witness and entry memory geometry connecting launcher [Startup](../external/Startup.v), [HelloJoin](HelloJoin.v)'s [main_spec], and [HelloClose](HelloClose.v)'s `close_stdout` callback.").
file_blurb('nanofil/rocq/theories/hello_contracts/LentLogic.v',
    "Old Hello reference proof (separation-logic support): ghost-token ownership ([lent]) in [Logic](../logic/Logic.v) for strings lent by the external world, such as `c: setlocale` category names.").
file_blurb('nanofil/rocq/theories/hello_contracts/Libc.v',
    "Old Hello reference proof (trusted libc boundary): assembles the composite libc world ([libc_world]) combining locale, `c: getopt_long`, `c: FILE` streams, `c: errno`, `c: mbrtowc`, and shutdown state.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcDiagnosticLogic.v',
    "Old Hello reference proof (separation-logic support): Hoare triples for returning and non-returning `c: error` diagnostic calls over [Libc](Libc.v)'s composite world.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcErrnoLogic.v',
    "Old Hello reference proof (separation-logic support): Hoare triples for `c: FILE` stream calls (`c: fclose`, `c: ferror`, `c: fflush`) that borrow and return program-owned `c: errno` bytes.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcExit.v',
    "Old Hello reference proof (trusted libc contract): non-returning external-call contract for `c: _exit` over [Libc](Libc.v)'s composite libc world.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamAdapter.v',
    "Old Hello reference proof (separation-logic support): world-interpretation adapter transferring stream handle tokens and `c: errno` ownership into the `close_stdout` exit callback.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamLogic.v',
    "Old Hello reference proof (separation-logic support): world-interpretation framing lemmas keeping program-owned memory pieces separate from private `c: FILE` stream storage in [LibcStreams](LibcStreams.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamTokens.v',
    "Old Hello reference proof (separation-logic support): ghost life-token bookkeeping for `c: stdout` and `c: stderr` handles across `close_stdout` callback teardown.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreams.v',
    "Old Hello reference proof (trusted libc boundary): composite `c: stdout` and `c: stderr` stream contracts over [Libc](Libc.v)'s [libc_world], tying `c: stdout` to [Shutdown](../external/Shutdown.v)'s output obligations.").
file_blurb('nanofil/rocq/theories/hello_contracts/Linked.v',
    "Old Hello reference proof (lifecycle model): labelled-machine execution of registered void exit callbacks (`close_stdout`) popped from [ExitMemory](ExitMemory.v) during shutdown.").
file_blurb('nanofil/rocq/theories/hello_contracts/Locale.v',
    "Old Hello reference proof (trusted libc contract): contract boundary and [locale_world] for `c: setlocale` over glibc's 13 locale categories, lending category name strings to the caller.").
file_blurb('nanofil/rocq/theories/hello_contracts/LocaleLogic.v',
    "Old Hello reference proof (separation-logic support): world interpretation ([locale_wi]) and Hoare triples for `c: setlocale` queries over [Locale](Locale.v) and [LentLogic](LentLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/Streams.v',
    "Old Hello reference proof (trusted libc contract): contracts for `c: FILE` stream queries (`c: ferror`, `c: fileno`, `__freading`) and `c: fclose` over projections of the composite libc world.").

%  Program-logic worked example: rocq/spikes/
file_blurb('nanofil/rocq/spikes/ListSum.v',
    "Worked example (shared setup): decodes `rocq/spikes/ListSumCode.v` and defines the `listsum` and `sum` functions, globals, and initial call frames used by [ListSumLogic](ListSumLogic.v).").
file_blurb('nanofil/rocq/spikes/ListSumCode.v',
    "Worked example (generated IR fixture): checked nanofil -O IR ([listsum_term]) of `rocq/spikes/listsum.c`, generated and checked by `rocq/spikes/code.sh`.").
file_blurb('nanofil/rocq/spikes/ListSumLogic.v',
    "Worked example (program logic): proves `rocq/spikes/listsum.c` using the production [Logic](../theories/logic/Logic.v) framework with modular Hoare triples ([wp_call_bind]) and list-segment Löb induction.").

%  Gallina compiler backend: rocq/backend/
file_blurb('nanofil/rocq/backend/Abi.v',
    "Gallina compiler backend: Fil-C ABI lowering pass ([lower_function], [lower_thunks]), translating checked-IR calls, arguments, returns, and function objects into [Plan](Plan.v) ABI actions to match filc_abi.pl.").
file_blurb('nanofil/rocq/backend/Asm.v',
    "Gallina compiler backend: inductive representation of x86-64 assembly lines ([line], [operand]) and GNU `as` (AT&T syntax) printer matching asm.pl byte for byte.").
file_blurb('nanofil/rocq/backend/AsmTerm.v',
    "Gallina compiler backend: decodes nanofil's asm-terms Prolog line terms into [Asm](Asm.v) assembly lines ([dline]) for differential testing of the assembly printer (`rocq/backend/tests/asm.sh`).").
file_blurb('nanofil/rocq/backend/Compile.v',
    "Gallina compiler backend: top-level Gallina compilation pipelines ([compile], [compile_promoted], [compile_allocated]) chaining promotion, copy propagation, pizlonation, validation, ABI lowering, and stack or register emission.").
file_blurb('nanofil/rocq/backend/Copy.v',
    "Gallina compiler backend: copy and trivial-[[phi]] propagation ([copy_module]) on strict-SSA unchecked IR terms, matching copy.pl.").
file_blurb('nanofil/rocq/backend/Emit.v',
    "Gallina compiler backend: emits the complete x86-64 assembly of a function from its ABI [plan] in stack-homed mode (`--registers=stack`), matching filc_amd64.pl's `function//2`.").
file_blurb('nanofil/rocq/backend/EmitData.v',
    "Gallina compiler backend: emits x86-64 assembly directives for global data objects, thread-local storage, constructor init entries, and symbol aliases, matching filc_amd64.pl.").
file_blurb('nanofil/rocq/backend/EmitInst.v',
    "Gallina compiler backend: emits x86-64 assembly for a single fused instruction, inline capability bounds check, or ABI action in the stack-homed backend.").
file_blurb('nanofil/rocq/backend/EmitModule.v',
    "Gallina compiler backend: assembles the x86-64 output of a whole checked module ([module_lines]) across functions, data objects, aliases, and weak thunks.").
file_blurb('nanofil/rocq/backend/EmitObject.v',
    "Gallina compiler backend: emits Fil-C function objects, symbol getters, and generic/variadic calling-convention entry adapters.").
file_blurb('nanofil/rocq/backend/EmitOps.v',
    "Gallina compiler backend: x86-64 scalar and x87 `c: long double` instruction selection for the stack-homed emitter, matching amd64.pl and filc_amd64.pl.").
file_blurb('nanofil/rocq/backend/EmitThunk.v',
    "Gallina compiler backend: emits x86-64 assembly for weak-symbol resolution thunks from their [Plan](Plan.v) [thunk] descriptions.").
file_blurb('nanofil/rocq/backend/Escape.v',
    "Gallina compiler backend: escape analysis ([alloc_classes]) on unchecked IR terms, identifying local [[alloc]] instructions used only by loads and stores at known constant offsets, matching escape.pl.").
file_blurb('nanofil/rocq/backend/Extract.v',
    "Gallina compiler backend: OCaml extraction of the Gallina backend passes and compilers for the backend differential test driver (`rocq/backend/extraction/main.ml`).").
file_blurb('nanofil/rocq/backend/FrameSlots.v',
    "Gallina compiler backend: first-fit stack-slot allocator ([temp_slots]) over temporary live intervals, sharing frame slots between non-overlapping temporaries of the same pool to match frame_slots.pl.").
file_blurb('nanofil/rocq/backend/Fuse.v',
    "Gallina compiler backend: fuses each capability [[check]] in checked IR with its following raw memory access or call ([fused_blocks]), matching filc_amd64.pl's `fused_blocks/5`.").
file_blurb('nanofil/rocq/backend/IrTerm.v',
    "Gallina compiler backend: total encoders from [Syntax](../theories/core/Syntax.v) checked-IR ASTs back to Prolog [term]s, inverting [Transport](../theories/core/Transport.v)'s decoders.").
file_blurb('nanofil/rocq/backend/IrText.v',
    "Gallina compiler backend: parser for nanofil's textual Prolog-clause IR format (`func/5`, `data/4`, `alias/3`, `context/2`), matching ir_text.pl.").
file_blurb('nanofil/rocq/backend/Layout.v',
    "Gallina compiler backend: stack-frame `%rbp` offset layout, symbol naming ([abi_symbol]), and assembly-line constructors shared by the `Emit*.v` modules.").
file_blurb('nanofil/rocq/backend/Liveness.v',
    "Gallina compiler backend: backward dataflow liveness analysis ([temp_liveness]) over fused basic blocks, computing live-in and live-out temporary ordsets to match cfg.pl.").
file_blurb('nanofil/rocq/backend/Nfb.v',
    "Gallina compiler backend (NFB bytecode): typed NFB bytecode encoder ([encode]) and canonical decoder ([decode]) for [Syntax](../theories/core/Syntax.v) checked-IR modules (`docs/nfb.md`).").
file_blurb('nanofil/rocq/backend/NfbProof.v',
    "Gallina compiler backend (NFB proof): top-level NFB bytecode theorems ([round_trip], [decode_canonical], [decode_identity]), proving canonical encoding and exact round-trip decoding of [Syntax](../theories/core/Syntax.v) modules.").
file_blurb('nanofil/rocq/backend/NfbRead.v',
    "Gallina compiler backend (NFB proof): proves the term-level NFB round-trip theorem ([read_encode_term]): [NfbTerm](NfbTerm.v)'s [read_term] inverts [encode_term] on every valid module term.").
file_blurb('nanofil/rocq/backend/NfbTerm.v',
    "Gallina compiler backend (NFB bytecode): Gallina encoder ([encode_term]) and decoder ([read_term]) for nanofil's binary module bytecode (`docs/nfb.md`) at the Prolog [term] level, matching nfb.pl.").
file_blurb('nanofil/rocq/backend/NfbTotal.v',
    "Gallina compiler backend (NFB proof): proves that [NfbTerm](NfbTerm.v)'s fuel-bounded bytecode readers never exhaust their word-length fuel budget ([sections_fuel], [blocks_fuel]).").
file_blurb('nanofil/rocq/backend/NfbTransport.v',
    "Gallina compiler backend (NFB proof): proves the AST-to-term half of the NFB round trip ([decode_enc_module]): [Transport](../theories/core/Transport.v)'s [decode_module] inverts [Nfb](Nfb.v)'s [enc_module].").
file_blurb('nanofil/rocq/backend/Order.v',
    "Gallina compiler backend: implements Prolog's standard term ordering (`sort/2`, `msort/2`, and `library(ordsets)`) on [Term](../theories/core/Term.v) so backend passes match the Prolog compiler's ordering.").
file_blurb('nanofil/rocq/backend/Pizlonate.v',
    "Gallina compiler backend: lowers unchecked IR terms to [[stage|checked]] capability IR ([pizlonate_module]), inserting capability bounds checks, [[flight|flights]], and back-edge GC [[poll|polls]] to match pizlonate.pl.").
file_blurb('nanofil/rocq/backend/Plan.v',
    "Gallina compiler backend: data types for a function's Fil-C ABI lowering plan ([plan], [thunk]), representing frame slot pools, fused checks, and ABI call/return actions before register assignment.").
file_blurb('nanofil/rocq/backend/PlanTerm.v',
    "Gallina compiler backend: encodes [Plan](Plan.v) ABI plans ([plan_term]) and weak thunks ([thunks_term]) as Prolog [term]s for differential testing against filc_abi.pl (`rocq/backend/tests/abi.sh`).").
file_blurb('nanofil/rocq/backend/Promote.v',
    "Gallina compiler backend: SSA slot promotion ([promote_module], pruned SSA) on unchecked IR terms, promoting non-escaping local allocations ([Escape](Escape.v)) into temporaries and [[phi]] nodes to match promote.pl.").
file_blurb('nanofil/rocq/backend/Regs.v',
    "Gallina compiler backend: loop-weighted interval register allocator ([alloc_regs]), executable allocation validator ([valid_alloc]), parallel-move [[phi]] resolver, and direct register assembly emitter (`docs/gallina-backend.md`, M7).").
file_blurb('nanofil/rocq/backend/RegsProof.v',
    "Gallina compiler backend (allocator proofs): kernel-checked proofs for [Regs](Regs.v)'s [valid_alloc] multi-block CFG trace simulation, [compile_pmoves] parallel-move compiler, and [build_rctx] frame/save/root invariants.").
file_blurb('nanofil/rocq/backend/TermCfg.v',
    "Gallina compiler backend: control-flow graph ([term_cfg]), reverse postorder, dominance frontiers ([cfg_frontiers]), and def/use sets for unchecked IR represented as [Term](../theories/core/Term.v) terms.").
file_blurb('nanofil/rocq/backend/Text.v',
    "Gallina compiler backend: difference-list string buffer ([parts]) used by the assembly printer to emit large `.s` files without quadratic string concatenation.").

%  Gallina compiler backend extraction: rocq/backend/crane/
file_blurb('nanofil/rocq/backend/crane/CraneExtract.v',
    "Gallina compiler backend (C++ extraction): extracts the Gallina backend ([Compile](../Compile.v) and [IrText](../IrText.v)) to C++ via Bloomberg's Crane (`rocq/backend/crane/Makefile`, `docs/gallina-backend.md`).").
file_blurb('nanofil/rocq/backend/crane/CraneMap.v',
    "Gallina compiler backend (C++ extraction): maps Rocq [Z], [N], [positive], [nat], [ascii], and `string` types and operations onto the C++ `rocq/backend/crane/nfrt.h` runtime for Crane extraction.").
file_blurb('nanofil/rocq/backend/crane/CraneSelfTest.v',
    "Gallina compiler backend (C++ extraction test): generates `vm_compute` reference values ([expected]) across boundary integer widths to test [CraneMap](CraneMap.v)'s C++ runtime primitives (`rocq/backend/crane/selftest.cpp`).").

%  λANF lowering campaign: anf/lower/ & anf/lower/tests/
file_blurb('nanofil/anf/lower/AnfExtract.v',
    "λANF lowering campaign: extracts `anf/lower/AnfLower.v`'s [lower] and [IrText](../../rocq/backend/IrText.v) to OCaml for the λANF compiler driver (`anf/lower/main.ml`).").
file_blurb('nanofil/anf/lower/AnfLower.v',
    "λANF lowering campaign: lowers CertiRocq's closure-converted λANF IR (`-O 1 --anf-variant 8`) to [[stage|checked]] nanofil IR ([lower]) over a 32-bit tagged-word arena (`docs/lambda-anf.md`, M2).").
file_blurb('nanofil/anf/lower/tests/Programs.v',
    "λANF lowering campaign (gate test suite): M2 gate test programs ([demo1_out], [demo2_out], [list_sum_out], [vs_easy_out], [vs_hard_out], [binom_out], [color_out], [clos_out], [rec_clos_out], [sha_fast_out], plus [Asm](../../../rocq/backend/Asm.v) and [Order](../../../rocq/backend/Order.v) tests).").
file_blurb('nanofil/anf/lower/tests/Ref.v',
    "λANF lowering campaign (gate test reference): extracts each gate program in `anf/lower/tests/Programs.v` directly to OCaml so its output bytes serve as the ground-truth reference for the arena build.").
file_blurb('nanofil/anf/lower/tests/Show.v',
    "λANF lowering campaign (gate test support): serializes test program results as byte lists ([out]) so arena-compiled binaries and OCaml reference programs can be compared byte for byte.").
file_blurb('nanofil/anf/lower/tests/Tap.v',
    "λANF lowering campaign (gate test harness): invokes `CertiRocq Show IR -O 1 --anf-variant 8` on each gate program in `anf/lower/tests/Programs.v` to dump λANF clauses for [lower].").
