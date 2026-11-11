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
    "Reference proof: GNU Hello over per-function libc contracts",
    ( "Retained Campaign 4/7 reference proof of GNU Hello 2.12.3 against per-function libc contracts (",
      el(a, none, [href="../docs/libc-contracts.html"], "libc-contracts.md"),
      "), kept compiled and gated while the ", el(code, none, "rocq/glibc/"),
      " campaign replaces those libc contracts with compiled userland glibc IR." ),
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

%  rocq/glibc/zsys/
file_blurb('nanofil/rocq/glibc/zsys/OsBlocks.v',
    "Packages contiguous byte ranges and their [[aux]] capability slots as borrowable blocks ([blk_any], [errno_any]) that external calls can overwrite and return.").
file_blurb('nanofil/rocq/glibc/zsys/OsClose.v',
    "Trusted contract and weakest-precondition rule for `c: zsys_close`, probed by [zsys-close.c](zsys-close.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsExit.v',
    "Non-returning contracts and weakest-precondition rules for `c: zsys_exit_soft` and `c: zsys_exit_hard`, probed by [zsys-exit.c](zsys-exit.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsFstat.v',
    "Trusted contract and weakest-precondition rule for `c: zsys_fstat`, borrowing the caller's 144-byte `c: struct stat` buffer and `c: errno`.").
file_blurb('nanofil/rocq/glibc/zsys/OsIoctl.v',
    "Trusted contract and weakest-precondition rule for variadic `c: zsys_ioctl`, audited against `c: filc_call_syscall_with_guarded_ptr`.").
file_blurb('nanofil/rocq/glibc/zsys/OsLseek.v',
    "Trusted contract and weakest-precondition rule for `c: zsys_lseek`, probed by [zsys-lseek.c](zsys-lseek.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsRegistry.v',
    "Collects the nine `zsys_*` and `c: zthread_self_cookie` contracts together with void-return `c: zmemmove` and `c: zmemset` into [os_registry].").
file_blurb('nanofil/rocq/glibc/zsys/OsThread.v',
    "Trusted contract and weakest-precondition rule for `c: zthread_self_cookie`, returning the calling thread's `c: struct pthread` pointer.").
file_blurb('nanofil/rocq/glibc/zsys/OsWorld.v',
    "Defines the shared thread and descriptor state [os_world], its world interpretation [os_wi], and the call rules [wp_os_call], [wp_os_errno_call], and [wp_os_noreturn].").
file_blurb('nanofil/rocq/glibc/zsys/OsWrite.v',
    "Trusted contract and weakest-precondition rule for `c: zsys_write`, probed by [zsys-write.c](../zsys-write.c).").
file_blurb('nanofil/rocq/glibc/zsys/OsWritev.v',
    "Trusted contract and weakest-precondition rule for scatter-gather `c: zsys_writev`, probed by [zsys-writev.c](zsys-writev.c).").

%  rocq/glibc/string/
file_blurb('nanofil/rocq/glibc/string/MallocCode.v',
    "Generated checked IR ([malloc_term]) of userland glibc's `c: malloc` and `c: free`.").
file_blurb('nanofil/rocq/glibc/string/MemFwdCode.v',
    "Generated checked IR ([memfwd_term]) of userland glibc's `c: memcpy`, `c: mempcpy`, `c: memset`, `c: strdup`, `c: errno`, and `c: ctype` units.").
file_blurb('nanofil/rocq/glibc/string/MemFwdLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: memcpy`, `c: mempcpy`, `c: memset`, and `c: strdup`.").
file_blurb('nanofil/rocq/glibc/string/MemchrFirst.v',
    "Proves the initial unaligned word check at entry to userland glibc's compiled `c: memchr`.").
file_blurb('nanofil/rocq/glibc/string/MemchrLast.v',
    "Proves the final partial-word and loop-exit cases of userland glibc's compiled `c: memchr`.").
file_blurb('nanofil/rocq/glibc/string/MemchrLogic.v',
    "Assembles the Hoare triple for userland glibc's compiled word-at-a-time `c: memchr`.").
file_blurb('nanofil/rocq/glibc/string/MemchrLoop.v',
    "Proves the aligned word-scan loop of userland glibc's compiled `c: memchr`.").
file_blurb('nanofil/rocq/glibc/string/MemcmpCode.v',
    "Generated checked IR ([memcmp_term]) of userland glibc's `c: memcmp`.").
file_blurb('nanofil/rocq/glibc/string/MemcmpLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: memcmp` on fewer than 16 bytes of two objects at any fractional shares.").
file_blurb('nanofil/rocq/glibc/string/MemrchrBits.v',
    "Last-match, leading-zero, and end-mask lemmas for userland glibc's word-at-a-time `c: memrchr`.").
file_blurb('nanofil/rocq/glibc/string/MemrchrCode.v',
    "Generated checked IR ([memrchr_term]) of userland glibc's `c: memrchr`.").
file_blurb('nanofil/rocq/glibc/string/MemrchrLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: memrchr` over a word window and [word_string].").
file_blurb('nanofil/rocq/glibc/string/MemrchrLoop.v',
    "Proves the downward 8-byte word loop of userland glibc's `c: memrchr` at any fractional share.").
file_blurb('nanofil/rocq/glibc/string/MemrchrMask.v',
    "Proves the initial masked last-word check of userland glibc's `c: memrchr`.").
file_blurb('nanofil/rocq/glibc/string/StrchrCode.v',
    "Generated checked IR ([strchr_term]) of userland glibc's `c: strchr`, `c: strchrnul`, `c: strrchr`, `c: memchr`, and `c: strnlen`.").
file_blurb('nanofil/rocq/glibc/string/StrchrnulLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: strchrnul` and `c: strchr` over [word_string] at any fractional share.").
file_blurb('nanofil/rocq/glibc/string/StrcmpBits.v',
    "Bitmask comparison and cross-word byte-difference lemmas for userland glibc's word-at-a-time `c: strcmp`.").
file_blurb('nanofil/rocq/glibc/string/StrcmpCode.v',
    "Generated checked IR ([strcmp_term]) of userland glibc's `c: strcmp`.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLogic.v',
    "Proves the Hoare triple for userland glibc's compiled `c: strcmp` over two [word_string] assertions at any fractional shares.").
file_blurb('nanofil/rocq/glibc/string/StrcmpLoop.v',
    "Proves the aligned and unaligned 8-byte word loops of userland glibc's `c: strcmp`.").
file_blurb('nanofil/rocq/glibc/string/StrlenLoop.v',
    "Proves the inner word-scan loop and popcount tail of userland glibc's `c: strlen` at any fractional share.").
file_blurb('nanofil/rocq/glibc/string/StrlenWord.v',
    "Proves the general Hoare triple for userland glibc's compiled `c: strlen` over a [word_string] at any share.").
file_blurb('nanofil/rocq/glibc/string/StrncmpBits.v',
    "Bounded-length word comparison and byte-difference lemmas for userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpCode.v',
    "Generated checked IR ([strncmp_term]) of userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLogic.v',
    "Proves the Hoare triple for userland glibc's compiled `c: strncmp` over two [word_string] assertions at any fractional shares.").
file_blurb('nanofil/rocq/glibc/string/StrncmpLoop.v',
    "Steps through the unrolled 4-word aligned and unaligned loop bodies of userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrncmpWords.v',
    "Proves the aligned and unaligned word-loop invariants for userland glibc's `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/string/StrnlenLogic.v',
    "Proves the Hoare triple for userland glibc's compiled `c: strnlen` via `c: memchr` over [word_string].").
file_blurb('nanofil/rocq/glibc/string/StrrchrLogic.v',
    "Proves the Hoare triple for userland glibc's compiled `c: strrchr` over [word_string] at any share.").
file_blurb('nanofil/rocq/glibc/string/WordString.v',
    "Defines fractional word-aligned C string ownership [word_string] over the 8-byte words read by glibc's string routines.").

%  rocq/glibc/stdlib/
file_blurb('nanofil/rocq/glibc/stdlib/AllocLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: malloc` and `c: free` over `c: zgc_alloc` and `c: zgc_free`.").
file_blurb('nanofil/rocq/glibc/stdlib/AtexitLogic.v',
    "Proves Hoare triples for userland glibc's exit-handler registration (`c: atexit` and `c: __cxa_atexit`) over the [exit_funcs_inv] table.").
file_blurb('nanofil/rocq/glibc/stdlib/LeavesLogic.v',
    "Proves Hoare triples for userland glibc's compiled `c: errno`, `c: ctype`, locale, and `c: mbsinit` leaf functions.").
file_blurb('nanofil/rocq/glibc/stdlib/StdlibCode.v',
    "Generated checked IR ([stdlib_term]) of userland glibc's `c: malloc`, `c: atexit`, `c: errno`, `c: ctype`, and `c: mbsinit` units.").

%  rocq/glibc/libio/
file_blurb('nanofil/rocq/glibc/libio/ExitRun.v',
    "Proves Hoare triples for userland glibc's compiled `c: exit` and exit-handler runner over `_IO_cleanup` and `c: zsys_exit_soft`.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunCode.v',
    "Generated checked IR ([exit_run_term]) of userland glibc's `__run_exit_handlers` and `c: exit`.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunLoop.v',
    "Proves the LIFO handler-execution loop of userland glibc's exit runner by reverse induction on registered handlers.").
file_blurb('nanofil/rocq/glibc/libio/ExitRunTail.v',
    "Proves the final step of userland glibc's exit runner, flushing open streams via `_IO_cleanup` before calling `c: zsys_exit_soft`.").
file_blurb('nanofil/rocq/glibc/libio/FileInv.v',
    "Defines the 224-byte `c: FILE` layout, the stream invariant [file_inv], the `_IO_list_all` chain invariant, and vtable capability tables.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanup.v',
    "Proves userland glibc's `_IO_cleanup` over [io_list_inv], flushing and unbuffering open streams at process exit.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupCode.v',
    "Generated checked IR ([libio_cleanup_term]) of userland glibc's `_IO_cleanup`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupExit.v',
    "Discharges the `_IO_cleanup` and NPTL cleanup-handler premises for [ExitRunTail](ExitRunTail.v).").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpLock.v',
    "Proves the per-stream lock acquisition step inside `_IO_cleanup`'s unbuffering loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupFpUnlock.v',
    "Proves the per-stream lock release and `_chain` advance ending one pass of `_IO_cleanup`'s loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupLock.v',
    "Proves `list_all_lock` acquisition, head load, and final lock release and cleanup-pop for `_IO_cleanup`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupMode.v',
    "Proves the backup-area check and `_mode` update inside `_IO_cleanup`'s unbuffering loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupPass.v',
    "Proves one full pass of `_IO_cleanup`'s unbuffering loop over an open stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioCleanupStart.v',
    "Proves the `_IO_flush_all` call and cleanup-handler push at entry to `_IO_cleanup`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseIt.v',
    "Proves userland glibc's stream-close helper (`_IO_file_close_maybe_unlink`), which flushes pending output and closes the file descriptor.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItCode.v',
    "Generated checked IR ([libio_close_it_term]) of userland glibc's `_IO_file_close_maybe_unlink` and `_IO_new_file_close_it`.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItEnd.v',
    "Proves the epilogue of `_IO_file_close_maybe_unlink`, releasing the stream buffer and marking the descriptor closed.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseItMid.v',
    "Proves the middle blocks of `_IO_file_close_maybe_unlink`, dispatching the vtable close method and detaching the buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioCloseSteps.v',
    "Shared symbolic-step lemmas and 32-byte cleanup-frame helpers for `libio` close, unlink, and flush proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputn.v',
    "Proves userland glibc's `_IO_default_xsputn` and its loop invariant over the vtable overflow method.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBuf.v',
    "Defines the stream write-buffer state ([wbuf], [wroom]) and vtable overflow premise for string output proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnBytes.v',
    "Proves `_IO_default_xsputn`'s byte-by-byte copy loop for short transfers up to 20 bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnCopy.v',
    "Proves `c: mempcpy` into a stream buffer at an arbitrary offset over `c: zmemmove`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnRoom.v',
    "Proves `_IO_default_xsputn`'s bulk buffer fill via `c: mempcpy` for transfers over 20 bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnSmall.v',
    "Proves `_IO_default_xsputn`'s short-transfer path filling at most 20 bytes of buffer space.").
file_blurb('nanofil/rocq/glibc/libio/LibioDefaultXsputnTail.v',
    "Proves the end of each `_IO_default_xsputn` round, either calling vtable overflow on the next byte or returning.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAlloc.v',
    "Proves userland glibc's `_IO_file_doallocate`, querying `c: fstat` and installing a newly allocated stream buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBase.v',
    "Proves `__gnu_dev_major` and defines the fresh-buffer continuation shared by `_IO_file_doallocate` proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocBuf.v',
    "Proves userland glibc's `_IO_doallocbuf` on a buffered stream, dispatching the vtable `__doallocate` method.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocMode.v',
    "Proves `_IO_file_doallocate`'s character-device and `c: isatty` check that selects line buffering.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocShort.v',
    "Proves `_IO_doallocbuf` on an unbuffered stream, installing the one-byte inline `_shortbuf`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoAllocTail.v',
    "Proves `_IO_file_doallocate`'s buffer allocation via `c: malloc` and installation via `_IO_setb`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWrite.v',
    "Proves userland glibc's `_IO_new_do_write`, which flushes a stream buffer through its vtable write method.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCall.v',
    "Proves the vtable bounds check and indirect write call inside `_IO_new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteCode.v',
    "Generated checked IR ([libio_do_write_term]) of userland glibc's `_IO_new_do_write` and `_IO_new_file_overflow`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteEnd.v',
    "Proves the return path of `_IO_new_do_write`, updating write-end pointers for line-buffered and block-buffered streams.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteRet.v',
    "Proves the column-tracking return join block of `_IO_new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteSetp.v',
    "Proves the write-pointer reset (`_IO_setp`) and stream mode check in `_IO_new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioDoWriteTail.v',
    "Proves the read-pointer reset (`_IO_setg`) after flushing in `_IO_new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFclose.v',
    "Proves userland glibc's compiled `c: fclose` on `c: stdout`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseCode.v',
    "Generated checked IR ([libio_fclose_term]) of userland glibc's `_IO_new_fclose`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseLock.v',
    "Proves single-threaded stream lock acquisition and release for userland glibc's `c: fclose`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFcloseTail.v',
    "Proves the stream-unlinking and vtable finish epilogue of `c: fclose` on static `c: stdout`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFinish.v',
    "Proves userland glibc's vtable finish methods on a closed, unlinked stream.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlush.v',
    "Proves userland glibc's `_IO_flush_all` by induction over the `_IO_list_all` stream chain.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushBody.v',
    "Defines the per-stream flush invariant and proves one pass of `_IO_flush_all`'s loop for streams at exit.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushClean.v',
    "Proves the clean-stream path of `_IO_flush_all` when no buffered output needs flushing.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushCode.v',
    "Generated checked IR ([libio_flush_term]) of userland glibc's `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpLock.v',
    "Proves per-stream lock acquisition in one pass of `_IO_flush_all`'s loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushFpUnlock.v',
    "Proves per-stream lock release and `_chain` advance ending one pass of `_IO_flush_all`'s loop.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOver.v',
    "Proves one pass of `_IO_flush_all` on a stream with pending buffered output.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushOverCall.v',
    "Proves the vtable check and indirect overflow call inside `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushStart.v',
    "Proves the cleanup-handler push and `list_all_lock` acquisition at entry to `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFlushTail.v',
    "Proves the `list_all_lock` release, cleanup-handler pop, and return of `_IO_flush_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputs.v',
    "Proves userland glibc's compiled `c: fputs` over a [word_string] at any fractional share.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsCall.v',
    "Proves stream orientation and the indirect `xsputn` vtable call inside `c: fputs`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsLock.v',
    "Proves the `c: strlen` call and stream lock acquisition at entry to `c: fputs`.").
file_blurb('nanofil/rocq/glibc/libio/LibioFputsUnlock.v',
    "Proves stream lock release and return for userland glibc's `c: fputs`.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenCode.v',
    "Generated checked IR ([libiogen_term]) of userland glibc's `__overflow`, `_IO_default_xsputn`, `_IO_unsave_markers`, and `__call_tls_dtors`.").
file_blurb('nanofil/rocq/glibc/libio/LibioGenLeaves.v',
    "Proves userland glibc's `__call_tls_dtors` and `_IO_unsave_markers` leaf helpers.").
file_blurb('nanofil/rocq/glibc/libio/LibioLogic.v',
    "Shared arithmetic lemmas, function-pointer lookup helpers, and symbolic step tactics for `libio` proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflow.v',
    "Proves userland glibc's `_IO_new_file_overflow` on a stream with an active write buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAlloc.v',
    "Proves userland glibc's `_IO_new_file_overflow` when allocating a stream's buffer on first write.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowAllocSetg.v',
    "Proves `_IO_new_file_overflow`'s first-write buffer allocation via `_IO_doallocbuf` and read-pointer setup.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowBase.v',
    "Defines the put-area state and return relation shared across the `_IO_new_file_overflow` proof modules.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowCall.v',
    "Proves `_IO_new_file_overflow`'s call to `_IO_new_do_write` flushing pending bytes.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFlush.v',
    "Proves `_IO_new_file_overflow`'s post-store flush and return of the written byte or `c: EOF`.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowFull.v',
    "Proves `_IO_new_file_overflow` when the write buffer is full and must be flushed before storing the new byte.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowGen.v',
    "Proves userland glibc's `__overflow`, orienting the stream to byte mode and dispatching the vtable overflow method.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowPut.v',
    "Proves `_IO_new_file_overflow`'s byte store at `_IO_write_ptr` and newline/unbuffered flush check.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSend.v',
    "Proves `_IO_new_file_overflow`'s dispatch between flushing on `c: EOF` and storing a character.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetp.v',
    "Proves the first half of `_IO_new_file_overflow`'s transition into put mode, initializing write pointers.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpEnd.v',
    "Proves `_IO_new_file_overflow`'s backup-area check and line-buffered write-end adjustment.").
file_blurb('nanofil/rocq/glibc/libio/LibioOverflowSetpRest.v',
    "Proves the second half of `_IO_new_file_overflow`'s transition into put mode, setting `_IO_CURRENTLY_PUTTING`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPuts.v',
    "Proves userland glibc's compiled `c: puts` over a [word_string] at any fractional share and `c: stdout`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsBuf.v',
    "Proves write-pointer bounds and the direct trailing-newline store in `c: puts`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsCall.v',
    "Proves the vtable check and indirect `_IO_new_file_xsputn` call inside `c: puts`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsCode.v',
    "Generated checked IR ([libio_puts_term]) of userland glibc's `c: puts` and `c: fputs`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsInv.v',
    "Defines the stream state [file_at] and vtable method premises shared by the `c: puts` and `c: fputs` proofs.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsLock.v',
    "Proves the `c: strlen` call and `c: stdout` lock acquisition at entry to `c: puts`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsMode.v',
    "Proves the narrow-stream orientation check in `c: puts`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsNl.v',
    "Proves the trailing newline emission in `c: puts`, either buffered directly or flushed via `__overflow`.").
file_blurb('nanofil/rocq/glibc/libio/LibioPutsUnlock.v',
    "Proves `c: stdout` lock release and return for userland glibc's `c: puts`.").
file_blurb('nanofil/rocq/glibc/libio/LibioRead.v',
    "Proves userland glibc's compiled `c: __fpending`, `c: ferror`, `_IO_file_close`, and `_IO_file_stat` over [file_inv].").
file_blurb('nanofil/rocq/glibc/libio/LibioReadCode.v',
    "Generated checked IR ([libio_read_term]) of userland glibc's `__fpending`, `_IO_ferror`, `_IO_file_close`, `_IO_file_stat`, `_IO_setb`, `_IO_doallocbuf`, `_IO_file_doallocate`, and `_IO_new_file_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioSetb.v',
    "Proves userland glibc's `_IO_setb`, freeing an owned buffer when `_IO_USER_BUF` is clear and updating buffer pointers.").
file_blurb('nanofil/rocq/glibc/libio/LibioStdfiles.v',
    "Proves userland glibc's `_IO_stdfiles_init` constructor, linking `c: stderr`, `c: stdout`, and `c: stdin` into `_IO_list_all`.").
file_blurb('nanofil/rocq/glibc/libio/LibioStdfilesCode.v',
    "Generated checked IR ([libiostdfiles_term]) of userland glibc's `_IO_stdfiles_init` constructor.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlink.v',
    "Proves userland glibc's `_IO_un_link`, removing a stream from the global `_IO_list_all` chain.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkCode.v',
    "Generated checked IR ([libio_unlink_term]) of userland glibc's `_IO_un_link`, `_IO_new_file_finish`, and `_IO_default_finish`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkLock.v',
    "Proves the cleanup-push and lock acquisition prefix of `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkMid.v',
    "Proves the doubly-linked `_IO_list_all` pointer splice inside `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioUnlinkTail.v',
    "Proves the flag-clearing, lock release, and cleanup-pop epilogue of `_IO_un_link`.").
file_blurb('nanofil/rocq/glibc/libio/LibioWrite.v',
    "Proves userland glibc's `_IO_new_file_write` and its write-retry loop over `c: write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteCall.v',
    "Proves a single iteration of `_IO_new_file_write`'s loop calling `c: write` on the remaining byte slice.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteCallDq.v',
    "Proves fractional-share `c: write` calls for `_IO_new_file_write` over shared or read-only caller buffers.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteDq.v',
    "Proves `_IO_new_file_write` over a caller buffer owned at any fractional share, as used by `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/LibioWriteExit.v',
    "Proves the loop exit, error-flag path, and byte-count advance of `_IO_new_file_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputn.v',
    "Proves userland glibc's `_IO_new_file_xsputn`, combining buffered prefix copies, direct block writes, and vtable overflow.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnBase.v',
    "Defines the stream field invariant, newline scan, and `_IO_default_xsputn` hand-off for `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCall.v',
    "Proves the indirect vtable write call inside `_IO_new_file_xsputn`'s inlined `new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnCode.v',
    "Generated checked IR ([libio_xsputn_term]) of userland glibc's `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnDo.v',
    "Proves `_IO_new_file_xsputn`'s direct-write path bypassing the stream buffer for large transfers.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnEnter.v',
    "Proves `_IO_new_file_xsputn`'s initial calculation of how many bytes fit in the current write buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFill.v',
    "Proves `_IO_new_file_xsputn`'s `c: mempcpy` copy of bytes that fit into the stream's write buffer.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlags.v',
    "Proves the write-end pointer selection from `_IO_LINE_BUF` and `_IO_UNBUFFERED` inside `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnFlush.v',
    "Proves `_IO_new_file_xsputn`'s buffer flush through vtable overflow on `c: EOF`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnReset.v',
    "Proves the `_IO_setg` and `_IO_setp` pointer resets inside `_IO_new_file_xsputn`'s inlined `new_do_write`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnSetp.v',
    "Proves the write-end store after `new_do_write` and hand-off of remaining bytes in `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/LibioXsputnWrite.v',
    "Proves the block-aligned byte count calculation for direct writes in `_IO_new_file_xsputn`.").
file_blurb('nanofil/rocq/glibc/libio/SysCleanup.v',
    "Proves userland glibc's NPTL cleanup-handler push (`__libc_cleanup_push_defer`) over `c: zthread_self_cookie`.").
file_blurb('nanofil/rocq/glibc/libio/SysCleanupPop.v',
    "Proves userland glibc's NPTL cleanup-handler pop (`__libc_cleanup_pop_restore`), restoring the thread cleanup chain.").
file_blurb('nanofil/rocq/glibc/libio/SysCode.v',
    "Generated checked IR ([sys_term]) of userland glibc's syscall wrappers (`c: _exit`, `c: write`, `c: fstat`, `c: lseek`, `c: close`, `c: isatty`) and NPTL cleanup helpers.").
file_blurb('nanofil/rocq/glibc/libio/SysWrappers.v',
    "Proves userland glibc's thin syscall wrappers (`c: _exit`, `c: write`, `c: fstat`, `c: lseek`, `c: close`, `c: isatty`) over `rocq/glibc/zsys/`.").

%  rocq/glibc/hello/
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcLeaf.v',
    "Proves GNU Hello's leaf helpers (`mbszero`, `strnlen1`, `streq`, `memeq`) linked against userland glibc.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgCells.v',
    "Defines the global pointer cells and slash-scanning helpers for GNU Hello's `set_program_name`.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgClosed.v',
    "Proves GNU Hello's `set_program_name` and `memeq` linked against userland glibc's `c: memrchr` and `c: memcmp` with no remaining callee premises.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgLibs.v',
    "Proves the `\"/.libs/\"` and `\"lt-\"` prefix-stripping path of GNU Hello's `set_program_name` over compiled glibc `c: strncmp`.").
file_blurb('nanofil/rocq/glibc/hello/HelloGlibcProgName.v',
    "Proves the full Hoare triple for GNU Hello's `set_program_name` linked against userland glibc's `c: strrchr` and `c: strncmp`.").

%  rocq/glibc/
file_blurb('nanofil/rocq/glibc/GlibcLogic.v',
    "Shared separation-logic rules and VM-computed step tactics for proofs over compiled userland glibc IR.").
file_blurb('nanofil/rocq/glibc/LenLogic.v',
    "Worked example proving that `len.c` (`c: strlen(\"hello, glibc\")`) linked with compiled glibc `c: strlen` never panics.").
file_blurb('nanofil/rocq/glibc/SayLogic.v',
    "Worked example proving `say.c` (`c: write(1, msg, strlen(msg))`) linked with compiled glibc `c: strlen` and `c: write` over [OsWrite](zsys/OsWrite.v).").
file_blurb('nanofil/rocq/glibc/StrlenBits.v',
    "Word-level byte extraction, bit-masking, and popcount lemmas for glibc's word-at-a-time string scans.").
file_blurb('nanofil/rocq/glibc/StrlenLogic.v',
    "Proves the Hoare triple and loop invariant for userland glibc's compiled `c: strlen` over whole-word objects.").

%  rocq/theories/core/
file_blurb('nanofil/rocq/theories/core/Cfg.v',
    "Control-flow graphs, Cooper–Harvey–Kennedy immediate dominators, and preorder dominator-tree intervals, transcribed from `cfg.pl`.").
file_blurb('nanofil/rocq/theories/core/Extract.v',
    "OCaml [[extraction]] of the IR decoder, [[interpreter]] semantics, and [[validator]] for the model and validator test drivers.").
file_blurb('nanofil/rocq/theories/core/Ieee.v',
    "Pure integer-bit-pattern IEEE 754 floating-point arithmetic (`binary32`, `binary64`, and x87 80-bit extended), transcribed from `ieee.pl`.").
file_blurb('nanofil/rocq/theories/core/Maps.v',
    "Hash-bucketed finite maps keyed by IR [name] ([[name-map|name_map]]), proved equivalent to association-list [lookup].").
file_blurb('nanofil/rocq/theories/core/Memory.v',
    "Byte memory, object [[region|regions]], [[aux]] capability slots, Fil-C bounds and alignment checks ([access]), and [[fresh]] allocations.").
file_blurb('nanofil/rocq/theories/core/Ops.v',
    "Integer ALU operations, shifts, divisions, conversions, and pointer arithmetic ([op_res]), transcribed from `interp.pl`.").
file_blurb('nanofil/rocq/theories/core/Run.v',
    "Builds a module's initial memory and steps a function call to an [[outcome]] under any [Runtime] implementation.").
file_blurb('nanofil/rocq/theories/core/Runtime.v',
    "Axiomatizes the Fil-C allocator, `c: free`, and garbage-collector [[poll|safepoints]] as `Module Type Runtime`, and instantiates it for nanofil's [[interpreter]].").
file_blurb('nanofil/rocq/theories/core/Semantics.v',
    "Small-step operational semantics ([step]) of the [[core subset]] of [[stage|checked IR]] over explicit call stacks and frames.").
file_blurb('nanofil/rocq/theories/core/Syntax.v',
    "Inductive syntax of the [[core subset]] of [[stage|checked IR]] ([inst], [jump], [block], [func], [module]) and its value [[class|classes]].").
file_blurb('nanofil/rocq/theories/core/Term.v',
    "Ground Prolog terms ([term]) used as IR identifier names and as the serialization format between Prolog and Rocq.").
file_blurb('nanofil/rocq/theories/core/Transport.v',
    "Decodes Prolog [term] representations into [Syntax](Syntax.v) ASTs and encodes model [[outcome|outcomes]] back to Prolog terms.").
file_blurb('nanofil/rocq/theories/core/ValidFast.v',
    "Fast [[validator]] implementation ([valid_fast]) using [[name-map|name_map]] for [[single definition|single-definition]] lookup, proved equivalent to [valid].").
file_blurb('nanofil/rocq/theories/core/Validate.v',
    "The [[stage|checked IR]] [[validator]] ([valid]), checking SSA dominance, capability checks, [[reuse]] forms, and scheduled checks.").
file_blurb('nanofil/rocq/theories/core/Values.v',
    "Run-time values ([cap], [ptr], [word]) pairing addresses with invisible [[capability|capabilities]] across integer and pointer [[class|classes]].").

%  rocq/theories/soundness/
file_blurb('nanofil/rocq/theories/soundness/Ahead.v',
    "Formalizes the validator's backward dataflow pass ([ahead_justified]) for hoisted [[check_ahead]] instructions and their pending obligations ([[need]]).").
file_blurb('nanofil/rocq/theories/soundness/Chain.v',
    "Proves that dominating [[single definition|single definitions]] justify the [[offset-interval|offset intervals]], [[guard chain|guard chains]], and pointer distances used by check reuse.").
file_blurb('nanofil/rocq/theories/soundness/Coverage.v',
    "Proves [covered_access_ok]: any [[raw access]] covered by a passed [[check]] is in bounds and never produces [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Dominance.v',
    "Proves that [Cfg](../core/Cfg.v)'s preorder dominator-tree interval test implies true control-flow path [[dominance]] from function entry.").
file_blurb('nanofil/rocq/theories/soundness/Doomed.v',
    "Proves that a [[doomed frame]] from a failed early [[check_ahead]] executes only transparent steps until its own access traps, never reaching [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Evidence.v',
    "Single-instruction soundness of the forward [[evidence pass]], showing that [[live facts]] survive instructions and cover raw accesses.").
file_blurb('nanofil/rocq/theories/soundness/Guard.v',
    "Proves soundness of the [[renew_if]] and [[limit|check_limit]] reuse forms from dominating [[span test|span tests]] and [[guard chain|guard chains]].").
file_blurb('nanofil/rocq/theories/soundness/Identity.v',
    "Proves object-[[identity]] persistence ([persists]) across runs: allocated regions are never reused at the same base, and freed objects stay freed.").
file_blurb('nanofil/rocq/theories/soundness/Interval.v',
    "Proves soundness of the validator's integer [[offset-interval|offset interval]] analysis ([offset_interval_iv], [iv_sound]).").
file_blurb('nanofil/rocq/theories/soundness/Invariant.v',
    "States the run-level [[evidence]] invariant ([inv]) across the active frame and waiting callers.").
file_blurb('nanofil/rocq/theories/soundness/Machine.v',
    "Couples [Semantics](../core/Semantics.v)'s small-step execution to an arbitrary [Runtime] ([mstep]) and proves that allocation readiness ([[ready]]) is preserved.").
file_blurb('nanofil/rocq/theories/soundness/Persistence.v',
    "Proves that the [[evidence]] invariant [inv] holds across every machine step, so non-doomed frames never perform an [[unchecked]] access.").
file_blurb('nanofil/rocq/theories/soundness/Renew.v',
    "Proves soundness of the [[renew]], [[renew_hull]], and [[half check]] reuse forms from dominating earlier checks and pointer distances.").
file_blurb('nanofil/rocq/theories/soundness/Single.v',
    "Proves the [[single-definition invariant]] ([sinv]): every dominating single definition still holds the value its instruction computed.").
file_blurb('nanofil/rocq/theories/soundness/Sites.v',
    "Connects [Validate](../core/Validate.v)'s single-definition table and strict-[[ssa|SSA]] site check so each single definition's [[site]] dominates its uses.").
file_blurb('nanofil/rocq/theories/soundness/Soundness.v',
    "Proves the main validator soundness theorem ([valid_no_unchecked]): a module accepted by the [[validator]] never steps to [[unchecked]].").
file_blurb('nanofil/rocq/theories/soundness/Steps.v',
    "Inversion and frame-preservation lemmas for individual [Semantics](../core/Semantics.v) steps.").
file_blurb('nanofil/rocq/theories/soundness/Walk.v',
    "Connects the validator's block-by-block fold ([evidence_pass]) to the live capability facts holding at each point inside a block.").

%  rocq/theories/external/
file_blurb('nanofil/rocq/theories/external/ExternalCalls.v',
    "Defines trusted [[external call]] [contract] records (ABI, precondition, writable spans, released objects, postcondition) and memory-effect paths ([effects]).").
file_blurb('nanofil/rocq/theories/external/ExternalMachine.v',
    "Extends [Machine](../soundness/Machine.v) with external contract invocations, call traces, and external world state.").
file_blurb('nanofil/rocq/theories/external/Shutdown.v',
    "Models the shutdown protocol for registered `c: atexit` callbacks, `c: stdout` flush obligations, and process exit.").
file_blurb('nanofil/rocq/theories/external/Startup.v',
    "Models initial memory layout from the Fil-C launcher (`filc_start_program.c`), with capability-backed `c: argv` and `c: environ` arrays.").
file_blurb('nanofil/rocq/theories/external/Stdio.v',
    "Logical `c: stdout` protocol tracking ordered output bytes and stream error state across external calls.").

%  rocq/theories/logic/
file_blurb('nanofil/rocq/theories/logic/ContractFrame.v',
    "Proves the separation-logic frame rule for [[external call|external calls]], showing that caller-owned memory outside borrowed buffers survives a call unchanged.").
file_blurb('nanofil/rocq/theories/logic/Heap.v',
    "Instantiates Iris's ghost heap over [Pieces](Pieces.v), defining the state interpretation [heap_interp] and update lemmas for allocations, stores, and frees.").
file_blurb('nanofil/rocq/theories/logic/Language.v',
    "Turns [ExternalMachine](../external/ExternalMachine.v) into an Iris language with the call stack as evaluation context, and proves that Iris [[adequacy]] implies [never_panics].").
file_blurb('nanofil/rocq/theories/logic/Logic.v',
    "Defines the separation-logic assertions ([live], [icell], [pcell], [obj]) and weakest-precondition rules for every checked-IR instruction and external call.").
file_blurb('nanofil/rocq/theories/logic/MemLogic.v',
    "Defines byte and [[aux]] block assertions in [Logic](Logic.v) and derives Hoare triples for contract-based libc memory calls (`c: memset`, `c: memcpy`, `c: malloc`, `c: free`).").
file_blurb('nanofil/rocq/theories/logic/Panics.v',
    "Defines the whole-program safety property [never_panics] (no run reaches a capability [[trap]], [[unchecked]] access, or UB) and its invariant proof rule.").
file_blurb('nanofil/rocq/theories/logic/Pieces.v',
    "Splits memory into ownable pieces ([PLive], [PByte], [PAux], [PName]) keyed by object [[identity]] and proves basic memory-agreement facts.").
file_blurb('nanofil/rocq/theories/logic/StepRules.v',
    "Forward per-instruction stepping lemmas for [Semantics](../core/Semantics.v)'s [step], reducing each instruction from local premises without unfolding the whole function.").
file_blurb('nanofil/rocq/theories/logic/StringLogic.v',
    "Defines C string ownership ([string]) in [Logic](Logic.v) and derives Hoare triples for contract-based libc string calls (`c: strlen`, `c: strchr`, `c: puts`).").
file_blurb('nanofil/rocq/theories/logic/Symbolic.v',
    "Ltac symbolic-execution tactics that discharge [StepRules](StepRules.v)'s instruction premises over abstract environments and memories.").
file_blurb('nanofil/rocq/theories/logic/VariadicLogic.v',
    "Weakest-precondition rules ([wp_snapshot], [wp_va_arg]) for Fil-C's variadic argument [[snapshot]] object and `c: va_arg` reads.").
file_blurb('nanofil/rocq/theories/logic/WordBits.v',
    "Little-endian 64-bit word byte extraction ([byte_of]), bitmask, shift, and carry-free arithmetic lemmas for word-at-a-time string proofs.").

%  rocq/theories/programs/
file_blurb('nanofil/rocq/theories/programs/Buffer.v',
    "Proves [never_panics] for `buffer.c` (allocating, filling, and summing a 4-word heap buffer) by a direct 32-point invariant over [Symbolic](../logic/Symbolic.v).").
file_blurb('nanofil/rocq/theories/programs/BufferLogic.v',
    "Proves [buffer_never_panics] for `buffer.c` in Iris separation logic ([Logic](../logic/Logic.v)) for direct comparison with [Buffer](Buffer.v).").
file_blurb('nanofil/rocq/theories/programs/Composition.v',
    "Combines the `stdio_world`, stdout byte protocol, and exit-callback registry into one [program_world] for `hi.c`.").
file_blurb('nanofil/rocq/theories/programs/CountLogic.v',
    "Proves [count_never_panics] for `count.c` in [Logic](../logic/Logic.v), giving helper `next_l` (`c: strchr`) a modular Hoare triple called in a loop.").
file_blurb('nanofil/rocq/theories/programs/Cycle.v',
    "Proves [never_panics] for `cycle.c` (summing `c: xs[i % 4]` for any trip count `n`) using Floyd inductive assertions and [Symbolic](../logic/Symbolic.v).").
file_blurb('nanofil/rocq/theories/programs/Hi.v',
    "Proves `hi.c` (`c: puts(\"hi\")`) against [ExternalCalls](../external/ExternalCalls.v)'s `puts` contract by a direct labelled-machine invariant.").
file_blurb('nanofil/rocq/theories/programs/HiArtifact.v',
    "Checks that decoding `HiCode.v`'s generated IR yields the exact [hi_module] proved in [Hi](Hi.v).").
file_blurb('nanofil/rocq/theories/programs/HiLogic.v',
    "Proves `hi.c` safe in Iris separation logic ([Logic](../logic/Logic.v)) using [StringLogic](../logic/StringLogic.v)'s [wp_puts] triple.").
file_blurb('nanofil/rocq/theories/programs/Program.v',
    "Composes launcher [Startup](../external/Startup.v), [Hi](Hi.v)'s `c: main` execution, and [Shutdown](../external/Shutdown.v) over [Composition](Composition.v).").
file_blurb('nanofil/rocq/theories/programs/ScanLogic.v',
    "Proves [scan_never_panics] for `scan.c` in [Logic](../logic/Logic.v), chaining `c: strlen`, `c: strchr`, and `c: puts`.").
file_blurb('nanofil/rocq/theories/programs/SlotLogic.v',
    "Proves [slot_never_panics] for `slot.c` in [Logic](../logic/Logic.v), verifying a callee that retains and reallocates a static heap buffer across calls.").
file_blurb('nanofil/rocq/theories/programs/Sum.v',
    "Proves [never_panics] for `sum.c` (summing a 4-element read-only global array) by symbolic execution over [Panics](../logic/Panics.v).").

%  rocq/theories/hello_contracts/
file_blurb('nanofil/rocq/theories/hello_contracts/CallbackLogic.v',
    "Bridges a Hoare triple for a registered void exit callback (`close_stdout`) to [Linked](Linked.v)'s callback execution step.").
file_blurb('nanofil/rocq/theories/hello_contracts/Diagnostics.v',
    "External-call contract for gnulib/glibc `c: error` diagnostics, separating status-zero returns from nonzero exit requests.").
file_blurb('nanofil/rocq/theories/hello_contracts/Ending.v',
    "Intercepts `c: exit` requests at the labelled machine boundary and runs registered exit callbacks before process termination.").
file_blurb('nanofil/rocq/theories/hello_contracts/ExitMemory.v',
    "Capability-backed memory layout of glibc's `__exit_funcs` callback table for `c: atexit` and `c: __cxa_atexit`.").
file_blurb('nanofil/rocq/theories/hello_contracts/Formatting.v',
    "External-call contracts for GNU Hello's formatted output calls (`c: printf`, `c: fprintf`, `c: fputs`, `c: putchar`, `c: wprintf`).").
file_blurb('nanofil/rocq/theories/hello_contracts/Getopt.v',
    "External-call contract for `c: getopt_long`, modeling `c: optarg` and `c: optind` updates in the composite libc world.").
file_blurb('nanofil/rocq/theories/hello_contracts/GetoptLogic.v',
    "Ghost-token ownership ([getopt_ps]) and read rules for `c: optarg` and `c: optind` cells updated by [Getopt](Getopt.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloClose.v',
    "Proves Hoare triples for gnulib's `close_stream` and `close_stdout` exit callback over per-function libc stream contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConv.v',
    "Proves Hoare triples for `c: mbrtowc` and gnulib's `rpl_mbrtowc` and `rpl_mbsrtowcs` wide-character greeting conversion.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloConvDefs.v',
    "Shared memory-span lemmas and IR definitions for gnulib's wide-character conversion helpers.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloDiagnosticChecks.v',
    "Discharges format-string and literal-argument preconditions for GNU Hello's concrete `c: error` call sites.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloJoin.v',
    "Proves GNU Hello's greeting conversion and `c: wprintf` output path and combines it with [HelloMain](HelloMain.v) into [main_spec].").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLeaf.v',
    "Proves Hoare triples for GNU Hello's four gnulib leaf helpers (`mbszero`, `memeq`, `streq`, `strnlen1`).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloLocale.v',
    "Proves Hoare triples for gnulib's `setlocale_null` and `hard_locale` wrappers over [LocaleLogic](LocaleLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloMain.v',
    "Proves GNU Hello's `c: main` from entry through `set_program_name`, `c: setlocale`, and `c: getopt_long` option parsing.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloModule.v',
    "Decodes `HelloCode.v` into [hello_module], checks [valid_fast], and lists the module's internal functions and external symbols.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloName.v',
    "Proves the Hoare triple for gnulib's `set_program_name` over per-function libc string contracts.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloProgName.v',
    "Strengthens [HelloName](HelloName.v)'s `set_program_name` triple to preserve full C string ownership of `c: argv[0]` and `program_name`.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloReach.v',
    "Verifies that `HelloCode.v`'s linked IR is closed under global symbol and callback-pointer references from `c: main`.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloStdio.v',
    "Derives Hoare triples for GNU Hello's concrete `c: printf`, `c: fprintf`, `c: fputs`, `c: putchar`, and `c: wprintf` call sites.").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloVersion.v',
    "Proves Hoare triples for GNU Hello's `print_help` and gnulib's `version_etc` functions using [VariadicLogic](../logic/VariadicLogic.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/HelloWorld.v',
    "Constructs the initial [libc_world] witness and entry memory connecting [Startup](../external/Startup.v), [HelloJoin](HelloJoin.v), and [HelloClose](HelloClose.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/LentLogic.v',
    "Ghost-token ownership ([lent]) in [Logic](../logic/Logic.v) for strings lent by the external world, such as `c: setlocale` category names.").
file_blurb('nanofil/rocq/theories/hello_contracts/Libc.v',
    "Assembles the composite per-function libc world ([libc_world]) combining locale, `c: getopt_long`, `c: FILE` streams, `c: errno`, and shutdown state.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcDiagnosticLogic.v',
    "Hoare triples for returning and non-returning `c: error` diagnostic calls over [Libc](Libc.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcErrnoLogic.v',
    "Hoare triples for `c: FILE` stream calls (`c: fclose`, `c: ferror`, `c: fflush`) that borrow and return `c: errno`.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcExit.v',
    "Non-returning external-call contract for `c: _exit` over [Libc](Libc.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamAdapter.v',
    "Transfers stream handle tokens and `c: errno` ownership into the `close_stdout` exit callback.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamLogic.v',
    "Framing lemmas keeping caller-owned memory disjoint from private `c: FILE` stream storage in [LibcStreams](LibcStreams.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreamTokens.v',
    "Ghost token bookkeeping for `c: stdout` and `c: stderr` handles across `close_stdout` callback teardown.").
file_blurb('nanofil/rocq/theories/hello_contracts/LibcStreams.v',
    "Composite `c: stdout` and `c: stderr` stream contracts over [Libc](Libc.v), tying `c: stdout` to [Shutdown](../external/Shutdown.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/Linked.v',
    "Models labelled-machine execution of registered void exit callbacks (`close_stdout`) popped from [ExitMemory](ExitMemory.v) at shutdown.").
file_blurb('nanofil/rocq/theories/hello_contracts/Locale.v',
    "External-call contract and [locale_world] for `c: setlocale` over glibc's 13 locale categories.").
file_blurb('nanofil/rocq/theories/hello_contracts/LocaleLogic.v',
    "World interpretation ([locale_wi]) and Hoare triples for `c: setlocale` queries over [Locale](Locale.v).").
file_blurb('nanofil/rocq/theories/hello_contracts/Streams.v',
    "External-call contracts for `c: FILE` stream queries (`c: ferror`, `c: fileno`, `c: __freading`) and `c: fclose`.").

%  rocq/spikes/
file_blurb('nanofil/rocq/spikes/ListSum.v',
    "Decodes `ListSumCode.v` and sets up the `listsum` and `sum` functions and initial call frames for [ListSumLogic](ListSumLogic.v).").
file_blurb('nanofil/rocq/spikes/ListSumLogic.v',
    "Proves `listsum.c` in [Logic](../theories/logic/Logic.v) with modular Hoare triples ([wp_call_bind]) and list-segment Löb induction.").
file_blurb('nanofil/rocq/spikes/Poison.v',
    "Taint-tracking operational semantics for constant-time verification, modeling secret poison propagation and branch/address leak checks.").
file_blurb('nanofil/rocq/spikes/PoisonSbox.v',
    "Proves constant-time execution (no secret-dependent branch or memory-address leaks) for an S-box lookup example under [Poison](Poison.v).").

%  rocq/backend/
file_blurb('nanofil/rocq/backend/Abi.v',
    "Lowers checked-IR calls, arguments, returns, and function objects into [Plan](Plan.v) Fil-C ABI actions, matching `filc_abi.pl`.").
file_blurb('nanofil/rocq/backend/Asm.v',
    "Inductive representation of x86-64 assembly lines ([line], [operand]) and AT&T syntax printer matching `asm.pl`.").
file_blurb('nanofil/rocq/backend/AsmTerm.v',
    "Decodes Prolog assembly-line terms into [Asm](Asm.v) instructions for differential testing of the assembly printer.").
file_blurb('nanofil/rocq/backend/Compile.v',
    "Top-level Gallina compilation pipelines ([compile], [compile_allocated]) chaining promotion, copy propagation, pizlonation, validation, ABI lowering, and emission.").
file_blurb('nanofil/rocq/backend/Copy.v',
    "Copy and trivial-[[phi]] propagation ([copy_module]) on strict-SSA unchecked IR, matching `copy.pl`.").
file_blurb('nanofil/rocq/backend/Emit.v',
    "Emits the x86-64 assembly of a function from its ABI [plan] in stack-homed mode (`--registers=stack`).").
file_blurb('nanofil/rocq/backend/EmitData.v',
    "Emits x86-64 assembly directives for global data objects, thread-local storage, constructors, and symbol aliases.").
file_blurb('nanofil/rocq/backend/EmitInst.v',
    "Emits x86-64 assembly for a single fused instruction, inline capability bounds check, or ABI action.").
file_blurb('nanofil/rocq/backend/EmitModule.v',
    "Assembles the complete x86-64 output of a checked module ([module_lines]) across functions, data objects, aliases, and thunks.").
file_blurb('nanofil/rocq/backend/EmitObject.v',
    "Emits Fil-C function objects, symbol getters, and generic/variadic calling-convention entry adapters.").
file_blurb('nanofil/rocq/backend/EmitOps.v',
    "Selects x86-64 scalar and x87 `c: long double` instructions for the stack-homed emitter, matching `amd64.pl`.").
file_blurb('nanofil/rocq/backend/EmitThunk.v',
    "Emits x86-64 assembly for weak-symbol resolution thunks from their [Plan](Plan.v) descriptions.").
file_blurb('nanofil/rocq/backend/Escape.v',
    "Escape analysis ([alloc_classes]) identifying local allocations used only by loads and stores at constant offsets, matching `escape.pl`.").
file_blurb('nanofil/rocq/backend/Extract.v',
    "Extracts the Gallina backend passes and compilers to OCaml for differential testing.").
file_blurb('nanofil/rocq/backend/FrameSlots.v',
    "First-fit stack-slot allocator ([temp_slots]) sharing frame slots between non-overlapping temporaries, matching `frame_slots.pl`.").
file_blurb('nanofil/rocq/backend/Fuse.v',
    "Fuses each capability [[check]] in checked IR with its following raw memory access or call ([fused_blocks]).").
file_blurb('nanofil/rocq/backend/IrTerm.v',
    "Encodes [Syntax](../theories/core/Syntax.v) checked-IR ASTs back to Prolog [term]s, inverting [Transport](../theories/core/Transport.v)'s decoder.").
file_blurb('nanofil/rocq/backend/IrText.v',
    "Parses nanofil's textual Prolog-clause IR format (`func/5`, `data/4`, `alias/3`, `context/2`), matching `ir_text.pl`.").
file_blurb('nanofil/rocq/backend/Layout.v',
    "Stack-frame `%rbp` offset layout, symbol naming ([abi_symbol]), and assembly-line helpers shared by the emitter modules.").
file_blurb('nanofil/rocq/backend/Liveness.v',
    "Backward dataflow liveness analysis ([temp_liveness]) over fused basic blocks, matching `cfg.pl`.").
file_blurb('nanofil/rocq/backend/Nfb.v',
    "Typed NFB bytecode encoder ([encode]) and canonical decoder ([decode]) for [Syntax](../theories/core/Syntax.v) modules.").
file_blurb('nanofil/rocq/backend/NfbProof.v',
    "Proves the top-level NFB bytecode round-trip and canonical decoding theorems ([round_trip], [decode_canonical]).").
file_blurb('nanofil/rocq/backend/NfbRead.v',
    "Proves the term-level NFB round-trip theorem ([read_encode_term]): [read_term] inverts [encode_term] on every valid module term.").
file_blurb('nanofil/rocq/backend/NfbTerm.v',
    "Term-level encoder ([encode_term]) and decoder ([read_term]) for nanofil's binary NFB module bytecode, matching `nfb.pl`.").
file_blurb('nanofil/rocq/backend/NfbTotal.v',
    "Proves that [NfbTerm](NfbTerm.v)'s fuel-bounded bytecode readers never exhaust their word-length fuel budget.").
file_blurb('nanofil/rocq/backend/NfbTransport.v',
    "Proves the AST-to-term half of the NFB round trip ([decode_enc_module]), showing [decode_module] inverts [enc_module].").
file_blurb('nanofil/rocq/backend/Order.v',
    "Implements Prolog's standard term ordering (`sort/2`, `msort/2`, and `library(ordsets)`) on [Term](../theories/core/Term.v).").
file_blurb('nanofil/rocq/backend/Pizlonate.v',
    "Lowers unchecked IR terms to [[stage|checked]] capability IR ([pizlonate_module]), inserting bounds checks, [[flight|flights]], and loop [[poll|polls]].").
file_blurb('nanofil/rocq/backend/Plan.v',
    "Data types for a function's Fil-C ABI lowering plan ([plan], [thunk]) before register assignment.").
file_blurb('nanofil/rocq/backend/PlanTerm.v',
    "Encodes [Plan](Plan.v) ABI plans and weak thunks as Prolog [term]s for differential testing against `filc_abi.pl`.").
file_blurb('nanofil/rocq/backend/Promote.v',
    "SSA slot promotion ([promote_module]) turning non-escaping local allocations into temporaries and [[phi]] nodes, matching `promote.pl`.").
file_blurb('nanofil/rocq/backend/Regs.v',
    "Loop-weighted interval register allocator ([alloc_regs]), allocation validator ([valid_alloc]), parallel-move resolver, and register assembly emitter.").
file_blurb('nanofil/rocq/backend/RegsProof.v',
    "Proves [Regs](Regs.v)'s multi-block register-allocation validator ([valid_alloc]), parallel-move compiler ([compile_pmoves]), and frame/root invariants.").
file_blurb('nanofil/rocq/backend/TermCfg.v',
    "Control-flow graph ([term_cfg]), reverse postorder, and dominance frontiers ([cfg_frontiers]) for unchecked IR terms.").
file_blurb('nanofil/rocq/backend/Text.v',
    "Difference-list string buffer ([parts]) used by the assembly printer to emit `.s` files in linear time.").

%  rocq/backend/crane/ & rocq/backend/certirocq/
file_blurb('nanofil/rocq/backend/crane/CraneExtract.v',
    "Extracts the Gallina backend ([Compile](../Compile.v) and [IrText](../IrText.v)) to C++ via Crane.").
file_blurb('nanofil/rocq/backend/crane/CraneMap.v',
    "Maps Rocq integer, natural, character, and string operations onto the C++ `nfrt.h` runtime for Crane extraction.").
file_blurb('nanofil/rocq/backend/crane/CraneSelfTest.v',
    "Generates reference values across boundary integer widths to test [CraneMap](CraneMap.v)'s C++ runtime primitives.").
file_blurb('nanofil/rocq/backend/certirocq/CertiExtract.v',
    "Compiles the Gallina backend ([Compile](../Compile.v) and [IrText](../IrText.v)) to C via CertiRocq.").

%  anf/lower/ & anf/backend/
file_blurb('nanofil/anf/lower/AnfExtract.v',
    "Extracts [AnfLower](AnfLower.v)'s [lower] pass and [IrText](../../rocq/backend/IrText.v) to OCaml for the λANF compiler driver.").
file_blurb('nanofil/anf/lower/AnfLower.v',
    "Lowers CertiRocq's closure-converted λANF IR to [[stage|checked]] nanofil IR ([lower]) over a 32-bit tagged-word arena.").
file_blurb('nanofil/anf/lower/Prims.v',
    "Declares the primitive operations exposed to λANF test programs.").
file_blurb('nanofil/anf/lower/tests/Programs.v',
    "Benchmark and gate test programs compiled through CertiRocq λANF and lowered to nanofil IR.").
file_blurb('nanofil/anf/lower/tests/Ref.v',
    "Extracts the test programs in [Programs](Programs.v) directly to OCaml as the ground-truth reference.").
file_blurb('nanofil/anf/lower/tests/Show.v',
    "Serializes test program outputs as byte lists so arena-compiled binaries and OCaml references can be compared byte for byte.").
file_blurb('nanofil/anf/lower/tests/Tap.v',
    "Invokes CertiRocq on each test program in [Programs](Programs.v) to dump λANF clauses for [AnfLower](../AnfLower.v).").
file_blurb('nanofil/anf/backend/Drive.v',
    "Drives the Gallina backend through CertiRocq's λANF pipeline.").
file_blurb('nanofil/anf/backend/Tap.v',
    "Dumps CertiRocq λANF IR for the Gallina backend driver.").
