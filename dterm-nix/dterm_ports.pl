:- encoding(utf8).
/*  Port lists as fact tables (included in dterm_nix.pl).

    ports.nix and the files it imports (ports/media.nix, …) are lists or
    sets of `for pkgs.x [ steps ]`, in the DSL of ports/default.nix. A
    file of that shape is drawn as the facts it states: each port is a
    table of its steps in the order they apply, a verb (linked to its
    definition in the DSL), its arguments, and the comment that says
    why. The comments before a port are its lede, `# ━━━ Title ━━━`
    comments make the sections, and an index at the top lists every
    port of the file and of the files it imports, with what each one
    changes.

    A port file's plan is a list of things in source order:

    - sec(Title, Notes): a section comment and the comments after it;
    - port(Lede, Name, Pkg, Steps, Head): `for Pkg Steps`, bound to Name
      (or named by its package); Head is the binding's start or `none`,
      and a function parameter `λ boost` for a port helper;
    - alias(Lede, Name, E, Head): another binding among ports, such as
      `boost186 = boostPort pkgs.boost186`;
    - local(Lede, Binds): the let bindings ports share, drawn as bindings;
    - import(Lede, Path, E) and other(Lede, E).
*/

%% Which files

%  port_file(+E): the file's value is a list or set of ports.
port_file(E) :-
    port_body(E, _, B),
    (   B = list(_, Is) -> member(I, Is), ( for_app(I, _, _) ; I = attrs(_, _, _) ), !
    ;   B = attrs(_, _, Bs), member(bind(_, _, V), Bs), for_app(V, _, _), !
    ).

%  The file's value through its functions and lets, and its let bindings.
port_body(lam(_, _, B), Ls, T) :- !, port_body(B, Ls, T).
port_body(let(_, Bs, B), Ls, T) :- !, port_body(B, Ls0, T), append(Bs, Ls0, Ls).
port_body(T, [], T).

for_app(paren(_, E), P, S) :- !, for_app(E, P, S).
for_app(app(_, var(_, for), [P, S]), P, S).

%  A port helper: a function whose body is a port.
port_helper(lam(_, pid(X), B), X, P, S) :- for_app(B, P, S), !.
port_helper(lam(_, _, B), X, P, S) :- port_helper(B, X, P, S).

%% The plan

%  port_plan(+E, +Cms, -Things): Cms the file's comments after its
%  start; the comments between things become ledes and sections.
port_plan(E, Cms, Things, Taken) :-
    port_body(E, _, B),
    ( B = list(P, Is) ; B = attrs(P, _, Is0), Is = [attrs(P, plain, Is0)] ), !,
    P = From-_,
    foldl(item_things, Is, Raw, []),
    gaps(Raw, From, Cms, Things, Taken).

item_things(paren(_, E)) --> !, item_things(E).
item_things(I) --> { for_app(I, Pkg, S) }, !, { pkg_name(Pkg, N), node_pos(I, F-T) }, [F-T-port(N, Pkg, S, none)].
item_things(attrs(_, _, Bs)) --> !, bind_things(Bs).
item_things(let(_, Bs, Body)) --> !, bind_things(Bs), item_things(Body).
item_things(app(P, var(_, import), [Path|_])) --> !, { P = F-T }, [F-T-import(Path, app(P, var(P, import), [Path]))].
item_things(I) --> { node_pos(I, F-T) }, [F-T-other(I)].

%  Bindings: ports, port helpers, aliases, and runs of other let
%  bindings drawn together.
bind_things([]) --> !, [].
bind_things([B|Bs]) --> { port_bind(B, Th) }, !, { node_pos(B, F-T) }, [F-T-Th], bind_things(Bs).
bind_things(Bs0) -->
    { local_run(Bs0, Run, Bs), Run = [B|_], node_pos(B, F-_), last(Run, L), node_pos(L, _-T) },
    [F-T-local(Run)], bind_things(Bs).

port_bind(bind(_, Path, V), Th) :-
    Path = [aid(AF-_, _)|_], path_name(Path, N),
    (   for_app(V, Pkg, S) -> Th = port(N, Pkg, S, AF)
    ;   port_helper(V, X, Pkg, S) -> Th = port(N, Pkg, S, AF-X)
    ;   V = app(_, Fn, _), is_fn(Fn, _) -> Th = alias(N, V, AF)
    ).

%  Bindings that are not ports, up to the next port.
local_run([], [], []).
local_run([B|Bs], Run, Rest) :-
    (   port_bind(B, _) -> Run = [], Rest = [B|Bs]
    ;   Run = [B|Run1], local_run(Bs, Run1, Rest)
    ).

pkg_name(select(_, _, Path, _), N) :- !, path_name(Path, N).
pkg_name(str(_, [lit(S)]), N) :- !, atom_string(N, S).
pkg_name(var(_, X), X) :- !.
pkg_name(paren(_, E), N) :- !, pkg_name(E, N).
pkg_name(path(_, [lit(S)]), N) :- !, file_base_name(S, B), file_name_extension(N, _, B).
pkg_name(app(_, _, [A|_]), N) :- A = str(_, Ps), last(Ps, lit(S)), !, file_base_name(S, N).
pkg_name(app(_, _, [A|_]), N) :- pkg_name(A, N), N \== '…', !.
pkg_name(_, '…').

%  The package is the name's attribute of pkgs.
plain_pkg(select(_, var(_, pkgs), [aid(_, N)], none), N).
plain_pkg(str(_, [lit(S)]), N) :- atom_string(N, S).

%  Each thing takes the comments before it as its lede; a section
%  comment among them starts a section.
gaps([], _, _, [], []).
gaps([F-T-Th|Rs], Prev, Cms, Things, Taken) :-
    include([cm(O, _, _, _)]>>( O >= Prev, O < F ), Cms, Gap),
    split_sections(Gap, Pre, Secs),
    lede_thing(Th, Pre, Thing),
    append(Secs, [Thing], Out),
    append(Out, Things1, Things),
    append(Gap, Taken1, Taken),
    gaps(Rs, T, Cms, Things1, Taken1).

%  The comments before the last section comment make sections; the rest
%  is the lede.
split_sections(Gap, Lede, Secs) :-
    (   append(Before, [C|After], Gap), section_title(C, _), \+ ( member(C2, After), section_title(C2, _) )
    ->  split_sections(Before, Pre0, Secs0),
        section_title(C, Title),
        (   Pre0 == [] -> append(Secs0, [sec(Title, [])], Secs) ; append(Secs0, [sec(Title, Pre0)], Secs) ),
        Lede = After
    ;   Lede = Gap, Secs = []
    ).

section_title(cm(_, _, Text, own), Title) :-
    sub_string(Text, B, _, A, "━━━"), sub_string(Text, _, A, 0, R0), sub_string(Text, 0, B, _, L0),
    sub_string(R0, B1, _, _, "━━━"), sub_string(R0, 0, B1, _, T0), split_string(L0, "", "# ", [""]),
    split_string(T0, "", " ", [T1]), atom_string(Title, T1).

lede_thing(port(N, P, S, H), L, port(L, N, P, S, H)).
lede_thing(alias(N, E, H), L, alias(L, N, E, H)).
lede_thing(local(Bs), L, local(L, Bs)).
lede_thing(import(P, E), L, import(L, P, E)).
lede_thing(other(E), L, other(L, E)).

%% The page

write_ports_page(Out, Pages, page(File, _, _, E, _), Body, Path) :-
    port_plan(E, Body, Things, Taken),
    subtract(Body, Taken, Rest),
    nb_setval(nix_notes_all, Rest), nb_setval(nix_notes, Rest),
    page_name(File, Name), directory_file_path(Out, Name, Path),
    findall(S, member(sec(S, _), Things), Secs),
    write_page(Path, ports_page(Pages, File, E, Things, Secs)).

ports_page(Pages, File, E, Things, Secs) -->
    { nb_getval(nix_head, Head), note_groups(Head, Gs), port_body(E, Shared, _),
      sections(Things, Sections) },
    shell(File, crumbs(File),
          ( el(nav, "toc dterm-nav", ( el(div, "toc-title", "Nix"),
                                        el(ul, none, ( seq(Pages, nav_ports(File, Secs)), nav_options )) )),
            el(article, "dterm nix ports",
               ( el(h1, "source-title", esc(File)),
                 el(div, "prose lede", seq(Gs, lede_group)),
                 port_index(Pages, Sections),
                 ( { Shared == [] } -> []
                 ; el(section, "port-shared", ( el(h2, none, [id="shared"], "Shared"),
                                                el(div, "clause nix-root", binds(Shared, let)) ))
                 ),
                 seq(Sections, port_section),
                 rest_notes )) )).

nav_ports(Current, Secs, page(File, _, _, _, _)) -->
    { page_name(File, Href) },
    (   { File == Current }
    ->  el(li, current, ( el(a, none, [href=Href], esc(File)),
                          el(ul, none, seq(Secs, sec_nav)) ))
    ;   el(li, none, el(a, none, [href=Href], esc(File)))
    ).

sec_nav(S) --> { sec_id(S, Id), atom_concat('#', Id, H) }, el(li, "nav-pred", el(a, none, [href=H], esc(S))).

%  Things grouped into sections; those before the first section are in
%  an untitled one.
sections(Things, Sections) :-
    (   append(Pre, [sec(T, N)|Rest], Things), \+ memberchk(sec(_, _), Pre)
    ->  ( Pre == [] -> Sections = Ss ; Sections = [sec(none, [], Pre)|Ss] ),
        sections_from(T, N, Rest, Ss)
    ;   Sections = [sec(none, [], Things)]
    ).
sections_from(T, N, Things, [sec(T, N, In)|Ss]) :-
    (   append(In, [sec(T1, N1)|Rest], Things), \+ memberchk(sec(_, _), In)
    ->  sections_from(T1, N1, Rest, Ss)
    ;   In = Things, Ss = []
    ).

%  Its words, lower-case and joined by dashes: sec-core-libraries.
sec_id(Title, Id) :-
    downcase_atom(Title, D), atom_codes(D, Cs),
    maplist([C, W]>>( code_type(C, alnum) -> W = C ; W = 0'  ), Cs, Ws),
    atom_codes(A, Ws), atomic_list_concat(Parts, ' ', A), exclude(==(''), Parts, Ps),
    atomic_list_concat([sec|Ps], '-', Id).

port_id(Name, Id) :- atom_concat('port-', Name, Id).

port_section(sec(T, Notes, Things)) -->
    el(section, "port-section",
       ( ( { T == none } -> [] ; { sec_id(T, Id) }, el(h2, none, [id=Id], esc(T)) ),
         ( { Notes == [] } -> [] ; { note_groups(Notes, Gs) }, seq(Gs, note_) ),
         seq(Things, port_thing) )).

port_thing(port(Lede, Name, Pkg, Steps, Head)) -->
    { node_pos(Pkg, PF-_), offset_line(PF, L), port_id(Name, Id) },
    el(section, "port", [id=Id],
       ( el(div, "port-head", ( line_link(L),
                                ( { Head = AF-X } -> { bid(AF, BId) }, el(span, "f def", [id=BId], esc(Name)),
                                                     " ", el(span, lambda, "λ"), el(span, "v", esc(X))
                                ; { Head == none } -> el(span, "f def", esc(Name))
                                ; { bid(Head, BId) }, el(span, "f def", [id=BId], esc(Name)) ),
                                ( { plain_pkg(Pkg, Name) } -> [] ; " ", el(span, "port-pkg", ( el(span, kw, "for"), " ", term(Pkg) )) ) )),
         lede_notes(Lede),
         el(table, "port-steps", el(tbody, none, steps(Steps))) )).
port_thing(alias(Lede, Name, E, Head)) -->
    { node_pos(E, F-T), offset_line(F, L), port_id(Name, Id), bid(Head, BId) },
    el(section, "port alias", [id=Id],
       ( el(div, "port-head", ( line_link(L), el(span, "f def", [id=BId], esc(Name)), el(span, eq, " = "),
                                el(span, "goal", term(E)), aside_after(T) )),
         lede_notes(Lede) )).
port_thing(local(Lede, Bs)) -->
    lede_notes(Lede), el(div, "clause nix-root port-local", binds(Bs, let)).
port_thing(import(Lede, Path, E)) -->
    { node_pos(E, F-_), offset_line(F, L) },
    lede_notes(Lede),
    el(div, "port-import", ( line_link(L), el(span, kw, "import"), " ", term(Path),
                             el(span, muted, " — its ports are listed in the index above") )).
port_thing(other(Lede, E)) --> lede_notes(Lede), el(div, "clause nix-root", blk(E)).

lede_notes([]) --> !, [].
lede_notes(Cms) --> { note_groups(Cms, Gs) }, el(div, "port-lede", seq(Gs, lede_group)).

%% Steps: a port's transforms in order

steps(S) --> { flat_steps(S, Es) }, seq(Es, step).

flat_steps(list(_, Es), Fs) :- !, foldl([E, A0, A]>>( flat_steps(E, F), append(A0, F, A) ), Es, [], Fs).
flat_steps(paren(_, E), Fs) :- flat_steps(E, Fs), Fs \= [paren(_, _)], !.
flat_steps(bin(_, '++', L, R), Fs) :- !, flat_steps(L, A), flat_steps(R, B), append(A, B, Fs).
flat_steps(E, [E]).

step(E) -->
    { node_pos(E, F-T) },
    step_notes(F),
    { step_parts(E, Verb, Args, Why) },
    el(tr, step,
       ( el(td, "step-verb", verb_(Verb)),
         el(td, "step-args", seq(Args, step_arg)),
         el(td, "step-why", ( seq(Why, [W]>>el(span, reason, term(W))), aside_after(T) )) )).

step_notes(F) -->
    { nb_getval(nix_notes, Q0), partition([cm(O, _, _, _)]>>(O < F), Q0, Now, Q), nb_setval(nix_notes, Q),
      note_groups(Now, Gs) },
    seq(Gs, [G]>>el(tr, note, el(td, none, [colspan=3], note_(G)))).

%  step_parts(+E, -Verb, -Args, -Why): a reason string is the why.
step_parts(paren(_, E), V, As, W) :- !, step_parts(E, V, As, W).
step_parts(app(_, var(P, V), As0), verb(P, V), As, W) :- !,
    (   memberchk(V, [broken, skipCheck, skipTests]), As0 = [S], S = str(_, _) -> As = [], W = [S]
    ;   As = As0, W = []
    ).
step_parts(app(_, F, [C, X]), cond(F), [C, X], []) :- is_fn(F, N), memberchk(N, [optional, optionals, optionalAttrs]), !.
step_parts(var(P, V), verb(P, V), [], []) :- !.
step_parts(E, none, [E], []).

verb_(verb(P, V)) --> { verb_href(V, H) }, !, el(a, "verb f call", [href=H, 'data-b'=V], esc(V)), { ignore(P = P) }.
verb_(verb(P, V)) --> !, var_ref(P, V, "verb f call").
verb_(cond(F)) --> !, el(span, "verb", fn_(F)).
verb_(none) --> [].

%  A verb of the DSL links to its definition in ports/default.nix.
verb_href(V, H) :-
    nb_getval(nix_dsl, Ids), memberchk(V-Id, Ids),
    format(atom(H), "ports-default.html#~w", [Id]).

step_arg(A) --> { block(A) }, !, blk(A).
step_arg(A) --> el(span, "goal", term(A)), " ".

%  The DSL's verbs and their anchors on ports/default.nix's page.
dsl_ids(Pages, Ids) :-
    (   memberchk(page('ports/default.nix', _, _, E, _), Pages), port_body(E, Bs, _)
    ->  findall(V-Id, ( member(bind(_, [aid(F-_, V)], _), Bs), bid(F, Id) ), Ids)
    ;   Ids = []
    ).

%% The index: every port and what it changes

port_index(Pages, Sections) -->
    el(section, "port-index",
       ( el(div, "port-filter", ( el(label, none, [for="port-filter"], "Find a port"), " ",
                                  el(input, none, [id="port-filter", type="search", placeholder="systemd, patch, skipCheck…", autocomplete="off"], []) )),
         seq(Sections, index_section),
         imported_index(Pages, Sections) )).

index_section(sec(T, _, Things)) -->
    { include([Th]>>( Th = port(_, _, _, _, _) ; Th = alias(_, _, _, _) ), Things, Ps) },
    (   { Ps == [] } -> []
    ;   el(div, "index-group",
           ( ( { T == none } -> [] ; { sec_id(T, Id), atom_concat('#', Id, H) }, el(h3, none, el(a, none, [href=H], esc(T))) ),
             el(table, "port-summary", el(tbody, none, seq(Ps, index_row(''))) ) ))
    ).

%  The ports of the files the list imports, from their pages.
imported_index(Pages, Sections) -->
    { findall(F, ( member(sec(_, _, Ths), Sections), member(import(_, path(_, [lit(S)]), _), Ths),
                   nb_getval(nix_file, Cur), file_directory_name(Cur, D), directory_file_path(D, S, F0), normalize_rel(F0, F) ), Fs) },
    seq(Fs, imported_group(Pages)).

imported_group(Pages, F) -->
    { memberchk(page(F, Text, Lines, E, Cms), Pages), page_name(F, Href) }, !,
    { nb_getval(nix_text, T0), nb_getval(nix_lines, L0),
      nb_setval(nix_text, Text), nb_setval(nix_lines, Lines),
      node_pos(E, From-_), exclude([cm(O, _, _, _)]>>(O < From), Cms, Body),
      port_plan(E, Body, Things, _),
      include([Th]>>( Th = port(_, _, _, _, _) ; Th = alias(_, _, _, _) ), Things, Ps) },
    el(div, "index-group",
       ( el(h3, none, ( "From ", el(a, none, [href=Href], esc(F)) )),
         el(table, "port-summary", el(tbody, none, seq_snippet(Ps, Href))) )),
    { nb_setval(nix_text, T0), nb_setval(nix_lines, L0) }.
imported_group(_, _) --> [].

seq_snippet(Ps, Href) --> { nb_getval(nix_snippet, S0), nb_setval(nix_snippet, true) },
    seq(Ps, index_row(Href)), { nb_setval(nix_snippet, S0) }.

index_row(Page, Th) -->
    { thing_name(Th, Name), port_id(Name, Id), atomic_list_concat([Page, '#', Id], H),
      thing_lede(Th, Lede), thing_words(Th, Name, Words) },
    el(tr, "port-row", ['data-find'=Words],
       ( el(td, "ps-name", el(a, "f", [href=H], esc(Name))),
         el(td, "ps-changes", thing_summary(Th)),
         el(td, "ps-why", Lede) )).

thing_name(port(_, N, _, _, _), N).
thing_name(alias(_, N, _, _), N).

%  A port's steps, counted by verb in the order they first apply; a pin
%  shows its version, broken its reason.
thing_summary(alias(_, _, E, _)) --> !, el(span, "goal", term(E)).
thing_summary(port(_, N, Pkg, S, _)) -->
    { flat_steps(S, Es), maplist([E, P]>>( step_parts(E, P0, As, W), P = P0-As-W ), Es, Parts),
      findall(V, member(verb(_, V)-_-_, Parts), Vs0), list_to_set(Vs0, Vs) },
    ( { plain_pkg(Pkg, N) } -> [] ; el(span, "goal port-pkg", ( el(span, kw, "for"), " ", term(Pkg) )), " " ),
    (   { Es == [] } -> el(span, muted, "no changes")
    ;   seq(Vs, verb_badge(Parts))
    ).

verb_badge(Parts, pin) --> { member(verb(_, pin)-[V|_]-_, Parts) }, !, el(span, "badge pin", ( "pin ", term(V) )).
verb_badge(Parts, V) --> { memberchk(V, [broken, wip]) }, !,
    el(span, "badge broken", ( esc(V), ( { member(verb(_, V)-_-[W], Parts) } -> " ", term(W) ; [] ) )).
verb_badge(Parts, V) -->
    { aggregate_all(count, member(verb(_, V)-_-_, Parts), N) },
    el(span, badge, ( esc(V), ( { N > 1 } -> el(span, count, ( "×", esc(N) )) ; [] ) )).

%  The first sentence of the lede.
thing_lede(Th, Out) :-
    arg(1, Th, Cms),
    (   Cms = [_|_], note_groups(Cms, [G|_]), group_lines(G, Ls0), dedent(Ls0, Ls),
        blocks(Ls, [p(S0)|_]), first_sentence(S0, S)
    ->  Out = inline(S)
    ;   Out = []
    ).

first_sentence(S0, S) :-
    (   sub_string(S0, B, _, _, ". "), B > 20 -> B1 is B + 1, sub_string(S0, 0, B1, _, S1) ; S1 = S0 ),
    (   string_length(S1, N), N > 160 -> sub_string(S1, 0, 157, _, S2), string_concat(S2, "…", S) ; S = S1 ).

%  The words the filter finds a port by: its name, package and verbs.
thing_words(alias(_, _, E, _), N, W) :- !, node_pos(E, P), src_text(P, T), format(atom(W), "~w ~w", [N, T]).
thing_words(port(_, _, Pkg, S, _), N, W) :-
    flat_steps(S, Es), findall(V, ( member(E, Es), step_parts(E, verb(_, V), _, _) ), Vs0), sort(Vs0, Vs),
    pkg_name(Pkg, PN), atomic_list_concat([N, PN|Vs], ' ', W).
