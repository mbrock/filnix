:- encoding(utf8).
/*  The option index (included in dterm_nix.pl): the options filnix's
    modules declare and set, as options.nix reads them from evaluating the
    modules, with the modules that read each one.

    Evaluation gives an option's declaration, type, default, example,
    description and the files that define it. It cannot say who reads an
    option, so that comes from the source: in each module, a selection
    such as `cfg.nix.enable` is followed back through the bindings it
    names (`cfg = config.filc`) and the `with` it is under
    (`with config.services; openssh.enable`) to a path in `config`. An
    interpolated name (`cfg.${name}.enable`) reads every option it can
    stand for.
*/

:- use_module(library(json)).

:- dynamic option_read/5.

%  read_options(+File, -Index): the JSON options.nix wrote.
read_options(File, Index) :-
    setup_call_cleanup(open(File, read, S, [encoding(utf8)]), json_read_dict(S, Index, [value_string_as(atom)]), close(S)).

index_options(Index, Os) :- findall(O, ( member(G, [nixos, finix]), get_dict(options, Index.G, L), member(O, L) ), Os).

%% Who reads an option

%  option_readers(+Root, +Nixpkgs, +Files, +Index): option_read(Option,
%  File, Line, Owner, OwnerId) for each read in the drawn Files and in
%  the Nixpkgs modules that declare the options. Each machine's options
%  are looked for only in the files that declare or define one of them,
%  so finix's cfg.${name} does not read NixOS's filc.* and back.
option_readers(Root, Nixpkgs, Files, Index) :-
    retractall(option_read(_, _, _, _, _)),
    forall(member(G, [nixos, finix]), machine_readers(Root, Nixpkgs, Files, Index.G.options)).

machine_readers(Root, Nixpkgs, Files, Os) :-
    findall(F, ( member(O, Os), member(D, O.declarations), atom_concat('nixpkgs/', F, D.file) ), Np0),
    sort(Np0, Np),
    findall(F-Path, ( member(F, Files),
                      once(( member(O, Os), ( member(D, O.declarations), D.file == F ; memberchk(F, O.definitions) ) )),
                      directory_file_path(Root, F, Path) ), Ours),
    (   Nixpkgs == none -> Theirs = []
    ;   findall(NF-Path, ( member(F, Np), atom_concat('nixpkgs/', F, NF), directory_file_path(Nixpkgs, F, Path) ), Theirs)
    ),
    append(Ours, Theirs, All),
    forall(member(F-Path, All), file_option_reads(F, Path, Os)).

file_option_reads(F, Path, Os) :-
    (   catch(nix_read_file(Path, Text, nix(E, _)), _, fail)
    ->  line_starts(Text, Lines), nb_setval(nix_lines, Lines), nb_setval(nix_text, Text),
        ( top_body(E, Top) -> node_pos(Top, TP), nb_setval(nix_top, TP) ; nb_setval(nix_top, none) ),
        resolve(E),
        findall(B, ( sub_term(B, E), compound(B), B = bind(_, _, _) ), Binds),
        forall(( sub_term(S, E), compound(S), S = select(P, _, _, _), config_path(S, 8, RP) ),
               record_reads(F, P, RP, Os, Binds))
    ;   format(user_error, "dterm-nix: cannot read ~w for its option reads~n", [Path])
    ).

record_reads(F, From-_, RP, Os, Binds) :-
    offset_line(From, Line),
    owner(From, Binds, Owner, OwnerId),
    forall(( member(O, Os), reads_option(RP, O.loc), \+ option_read(O.name, F, _, Owner, _) ),
           assertz(option_read(O.name, F, Line, Owner, OwnerId))).

%  The innermost binding around offset O, other than an option's own
%  fields (a read in `default = cfg.enable` is the read of the binding
%  that makes the option).
owner(O, Binds, Owner, Id) :-
    findall(L-B, ( member(B, Binds), B = bind(F-T, Path, _), F =< O, O < T, \+ option_field(Path),
                   L is T - F ), Ls),
    (   keysort(Ls, [_-bind(F-_, Path, _)|_])
    ->  path_name(Path, Owner), Path = [A|_], node_pos(A, AF-_), bid(AF, Id), F = F
    ;   Owner = '', Id = none
    ).

option_field([aid(_, X)]) :- memberchk(X, [default, defaultText, example, description, type, apply, readOnly]).

%  A read of path RP reads option Loc when Loc is RP or begins it. A *
%  in RP (an interpolated name) stands for any name, but then RP must be
%  as long as Loc: cfg.${name}.enable reads filc.openssh.enable, not
%  filc.units.
reads_option(RP, Loc) :-
    length(Loc, N), length(Pre, N), append(Pre, Rest, RP), maplist(loc_name, Pre, Loc),
    ( memberchk('*', Pre) -> Rest == [] ; true ).

loc_name('*', _) :- !.
loc_name(X, Y) :- X == Y.

%  config_path(+E, +Depth, -Path): E is config.Path.
config_path(var(P, X), D, Path) :- D > 0, D1 is D - 1,
    (   ref(P, Id)
    ->  (   binder(Id, config, param, _) -> Path = []
        ;   binder_value(Id, V), config_path(V, D1, Path)
        )
    ;   with_ref(P, W), config_path(W, D1, WP), append(WP, [X], Path)
    ).
config_path(select(_, E, AP, none), D, Path) :-
    config_path(E, D, B), maplist(attr_key, AP, Ks), append(B, Ks, Path).
config_path(paren(_, E), D, Path) :- config_path(E, D, Path).

attr_key(aid(_, X), X) :- !.
attr_key(astr(_, [lit(S)]), A) :- !, atom_string(A, S).
attr_key(_, '*').

%% The page

options_page(Pages, Index) -->
    shell("Options", ( el(a, crumb, [href="../index.html"], "Wiki"), el(span, "crumb-sep", "›"),
                       el(a, crumb, [href="index.html"], "Nix"), el(span, "crumb-sep", "›"),
                       el(span, "crumb current", "Options") ),
          ( el(nav, "toc dterm-nav", ( el(div, "toc-title", "Nix"),
                                        el(ul, none, ( seq(Pages, nav_file(none, [])),
                                                       el(li, current, ( el(a, none, [href="options.html"], "Options"),
                                                                         el(ul, none, options_nav(Index)) )) )) )),
            el(article, "dterm nix options",
               ( el(h1, "source-title", "Options"),
                 el(div, "prose lede",
                    el(p, none, ( "The options filnix's NixOS and finix modules declare and the ones they set, ",
                                  "as evaluating the modules gives them: where each is declared, its type, default and ",
                                  "description, and the files that define it in the machine evaluated. Which modules ",
                                  "read an option comes from their source: a selection such as ",
                                  el(code, none, "cfg.nix.enable"), " followed back to ", el(code, none, "config"), "." ))),
                 module_section("NixOS: nixosModules.filc", "nixos/filc.nix", Index.nixos),
                 module_section("finix: finixModules.filc-userland", "finix/userland.nix", Index.finix) )) )).

options_nav(Index) -->
    el(li, "nav-section", "NixOS"), seq(Index.nixos.options, opt_nav),
    el(li, "nav-section", "finix"), seq(Index.finix.options, opt_nav).

opt_nav(O) --> { opt_id(O.name, Id), atom_concat('#', Id, H) }, el(li, "nav-pred", el(a, none, [href=H], esc(O.name))).

opt_id(Name, Id) :- atom_concat('opt-', Name, Id).

module_section(Title, File, M) -->
    { include([O]>>get_dict(group, O, declared), M.options, Decl),
      include([O]>>get_dict(group, O, set), M.options, Set) },
    el(h2, none, esc(Title)),
    el(p, "options-note", ( "Definitions are those of ", file_link(M.machine, none), " with ", file_link(File, none), "." )),
    ( { Decl == [] } -> [] ; el(h3, none, ( "Declared by ", file_link(File, none) )), seq(Decl, option_) ),
    ( { Set == [] } -> [] ; el(h3, none, ( "Set by ", file_link(File, none) )), seq(Set, option_) ).

option_(O) -->
    { opt_id(O.name, Id) },
    el(section, "pred option", [id=Id],
       el(div, "doc dterm-doc",
          ( el(div, sig, ( el(span, "f def", esc(O.name)),
                           ( { O.type == null } -> [] ; el(span, "opt-type", esc(O.type)) ),
                           ( { O.readOnly == true } -> el(span, det, "read-only") ; [] ) )),
            el(table, "modes opt-facts", el(tbody, none,
               ( opt_value_row("default", O.default),
                 opt_value_row("example", O.example),
                 el(tr, none, ( el(td, name, "declared"), el(td, desc, seq_sep(O.declarations, decl_link)) )),
                 el(tr, none, ( el(td, name, "defined"), el(td, desc, defined(O.definitions)) )),
                 readers(O.name) ))),
            description(O.description) ))).

opt_value_row(_, null) --> !, [].
opt_value_row(Label, V) --> el(tr, none, ( el(td, name, esc(Label)), el(td, desc, opt_value(V)) )).

%  A default or example: a literalExpression is drawn as Nix, Markdown as
%  prose, anything else as the text the manual shows.
opt_value(V) --> { is_dict(V), V.kind == literalExpression, catch(code_expr(V.text, E), _, fail) }, !,
    { atom_string(V.text, T) }, el(code, term, snippet(T, term(E))).
opt_value(V) --> { is_dict(V), V.kind == literalMD }, !, { split_string(V.text, "\n", "", Ls) }, prose_lines(Ls).
opt_value(V) --> { is_dict(V) }, !, el(code, none, esc(V.text)).
opt_value(V) --> el(code, none, esc(V)).

description(null) --> !, [].
description(D) --> { ( is_dict(D) -> T = D.text ; T = D ), split_string(T, "\n", "", Ls) }, prose_lines(Ls).

defined([]) --> !, el(span, muted, "only by its default").
defined(Fs) -->
    { partition([F]>>sub_atom(F, 0, _, _, 'nixpkgs/'), Fs, Np, Ours), length(Np, N) },
    seq_sep(Ours, [F]>>file_link(F, none)),
    (   { N == 0 } -> []
    ;   { N =< 3 } -> ( { Ours == [] } -> [] ; ", " ), seq_sep(Np, [F]>>file_link(F, none))
    ;   ( { Ours == [] } -> [] ; ", " ), el(details, "more-defs", ( el(summary, none, ( esc(N), " Nixpkgs modules" )),
                                                                   seq_sep(Np, [F]>>file_link(F, none)) ))
    ).

readers(Name) -->
    { findall(F-r(L, Ow, Id), option_read(Name, F, L, Ow, Id), Rs0), keysort(Rs0, Rs1),
      group_pairs_by_key(Rs1, Groups) },
    (   { Groups == [] } -> el(tr, none, ( el(td, name, "read by"), el(td, desc, el(span, muted, "no module read found")) ))
    ;   el(tr, none, ( el(td, name, "read by"), el(td, desc, seq(Groups, reader_group)) ))
    ).

reader_group(F-Rs) -->
    el(div, "reader", ( file_link(F, none), ": ", seq_sep(Rs, reader(F)) )).

reader(F, r(L, Ow, Id)) -->
    { reader_href(F, L, Id, H), ( Ow == '' -> Label = L ; Label = Ow ), format(atom(T), "line ~w", [L]) },
    el(a, none, [href=H, title=T], esc(Label)).

reader_href(F, _, Id, H) :- Id \== none, nb_getval(nix_pages, Ps), memberchk(F, Ps), !,
    page_name(F, P), atomic_list_concat([P, '#', Id], H).
reader_href(F, L, _, H) :- file_href(F, L, H).

decl_link(D) --> file_link(D.file, D.line).

%  file_link(+File, +Line): File in filnix ("nixos/filc.nix") or Nixpkgs
%  ("nixpkgs/…"), at Line or none.
file_link(F, L) --> { file_href(F, L, H), ( L == none -> T = F ; format(atom(T), "~w:~w", [F, L]) ) },
    el(a, path, [href=H], esc(T)).

file_href(F, L, H) :-
    atom_concat('nixpkgs/', P, F), !,
    nb_getval(nix_options, Index), Rev = Index.nixpkgsRev,
    ( L == none -> Frag = '' ; format(atom(Frag), "#L~w", [L]) ),
    format(atom(H), "https://github.com/NixOS/nixpkgs/blob/~w/~w~w", [Rev, P, Frag]).
file_href(F, L, H) :-
    nb_getval(nix_pages, Ps), memberchk(F, Ps), !, page_name(F, P),
    (   L \== none, line_anchor(F, L, Id) -> atomic_list_concat([P, '#', Id], H) ; H = P ).
file_href(F, L, H) :-
    github(G), ( L == none -> format(atom(H), "~w~w", [G, F]) ; format(atom(H), "~w~w#L~w", [G, F, L]) ).

seq_sep([], _) --> [].
seq_sep([X], G) --> !, call(G, X).
seq_sep([X|Xs], G) --> call(G, X), ", ", seq_sep(Xs, G).

%  line_anchor(File, Line, Id): a binding of a drawn page starts at Line.
:- dynamic line_anchor/3.
