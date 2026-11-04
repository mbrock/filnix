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

:- dynamic option_read/6.

%  read_options(+File, -Index): the JSON options.nix wrote.
read_options(File, Index) :-
    setup_call_cleanup(open(File, read, S, [encoding(utf8)]), json_read_dict(S, Index, [value_string_as(atom)]), close(S)).

index_options(Index, Os) :- findall(O, ( member(M, Index.modules), member(O, M.options) ), Os).

%% Who reads an option

%  option_readers(+Root, +Nixpkgs, +Files, +Index): option_read(Option,
%  Kind, File, Line, Owner, OwnerId) for each read, Kind exact or interpolated
%  (reads_option/3), in the drawn Files and in
%  the Nixpkgs modules that declare the options. Each machine's options
%  are looked for only in the files that declare or define one of them,
%  so finix's cfg.${name} does not read NixOS's filc.* and back.
option_readers(Root, Nixpkgs, Files, Index) :-
    retractall(option_read(_, _, _, _, _, _)),
    forall(member(M, Index.modules), machine_readers(Root, Nixpkgs, Files, M.options)).

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
        ( module_config(E, CId) -> true ; CId = none ), nb_setval(nix_config, CId),
        findall(B, ( sub_term(B, E), compound(B), B = bind(_, _, _) ), Binds),
        forall(( sub_term(S, E), compound(S), S = select(P, _, _, _), config_path(S, 8, RP) ),
               record_reads(F, P, RP, Os, Binds))
    ;   format(user_error, "dterm-nix: cannot read ~w for its option reads~n", [Path])
    ).

record_reads(F, From-_, RP, Os, Binds) :-
    offset_line(From, Line),
    owner(From, Binds, Owner, OwnerId),
    forall(( member(O, Os), reads_option(RP, O.loc, Kind), \+ option_read(O.name, Kind, F, _, Owner, _) ),
           assertz(option_read(O.name, Kind, F, Line, Owner, OwnerId))).

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

%  reads_option(+RP, +Loc, -Kind): a read of path RP reads option Loc
%  (Kind exact) when Loc is RP or begins it. A * in RP (an interpolated
%  name) may stand for the option's name (Kind interpolated) when RP is as
%  long as Loc and begins with a name of it: cfg.${name}.enable may read
%  filc.openssh.enable, but not filc.units, and config.${name} reads no
%  option it can name.
reads_option(RP, Loc, Kind) :-
    length(Loc, N), length(Pre, N), append(Pre, Rest, RP), maplist(loc_name, Pre, Loc),
    (   memberchk('*', Pre) -> Rest == [], Pre = [P1|_], P1 \== '*', Kind = interpolated
    ;   Kind = exact
    ).

loc_name('*', _) :- !.
loc_name(X, Y) :- X == Y.

%  module_config(+E, -Id): the module function's config parameter, the
%  first argument set with a config through the file's functions (after
%  { filnix }: and the like). A submodule's own config is not it.
module_config(lam(_, pset(Fs, _, _), _), Id) :- member(formal(F-_, config, _), Fs), !, bid(F, Id).
module_config(lam(_, _, B), Id) :- !, module_config(B, Id).
module_config(let(_, _, B), Id) :- !, module_config(B, Id).
module_config(with(_, _, B), Id) :- !, module_config(B, Id).
module_config(assert(_, _, B), Id) :- !, module_config(B, Id).
module_config(paren(_, B), Id) :- module_config(B, Id).

%  config_path(+E, +Depth, -Path): E is config.Path.
config_path(var(P, X), D, Path) :- D > 0, D1 is D - 1,
    (   ref(P, Id)
    ->  (   nb_getval(nix_config, Id) -> Path = []
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
                                                                         el(ul, none, seq(Index.modules, module_nav)) )) )) )),
            el(article, "dterm nix options",
               ( el(h1, "source-title", "Options"),
                 el(div, "prose lede",
                    el(p, none, ( "The options filnix's exported NixOS and finix modules declare and the ones they set, ",
                                  "as evaluating the modules gives them: where each is declared, its type, default and ",
                                  "description, and the files that define it in the machine evaluated. For an option a ",
                                  "module sets: the definition as written, its value in that machine, and the port that ",
                                  "builds the package. Which modules read an option comes from their source: a selection ",
                                  "such as ", el(code, none, "cfg.nix.enable"), " followed back to the module's ",
                                  el(code, none, "config"), "." ))),
                 seq(Index.modules, module_section(Pages)) )) )).

module_nav(M) --> el(li, "nav-section", esc(M.name)), seq(M.options, opt_nav(M)).

opt_nav(M, O) --> { opt_id(M, O, Id), atom_concat('#', Id, H) }, el(li, "nav-pred", el(a, none, [href=H], esc(O.name))).

%  A declared option is opt-Name, which source pages link to; an option
%  a module sets is named after the module too, as two modules may set it.
opt_id(M, O, Id) :-
    (   O.group == declared -> atom_concat('opt-', O.name, Id)
    ;   format(atom(Id), "set-~w-~w", [M.name, O.name])
    ).

module_section(Pages, M) -->
    { include([O]>>get_dict(group, O, declared), M.options, Decl),
      include([O]>>get_dict(group, O, set), M.options, Set),
      File = M.file, ( M.kind == nixos -> Kind = "NixOS" ; Kind = "finix" ),
      format(string(Title), "~w: ~w", [Kind, M.name]) },
    el(h2, none, esc(Title)),
    el(p, "options-note", ( "Evaluated in ", file_link(M.machine, none), " with ", file_link(File, none), "." )),
    ( { Decl == [] } -> [] ; el(h3, none, ( "Declared by ", file_link(File, none) )), seq(Decl, option_(Pages, M)) ),
    ( { Set == [] } -> [] ; el(h3, none, ( "Set by ", file_link(File, none) )), seq(Set, option_(Pages, M)) ).

option_(Pages, M, O) -->
    { opt_id(M, O, Id) },
    el(section, "pred option", [id=Id],
       el(div, "doc dterm-doc",
          ( el(div, sig, ( el(span, "f def", esc(O.name)),
                           ( { O.type == null } -> [] ; el(span, "opt-type", esc(O.type)) ),
                           ( { O.readOnly == true } -> el(span, det, "read-only") ; [] ) )),
            el(table, "modes opt-facts", el(tbody, none,
               ( ( { O.group == set } -> set_rows(Pages, M, O) ; [] ),
                 opt_value_row("default", O.default),
                 opt_value_row("example", O.example),
                 el(tr, none, ( el(td, name, "declared"), el(td, desc, seq_sep(O.declarations, decl_link)) )),
                 el(tr, none, ( el(td, name, "defined"), el(td, desc, defined(O.definitions)) )),
                 readers(O.name) ))),
            description(O.description) ))).

%% What a module sets an option to

%  The definitions as written in the module's file, and the value in the
%  machine: each package's derivation name and what builds it.
set_rows(Pages, M, O) -->
    { memberchk(page(M.file, Text, Lines, E, _), Pages) }, !,
    { findall(B, def_bind(E, O.loc, B), Bs),
      nb_setval(nix_text, Text), nb_setval(nix_lines, Lines), nb_setval(nix_file, M.file),
      nb_setval(nix_snippet, true), nb_setval(nix_notes, []), nb_setval(nix_notes_all, []),
      nb_setval(nix_prose, false), nb_setval(nix_top, none),
      ( get_dict(value, O, V0), V0 \== null -> Vs = V0 ; Vs = [] ),
      def_selections(Bs, Sel) },
    ( { Bs == [] } -> [] ; el(tr, "set-to", ( el(td, name, "set to"), el(td, desc, seq(Bs, def_row(M.file))) )) ),
    ( { Vs == [] } -> [] ; el(tr, none, ( el(td, name, "evaluates to"), el(td, desc, seq(Vs, pkg_value(Pages, Sel))) )) ),
    { nb_setval(nix_snippet, false) }.
set_rows(_, _, _) --> [].

def_row(File, bind(F-_, Path, V)) -->
    { offset_line(F, L) },
    el(div, "set-def",
       ( el(div, "set-where", file_link(File, L)),
         el(div, binds, el(div, "clause bind",
                           ( el(div, head, ( attrpath(Path, none), el(span, eq, "=") )),
                             el(div, value, blk(V)) ))) )).

%  A package and what builds it: the port or the override of
%  ports/overlay.nix whose derivation it is, as evaluation found
%  (options.nix); else, when none is, the selection it was made from.
pkg_value(Pages, Sel, V) -->
    el(div, "pkg-value", ( el(code, "drv-name", esc(V.name)), " ", built_by(Pages, Sel, V) )).

built_by(_, _, V) --> { member(A, V.attrs), port_at(A, H, Th) }, !,
    el(span, "built-by", ( el(span, muted, "port "), el(a, "f", [href=H], esc(A)), " ", thing_summary(Th) )).
built_by(Pages, _, V) --> { member(A, V.attrs), overlay_href(Pages, A, H) }, !,
    el(span, "built-by", ( el(span, muted, "override "), el(a, "f", [href=H], esc(A)),
                           el(span, muted, " in ports/overlay.nix") )).
built_by(_, _, V) --> { V.attrs = [A|_] }, !, el(span, "built-by", ( el(span, muted, "pkgsFilc."), esc(A) )).
built_by(_, _, V) --> { V.plain == true }, !,
    el(span, "built-by muted", ( "pkgsFilc.", esc(V.pname), ": no port or override, Nixpkgs' recipe built with Fil-C" )).
built_by(_, Sel, V) -->
    { nb_getval(nix_options, I), Names = I.overlayNames,
      ( get_dict(pname, V, P), P \== null, memberchk(P, Names) -> Variant = P ; Variant = none ) },
    (   { Variant \== none }
    ->  el(span, "built-by muted", ( "a variant of ", el(code, none, esc(Variant)), " (its pname), which ",
                                     ( { port_at(Variant, H, _) } -> ( "the port ", el(a, "f", [href=H], esc(Variant)) ) ; "ports/overlay.nix" ),
                                     " builds" ))
    ;   { Sel = [C|_] }
    ->  el(span, "built-by muted", ( "a derivation of its own, made from ", el(code, none, esc(C)) ))
    ;   el(span, "built-by muted", "not found among the ports and overrides")
    ).

%  The attributes the definitions select from a package set: fp.openssh.
def_selections(Bs, Sel) :-
    findall(A, ( member(bind(_, _, V), Bs), sub_term(S, V), compound(S),
                 S = select(_, var(_, _), [aid(_, A)|_], _) ), Sel0),
    list_to_set(Sel0, Sel).

%  overlay_href(+Pages, +Name, -Href): ports/overlay.nix's own binding of
%  Name, among the sets its overlay adds to the ports.
overlay_href(Pages, N, H) :-
    memberchk(page('ports/overlay.nix', _, _, E, _), Pages), page_name('ports/overlay.nix', P),
    sub_term(bind(_, [aid(F-_, N)], _), E), !, bid(F, Id), atomic_list_concat([P, '#', Id], H).

%  def_bind(+E, +Loc, -Bind): a binding of the module that defines Loc:
%  its attribute path, with those of the sets around it, ends in config
%  followed by Loc (config.services.tor.package = …, or
%  services.openssh.package inside config = { … }).
def_bind(E, Loc, B) :-
    atom_list(Loc, L),
    def_walk(E, [], Full-B), append(Pre, L, Full), last(Pre, config).

atom_list(Loc, L) :- maplist([X, A]>>( atom(X) -> A = X ; atom_string(A, X) ), Loc, L).

def_walk(attrs(_, _, Bs), Pre, R) :- !, member(B, Bs), B = bind(_, Path, V),
    maplist(attr_key, Path, Ks), append(Pre, Ks, Full),
    ( R = Full-B ; def_walk(V, Full, R) ).
def_walk(let(_, Bs, Body), Pre, R) :- !,
    (   member(bind(_, Path, V), Bs), maplist(attr_key, Path, Ks), append(Pre, Ks, Full), def_walk(V, Full, R)
    ;   def_walk(Body, Pre, R)
    ).
def_walk(N, Pre, R) :- compound(N), N =.. [_, _|As], member(A, As), def_sub(A, Pre, R).

def_sub(A, Pre, R) :- is_list(A), !, member(X, A), def_sub(X, Pre, R).
def_sub(A, Pre, R) :- compound(A), functor(A, _, N), N > 0, arg(1, A, _-_), def_walk(A, Pre, R).

:- dynamic port_at/3.

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
    { reader_groups(Name, exact, Exact), reader_groups(Name, interpolated, Dyn) },
    (   { Exact == [] } -> el(tr, none, ( el(td, name, "read by"), el(td, desc, el(span, muted, "no module read found")) ))
    ;   el(tr, none, ( el(td, name, "read by"), el(td, desc, seq(Exact, reader_group)) ))
    ),
    (   { Dyn == [] } -> []
    ;   el(tr, "may-read", ( el(td, name, "may read"),
                            el(td, desc, ( el(div, muted, "dynamic: a selection with an interpolated name, such as cfg.${name}.enable, that can name this option"),
                                           seq(Dyn, reader_group) )) ))
    ).

reader_groups(Name, Kind, Groups) :-
    findall(F-r(L, Ow, Id), option_read(Name, Kind, F, L, Ow, Id), Rs0), keysort(Rs0, Rs1),
    group_pairs_by_key(Rs1, Groups).

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
