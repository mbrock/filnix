:- encoding(utf8).
/*  Ports (included in dterm_nix.pl): `for Pkg Steps`, the call of
    ports/default.nix's DSL that ports.nix and the files of ports/ are lists of,
    wherever it is written, is drawn as the fact it states. A table of
    its steps in the order they apply has a row per step: its verb
    (linked to the verb's definition in the DSL), its arguments, and the
    comment that says why. Comments between steps are rows of their own.

    Each port is anchored as port-Name on its page (Name its package's
    attribute), so the option index can link a package to the port that
    builds it: port_at(Name, Href, Steps) for the first port of a name,
    and for a binding that applies a port helper, such as
    `boost186 = boostPort pkgs.boost186`.
*/

for_app(paren(_, E), P, S) :- !, for_app(E, P, S).
for_app(app(_, var(_, for), [P, S]), P, S).

%  port_helper(+E): E is a function whose body is a port.
port_helper(lam(_, _, B)) :- for_app(B, _, _), !.
port_helper(lam(_, _, B)) :- port_helper(B).

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

%% Anchors

:- dynamic port_site/3, port_at/3.

%  port_sites(+Pages): each port of each page gets its anchor, port-Name
%  for the first of its name on the page and port-Name-K for the K-th;
%  port_at/3 for the first of a name among all pages.
port_sites(Pages) :-
    retractall(port_site(_, _, _)), retractall(port_at(_, _, _)),
    forall(member(page(File, _, _, E, _), Pages), page_ports(File, E)).

page_ports(File, E) :-
    findall(F-Name-S, ( sub_term(X, E), X = app(F-_, var(_, for), [Pkg, S]), pkg_name(Pkg, Name) ), Ps0),
    msort(Ps0, Ps), page_name(File, Page),
    foldl(port_anchor(File, Page), Ps, [], _),
    %  A port bound to a name, such as `bash = for pkgs.bashNonInteractive`,
    %  is that name's port too.
    forall(( sub_term(X, E), X = bind(_, [aid(_, Name)], V), for_app(V, _, S),
             sub_term(app(F-_, var(_, for), _), V), port_site(File, F, Id), \+ port_at(Name, _, _) ),
           ( atomic_list_concat([Page, '#', Id], H), assertz(port_at(Name, H, S)) )),
    forall(( sub_term(X, E), port_alias(X, Name, F) ),
           ( bid(F, Id), atomic_list_concat([Page, '#', Id], H),
             ( port_at(Name, _, _) -> true ; assertz(port_at(Name, H, none)) ) )).

port_anchor(File, Page, F-Name-S, Seen, [Name|Seen]) :-
    aggregate_all(count, member(Name, Seen), K0),
    (   K0 =:= 0 -> port_id(Name, Id) ; K is K0 + 1, format(atom(Id), "port-~w-~w", [Name, K]) ),
    assertz(port_site(File, F, Id)),
    atomic_list_concat([Page, '#', Id], H),
    ( port_at(Name, _, _) -> true ; assertz(port_at(Name, H, S)) ).

%  A let binding that applies a port helper bound in the same let.
port_alias(let(_, Bs, _), Name, F) :-
    member(bind(_, [aid(_, Fn)], V), Bs), port_helper(V),
    member(bind(_, [aid(F-_, Name)], app(_, var(_, Fn), _)), Bs).

port_id(Name, Id) :- atom_concat('port-', Name, Id).

%% Drawing

port_block(F-_, Pkg, S) -->
    { pkg_name(Pkg, Name), node_pos(Pkg, PF-_), offset_line(PF, L),
      ( nb_getval(nix_snippet, false), nb_getval(nix_file, File), port_site(File, F, Id) -> As = [id=Id] ; As = [] ) },
    el(div, "port", As,
       ( el(div, "port-head", ( line_link(L), el(span, "f def", esc(Name)),
                                ( { plain_pkg(Pkg, Name) } -> [] ; " ", el(span, "port-pkg", ( el(span, kw, "for"), " ", term(Pkg) )) ) )),
         el(table, "port-steps", el(tbody, none, steps(S))) )).

%  Steps: a port's transforms in order

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

verb_(verb(_, V)) --> { verb_href(V, H) }, !, el(a, "verb f call", [href=H, 'data-b'=V], esc(V)).
verb_(verb(P, V)) --> !, var_ref(P, V, "verb f call").
verb_(cond(F)) --> !, el(span, "verb", fn_(F)).
verb_(none) --> [].

%  A verb of the DSL links to its definition in ports/default.nix.
verb_href(V, H) :-
    nb_getval(nix_dsl, Ids), memberchk(V-Id, Ids),
    format(atom(H), "ports-default.html#~w", [Id]).

step_arg(A) --> { block(A) }, !, blk(A).
step_arg(A) --> el(span, "goal", term(A)), " ".

%  The DSL's verbs and their anchors on ports/default.nix's page: its
%  let bindings.
dsl_ids(Pages, Ids) :-
    (   memberchk(page('ports/default.nix', _, _, E, _), Pages), let_binds(E, Bs)
    ->  findall(V-Id, ( member(bind(_, [aid(F-_, V)], _), Bs), bid(F, Id) ), Ids)
    ;   Ids = []
    ).

let_binds(lam(_, _, B), Bs) :- !, let_binds(B, Bs).
let_binds(let(_, Bs0, B), Bs) :- !, let_binds(B, Bs1), append(Bs0, Bs1, Bs).
let_binds(_, []).

%  The verbs of a port's steps, in the order they first apply, for the
%  option index.
port_verbs(none) --> !, [].
port_verbs(S) -->
    { flat_steps(S, Es), findall(V, ( member(E, Es), step_parts(E, verb(_, V), _, _) ), Vs0), list_to_set(Vs0, Vs),
      atomic_list_concat(Vs, ', ', T) },
    ( { Vs == [] } -> el(span, muted, "no changes") ; el(span, "port-verbs", esc(T)) ).
