:- encoding(utf8).
/*  reprint.pl: a Rocq file as rocq_syntax.pl reads it, printed back with
    every subterm in parentheses (tests/parse.sh).

    Usage: swipl tests/reprint.pl FILE.v [--strict] >OUT.v

    Inductive, Record, Definition, Fixpoint, theorems and axioms are
    printed from their trees; everything else (directives, notations,
    modules, proofs) is copied from the source. If the reprint still
    compiles, and its proofs still go through, the grammar read every
    operator at Rocq's precedence and every binder where Rocq puts it.
    With --strict a sentence the grammar did not read fails the run
    (raw/2 is only for commands dterm-rocq copies as text).
*/
:- use_module('../rocq_syntax').
:- use_module(library(lists)).
:- use_module(library(apply)).

:- initialization(main, main).

main :-
    current_prolog_flag(argv, [File|Opts]),
    rocq_read_file(File, Text, rocq(Items, _)),
    nb_setval(text, Text),
    (   memberchk('--strict', Opts), raws(Items, Raws), Raws \== []
    ->  forall(member(raw(F-_, Kw), Raws),
               ( sub_string(Text, 0, F, _, Pre), split_string(Pre, "\n", "", Ls), length(Ls, L),
                 format(user_error, "~w:~w: the grammar does not read this ~w~n", [File, L, Kw]) )),
        halt(1)
    ;   true
    ),
    maplist(item, Items).

%  Commands that are copied as text on purpose.
copied(K) :- memberchk(K, ['Ltac', 'Check', 'Compute', 'Print', 'Eval', 'Search', 'About', 'Locate',
                           'Extraction', 'Recursive', 'Next', 'Obligation', 'Opaque', 'Transparent']).

raws(Items, Raws) :-
    findall(raw(P, K), ( sub_item(Items, raw(P, K)), \+ copied(K) ), Raws).

sub_item(Items, I) :- member(I0, Items), ( I = I0 ; I0 = block(_, B, _), sub_item(B, I) ; I0 = proved(I, _) ).

src(F-T) :- nb_getval(text, Text), L is T - F, sub_string(Text, F, L, _, S), write(S), nl.

item(block(S, Body, E)) :- !, sent(S), maplist(item, Body), ( E == none -> true ; sent(E) ).
item(proved(S, pf(Steps, End))) :- !,
    sent(S), maplist(step, Steps), ( End = qed(P, _) -> src(P) ; true ).
item(S) :- sent(S).

step(step(P, Bs, _)) :- maplist([B]>>format("~w ", [B]), Bs), src(P).
step(bullets(Bs)) :- maplist([B]>>format("~w ", [B]), Bs), nl.

sent(ind(_, Kw, Bodies)) :- !, format("~w ", [Kw]), bodies(Bodies), write(".\n").
sent(rec(_, Kw, n(_, N), Bs, Sort, Ctor, Fs)) :- !,
    format("~w ~w", [Kw, N]), binders(Bs), opt_type(Sort), write(" :="),
    ( Ctor = n(_, C) -> format(" ~w", [C]) ; true ),
    write(" {\n"), fields(Fs), write("}.\n").
sent(def(_, Kw, n(_, N), Bs, Ty, Body)) :- !,
    format("~w ~w", [Kw, N]), binders(Bs), opt_type(Ty),
    ( Body == none -> true ; write(" :=\n  "), pr(Body) ), write(".\n").
sent(thm(_, 'Goal', none, [], Ty)) :- !, write("Goal "), pr(Ty), write(".\n").
sent(thm(_, Kw, n(_, N), Bs, Ty)) :- !,
    format("~w ~w", [Kw, N]), binders(Bs), write(" : "), pr(Ty), write(".\n").
sent(decl(_, Kw, [g(Ns, Ty)])) :- !,
    format("~w ", [Kw]), names(Ns), write(" : "), pr(Ty), write(".\n").
sent(decl(_, Kw, Gs)) :- !,
    format("~w", [Kw]), forall(member(g(Ns, Ty), Gs), ( write(" ("), names(Ns), write(" : "), pr(Ty), write(")") )), write(".\n").
sent(S) :- arg(1, S, P), src(P).

bodies([B]) :- !, body(B).
bodies([B|Bs]) :- body(B), write("\nwith "), bodies(Bs).

body(ib(n(_, N), Bs, Ty, Cs)) :-
    write(N), binders(Bs), opt_type(Ty), write(" :="),
    forall(member(ctor(_, C, CBs, CTy), Cs), ( format("\n  | ~w", [C]), binders(CBs), opt_type(CTy) )).

fields([]).
fields([field(_, N, Bs, Ty, D)|Fs]) :-
    format("  ~w", [N]), binders(Bs), opt_type(Ty),
    ( D == none -> true ; write(" := "), pr(D) ),
    ( Fs == [] -> nl ; write(";\n") ), fields(Fs).

opt_type(none) :- !.
opt_type(T) :- write(" : "), pr(T).

names([n(_, N)]) :- !, write(N).
names([n(_, N)|Ns]) :- format("~w ", [N]), names(Ns).

binders(Bs) :- maplist([B]>>( write(" "), binder(B) ), Bs).

binder(b(_, struct, [n(_, X)], _)) :- !, format("{struct ~w}", [X]).
binder(b(_, brace, Ns, none)) :- !, write("{"), names(Ns), write("}").
binder(b(_, brace, Ns, T)) :- !, write("{"), names(Ns), write(" : "), pr(T), write("}").
binder(b(_, _, Ns, none)) :- !, names(Ns).
binder(b(_, _, Ns, T)) :- write("("), names(Ns), write(" : "), pr(T), write(")").

pr(id(_, X)) :- !, write(X).
pr(hole(_)) :- !, write("_").
pr(num(_, N)) :- !, write(N).
pr(str(_, S)) :- !, format("\"~w\"", [S]).
pr(explicit(_, X)) :- !, format("@~w", [X]).
pr(app(_, F, As)) :- !, write("("), pr(F), forall(member(A, As), ( write(" "), pr(A) )), write(")").
pr(bin(_, Op, L, R)) :- !, write("("), pr(L), format(" ~w ", [Op]), pr(R), write(")").
pr(chain(_, [O1, O2], [A, B, C])) :- !,
    write("("), pr(A), format(" ~w ", [O1]), pr(B), format(" ~w ", [O2]), pr(C), write(")").
pr(pre(_, Op, E)) :- !, format("(~w ", [Op]), pr(E), write(")").
pr(paren(_, E)) :- !, write("("), pr(E), write(")").
pr(cast(_, E, T)) :- !, write("("), pr(E), write(" : "), pr(T), write(")").
pr(tuple(_, Es)) :- !, write("("), sep(Es, ", "), write(")").
pr(forall(_, Bs, B)) :- !, write("(forall"), binders(Bs), write(", "), pr(B), write(")").
pr(exists(_, Bs, B)) :- !, write("(exists"), binders(Bs), write(", "), pr(B), write(")").
pr(fun(_, Bs, B)) :- !, write("(fun"), binders(Bs), write(" => "), pr(B), write(")").
pr(let(_, Lhs, Ty, V, B)) :- !,
    write("(let "),
    ( Lhs = tuple(Ns) -> write("("), names_c(Ns), write(")") ; Lhs = name(n(_, X), Bs), write(X), binders(Bs) ),
    opt_type(Ty), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(letstar(_, n(_, X), V, B)) :- !, format("(let* ~w := ", [X]), pr(V), write(" in "), pr(B), write(")").
pr(letpat(_, P, V, B)) :- !, write("(let '"), pr(P), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(letfix(_, n(_, F), Bs, Ty, V, B)) :- !,
    format("(let fix ~w", [F]), binders(Bs), opt_type(Ty), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(orpat(_, Ps)) :- !, write("("), sep(Ps, " | "), write(")").
pr(if(_, C, T, E)) :- !, write("(if "), pr(C), write(" then "), pr(T), write(" else "), pr(E), write(")").
pr(match(_, Ss, Ret, Brs)) :- !,
    write("(match "), scruts(Ss), ( Ret == none -> true ; write(" return "), pr(Ret) ), write(" with"),
    forall(member(br(Alts, R), Brs), ( write("\n    | "), alts(Alts), write(" => "), pr(R) )),
    write("\n  end)").
pr(list(_, Es)) :- !, write("["), sep(Es, "; "), write("]").
pr(record(_, Fs)) :- !, write("{| "), fsep(Fs), write(" |}").
pr(scope(_, E, K)) :- !, write("("), pr(E), format(")%~w", [K]).
pr(braces(_, E)) :- !, write("{"), pr(E), write("}").
pr(sig(_, n(_, X), T, Q)) :- !, format("{~w : ", [X]), pr(T), write(" | "), pr(Q), write("}").

names_c([n(_, N)]) :- !, write(N).
names_c([n(_, N)|Ns]) :- format("~w, ", [N]), names_c(Ns).

sep([E], _) :- !, pr(E).
sep([E|Es], S) :- pr(E), write(S), sep(Es, S).
sep([], _).

fsep([fld(_, N, E)]) :- !, format("~w := ", [N]), pr(E).
fsep([fld(_, N, E)|Fs]) :- format("~w := ", [N]), pr(E), write("; "), fsep(Fs).
fsep([]).

scruts([S]) :- !, scrut(S).
scruts([S|Ss]) :- scrut(S), write(", "), scruts(Ss).
scrut(as(E, n(_, N))) :- !, pr(E), format(" as ~w", [N]).
scrut(E) :- pr(E).

alts([A]) :- !, sep(A, ", ").
alts([A|As]) :- sep(A, ", "), write(" | "), alts(As).
