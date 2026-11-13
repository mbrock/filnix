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
    % Rocq reads UTF-8, whatever the locale (a Nix build has none).
    set_stream(user_output, encoding(utf8)),
    rocq_read_file(File, Text, rocq(Items, _)),
    nb_setval(text, Text),
    nb_setval(strict, Opts),
    (   memberchk('--strict', Opts), raws(Items, Raws), Raws \== []
    ->  forall(member(raw(F-_, Kw), Raws),
               ( sub_string(Text, 0, F, _, Pre), split_string(Pre, "\n", "", Ls), length(Ls, L),
                 format(user_error, "~w:~w: the grammar does not read this ~w~n", [File, L, Kw]) )),
        halt(1)
    ;   true
    ),
    maplist(item, Items).

%  Commands that are copied as text on purpose.
copied(K) :- memberchk(K, ['Check', 'Compute', 'Print', 'Eval', 'Search', 'About', 'Locate',
                           'Extraction', 'Extract', 'Crane', 'CertiRocq', 'Recursive', 'Next', 'Obligation', 'Opaque', 'Transparent']).

raws(Items, Raws) :-
    findall(raw(P, K), ( sub_item(Items, raw(P, K)), \+ copied(K) ), Raws).

sub_item(Items, I) :- member(I0, Items), ( I = I0 ; I0 = block(_, B, _), sub_item(B, I) ; I0 = proved(I, _) ).

src(F-T) :- nb_getval(text, Text), L is T - F, sub_string(Text, F, L, _, S), write(S), nl.

item(block(S, Body, E)) :- !, sent(S), maplist(item, Body), ( E == none -> true ; sent(E) ).
item(proved(S, pf(Steps, End))) :- !,
    sent(S), maplist(step, Steps), ( End = qed(P, _) -> src(P) ; true ).
item(S) :- sent(S).

step(step(P, Bs, Ts)) :-
    maplist(focus, Bs),
    ( rocq_tactic_tokens(Ts, T) -> pt(T), write(".\n")
    ; nb_getval(strict, Opts), memberchk('--strict', Opts)
    -> format(user_error, "unparsed tactic at ~w~n", [P]), halt(1)
    ; src(P) ).
step(bullets(Bs)) :- maplist(focus, Bs), nl.

focus(focus(N)) :- !, format("~w: { ", [N]).
focus(B) :- format("~w ", [B]).

sent(ind(_, Kw, Bodies)) :- !, format("~w ", [Kw]), bodies(Bodies), write(".\n").
sent(rec(_, Kw, n(_, N), Bs, Sort, Ctor, Fs)) :- !,
    format("~w ~w", [Kw, N]), binders(Bs), opt_type(Sort), write(" :="),
    ( Ctor = n(_, C) -> format(" ~w", [C]) ; true ),
    write(" {\n"), fields(Fs), write("}.\n").
sent(def(P, Kw, N, Bs, Ty, Body)) :- !, def(def(P, Kw, N, Bs, Ty, Body)), write(".\n").
sent(mutual(_, [D|Ds])) :- !, def(D), forall(member(E, Ds), ( nl, def(E) )), write(".\n").
sent(thm(_, 'Goal', none, [], Ty)) :- !, write("Goal "), pr(Ty), write(".\n").
sent(thm(_, Kw, n(_, N), Bs, Ty)) :- !,
    format("~w ~w", [Kw, N]), binders(Bs), write(" : "), pr(Ty), write(".\n").
sent(tacdef(_, n(_, N), Args, T)) :- !,
    format("Ltac ~w ", [N]), names(Args), write(" := "), pt(T), write(".\n").
sent(decl(_, 'Context', Gs)) :- Gs \= [bs(_)], !,
    write("Context"), forall(member(g(Ns, Ty), Gs), ( write(" ("), names(Ns), write(" : "), pr(Ty), write(")") )), write(".\n").
sent(decl(_, Kw, [g(Ns, Ty)])) :- !,
    format("~w ", [Kw]), names(Ns), write(" : "), pr(Ty), write(".\n").
sent(decl(_, Kw, [bs(Bs)])) :- !, write(Kw), binders(Bs), write(".\n").
sent(decl(_, Kw, Gs)) :- !,
    format("~w", [Kw]), forall(member(g(Ns, Ty), Gs), ( write(" ("), names(Ns), write(" : "), pr(Ty), write(")") )), write(".\n").
sent(S) :- arg(1, S, P), src(P).

def(def(_, Kw, n(_, N), Bs, Ty, Body)) :-
    format("~w ~w", [Kw, N]), binders(Bs), opt_type(Ty),
    ( Body == none -> true ; write(" :=\n  "), pr(Body) ).

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

names([]).
names([n(_, N)]) :- !, write(N).
names([n(_, N)|Ns]) :- format("~w ", [N]), names(Ns).

binders(Bs) :- maplist([B]>>( write(" "), binder(B) ), Bs).

binder(b(_, pattern(P), _, _)) :- !, write("'"), pr(P).
binder(b(_, gen(Open, Items), _, _)) :- !,
    rocq_syntax:matching(Open, Close), format("`~w", [Open]), gen_items(Items), write(Close).
binder(b(_, struct, [n(_, X)], _)) :- !, format("{struct ~w}", [X]).
binder(b(_, brace, Ns, none)) :- !, write("{"), names(Ns), write("}").
binder(b(_, brace, Ns, T)) :- !, write("{"), names(Ns), write(" : "), pr(T), write("}").
binder(b(_, _, Ns, none)) :- !, names(Ns).
binder(b(_, _, Ns, T)) :- write("("), names(Ns), write(" : "), pr(T), write(")").

gen_items([I]) :- !, gen_item(I).
gen_items([I|Is]) :- gen_item(I), write(", "), gen_items(Is).
gen_item(bang(E)) :- !, write("!"), pr(E).
gen_item(E) :- pr(E).

pr(id(_, X)) :- !, write(X).
pr(hole(_)) :- !, write("_").
pr(meta(_, X)) :- !, format("?~w", [X]).
pr(ltac(_, T)) :- !, write("ltac:("), pt(T), write(")").
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
% ∀ and ∃ stay as they were written: in Iris's scope they are the
% logic's quantifiers, forall and exists Rocq's.
pr(forall(P, Bs, B)) :- !, quantifier(P, "∀", forall, Q), format("(~w", [Q]), binders(Bs), write(", "), pr(B), write(")").
pr(exists(P, Bs, B)) :- !, quantifier(P, "∃", exists, Q), format("(~w", [Q]), binders(Bs), write(", "), pr(B), write(")").
pr(fun(_, Bs, B)) :- !, write("(fun"), binders(Bs), write(" => "), pr(B), write(")").
pr(let(_, Lhs, Ty, V, B)) :- !,
    write("(let "),
    ( Lhs = tuple(Ns) -> write("("), names_c(Ns), write(")") ; Lhs = name(n(_, X), Bs), write(X), binders(Bs) ),
    opt_type(Ty), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(letstar(_, n(_, X), V, B)) :- !, format("(let* ~w := ", [X]), pr(V), write(" in "), pr(B), write(")").
pr(letq(_, P, V, B)) :- !, write("(let? "), pr(P), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(letpat(_, P, V, B)) :- !, write("(let '"), pr(P), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(letfix(_, n(_, F), Bs, Ty, V, B)) :- !,
    format("(let fix ~w", [F]), binders(Bs), opt_type(Ty), write(" := "), pr(V), write(" in "), pr(B), write(")").
pr(orpat(_, Ps)) :- !, write("("), sep(Ps, " | "), write(")").
pr(fix(_, n(_, F), Bs, Ty, B)) :- !,
    format("(fix ~w", [F]), binders(Bs), opt_type(Ty), write(" := "), pr(B), write(")").
pr(named(_, X, E)) :- !, format("(~w := ", [X]), pr(E), write(")").
pr(aspat(_, P, n(_, X))) :- !, write("("), pr(P), format(" as ~w)", [X]).
pr(bits(_, E, Ds)) :- !, write("("), pr(E), write(")"), atom_chars(Ds, Cs), forall(member(C, Cs), format("~~~w", [C])).
pr(if(_, C, T, E)) :- !, write("(if "), pr(C), write(" then "), pr(T), write(" else "), pr(E), write(")").
pr(match(_, Ss, Ret, Brs)) :- !,
    write("(match "), scruts(Ss), ( Ret == none -> true ; write(" return "), pr(Ret) ), write(" with"),
    forall(member(br(Alts, R), Brs), ( write("\n    | "), alts(Alts), write(" => "), pr(R) )),
    write("\n  end)").
pr(list(_, Es)) :- !, write("["), sep(Es, "; "), write("]").
pr(record(_, Fs)) :- !, write("{| "), fsep(Fs), write(" |}").
pr(scope(_, E, K)) :- !, write("("), pr(E), format(")%~w", [K]).
pr(braces(_, E)) :- !, write("{"), pr(E), write("}").
pr(pure(_, E)) :- !, write("⌜"), pr(E), write("⌝").
pr(const(_, C)) :- !, write(C).
pr(unit(_)) :- !, write("()").
pr(insert(_, K, V)) :- !, write("<["), pr(K), write(" := "), pr(V), write("]>").
pr(proj(_, E, Op)) :- !, write("(("), pr(E), format(") ~w)", [Op]).
pr(gfunctors(_, Es)) :- !, write("#["), sep(Es, "; "), write("]").
pr(fupd(_, Ms, A)) :- !, write("(|={"), sep(Ms, ","), write("}=> "), pr(A), write(")").
pr(fupdw(_, Ms, L, R)) :- !, write("("), pr(L), write(" ={"), sep(Ms, ","), write("}=∗ "), pr(R), write(")").
pr(stepupd(_, Ms, N, A)) :- !, write("(|={"), sep(Ms, ","), write("}▷=>"), count(N), write(" "), pr(A), write(")").
pr(stepupdw(_, Ms, N, L, R)) :- !, write("("), pr(L), write(" ={"), sep(Ms, ","), write("}▷=∗"), count(N), write(" "), pr(R), write(")").
pr(laterN(_, N, A)) :- !, write("(▷^("), pr(N), write(") "), pr(A), write(")").
pr(ifis(_, C, P, T, E)) :- !,
    write("(if "), pr(C), write(" is "), pr(P), write(" then "), pr(T), write(" else "), pr(E), write(")").
pr(pointsto(_, Op, L, Ms, R)) :- !,
    write("("), pr(L), format(" ~w", [Op]),
    forall(member(M, Ms), ( M = name(G) -> write("["), pr(G), write("]")
                          ; M = dfrac(D) -> write("{"), pr(D), write("}")
                          ; M = own(Q) -> write("{#"), pr(Q), write("}") ; write("□") )),
    write(" "), pr(R), write(")").
pr(indexed(_, '✓', N, none, A)) :- !, write("(✓{"), pr(N), write("} "), pr(A), write(")").
pr(indexed(_, Op, N, L, R)) :- !,
    write("("), pr(L), format(" ~w{", [Op]), pr(N), write("}"), ( Op == '≡' -> write("≡") ; true ), write(" "), pr(R), write(")").
pr(wp(_, E, At, Post)) :- !, write("(WP "), pr(E), wp_at(At), write(" "), post(Post), write(")").
pr(triple(_, Pre, E, At, Bs, Ret, Post)) :- !,
    write("{{{ "), pr(Pre), write(" }}} "), pr(E), wp_at(At), write(" {{{"),
    ( Bs == [] -> true ; binders(Bs), write(",") ), write(" RET "), pr(Ret), write("; "), pr(Post), write(" }}}").
pr(bigop(_, Op, Kind, binds(K, Xs), Cs, B)) :- !,
    format("([~w ~w] ", [Op, Kind]), ( K = n(_, KN) -> format("~w ↦ ", [KN]) ; true ),
    maplist([n(_, X), X]>>true, Xs, Ns), atomic_list_concat(Ns, ';', NA), write(NA),
    write(" ∈ "), sep(Cs, ";"), write(", "), pr(B), write(")").
pr(bigall(_, Op, E)) :- !, format("([~w] ", [Op]), pr(E), write(")").
pr(eval(_, Ws, E)) :- !, atomic_list_concat(Ws, ' ', W), format("Eval ~w in ", [W]), pr(E).
pr(sig(_, n(_, X), T, Q)) :- !, format("{~w : ", [X]), pr(T), write(" | "), pr(Q), write("}").

wp_at(none).
wp_at(at(none, M)) :- !, write(" @ "), pr(M).
wp_at(at(S, M)) :- write(" @ "), pr(S), write("; "), pr(M).

post(post(none, Q)) :- !, write("{{ "), pr(Q), write(" }}").
post(post(n(_, X), Q)) :- format("{{ ~w, ", [X]), pr(Q), write(" }}").

quantifier(F-_, Glyph, Word, Q) :-
    nb_getval(text, Text), ( sub_string(Text, F, 1, _, Glyph) -> Q = Glyph ; Q = Word ).

names_c([n(_, N)]) :- !, write(N).
names_c([n(_, N)|Ns]) :- format("~w, ", [N]), names_c(Ns).

sep([E], _) :- !, pr(E).
sep([E|Es], S) :- pr(E), write(S), sep(Es, S).
sep([], _).

fsep([F]) :- !, fld(F).
fsep([F|Fs]) :- fld(F), write("; "), fsep(Fs).
fsep([]).
fld(fld(_, N, E)) :- format("~w := ", [N]), pr(E).
fld(fldb(_, N, Bs, E)) :- write(N), binders(Bs), write(" := "), pr(E).

scruts([S]) :- !, scrut(S).
scruts([S|Ss]) :- scrut(S), write(", "), scruts(Ss).
scrut(as(E, n(_, N))) :- !, pr(E), format(" as ~w", [N]).
scrut(E) :- pr(E).

alts([A]) :- !, sep(A, ", ").
alts([A|As]) :- sep(A, ", "), write(" | "), alts(As).

% Tactic grouping is made explicit too, so coqc checks its precedence
% and the embedded Gallina, not just the untouched source script.
pt(tbin(Op, L, R)) :- format("("), pt(L), format(" ~w ", [Op]), pt(R), write(")").
pt(prefix(K, T)) :- format("(~w ", [K]), pt(T), write(")").
pt(do(N, T)) :- format("(do ~w ", [N]), pt(T), write(")").
pt(select(S, T)) :- format("~w: ", [S]), pt(T).
pt(tgroup(T)) :- write("("), pt(T), write(")").
pt(choices(K, Ts)) :- format("~w [", [K]), pt_choices(Ts), write("]").
pt(dispatch(T, Ts)) :- write("("), pt(T), write("; ["), pt_choices(Ts), write("])").
pt(tmatch(K, Subject, Bs)) :-
    format("~w ", [K]), pt_subject(Subject), write(" with "),
    forall(member(tbr(Ps, T), Bs), ( write(" | "), pt_parts(Ps), write(" => "), pt(T) )), write(" end").
pt(call(N, Ps)) :- format("~w ", [N]), pt_parts(Ps).
pt(tlet(n(_, N), V, B)) :- format("(let ~w := ", [N]), pt(V), write(" in "), pt(B), write(")").
pt(empty).

pt_subject(goal) :- write("goal").
pt_subject(type(E)) :- write("type of "), pr(E).
pt_subject(term(E)) :- pr(E).

pt_choices([T]) :- !, pt(T).
pt_choices([T|Ts]) :- pt(T), write(" | "), pt_choices(Ts).

pt_parts([]).
pt_parts([P|Ps]) :- pt_part(P), write(" "), pt_parts(Ps).
pt_part(intro(Ps)) :- pt_intro_seq(Ps).
pt_part(ipm_intros(Is)) :- forall(member(I, Is), ( I = coq(Ps) -> write("("), pt_intro_seq(Ps), write(") ") ; I = str(S), format('"~w" ', [S]) )).
pt_part(ipm_as(Ps, Pat)) :-
    ( Ps == [] -> true ; write("("), pt_intro_seq(Ps), write(") ") ),
    ( Pat = str(S) -> format('"~w"', [S]) ; Pat = pure(P), write("%"), pt_intro(P) ).
pt_part(ipm(H, Args, Spat)) :-
    write("("), ( H = hyp(S) -> format('"~w"', [S]) ; pr(H) ),
    ( Args == [] -> true ; write(" $!"), forall(member(A, Args), ( write(" "), pr(A) )) ),
    ( Spat == none -> true ; format(' with "~w"', [Spat]) ), write(")").
pt_part(terms(Es)) :- sep(Es, ", ").
pt_part(clause(K, Ps)) :- write(K), ( K == eqn -> write(": ") ; write(" ") ), pt_parts(Ps).
pt_part(term(E)) :- pr(E).
pt_part(tactic(T)) :- write("("), pt(T), write(")").
pt_part(binding(n(_, N), Op, E)) :- format("(~w ~w ", [N, Op]), pr(E), write(")").
pt_part(context(E)) :- write("context ["), pr(E), write("]").
pt_part(hyp(n(_, N), context(E))) :- !, format("~w : ", [N]), pt_part(context(E)).
pt_part(hyp(n(_, N), E)) :- format("~w : ", [N]), pr(E).
pt_part(group(Open, Ps, Close)) :- write(Open), pt_parts(Ps), write(Close).
pt_part(token(str(S))) :- !, format('"~w"', [S]).
pt_part(token(K)) :- rocq_syntax:tok_text(K, S), write(S).

pt_intro(ip_name(n(_, N))) :- write(N).
pt_intro(ip_rewrite(Op)) :- write(Op).
pt_intro(ip_auto(K)) :- write(K).
pt_intro(ip_fresh(n(_, N))) :- format("?~w", [N]).
pt_intro(ip_and(Ps)) :- write("("), pt_intro_sep(Ps, " & "), write(")").
pt_intro(ip_or(Arms)) :- write("["), pt_intro_arms(Arms), write("]").
pt_intro(ip_inj(Ps)) :- write("[= "), pt_intro_seq(Ps), write("]").
pt_intro_seq(Ps) :- pt_intro_sep(Ps, " ").
pt_intro_sep([], _).
pt_intro_sep([P], _) :- !, pt_intro(P).
pt_intro_sep([P|Ps], S) :- pt_intro(P), write(S), pt_intro_sep(Ps, S).
pt_intro_arms([Ps]) :- !, pt_intro_seq(Ps).
pt_intro_arms([Ps|Arms]) :- pt_intro_seq(Ps), write(" | "), pt_intro_arms(Arms).

count(none) :- !.
count(N) :- write("^("), pr(N), write(")").
