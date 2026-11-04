/*  reprint.pl FILE OUT: FILE's tree, printed back as Nix with every
    subexpression in parentheses. nix-instantiate --parse prints the same
    for OUT as for FILE exactly when nix_syntax read FILE as Nix does:
    same precedence, associativity and nesting (parse.sh).
*/
:- use_module('../nix_syntax').
:- initialization(main, main).
main :- current_prolog_flag(argv, [F, Out]),
  nix_read_file(F, Text, nix(E, _)), nb_setval(text, Text),
  phrase(r(E), Cs), setup_call_cleanup(open(Out, write, S), format(S, "~s~n", [Cs]), close(S)).
src(F-T) --> { nb_getval(text, X), L is T-F, sub_string(X, F, L, _, S), string_codes(S, Cs) }, Cs.
p(G) --> "(", G, ")".
r(var(_, X)) --> { atom_codes(X, Cs) }, Cs.
r(int(P, _)) --> src(P).
r(float(P, _)) --> src(P).
r(str(_, Ps)) --> "\"", parts(Ps), "\"".
r(istr(_, Ps)) --> "''", parts(Ps), "''".
r(path(_, Ps)) --> parts(Ps).
r(spath(P, _)) --> src(P).
r(uri(P, _)) --> src(P).
r(paren(_, E)) --> p(r(E)).
r(list(_, Es)) --> "[ ", seqr(Es), "]".
r(attrs(_, Rec, Bs)) --> ( { Rec == rec } -> "rec " ; [] ), "{ ", binds(Bs), "}".
r(select(_, E, Path, D)) --> p(r(E)), ".", apath(Path), ( { D == none } -> [] ; " or ", p(r(D)) ).
r(app(_, F, As)) --> p(r(F)), " ", seqr(As).
r(lam(_, Param, B)) --> p((param(Param), ": ", p(r(B)))).
r(let(_, Bs, B)) --> p(("let ", binds(Bs), " in ", p(r(B)))).
r(with(_, E, B)) --> p(("with ", p(r(E)), "; ", p(r(B)))).
r(assert(_, E, B)) --> p(("assert ", p(r(E)), "; ", p(r(B)))).
r(if(_, C, T, E)) --> p(("if ", p(r(C)), " then ", p(r(T)), " else ", p(r(E)))).
r(bin(_, Op, L, R)) --> { atom_codes(Op, O) }, p((p(r(L)), " ", O, " ", p(r(R)))).
r(has(_, E, Path)) --> p((p(r(E)), " ? ", apath(Path))).
r(not(_, E)) --> p(("!", p(r(E)))).
r(neg(_, E)) --> p(("-", p(r(E)))).
seqr([]) --> [].
seqr([E|Es]) --> p(r(E)), " ", seqr(Es).
parts([]) --> [].
parts([lit(S)|Ps]) --> { string_codes(S, Cs) }, Cs, parts(Ps).
parts([interp(_, E)|Ps]) --> "${", r(E), "}", parts(Ps).
binds([]) --> [].
binds([bind(_, P, E)|Bs]) --> apath(P), " = ", p(r(E)), "; ", binds(Bs).
binds([inherit(_, F, Ns)|Bs]) --> "inherit ", ( { F == none } -> [] ; p(r(F)), " " ), names(Ns), "; ", binds(Bs).
names([]) --> [].
names([N|Ns]) --> attr(N), " ", names(Ns).
apath([A]) --> !, attr(A).
apath([A|As]) --> attr(A), ".", apath(As).
attr(aid(_, X)) --> { atom_codes(X, Cs) }, Cs.
attr(astr(_, Ps)) --> "\"", parts(Ps), "\"".
attr(ainterp(_, E)) --> "${", r(E), "}".
param(pid(X)) --> { atom_codes(X, Cs) }, Cs.
param(pset(Fs, Ell, At)) --> ( { At = before(X) } -> { atom_codes(X, C) }, C, " @ " ; [] ),
  "{ ", formals(Fs, Ell), "}", ( { At = after(Y) } -> { atom_codes(Y, C2) }, " @ ", C2 ; [] ).
formals([], true) --> "... ".
formals([], false) --> [].
formals([formal(_, X, D)|Fs], Ell) --> { atom_codes(X, C) }, C, ( { D == none } -> [] ; " ? ", p(r(D)) ), ( { Fs == [], Ell == false } -> " " ; ", " ), formals(Fs, Ell).
