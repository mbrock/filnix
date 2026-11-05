% A deterministic SWI-Prolog workload: each section prints what it
% computes, so the filcc and nanofil builds' outputs must be equal byte
% for byte. It runs the core (bignums, floats, the reader and writer,
% assert/retract, tabling, exceptions, garbage collection and stack
% shifts) and the packages whose C nanofil compiled (clpfd, sgml, pcre,
% yaml, sha/md5, uri, memfile, zlib, utf8proc, porter stemmer).
:- use_module(library(clpfd)).
:- use_module(library(sgml)).
:- use_module(library(pcre)).
:- use_module(library(yaml)).
:- use_module(library(sha)).
:- use_module(library(md5)).
:- use_module(library(uri)).
:- use_module(library(memfile)).
:- use_module(library(zlib)).
:- use_module(library(unicode)).
:- use_module(library(porter_stem)).
:- use_module(library(readutil)).

:- initialization(main, main).

section(Name, Goal) :-
    format("## ~w~n", [Name]),
    (   catch(Goal, E, (print_message(error, E), format("exception ~q~n", [E])))
    ->  true
    ;   format("failed~n")
    ).

main :-
    section(bignums, bignums),
    section(floats, floats),
    section(terms, terms),
    section(database, database),
    section(tabling, tabling_),
    section(exceptions, exceptions),
    section(gc, gc),
    section(clpfd, clpfd_),
    section(sgml, sgml_),
    section(pcre, pcre_),
    section(yaml, yaml_),
    section(hashes, hashes),
    section(uri, uri_),
    section(zlib, zlib_),
    section(unicode, unicode_),
    format("## done~n").

bignums :-
    numlist(1, 300, L), foldl([X,A0,A]>>(A is A0*X), L, 1, F300),
    format("300! = ~d~n", [F300]),
    X is 2**4423 - 1, Y is X mod 1000000007, format("M4423 mod p = ~d~n", [Y]),
    G is gcd(F300, 2**200*3**50), format("gcd = ~d~n", [G]),
    R is 22 rdiv 7 - 355 rdiv 113, format("rational = ~q~n", [R]),
    P is powm(3, 10**40, 10**9+9), format("powm = ~d~n", [P]),
    S is msb(F300), format("msb = ~d~n", [S]).

floats :-
    forall(member(X, [0.1, 1.0e-300, 2.5, 1.0e300, -0.0]),
           ( A is sin(X), B is exp(X/1.0e300), C is X*3, format("~15e ~15e ~w~n", [A, B, C]) )),
    Pi is pi, format("~20f~n", [Pi]),
    Z is 2.0**0.5, format("~w ~a~n", [Z, '']),
    format("~2f ~e ~g~n", [1/3, 12345.678, 0.000123]).

terms :-
    term_string(T, "foo(X, [a,b|Y], \"str\", 0'c, 1.5e10, {X,Y}, -(-(1)), 'hello world')"),
    show(T), \+ \+ ( numbervars(T, 0, _), write_canonical(T), nl ),
    length(L, 2000), maplist(=(x), L), atomic_list_concat(L, '-', A),
    atom_length(A, N), sub_atom(A, 10, 5, _, Sub), format("~d ~w~n", [N, Sub]),
    findall(B-Af, sub_atom(abcd, B, 2, Af, _), Subs), print(Subs), nl,
    string_code(1, "abc", C), format("~c~n", [C]),
    msort([c, 1, "s", 2.0, f(x), b, 1.0], S), print(S), nl,
    predsort([O,P1,P2]>>(compare(O, P2, P1)), [3,1,4,1,5,9,2,6], PS), print(PS), nl,
    copy_term([Z, Z, W], Copy), show(Copy-[Z,W]),
    numbervars(f(Q, R, Q), 0, End), print(f(Q, R, Q)-End), nl,
    phrase(digits(Ds), `12345abc`, Rest), atom_codes(DA, Ds), atom_codes(RA, Rest),
    format("~w ~w~n", [DA, RA]).

% show(+T): T printed with its variables named by position, the same
% whatever stack addresses they have.
show(T) :- \+ \+ ( numbervars(T, 0, _), print(T), nl ).

digits([D|T]) --> [D], { code_type(D, digit) }, !, digits(T).
digits([]) --> [].

:- dynamic fact/2.

database :-
    forall(between(1, 5000, I), assertz(fact(I, I))),
    aggregate_all(sum(V), fact(_, V), Sum), format("sum = ~d~n", [Sum]),
    forall(between(1, 5000, I), ( 0 =:= I mod 3 -> retract(fact(I, _)) ; true )),
    aggregate_all(count, fact(_, _), Count), format("count = ~d~n", [Count]),
    fact(4999, F), format("4999 -> ~d~n", [F]),
    retractall(fact(_, _)),
    setof(K-Vs, setof(V, member(K-V, [b-2, a-1, b-1, a-3, c-0]), Vs), KVs),
    print(KVs), nl.

:- table fib/2.
fib(0, 0).
fib(1, 1).
fib(N, F) :- N > 1, N1 is N-1, N2 is N-2, fib(N1, F1), fib(N2, F2), F is F1+F2.

:- table path/2.
edge(a, b). edge(b, c). edge(c, a). edge(c, d).
path(X, Y) :- edge(X, Y).
path(X, Y) :- path(X, Z), edge(Z, Y).

tabling_ :-
    fib(400, F), format("fib(400) = ~d~n", [F]),
    findall(X-Y, path(X, Y), Ps), msort(Ps, S), print(S), nl,
    abolish_all_tables.

exceptions :-
    catch(atom_length(_, _), error(E1, _), true), print(E1), nl,
    catch(atom_length(f(x), _), error(E2, _), true), print(E2), nl,
    catch(throw(my(x)), my(Y), true), print(Y), nl,
    catch(number_codes(_, "12x"), error(Err, _), true), print(Err), nl,
    catch(call_cleanup(throw(oops), format("cleanup~n")), oops, format("caught oops~n")).

gc :-
    numlist(1, 200000, L), sum_list(L, S), format("~d~n", [S]),
    findall(X-Y, (between(1, 300, X), between(1, 300, Y)), Ps), length(Ps, N), format("~d~n", [N]),
    length(Big, 300000), maplist([E]>>(E = f(_, a)), Big),
    garbage_collect, garbage_collect_atoms,
    deep(100000, D), format("~d~n", [D]),
    atom_garbage(2000), garbage_collect_atoms,
    format("ok~n").

deep(0, 0) :- !.
deep(N, D) :- N1 is N-1, deep(N1, D1), D is D1+1.

atom_garbage(N) :-
    forall(between(1, N, I), (format(atom(A), "atom_~d", [I]), atom_length(A, _))).

clpfd_ :-
    puzzle(P), format("~w~n", [P]),
    findall(Qs, (length(Qs, 8), queens(Qs)), All), length(All, NQ), All = [Q1|_],
    format("~d ~w~n", [NQ, Q1]),
    X #> 3, X #< 6, findall(X, label([X]), Xs), print(Xs), nl.

puzzle([S,E,N,D] + [M,O,R,E] = [M,O,N,E,Y]) :-
    Vars = [S,E,N,D,M,O,R,Y], Vars ins 0..9, all_different(Vars),
    S*1000 + E*100 + N*10 + D + M*1000 + O*100 + R*10 + E #=
    M*10000 + O*1000 + N*100 + E*10 + Y, M #\= 0, S #\= 0, label(Vars).

queens(Qs) :-
    length(Qs, N), Qs ins 1..N, safe(Qs), labeling([ff], Qs).
safe([]).
safe([Q|Qs]) :- no_attack(Q, Qs, 1), safe(Qs).
no_attack(_, [], _).
no_attack(Q, [Q1|Qs], D) :- Q #\= Q1, abs(Q - Q1) #\= D, D1 is D+1, no_attack(Q, Qs, D1).

sgml_ :-
    XML = "<doc a='1'><p>Hello &amp; <b>bye</b></p><e/><![CDATA[x<y]]></doc>",
    open_string(XML, In), load_structure(In, DOM, [dialect(xml), space(remove)]), close(In),
    print(DOM), nl,
    with_output_to(string(Out), xml_write(current_output, DOM, [header(false)])),
    format("~s~n", [Out]).

pcre_ :-
    re_matchsub("(?<y>\\d{4})-(?<m>\\d\\d)", "on 2026-11-04 at", D, []),
    print(D), nl,
    re_replace("a+"/g, "<\\0>", "caaandy aardvark", R), format("~w~n", [R]),
    re_split("\\s*,\\s*", "a , b,c ,d", Parts), print(Parts), nl,
    re_foldl([Mt,V0,[W|V0]]>>get_dict(0, Mt, W), "\\w+", "one two three", [], Ms, []),
    print(Ms), nl.

yaml_ :-
    yaml_read(string("a: 1\nb: [x, 2.5, true]\nc:\n  d: null\n  e: 'str'\n"), Y),
    print(Y), nl,
    with_output_to(string(S), yaml_write(current_output, Y)), format("~s", [S]).

hashes :-
    sha_hash("The quick brown fox", H1, [algorithm(sha256)]), hash_atom(H1, A1), format("~w~n", [A1]),
    sha_hash("", H2, [algorithm(sha1)]), hash_atom(H2, A2), format("~w~n", [A2]),
    md5_hash("hello", M, []), format("~w~n", [M]).

uri_ :-
    uri_components('https://user@example.org:8080/a/b%20c?q=1&r=two#frag', C), print(C), nl,
    uri_encoded(query_value, 'a b&c=d', E), format("~w~n", [E]),
    uri_normalized('HTTP://Example.ORG/a/./b/../c', N), format("~w~n", [N]).

zlib_ :-
    numlist(1, 2000, L), format(string(S), "~w", [L]),
    new_memory_file(MF),
    open_memory_file(MF, write, Out0, [encoding(octet)]),
    zopen(Out0, Out, [format(gzip)]), write(Out, S), close(Out),
    size_memory_file(MF, Size, octet), format("compressed ~w~n", [Size]),
    open_memory_file(MF, read, In0, [encoding(octet)]),
    zopen(In0, In, []), read_string(In, _, S2), close(In),
    ( S2 == S -> format("roundtrip ok~n") ; format("roundtrip differs~n") ).

unicode_ :-
    unicode_nfkd('ﬁ é', D), atom_codes(D, Cs), print(Cs), nl,
    unicode_property(0'A, category(G)), print(G), nl,
    porter_stem(running, St), tokenize_atom('The runners ran 3.5 miles!', T),
    print(St-T), nl.
