/*  The documentation gate: every module in src/ has a header, and every
    exported predicate has PlDoc.

    Usage: swipl tests/docs.pl -- SRC-DIR

    A module's header is a block comment before anything else in the
    file, written in the little Markdown dterm reads (docs/dterm.md). An
    exported predicate Name/Arity is documented by a `%!` signature line
    for it, such as `%! valid_module(+M) is semidet.`, or a doc/3 fact
    whose head is Name with Arity arguments. An exported nonterminal
    Name//N is documented by a signature `%! name(+A)// is det.` or a
    doc/3 fact whose head has N arguments. Prints what is missing and
    exits 1, or prints a count and exits 0.

    SWI-Prolog only, as dterm is: it reads the signatures with SWI's
    term_string/3.
*/
:- initialization(main, main).

% PlDoc's argument modes, for reading signatures.
:- op(200, fy, docs_sig:(?)).
:- op(200, fy, docs_sig:(@)).
:- op(200, fy, docs_sig:(:)).

main :-
    current_prolog_flag(argv, [Dir]),
    directory_files(Dir, Names0),
    msort(Names0, Names),
    include([N]>>file_name_extension(_, pl, N), Names, Files),
    foldl(check_file(Dir), Files, 0-0, Missing-Exports),
    length(Files, NF),
    (   Missing =:= 0
    ->  format("docs: ~w modules with headers, ~w exports documented~n", [NF, Exports])
    ;   format("docs: ~w problems (docs/guide.md, Conventions)~n", [Missing]),
        halt(1)
    ).

check_file(Dir, File, M0-E0, M-E) :-
    directory_file_path(Dir, File, Path),
    read_file_to_string(Path, Text, [encoding(utf8)]),
    split_string(Text, "", " \t\n", [Trimmed]),
    (   string_concat("/*", _, Trimmed) -> M1 = M0
    ;   format("~w: no header comment~n", [File]), M1 is M0 + 1
    ),
    file_exports(Path, Exports),
    split_string(Text, "\n", "", Lines),
    findall(K, ( member(L, Lines), signature_key(L, K) ), SigKeys),
    file_doc_keys(Path, DocKeys, Defined),
    append(SigKeys, DocKeys, Keys),
    % An export the file does not define is a re-export, documented where
    % it is defined (filc_amd64's signature/3 is filc_abi's).
    include([X]>>( export_pi(X, PI), memberchk(PI, Defined),
                   \+ documented(X, Keys) ), Exports, Undocumented),
    forall(member(X, Undocumented),
           format("~w: ~q exported without %! or doc/3~n", [File, X])),
    length(Undocumented, NU),
    length(Exports, NE),
    M is M1 + NU,
    E is E0 + NE.

documented(N/A, Keys) :- memberchk(N/A, Keys), !.
documented(N//A, Keys) :- ( memberchk(N//A, Keys) ; memberchk(doc(N/A), Keys) ), !.
documented(N/A, Keys) :- memberchk(doc(N/A), Keys).

file_exports(Path, Exports) :-
    setup_call_cleanup(open(Path, read, S, [encoding(utf8)]),
                       read_term(S, T, [syntax_errors(quiet)]),
                       close(S)),
    (   T = (:- module(_, Exports)) -> true ; Exports = [] ).

% signature_key(+Line, -Key): Line is a %! signature of Name/Arity, or
% of the nonterminal Name//Arity when its head ends in //.
signature_key(Line, Key) :-
    string_concat("%!", S0, Line),
    split_string(S0, "", " .", [S1]),
    (   sub_string(S1, B, _, A, "//"), sub_string(S1, 0, B, _, H),
        sub_string(S1, _, A, 0, After), \+ sub_string(H, _, _, _, " is "),
        ( After == "" ; string_concat(" ", _, After) )
    ->  string_concat(H, After, S2), Dcg = true
    ;   S2 = S1, Dcg = false
    ),
    catch(term_string(T, S2, [module(docs_sig)]), _, fail),
    (   T = (Head is _) -> true ; Head = T ),
    callable(Head),
    functor(Head, N, Ar),
    (   Dcg == true -> Key = N//Ar ; Key = N/Ar ).

export_pi(N/A, N/A).
export_pi(N//A, N/A2) :- A2 is A + 2.

% file_doc_keys(+Path, -Keys, -Defined): Keys has doc(Name/Arity) for
% each doc/3 fact, and Defined the Name/Arity of every clause (a DCG
% rule's with its two list arguments).
file_doc_keys(Path, Keys, Defined) :-
    setup_call_cleanup(open(Path, read, S, [encoding(utf8)]), read_docs(S, Keys0), close(S)),
    findall(K, member(doc(K), Keys0), Ks), findall(D, member(def(D), Keys0), Ds),
    maplist([K, doc(K)]>>true, Ks, Keys), sort(Ds, Defined).

% A clause the reader cannot parse (clpz operators, say) is skipped.
read_docs(S, Keys) :-
    (   catch(read_term(S, T0, [syntax_errors(quiet)]), _, fail) -> T = T0 ; T = skip ),
    (   T == end_of_file -> Keys = []
    ;   T = doc(H, _, _), callable(H)
    ->  functor(H, N, A), Keys = [doc(N/A)|Keys1], read_docs(S, Keys1)
    ;   clause_pi(T, PI)
    ->  Keys = [def(PI)|Keys1], read_docs(S, Keys1)
    ;   read_docs(S, Keys)
    ).

clause_pi((:- _), _) :- !, fail.
clause_pi((H --> _), N/A) :- !, ( H = (H1, _) -> true ; H1 = H ),
    callable(H1), functor(H1, N, A0), A is A0 + 2.
clause_pi((H :- _), N/A) :- !, callable(H), functor(H, N, A).
clause_pi(H, N/A) :- callable(H), functor(H, N, A).
