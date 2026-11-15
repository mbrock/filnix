/* image.pl selects a few named items from a large linked image, so that a
   proof can name them without decoding the whole image. It is meant for an
   image too large to decode in Rocq, such as GNU Hello linked with the user
   glibc it reaches.

     swipl image.pl LINKED REFERENCE REPORT NAME...

   Each NAME, and the target of each selected alias, must have exactly one item
   in LINKED, and that item must be a function or an alias. Generation stops
   otherwise, because a lookup in the selection would then not be the lookup
   in LINKED. The selected items keep LINKED's order and terms. REFERENCE is
   another linked image, or `-` for none: when one is given, each selected
   name must have exactly one item there too, and it must be the same term.

   The selection goes to standard output as `module(Items).` REPORT receives
   one line per selected name, giving its kind, its alias target, and the
   SHA-256 of the item's canonical text. Uniqueness in LINKED and equality with
   REFERENCE are checks made here, by the producer: the proof sees only the
   selection. */
:- initialization(main, main).
:- use_module(library(sha)).

%  item_name(+Item, -Name) gives the name that an item defines.
item_name(func(N, _, _, _, _), N).
item_name(alias(N, _, _), N).
item_name(data(N, _, _, _), N).
item_name(outside(N, _), N).

%  named(+Items, +Name, -Matches) lists the items that define Name.
named(Is, N, Ms) :- include([I]>>item_name(I, N), Is, Ms).

fail_with(Format, Args) :- format(user_error, Format, Args), nl(user_error), halt(1).

%  closure(+Items, +Names, +Seen, -Closed) adds alias targets until none are new.
closure(_, [], Seen, Seen).
closure(Is, [N|Ns], Seen, Closed) :-
    (   memberchk(N, Seen) -> closure(Is, Ns, Seen, Closed)
    ;   named(Is, N, Ms),
        (   Ms = [] -> fail_with('missing name in linked image: ~w', [N])
        ;   Ms = [_, _|_] -> length(Ms, K), fail_with('~w items name ~w in linked image', [K, N])
        ;   Ms = [alias(N, _, T)] -> closure(Is, [T|Ns], [N|Seen], Closed)
        ;   Ms = [func(N, _, _, _, _)] -> closure(Is, Ns, [N|Seen], Closed)
        ;   fail_with('~w is neither a function nor an alias in linked image', [N])
        )
    ).

hex(Item, Hex) :-
    format(atom(Text), '~k', [Item]), atom_codes(Text, Codes),
    sha_hash(Codes, Hash, [algorithm(sha256)]), hash_atom(Hash, Hex).

%  compare_ref(+Ref, +Item, -Verdict) checks one selected item against REFERENCE.
compare_ref(none, _, 'no reference').
compare_ref(Rs, I, 'equal to reference') :-
    item_name(I, N), named(Rs, N, Ms),
    (   Ms == [I] -> true
    ;   fail_with('~w differs from the reference image', [N])
    ).

report(Out, Ref, I) :-
    item_name(I, N), compare_ref(Ref, I, Verdict), hex(I, Hex),
    (   I = alias(_, L, T) -> format(Out, '~w: unique alias (~w) of ~w, sha256 ~w, ~w~n', [N, L, T, Hex, Verdict])
    ;   format(Out, '~w: unique function, sha256 ~w, ~w~n', [N, Hex, Verdict])
    ).

main :-
    set_stream(user_output, encoding(utf8)),
    current_prolog_flag(argv, [F, R, Report|Ns0]),
    read_file_to_terms(F, [module(Is)], [encoding(utf8)]),
    (   R == '-' -> Ref = none ; read_file_to_terms(R, [module(Ref)], [encoding(utf8)]) ),
    maplist([S, A]>>atom_string(A, S), Ns0, Ns),
    closure(Is, Ns, [], Closed),
    include([I]>>(item_name(I, N), memberchk(N, Closed)), Is, Sel),
    setup_call_cleanup(open(Report, write, Out, [encoding(utf8)]),
                       maplist(report(Out, Ref), Sel), close(Out)),
    write_canonical(module(Sel)), write('.'), nl.
