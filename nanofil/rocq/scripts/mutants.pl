/*  Mutants of a checked module, judged by ir:valid_module/1, for the
    Rocq model's validator gate (docs/rocq.md, rocq/scripts/valid.sh).

    Reads `nanofil outcomes FILE`'s output on stdin and keeps its first
    term, the checked module, without its context(_, _) items. Prints
    that module, then verdict(Name, At, Id, Change, Verdict) for each
    item and each of its mutants: Change is replace(Item), delete or
    insert(Item) at the index At of the module's items, Id names the
    mutation (base for the item as it is), and Verdict is valid when
    valid_module/1 accepts the changed module, else invalid. Run from
    nanofil/src:

      ../bin/nanofil outcomes FILE | ../bin/nanofil --script ../rocq/scripts/mutants.pl

    Optional arguments I N select item indices congruent to I modulo N
    (0 <= I < N). Every partition still validates the whole changed
    module; partition 0 also emits the inserted-item verdicts. Joining
    the partitions' verdicts gives the unpartitioned stream exactly once.
    --base instead emits only unchanged-item verdicts, generating no
    mutations, for the routine quick gate.

    The mutations aim at what the validator decides. In a function: a
    check deleted or moved from its access, a check narrowed or its
    rights or alignment changed, a raw access moved, a cas given another
    type, a poll edge removed, a free inserted between evidence and its
    use, a reuse form given another proof, a cas's own check deleted
    and another proof read instead. A data object: its alignment, its linkage, an
    item of each shape the validator looks at, deleted or renamed. An
    alias: its linkage, target and name, or deleted. And a data object
    or an alias inserted. At most 150 per item are kept, evenly spaced.
    A mutant that would make the module plain is skipped: the model
    judges Fil-C modules only.
*/
:- use_module('../../src/ir').
:- use_module('../../src/provenance', [code_items/2]).
:- use_module(library(lists)).
:- use_module(library(aggregate)).

:- initialization(main).

main :-
    current_prolog_flag(argv, Args),
    (   Args = ['--base'] -> Base = true, Parts = []
    ;   Base = false, Parts = Args
    ),
    (   Parts = []
    ->  Shard = 0, Shards = 1
    ;   catch((Parts = [I, N], atom_number(I, Shard), atom_number(N, Shards),
               integer(Shard), integer(Shards), Shards > 0,
               Shard >= 0, Shard < Shards), _, fail)
    ->  true
    ;   format(user_error, 'mutants.pl: expected I N, 0 <= I < N~n', []), halt(2)
    ),
    read_term(user_input, module(All), []),
    code_items(All, Items),
    format("~k.~n", [module(Items)]),
    forall((nth0(At, Items, Item), At mod Shards =:= Shard),
           ( Base == true
           -> item_name(Item, Name), emit(Items, Name, At, base, replace(Item))
           ;  item_verdicts(Items, At, Item) )),
    (   Base == false, Shard =:= 0
    ->  thinned(inserted(Items, Name, Id, Change),
                emit(Items, Name, 0, Id, Change))
    ;   true
    ),
    halt.

item_verdicts(Items, At, Item) :-
    item_name(Item, Name),
    emit(Items, Name, At, base, replace(Item)),
    thinned(item_mutant(Items, Item, Id, Change),
            emit(Items, Name, At, Id, Change)).

% thinned(:Generator, :Action): Action for at most 150 of
% Generator's solutions, evenly spaced, each built and dropped in turn:
% a large function has too many mutants to hold at once.
thinned(Generator, Action) :-
    aggregate_all(count, Generator, N),
    Step is max(1, (N + 149) // 150),
    Count = count(0),
    forall(Generator,
           ( arg(1, Count, I), I1 is I + 1, nb_setarg(1, Count, I1),
             ( I mod Step =:= 0 -> Action ; true ) )).

item_name(func(N, _, _, _, _), N).
item_name(data(N, _, _, _), N).
item_name(alias(N, _, _), N).

emit(Items, Name, At, Id, Change) :-
    changed(Items, At, Change, Items1),
    (   module_mode(module(Items1), filc)
    ->  (   catch(once(valid_module(module(Items1))), _, fail) -> V = valid ; V = invalid ),
        format("~k.~n", [verdict(Name, At, Id, Change, V)])
    ;   true
    ).

changed(Items, At, replace(I), Items1) :- nth0(At, Items, _, Rest), nth0(At, Items1, I, Rest).
changed(Items, At, delete, Items1) :- nth0(At, Items, _, Items1).
changed(Items, At, insert(I), Items1) :- nth0(At, Items1, I, Items).

item_mutant(_, F, Id, replace(F1)) :-
    F = func(_, _, _, _, _),
    mutant(F, Id, F1).
item_mutant(Items, D, Id, Change) :-
    D = data(_, _, _, _),
    data_mutant(Items, D, Id, Change).
item_mutant(Items, A, Id, Change) :-
    A = alias(_, _, _),
    alias_mutant(Items, A, Id, Change).

% data_mutant(+Items, +D, -Id, -Change): D's alignment, linkage or items
% changed (an item appended, or one prepended, which moves every pointer
% item after it), D renamed, also to another item's name, or D deleted.
data_mutant(_, data(N, Lk, Al, Is), align(Al1), replace(data(N, Lk, Al1, Is))) :-
    Al2 is Al * 2,
    member(Al1, [0, 3, Al2, 8192]), Al1 \== Al.
data_mutant(Items, data(N, Lk, Al, Is), linkage(Lk1), replace(data(N, Lk1, Al, Is1))) :-
    linkage(Items, Lk1, Is, Is1), Lk1 \== Lk.
data_mutant(Items, data(N, Lk, Al, Is), item(I), replace(data(N, Lk, Al, Is1))) :-
    data_item(Items, N, I), append(Is, [I], Is1).
data_mutant(_, data(N, Lk, Al, Is), prepend(I), replace(data(N, Lk, Al, [I|Is]))) :-
    member(I, [item(b, const(1)), item(x, const(0)), item(l, const(0))]).
data_mutant(Items, data(N, Lk, Al, Is), rename(N1), replace(data(N1, Lk, Al, Is))) :-
    other_name(Items, N, N1).
data_mutant(_, data(_, _, _, _), delete, delete).

% linkage(+Items, -Linkage, +Is, -Is1): a linkage, and the items it is
% tried with (an init entry's own, a weak declaration's none).
linkage(_, Lk, Is, Is) :-
    member(Lk, [export, local, weak, ro(export), ro(local), ro(weak), ro(tls),
                tls(export), tls(local), tls(weak), extern(weak),
                init(ctor, none), init(other, none), common]).
linkage(_, extern(weak), _, []).
linkage(Items, init(K, P), _, [item(p, sym(F, Off))]) :-
    once(member(func(F, _, _, _, _), Items)),
    member(K-P-Off, [ctor-none-0, dtor-101-0, ctor-65535-0, ctor-70000-0, ctor-none-8]).
linkage(Items, init(ctor, none), _, [item(p, sym(D, 0))]) :-
    findall(D1, ( member(data(D1, Lk, _, _), Items), Lk \== extern(weak) ), Ds0),
    ( Ds0 = [D0|_] -> Ds = [rocq_undefined, D0] ; Ds = [rocq_undefined] ),
    member(D, Ds).

% data_item(+Items, +N, -I): an item of each shape the validator reads.
data_item(Items, N, I) :-
    char_code(C256, 256), char_code(C19968, 19968),
    (   member(I, [item(s, const(-1)), item(s, const(4294967295)), item(s, const(4294967296)),
                   item(d, const(18446744073709551616)), item(x, const(1)), item(s, foo),
                   item(l, sym(N, 0)), item(p, sym(N, 0)), item(w, const(7)),
                   item(b, str([a, b])), item(b, str([ab])), item(b, str([C256])),
                   item(b, str([C19968])), item(w, str([a])), item(b, str(a)),
                   item(w, foo), zero(3), bar, zero(-1), item(q, const(1)),
                   item(p, sym(N, x)), item(p, sym(3, 0))])
    ;   once(member(func(F, _, _, _, _), Items)), I = item(p, sym(F, 8))
    ;   once(member(data(E, init(_, _), _, _), Items)), I = item(p, sym(E, 0))
    ).

% other_name(+Items, +N, -N1): a fresh name, or the name of another item.
other_name(_, _, rocq_fresh).
other_name(Items, N, N1) :-
    once(( member(I, Items), item_name(I, N1), N1 \== N, I = func(_, _, _, _, _) )).
other_name(Items, N, N1) :-
    once(( member(I, Items), item_name(I, N1), N1 \== N, I = data(_, _, _, _) )).

% alias_mutant(+Items, +A, -Id, -Change): A's linkage, target or name
% changed, or A deleted.
alias_mutant(_, alias(N, Lk, T), linkage(Lk1), replace(alias(N, Lk1, T))) :-
    member(Lk1, [export, weak, local, ro(export)]), Lk1 \== Lk.
alias_mutant(Items, alias(N, Lk, T), target(T1), replace(alias(N, Lk, T1))) :-
    target(Items, T1), T1 \== T.
alias_mutant(_, alias(N, Lk, T), target(N), replace(alias(N, Lk, N))) :- T \== N.
alias_mutant(Items, alias(N, Lk, T), rename(N1), replace(alias(N1, Lk, T))) :-
    other_name(Items, N, N1).
alias_mutant(_, alias(_, _, _), delete, delete).

% target(+Items, -T): the first function, the first data object of each
% linkage, and a name the module does not define.
target(Items, T) :-
    once(member(func(T, _, _, _, _), Items)).
target(Items, T) :-
    findall(Lk, member(data(_, Lk, _, _), Items), Lks0), sort(Lks0, Lks),
    member(Lk, Lks), once(member(data(T, Lk, _, _), Items)).
target(_, rocq_undefined).

% inserted(+Items, -Name, -Id, -Change): a data object or an alias
% inserted at the front: an alias of each target under a fresh name and
% under the name of a function the module calls without defining; a
% data object of each linkage, one under the first function's name, and
% a weak declaration of a name the module defines.
inserted(Items, Name, alias(Name, T), insert(alias(Name, export, T))) :-
    findall(T, target(Items, T), Ts0), sort(Ts0, Ts),
    member(T, Ts),
    (   Name = rocq_alias
    ;   once(( member(func(_, _, _, _, Bs), Items), member(block(_, _, Is, _), Bs),
               member(call(_, global(Name), _), Is),
               \+ member(func(Name, _, _, _, _), Items) ))
    ).
inserted(Items, rocq_data, data(Lk1), insert(data(rocq_data, Lk1, 8, Is1))) :-
    linkage(Items, Lk1, [item(w, const(1))], Is1).
inserted(Items, F, data_named_as(F), insert(data(F, export, 8, [item(w, const(1))]))) :-
    once(member(func(F, _, _, _, _), Items)).
inserted(Items, N, weak_declaration_of(N), insert(data(N, extern(weak), 1, []))) :-
    (   once(member(func(N, export, _, _, _), Items))
    ;   once(member(func(N, local, _, _, _), Items))
    ;   member(Lk, [export, local, ro(local), tls(local)]),
        once(member(data(N, Lk, _, _), Items))
    ).

% mutant(+F, -Id, -F1): F1 is F mutated as Id says.
mutant(F, Id, F1) :-
    F = func(Fn, Lk, Ret, Ps, Bs),
    nth0(B, Bs, block(L, Phis, Is, J)),
    block_mutant(Is, J, F, Id0, Is1, J1),
    Id = at(L, Id0),
    nth0(B, Bs, _, Rest), nth0(B, Bs1, block(L, Phis, Is1, J1), Rest),
    F1 = func(Fn, Lk, Ret, Ps, Bs1).

block_mutant(Is, J, _, delete(I), Is1, J) :-
    nth0(I, Is, _, Is1).
block_mutant(Is, J, _, swap(I), Is1, J) :-
    append(Pre, [A, B|Post], Is), length(Pre, I),
    append(Pre, [B, A|Post], Is1).
block_mutant(Is, J, _, Id, Is1, J) :-
    nth0(I, Is, Inst, Rest),
    inst_mutant(Inst, Id0, Inst1),
    Id = change(I, Id0),
    nth0(I, Is1, Inst1, Rest).
block_mutant(Is, J, _, free(I), Is1, J) :-
    nth0(I, Is, _),
    nth0(I, Is1, call(void, global(free), [arg(p, const(0))]), Is).
block_mutant(Is, J, F, Id, Is1, J) :-
    nth0(I, Is, let(D, a, Op, [tmp(Q1)|Args]), Rest),
    memberchk(Op, [renew(_, _, _, _), half_check(_, _, _, _, _), renew_hull(_, _, _, _)]),
    other_proof(F, Q1, Q2),
    Id = reprove(I, Q2),
    nth0(I, Is1, let(D, a, Op, [tmp(Q2)|Args]), Rest).
% A cas reads another proof, its own check deleted: a scalar raw access
% could reuse a live proof there, a cas may not (reusing_access/2).
block_mutant(Is, J, F, reuse_cas(I, Q2), Is1, J) :-
    append(Pre, [let(tmp(Q1), a, _, _), let(D, K, raw_cas(T, Off), [tmp(Q1)|Args])|Post], Is),
    length(Pre, I),
    other_proof(F, Q1, Q2),
    append(Pre, [let(D, K, raw_cas(T, Off), [tmp(Q2)|Args])|Post], Is1).
block_mutant(Is, J, _, unpoll, Is, J1) :-
    jump_unpolled(J, J1).

jump_unpolled(goto(poll(L)), goto(L)).
jump_unpolled(branch(V, poll(L), T), branch(V, L, T)).
jump_unpolled(branch(V, T, poll(L)), branch(V, T, L)).

other_proof(func(_, _, _, _, Bs), Q1, Q2) :-
    once(( member(block(_, _, Is, _), Bs), member(let(tmp(Q2), a, _, _), Is), Q2 \== Q1 )).

inst_mutant(let(D, a, Op, Args), Id, let(D, a, Op1, Args)) :- check_mutant(Op, Id, Op1).
inst_mutant(let(D, K, raw_load(T, Off), Args), off(Dlt), let(D, K, raw_load(T, Off1), Args)) :-
    member(Dlt, [-1, 1]), Off1 is Off + Dlt.
inst_mutant(raw_store(W, Off, V, A), off(Dlt), raw_store(W, Off1, V, A)) :-
    member(Dlt, [-1, 1]), Off1 is Off + Dlt.
% A cas moved off its width's alignment or out of its check, or given
% another type: another width (still covered when narrower) or another
% class (refused unless load(T) allows the result class).
inst_mutant(let(D, K, raw_cas(T, Off), Args), off(Dlt), let(D, K, raw_cas(T, Off1), Args)) :-
    member(Dlt, [-1, 1, 4]), Off1 is Off + Dlt.
inst_mutant(let(D, K, raw_cas(T, Off), Args), cas_type(T1), let(D, K, raw_cas(T1, Off), Args)) :-
    member(T1, [l, p, sw, uh, ub]), T1 \== T.

check_mutant(Op, Id, Op1) :-
    Op =.. [Name|Xs], check_bounds(Name, Pre, Xs, Lo, Hi, R, Al, Post),
    (   Lo1 is Lo + 1, Lo1 < Hi, Id = lo, append(Pre, [Lo1, Hi, R, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   Hi1 is Hi - 1, Lo < Hi1, Id = hi, append(Pre, [Lo, Hi1, R, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   flip(R, R1), Id = rights, append(Pre, [Lo, Hi, R1, Al|Post], Pre1), Op1 =.. [Name|Pre1]
    ;   Al < 16, Al1 is Al * 2, Id = align, append(Pre, [Lo, Hi, R, Al1|Post], Pre1), Op1 =.. [Name|Pre1]
    ).

flip(read, write).
flip(write, read).

% check_bounds(+Name, -Pre, +Xs, -Lo, -Hi, -Rights, -Align, -Post): a
% check-like op's arguments around its (Lo, Hi, Rights, Align).
check_bounds(Name, [], [Lo, Hi, R, Al], Lo, Hi, R, Al, []) :-
    memberchk(Name, [check, renew, renew_hull, renew_if, check_limit]).
check_bounds(check_ahead, [], [Lo, Hi, R, Al, AHi], Lo, Hi, R, Al, [AHi]).
check_bounds(half_check, [B], [B, Lo, Hi, R, Al], Lo, Hi, R, Al, []).
