/*  Scheduled checks (docs/schedule.md): a check of a struct pointer
    covers, early, the bytes that every path ahead of it will need, so
    that the later checks of the same object become renewals.

    FilPizlonator's scheduleChecks moves bounds requirements backward to
    where every path will need them, and merges them into one range
    check. This pass does the part of that which pays in nanofil, in two
    steps that keep every check where it is:

    1. **Widen.** A heap check of P, a pointer at an exact offset K from
       a single-definition base B (ir.pl's guard_chain/3), whose access
       is followed on every path, before anything but the closed list
       crossable/1, a poll edge or an edge back, by accesses through B
       that reach B + H, becomes `check_ahead(Lo, H - K, Rights, Align,
       Hi)`. Only the upper end moves. Its trap comes earlier than the
       reference's only on executions on which the reference traps later.
    2. **Renew at a distance.** Every check that a dominating check or
       check_ahead of the same base covers, shifted by their distance,
       becomes a renew (check_reuse's renew_checks/3 with `any`), a flag
       test.

    ## Facts

    | Fact | Means |
    |---|---|
    | `B-H` in `need` | every path from here, before a blocker, accesses bytes through base `tmp(B)` reaching B + H |

    A block's exit facts are the meet of what its edges carry (a plain
    edge to a later block: that block's entry facts; any other edge:
    none), each base keeping its least H. Walking backward, an
    instruction that is not crossable/1 ends every fact, a definition of
    B ends B's fact, and an access raises the needs of its pointer's
    exact bases. The validator (ir.pl's ahead_justified/3) recomputes
    the same facts by its own code and accepts each check_ahead only if
    they justify it; schedule_refines/2 checks that nothing else
    changed.

    The pass is selected with `--checks=schedule`, after reuse and
    renewal; it is opt-in, since it changes when a trap happens.
*/
:- module(schedule, [schedule_checks/2, schedule_refines/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(ir, [single_definitions/3, guard_chain/3, access_size_align/3,
                   pointer_memory_effects/2]).
:- use_module(check_reuse, [renew_checks/3]).

%! schedule_checks(+M0, -M) is det.
%
%  M is the checked module M0 with each heap check widened to a
%  check_ahead over the bytes that every path ahead needs from its
%  base, then each check that a dominating check or check_ahead covers
%  at a distance renewed. Functions with a setjmp are unchanged.
schedule_checks(M0, M) :-
    M0 = module(Items0),
    maplist(widened_item, Items0, Items1),
    renew_checks(any, module(Items1), module(Items2)),
    maplist(repointed_item, Items1, Items2, Items),
    M = module(Items).

/* repointed_item(+Item1, +Item2, -Item): a renew that renewal at
   distance 0 made reads a check's proof Q; when this pass renewed that
   check too, from Q1, the renew reads Q1 instead (its root, following
   such renewals), which covers it by transitivity: Q1's check covers
   Q's range shifted by their distance, and Q's covered the renew's. */
repointed_item(func(_, _, _, _, Bs1), func(N, L, R, Ps, Bs2), func(N, L, R, Ps, Bs)) :- !,
    findall(Q-Q1, ( nth0(I, Bs1, block(_, _, Is1, _)), nth0(I, Bs2, block(_, _, Is2, _)),
                    nth0(J, Is1, let(tmp(Q), a, Op, _)), Op \= renew(_, _, _, _),
                    nth0(J, Is2, let(tmp(Q), a, renew(_, _, _, _), [tmp(Q1), _])) ),
            Pairs0),
    (   Pairs0 == [] -> Bs = Bs2
    ;   sort(Pairs0, Pairs), list_to_assoc(Pairs, Moved),
        maplist(repointed_block(Moved), Bs2, Bs)
    ).
repointed_item(_, Item, Item).

repointed_block(Moved, block(L, Ph, Is0, J), block(L, Ph, Is, J)) :-
    maplist(repointed_inst(Moved), Is0, Is).

repointed_inst(Moved, let(Q, a, renew(Lo, Hi, Rs, Al), [tmp(S0), P]),
               let(Q, a, renew(Lo, Hi, Rs, Al), [tmp(S), P])) :- !,
    root_source(Moved, S0, S).
repointed_inst(_, I, I).

root_source(Moved, S0, S) :-
    (   get_assoc(S0, Moved, S1) -> root_source(Moved, S1, S) ; S = S0 ).

widened_item(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :-
    \+ ( member(block(_, _, Is, _), Bs0), member(let(_, _, setjmp(_), _), Is) ),
    member(block(_, _, Is0, _), Bs0), member(let(_, a, check(_, _, _, _), _), Is0), !,
    single_definitions(Ps, Bs0, Once),
    findall(Q-P, ( member(block(_, _, Is, _), Bs0),
                   member(let(tmp(Q), a, Op, Args), Is),
                   proven_pointer(Op, Args, P),
                   get_assoc(Q, Once, _) ), QPs0),
    sort(QPs0, QPs), list_to_assoc(QPs, Proven),
    findall(Lb-Ix, nth1(Ix, Bs0, block(Lb, _, _, _)), Pos0),
    list_to_assoc(Pos0, Pos),
    reverse(Bs0, Rev),
    empty_assoc(E),
    foldl(widened_block(Once-Proven, Pos), Rev, E-[], _-RevBs),
    Bs = RevBs.
widened_item(Item, Item).

proven_pointer(check(_, _, _, _), [P], P).
proven_pointer(renew(_, _, _, _), [_, P], P).
proven_pointer(renew_if(_, _, _, _), [P, _], P).
proven_pointer(check_limit(_, _, _, _), [P, _], P).

% widened_block(+Env, +Pos, +Block, +Entries0-Done0, -Entries-Done):
% Entries maps each walked block to its entry needs; Done collects the
% widened blocks, front first, as the walk goes from the last block.
widened_block(Env, Pos, block(L, Phis, Is0, J), Entries0-Done0, Entries-[block(L, Phis, Is, J)|Done0]) :-
    get_assoc(L, Pos, Here),
    findall(T, jump_target_edge(J, T), Ts),
    maplist(carried(Pos, Here, Entries0), Ts, Carried),
    meet(Carried, Exit),
    reverse(Is0, Rev0),
    need_walk(Rev0, Env, Exit, none, Entry0, [], Is),
    foldl(phi_kill, Phis, Entry0, Entry),
    put_assoc(L, Entries0, Entry, Entries).

jump_target_edge(goto(T), T).
jump_target_edge(branch(_, T, _), T).
jump_target_edge(branch(_, _, T), T).

carried(_, _, _, poll(_), E) :- !, empty_assoc(E).
carried(Pos, Here, Entries, T, Need) :-
    (   get_assoc(T, Pos, There), There > Here, get_assoc(T, Entries, Need0)
    ->  Need = Need0
    ;   empty_assoc(Need)
    ).

meet([], E) :- empty_assoc(E).
meet([N|Ns], M) :-
    assoc_to_list(N, Ps),
    include(in_all(Ns), Ps, Ks),
    maplist(least(Ns), Ks, Ms),
    list_to_assoc(Ms, M).

in_all(Ns, B-_) :- forall(member(N, Ns), get_assoc(B, N, _)).
least(Ns, B-H0, B-H) :-
    foldl([N, A0, A]>>(get_assoc(B, N, A1), A is min(A0, A1)), Ns, H0, H).

% need_walk(+RevInsts, +Env, +After, +AfterNext, -Before, +Acc, -Insts):
% Insts are the block's instructions (Acc holds those after them), each
% widened check rewritten; After are the needs after the first of
% RevInsts, AfterNext those after the instruction that follows it.
need_walk([], _, Need, _, Need, Is, Is).
need_walk([I0|Rev], Env, After, Next, Before, Acc, Is) :-
    widened(I0, Env, Next, Acc, I),
    need_before(I0, Env, After, Need),
    need_walk(Rev, Env, Need, After, Before, [I|Acc], Is).

widened(let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Once-_, Next, [Access|_],
        let(tmp(Q), a, check_ahead(Lo, Hi1, Rights, Align, Hi), [P])) :-
    Next \== none,
    % Its own access runs after the early trap point, so it must be
    % crossable too (not a pointer store or an atomic).
    crossable(Access),
    guard_chain(Once, P, Chain),
    findall(H1, ( member(tmp(B)-i(K, K), Chain), get_assoc(B, Once, _), near(K),
                  get_assoc(B, Next, H), H1 is H - K ), H1s),
    max_list(H1s, Hi1),
    Hi1 > Hi, Hi1 - Lo =< 2147483647, !.
widened(I, _, _, _, I).

need_before(I, Once-Proven, After, Need) :-
    (   crossable(I)
    ->  (   defines(I, D), del_assoc(D, After, _, N1) -> true ; N1 = After ),
        (   heap_access(I, Q, X, Off), access_size_align(X, Size, _),
            get_assoc(Q, Proven, P)
        ->  guard_chain(Once, P, Chain),
            foldl(needs(Once, Off, Size), Chain, N1, Need)
        ;   Need = N1
        )
    ;   empty_assoc(Need)
    ).

needs(Once, Off, Size, tmp(B)-i(K, K1), N0, N) :-
    K == K1, get_assoc(B, Once, _),
    H is K + Off + Size, near(K), near(H), !,
    (   get_assoc(B, N0, H0), H0 >= H -> N = N0 ; put_assoc(B, N0, H, N) ).
needs(_, _, _, _, N, N).

% near(+K): offsets are exact only modulo 2^64; count only those well
% inside the signed range (ir.pl's near_offset/1, by its own code).
near(K) :- K >= -(1 << 62), K =< 1 << 62.

phi_kill(phi(tmp(D), _, _), N0, N) :- ( del_assoc(D, N0, _, N) -> true ; N = N0 ).

defines(let(tmp(D), _, _, _), D).
defines(flight(tmp(D), _, _, _), D).

heap_access(let(_, _, raw_load(T, Off), [tmp(Q)]), Q, T, Off).
heap_access(raw_store(W, Off, _, tmp(Q)), Q, W, Off).
heap_access(let(_, p, raw_load_pointer(Off, _), [tmp(Q)]), Q, p, Off).

/* crossable(+Inst): a check may be widened past Inst toward a later
   access: Inst cannot exit to the runtime, call, free, run a signal
   handler, fault otherwise than a Fil-C trap or loop. Pointer stores
   (ensure-aux may exit), calls, allocation, getters, atomics, setjmp,
   va_arg and division are not. */
crossable(loc(_, _)).
crossable(touch(_)).
crossable(flight(_, _, _, _)).
crossable(raw_store(W, _, _, _)) :- W \== p.
crossable(let(_, p, raw_load_pointer(_, Es), _)) :- pointer_memory_effects(load, Es), !.
crossable(let(_, _, Op, Args)) :- crossable_op(Op, Args).

crossable_op(check(_, _, _, _), _).
crossable_op(check_ahead(_, _, _, _, _), _).
crossable_op(renew(_, _, _, _), _).
crossable_op(raw_load(T, _), _) :- T \== p.
crossable_op(cmp(_, _), _).
crossable_op(ext(_), _).
crossable_op(copy, Args) :- \+ memberchk(global(_), Args).
crossable_op(Op, _) :-
    memberchk(Op, [add, sub, mul, and, or, xor, sar, shr, shl, neg, ptoi, cast]).

%! schedule_refines(+M0, +M) is semidet.
%
%  M is M0 except for heap checks, each at its own index with its own
%  pointer, rights, alignment and lower end, that became a check_ahead
%  of a wider range whose access's own range is the check's, or a renew
%  of at least the check's range. This is identity, not safety or
%  timing: the validator (ir.pl) accepts each check_ahead only where its
%  early bytes are needed ahead, and each renew only where an earlier
%  check covers it.
schedule_refines(module(Items0), module(Items)) :-
    maplist(item_refines, Items0, Items).

item_refines(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    maplist(block_refines, Bs0, Bs).
item_refines(Item, Item).

block_refines(block(L, Ph, Is0, J), block(L, Ph, Is, J)) :-
    maplist(inst_refines, Is0, Is).

inst_refines(I, I) :- !.
inst_refines(let(Q, a, check(Lo, Hi, Rs, Al), [P]),
             let(Q, a, check_ahead(Lo, Hi1, Rs, Al, Hi), [P])) :- !,
    Hi1 > Hi.
inst_refines(let(Q, a, check(Lo, Hi, Rs, Al), [P]),
             let(Q, a, renew(Lo, Hi1, Rs, Al), [tmp(_), P1])) :-
    P1 == P, Hi1 >= Hi.
inst_refines(let(Q, a, renew(Lo, Hi, Rs, Al), [tmp(_), P]),
             let(Q, a, renew(Lo, Hi, Rs, Al), [tmp(_), P1])) :-
    P1 == P.
