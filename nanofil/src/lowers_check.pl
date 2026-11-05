/*  The GC-root contract of a frame, checked: at every point of every
    reachable block, each live pointer temporary's `lowers[]` entry
    holds its current lower (docs/lowers.md). The collector marks the
    object of every lower in the frame record at each safepoint, so a
    live pointer whose entry held anything else could lose its object.

    check_lowers/4 validates the frame filc_abi.pl built, whatever chose
    it: it does not ask which flights lower_roots.pl derived or how
    frame_slots.pl pooled the slots, only what each instruction writes.

    ## Facts

    | Fact | Holds at a point when |
    |---|---|
    | `holds(E, Ns)` | on every path here, entry E was last written with a lower that is the current lower of each name in Ns |

    The state maps each entry to its Ns; an absent entry holds nothing
    known. Every name is only ever added to its own entry's Ns.

    ## Transfer

    | Event | Effect |
    |---|---|
    | entry | each `p` parameter N, in order: `holds(E(N), [N])` |
    | a phi or an instruction defining `p` temporary N | `holds(E(N), [N])` |
    | `flight(tmp(N), _, _, lower(tmp(P)))`, P ≠ N, E(P) = E(N) | emits no store (filc_amd64.pl); requires P in E's Ns, then adds N |
    | on the edge from B, a `p` phi N whose inputs are all temporaries with entry E(N) | copies no lower; requires the input V from B in E's Ns at B's end, then adds N |

    Nothing else writes a temporary's entry: the runtime writes
    `lowers[]` only in zlongjmp, and a function with setjmp must give
    every pointer an entry of its own (today's discipline). Calls,
    polls and helpers only read it. Shadows, stack-aux, snapshot and
    jmpbuf roots are other entries.

    ## Merge and check

    A block's state is the meet of its reachable predecessors': per
    entry, the names in all of them. Then each live pointer (cfg.pl's
    liveness, refined per instruction) must be in its entry's Ns: before
    each instruction, after the last one (live out and the jump's uses,
    where an edge's poll would see them if it polled first) and before
    the first after the phis (where an edge's poll does see them).
    Unreachable blocks are not checked; they never run.
*/
:- module(lowers_check, [check_lowers/4]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir, [temp_defs/3]).
:- use_module(cfg, [func_cfg/2, temp_liveness/3, inst_uses/2, inst_def/2, jump_uses/2]).

%! check_lowers(+Fn, +Params, +LiveBlocks, +Frame) is det.
%
%  Frame = frame(Plain, Roots, Aliases), filc_abi.pl's, satisfies the
%  contract above for function Fn with body parameters Params and the
%  liveness view LiveBlocks. Throws nanofil_error otherwise.
check_lowers(Fn, Params, Blocks, frame(_, Roots, Aliases)) :-
    maplist(bare_block, Blocks, Bare),
    temp_defs(Params, Bare, Defs),
    findall(N, member(N-p, Defs), Ps0), sort(Ps0, Ps),
    list_to_assoc(Aliases, A),
    maplist(entry(A), Ps, EntryPairs),
    list_to_assoc(EntryPairs, E),
    findall(N-x, member(N-_, Defs), Known0), sort(Known0, Known1), list_to_assoc(Known1, Known),
    msort(Roots, R0), sort(Roots, R1),
    (   R0 == R1 -> true ; fail_check(Fn, 'two roots share a lowers[] entry', []) ),
    forall(member(N-K, EntryPairs),
           (   temp_root(N, K), memberchk(K, Roots) -> true
           ;   fail_check(Fn, 'the lower of ~w is not in a temporary''s lowers[] entry', [N])
           )),
    (   member(block(_, _, Is, _), Bare), memberchk(let(_, w, setjmp(_), _), Is)
    ->  pairs_values(EntryPairs, Ks0), msort(Ks0, Ks1), sort(Ks0, Ks2),
        (   Ks1 == Ks2 -> true
        ;   fail_check(Fn, 'a function with setjmp shares a lowers[] entry', [])
        )
    ;   true
    ),
    empty_assoc(S0),
    foldl(param_write(E), Params, S0, Start),
    func_cfg(Bare, cfg(Entry, Rpo, _, Preds)),
    findall(L-B, ( member(B, Bare), B = block(L, _, _, _) ), LBs),
    list_to_assoc(LBs, ByLabel),
    temp_liveness(Blocks, _, Out),
    findall(L-B, ( member(B, Blocks), B = block(L, _, _, _) ), LiveLBs),
    list_to_assoc(LiveLBs, LiveByLabel),
    Ctx = ctx(Fn, E-Known, ByLabel, Preds, Entry-Start),
    empty_assoc(Outs0),
    fixpoint(Rpo, Ctx, Outs0, Outs),
    forall(member(L, Rpo),
           (   block_in(Ctx, Outs, L, In),
               get_assoc(L, ByLabel, Block),
               get_assoc(L, LiveByLabel, LiveBlock),
               get_assoc(L, Out, LiveOut),
               check_block(Ctx, Block, LiveBlock, LiveOut, In)
           )).

fail_check(Fn, Format, Args) :-
    format(atom(Why), Format, Args),
    format(atom(Msg), 'lowers check, in ~w: ~w', [Fn, Why]),
    throw(nanofil_error(Msg)).

% A temporary's entry: the root its lower key names, through Aliases.
entry(A, N, N-K) :-
    (   get_assoc(lower(tmp(N)), A, K0) -> K = K0 ; K = lower(tmp(N)) ).

% A temporary's entry is its own lower key or a pointer-pool entry, never
% a shadow, stack-aux, snapshot or jmpbuf root (lower(tmp(hidden(_)))).
temp_root(N, lower(tmp(M))) :- M == N.
temp_root(_, lower(storage(pointer, _))).

param_write(E, param(p, tmp(N)), S0, S) :- !, write_entry(E, N, S0, S).
param_write(_, _, S, S).

write_entry(E, N, S0, S) :-
    get_assoc(N, E, K), put_assoc(K, S0, [N], S).

holds(E, S, N) :-
    get_assoc(N, E, K), get_assoc(K, S, Ns), ord_memberchk(N, Ns).

% fixpoint(+Rpo, +Ctx, +Outs0, -Outs): Outs maps each reachable block to
% its state after its last instruction, the greatest fixpoint from top
% (an unvisited predecessor is ignored by the meet).
fixpoint(Rpo, Ctx, Outs0, Outs) :-
    foldl(block_pass(Ctx), Rpo, Outs0-false, Outs1-Changed),
    (   Changed == true -> fixpoint(Rpo, Ctx, Outs1, Outs) ; Outs = Outs1 ).

block_pass(Ctx, L, Outs0-C0, Outs-C) :-
    block_in(Ctx, Outs0, L, In),
    Ctx = ctx(_, _, ByLabel, _, _),
    get_assoc(L, ByLabel, block(_, _, Is, _)),
    foldl(inst_transfer(Ctx), Is, In, Out),
    (   get_assoc(L, Outs0, Old), Old == Out
    ->  Outs = Outs0, C = C0
    ;   put_assoc(L, Outs0, Out, Outs), C = true
    ).

% block_in(+Ctx, +Outs, +L, -In): the meet of the states its visited
% predecessors' edges leave, after L's phis, and the parameters' at the
% entry block.
block_in(Ctx, Outs, L, In) :-
    Ctx = ctx(_, _, ByLabel, Preds, Entry-Start),
    get_assoc(L, Preds, Ps),
    get_assoc(L, ByLabel, block(_, Phis, _, _)),
    findall(S, ( member(P, Ps), get_assoc(P, Outs, S0),
                 foldl(phi_transfer(Ctx, P), Phis, S0, S) ), Ss0),
    (   L == Entry -> Ss = [Start|Ss0] ; Ss = Ss0 ),
    (   Ss = [S1|Rest] -> foldl(meet, Rest, S1, In) ; empty_assoc(In) ).

meet(S1, S2, S) :-
    assoc_to_list(S1, L1), assoc_to_list(S2, L2),
    meet_lists(L1, L2, L), list_to_assoc(L, S).

meet_lists([], _, []) :- !.
meet_lists(_, [], []) :- !.
meet_lists([K1-V1|T1], [K2-V2|T2], L) :-
    compare(O, K1, K2),
    meet_step(O, K1-V1, T1, K2-V2, T2, L).

meet_step(<, _, T1, P2, T2, L) :- meet_lists(T1, [P2|T2], L).
meet_step(>, P1, T1, _, T2, L) :- meet_lists([P1|T1], T2, L).
meet_step(=, K-V1, T1, _-V2, T2, L) :-
    ord_intersection(V1, V2, V),
    (   V == [] -> L = L1 ; L = [K-V|L1] ),
    meet_lists(T1, T2, L1).

% phi_transfer(+Ctx, +From, +Phi, +S0, -S): Phi's write on the edge from
% From. A phi whose inputs all have its entry copies no lower
% (filc_amd64.pl), so its input from From must hold there.
phi_transfer(ctx(Fn, E-_, _, _, _), From, phi(tmp(N), p, Pairs), S0, S) :- !,
    (   shared_phi(E, N, Pairs)
    ->  (   memberchk(From-tmp(V), Pairs) -> true
        ;   fail_check(Fn, 'the phi ~w has no input from ~w', [N, From])
        ),
        (   holds(E, S0, V)
        ->  get_assoc(N, E, K), get_assoc(K, S0, Ns0),
            ord_add_element(Ns0, N, Ns), put_assoc(K, S0, Ns, S)
        ;   fail_check(Fn, 'the phi ~w shares the entry of ~w, which does not hold its lower at the end of ~w', [N, V, From])
        )
    ;   write_entry(E, N, S0, S)
    ).
phi_transfer(_, _, _, S, S).

shared_phi(E, N, Pairs) :-
    get_assoc(N, E, K),
    forall(member(_-V, Pairs), ( V = tmp(M), get_assoc(M, E, K) )).

% inst_transfer(+Ctx, +Inst, +S0, -S): Inst's writes of entries. Only a
% flight whose donor has its entry is no write (filc_amd64.pl emits
% none), and only when the donor's lower is there.
inst_transfer(ctx(Fn, E-_, _, _, _), I, S0, S) :-
    (   shared_flight(E, I, N, P)
    ->  (   holds(E, S0, P)
        ->  get_assoc(N, E, K), get_assoc(K, S0, Ns0),
            ord_add_element(Ns0, N, Ns), put_assoc(K, S0, Ns, S)
        ;   fail_check(Fn, 'the flight ~w shares the entry of ~w, which does not hold its lower', [N, P])
        )
    ;   findall(N, ( inst_def(I, N), get_assoc(N, E, _) ), Ns),
        foldl(write_entry(E), Ns, S0, S)
    ).

shared_flight(E, flight(tmp(N), _, _, lower(tmp(P))), N, P) :-
    P \== N, get_assoc(N, E, K), get_assoc(P, E, K).

% check_block(+Ctx, +Block, +LiveBlock, +LiveOut, +In): every live
% pointer holds at every point of Block.
check_block(Ctx, block(L, _, Is, J), block(_, _, LiveIs, _), LiveOut, In) :-
    Ctx = ctx(Fn, EK, _, _, _),
    jump_uses(J, JUs), ord_union(LiveOut, JUs, Last),
    reverse(LiveIs, Rev), live_befores(Rev, Last, [], Befores),
    foldl(check_inst(Ctx, L), Is, Befores, In, S2),
    check_live(Fn, EK, L, end, S2, Last).

% live_befores(+RevInsts, +After, +Acc, -Befores): the live set before
% each instruction, walking them backwards from the set After the last.
live_befores([], _, Bs, Bs).
live_befores([I|Is], After, Acc, Bs) :-
    findall(N, inst_def(I, N), Ds0), sort(Ds0, Ds),
    inst_uses(I, Us),
    ord_subtract(After, Ds, Through), ord_union(Through, Us, Before),
    live_befores(Is, Before, [Before|Acc], Bs).

check_inst(Ctx, L, I, Before, S0, S) :-
    Ctx = ctx(Fn, EK, _, _, _),
    check_live(Fn, EK, L, I, S0, Before),
    inst_transfer(Ctx, I, S0, S).

% Every live name is defined somewhere, and a live pointer holds.
check_live(Fn, E-K, L, At, S, Live) :-
    (   member(N, Live), \+ get_assoc(N, K, _)
    ->  fail_check(Fn, '~w is live in block ~w at ~q but never defined', [N, L, At])
    ;   member(N, Live), get_assoc(N, E, _), \+ holds(E, S, N)
    ->  fail_check(Fn, 'pointer ~w is live in block ~w at ~q, but its lowers[] entry does not hold its lower', [N, L, At])
    ;   true
    ).

bare_block(block(L, Phis, Is0, J), block(L, Phis, Is, J)) :- maplist(bare, Is0, Is).

bare(uses(I0, _), I) :- !, bare(I0, I).
bare(I, I).
