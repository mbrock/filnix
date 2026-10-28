/*  Conservative stack-slot allocation for the Fil-C backend:
    temp_slots/6 assigns each temporary a frame slot, and temporaries
    whose live intervals are disjoint may share one.

    A temporary's interval is closed and covers every write (even of a
    dead result), every use by an instruction and every block boundary
    where it is live in or out. One lowered instruction, including all
    its helper calls, is thus indivisible. Two temporaries share a slot
    only when their intervals are strictly disjoint, so a result never
    overwrites its operands.

    | Pool | Holds |
    |---|---|
    | `pointer` | `p` temporaries: each slot is a payload slot and its lower, allocated together |
    | `scalar` | `w` and `l` temporaries, and `s` and `d` ones when the pools are `shared`; they never use the pointer pool. With pools `own`, never reused |
    | `float` | `s` and `d` temporaries when the pools are `own` |
    | `wide` | `x` temporaries: 16-byte slots for the 10 bytes of a long double |

    A variadic function's hidden `va_snapshot` parameter is kept live for
    the whole invocation. Functions that call setjmp must not use this
    allocator (docs/setjmp.md).
*/
:- module(frame_slots, [temp_slots/7, temp_slots/9]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(cfg).

% temp_slots(+Params, +Blocks, +Temps, -Aliases, -ScalarCount, -PtrCount,
% -WideCount). Aliases maps each temp name to physical storage(Pool, Index).
% The pools are shared: s and d temporaries use scalar slots.
temp_slots(Params, Blocks, Temps, Aliases, NS, NP, NW) :-
    temp_slots(shared, Params, Blocks, Temps, Aliases, NS, NP, NW, 0).

% temp_slots(+Pools, +Params, +Blocks, +Temps, -Aliases, -ScalarCount,
% -PtrCount, -WideCount, -FloatCount): as temp_slots/7, with Pools shared,
% own, own(Groups) or own(Groups, Ranges). Own gives s and d
% temporaries a float pool of their own, so no scalar slot holds both an
% integer and a float temporary (register allocation, docs/perf.md item
% 3, takes only w/l homes), and reuses no scalar slot: each w/l
% temporary has its own home, so a home is one live range (docs/perf.md
% 3d). Own(Groups), with Groups a list of Temporary-Key pairs, pools each
% key's w/l temporaries among themselves, as shared pools them; key frame
% first. (A split choice, own's float pool with shared scalar slots, served
% the retired function, operands and cells modes.)
% Own(Groups, Ranges) is own(Groups) that binds Ranges to the live
% ranges, or takes them when Ranges is bound (temp_ranges/6).
temp_slots(Pools, Params, Blocks, Temps, Aliases, NS, NP, NW, NF) :-
    (   Pools = own(_, Ranges), nonvar(Ranges)
    ->  Ranges = ranges(Wides, Intervals)
    ;   temp_ranges(Pools, Params, Blocks, Temps, Wides, Intervals),
        ( Pools = own(_, Ranges) -> Ranges = ranges(Wides, Intervals) ; true )
    ),
    own_groups(Pools, Groups),
    % The frame group takes the first scalar slots, near %rbp, so the
    % homes that stay in the frame sit together; each other group's
    % temporaries share slots among themselves, and ungrouped ones
    % (own) have homes of their own.
    partition(frame_range(Groups), Intervals, Frame, Rest0),
    allocate(Frame, all, st([]-0, []-0, []-0), St1, Pairs, Pairs1),
    group_ranges(Rest0, Groups, Grouped, Owns),
    foldl(group_allocate, Grouped, St1-Pairs1, St2-Pairs2),
    allocate(Owns, own, St2, st(_-NS, _-NP, _-NF), Pairs2, WidePairs),
    foldl(wide_slot, Wides, []-0-WidePairs, _-NW-[]),
    % Each temporary has one interval, so the pairs have distinct keys
    % and make the assoc at once, not by an insertion per temporary.
    list_to_assoc(Pairs, Aliases).

% temp_ranges(+Pools, +Params, +Blocks, +Temps, -Wides, -Intervals): each
% temporary's live range, wide ones apart. They do not depend on the
% scalar groups, so own(Groups, Ranges) lowers again with the ranges of
% an earlier lowering (temps mode, docs/perf.md 3d).
temp_ranges(Pools, Params, Blocks, Temps, Wides, Intervals) :-
    temp_liveness(Blocks, In, Out),
    findall(N, member(param(_, tmp(N)), Params), ParamNs),
    block_ranges(Blocks, In, Out, [], 1, End, Touches1, Touches2),
    % va_args reads this backend-only parameter implicitly. Reserve both
    % its address and lower for the entire invocation.
    (   memberchk(param(p, tmp(hidden(va_snapshot))), Params)
    ->  Touches2 = [[hidden(va_snapshot)]-End]
    ;   Touches2 = []
    ),
    Touches = [ParamNs-0|Touches1],
    % Touches are groups Ns-P in increasing P, sharing the liveness sets
    % rather than copying a point per temporary and block (1.7 million
    % in SQLite's sqlite3VdbeExec). A temporary's convex hull runs from
    % its first touch to its last, so each bound is one insertion per
    % temporary, not a tree update per use, which Trealla would retain.
    % Liveness gives In = Gen ∪ (Out − Kill) for every block, so a
    % live-out temporary is live in or written in the block, at a point
    % before its exit, and a live-in one is read or live out at or after
    % its entry: live-out sets never move a first touch, nor live-in
    % sets a last one, and each pass skips them. Nor does a live-in
    % temporary that was live out of the block before, or a live-out
    % one live into the block after: block_ranges/8 leaves them out.
    first_touches(out, Touches, Lo),
    reverse(Touches, Backwards), first_touches(in, Backwards, Hi),
    maplist(temp_interval(Pools, Lo, Hi), Temps, Intervals0),
    sort(Intervals0, Intervals1),
    partition(wide_range, Intervals1, Wides, Intervals).

% own_groups(+Pools, -Groups): all when every scalar temporary is
% pooled (shared), else an assoc from temporary to its group
% (own(Pairs); own has no groups, so every scalar home is its own).
own_groups(own, G) :- !, empty_assoc(G).
own_groups(own(Ps), G) :- !, list_to_assoc(Ps, G).
own_groups(own(Ps, _), G) :- !, list_to_assoc(Ps, G).
own_groups(_, all).

% Everything but grouped or own scalar temporaries is in the frame group.
frame_range(all, _) :- !.
frame_range(_, range(_, _, Pool, _)) :- Pool \== scalar, !.
frame_range(G, range(_, _, scalar, N)) :- get_assoc(N, G, frame).

% group_ranges(+Ranges, +Groups, -Grouped, -Owns): Grouped lists
% Key-Ranges for each group but frame, in key order; Owns are the
% scalar ranges of temporaries in no group.
group_ranges(Rs, all, [], []) :- !, Rs = [].
group_ranges(Rs, G, Grouped, Owns) :-
    findall(K-R, ( member(R, Rs), R = range(_,_,scalar,N), get_assoc(N, G, K) ), KRs),
    findall(R, ( member(R, Rs), R = range(_,_,scalar,N), \+ get_assoc(N, G, _) ), Owns),
    keysort(KRs, Sorted), group_pairs_by_key(Sorted, Grouped).

% A group's temporaries reuse each other's slots, not other groups'.
group_allocate(_-Rs, st(_-N0, P, F)-Ps0, St-Ps) :-
    allocate(Rs, all, st([]-N0, P, F), St, Ps0, Ps).

wide_range(range(_, _, wide, _)).

% Wide slots are a pool of their own, reused as scalar slots are.
wide_slot(range(S, E, wide, N), Ss0-N0-[N-storage(wide, I)|Ps], Ss-N1-Ps) :-
    reuse_slot(Ss0, S, E, N0, N1, Ss, I).

% first_touches(+Skip, +Touches, -First): First maps each temporary to
% the point of its first touch in Touches, leaving out the live sets
% tagged Skip (in or out).
first_touches(Skip, Touches, First) :-
    empty_assoc(A0), foldl(first_touch_group(Skip), Touches, A0, First).

first_touch_group(Skip, Group-P, A0, A) :-
    (   Group = live(Skip, _) -> A = A0
    ;   Group = live(_, Ns) -> foldl(first_touch(P), Ns, A0, A)
    ;   foldl(first_touch(P), Group, A0, A)
    ).

first_touch(P, N, A0, A) :-
    (   get_assoc(N, A0, _) -> A = A0 ; put_assoc(N, A0, P, A) ).

% block_ranges(+Blocks, +In, +Out, +PrevOut, +P0, -End, -Touches,
% ?Tail): the touch groups of Blocks from point P0: live-in and phis at
% the block's point, each instruction's uses and definitions at its own,
% and the jump's uses and live-out at the exit. PrevOut is the live-out
% set of the block before; the live sets keep only what can move a
% bound (above): the live-in set less PrevOut, the live-out set less
% the next block's live-in set.
block_ranges([], _, _, _, P, P, T, T).
block_ranges([block(L, Phis, Insts, Jump)|Bs], In, Out, PrevOut, P,
             End, [live(in, NewIn)-P, PhiNs-P|T0], T) :-
    get_assoc(L, In, LiveIn),
    ord_subtract(LiveIn, PrevOut, NewIn),
    findall(N, member(phi(tmp(N), _, _), Phis), PhiNs),
    P1 is P + 1,
    inst_ranges(Insts, P1, Exit, T0, [Uses-Exit, live(out, LastOut)-Exit|T1]),
    jump_uses(Jump, Uses),
    get_assoc(L, Out, LiveOut),
    (   Bs = [block(Next, _, _, _)|_] -> get_assoc(Next, In, NextIn) ; NextIn = [] ),
    ord_subtract(LiveOut, NextIn, LastOut),
    Next1 is Exit + 1,
    block_ranges(Bs, In, Out, LiveOut, Next1, End, T1, T).

inst_ranges([], P, P, T, T).
inst_ranges([I|Is], P, End, [Uses-P, Defs-P|T0], T) :-
    inst_uses(I, Uses),
    findall(N, inst_def(I, N), Defs),
    Next is P + 1,
    inst_ranges(Is, Next, End, T0, T).

temp_interval(Pools, Lo, Hi, N-K, range(Start, End, Pool, N)) :-
    get_assoc(N, Lo, Start), get_assoc(N, Hi, End),
    class_pool(K, Pools, Pool).

class_pool(p, _, pointer).
class_pool(w, _, scalar).
class_pool(l, _, scalar).
class_pool(s, shared, scalar).
class_pool(d, shared, scalar).
class_pool(s, own, float).
class_pool(d, own, float).
class_pool(s, own(_), float).
class_pool(d, own(_), float).
class_pool(s, own(_,_), float).
class_pool(d, own(_,_), float).
class_pool(x, _, wide).

% The pools' states st(Scalar, Pointer, Float), each Slots-Count.
allocate([], _, St, St, Ps, Ps).
allocate([range(Start, End, Pool, N)|Rs], Pooled, St0, St,
         [N-storage(Pool, I)|Ps0], Ps) :-
    pool_slot(Pool, Pooled, Start, End, St0, St1, I),
    allocate(Rs, Pooled, St1, St, Ps0, Ps).

% An own scalar temporary gets a new slot that nothing reuses: only
% pooled temporaries are entered in the reuse list.
pool_slot(scalar, own, _, _, st(SS-N0, P, F), st(SS-N, P, F), N0) :- !,
    N is N0 + 1.
pool_slot(scalar, all, S, E, st(SS0-N0, P, F), st(SS-N, P, F), I) :-
    reuse_slot(SS0, S, E, N0, N, SS, I).
pool_slot(pointer, _, S, E, st(C, PS0-N0, F), st(C, PS-N, F), I) :-
    reuse_slot(PS0, S, E, N0, N, PS, I).
pool_slot(float, _, S, E, st(C, P, FS0-N0), st(C, P, FS-N), I) :-
    reuse_slot(FS0, S, E, N0, N, FS, I).

% One end point per physical slot, not an interference graph. Reuse only
% strictly disjoint intervals: results cannot overwrite their operands.
reuse_slot([], _, E, N0, N, [slot(N0, E)], N0) :- N is N0 + 1.
reuse_slot([slot(I0, E0)|Ss0], S, E, N0, N, Ss, I) :-
    (   E0 < S
    ->  Ss = [slot(I0, E)|Ss0], I = I0, N = N0
    ;   Ss = [slot(I0, E0)|Tail],
        reuse_slot(Ss0, S, E, N0, N, Tail, I)
    ).
