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
    | `scalar` | `w`, `l`, `s` and `d` temporaries; they never use the pointer pool |
    | `wide` | `x` temporaries: 16-byte slots for the 10 bytes of a long double |

    A variadic function's hidden `va_snapshot` parameter is kept live for
    the whole invocation. Functions that call setjmp must not use this
    allocator (docs/setjmp.md).
*/
:- module(frame_slots, [temp_slots/7]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(cfg).

% temp_slots(+Params, +Blocks, +Temps, -Aliases, -ScalarCount, -PtrCount,
% -WideCount). Aliases maps each temp name to physical storage(Pool, Index).
temp_slots(Params, Blocks, Temps, Aliases, NS, NP, NW) :-
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
    maplist(temp_interval(Lo, Hi), Temps, Intervals0),
    sort(Intervals0, Intervals1),
    partition(wide_range, Intervals1, Wides, Intervals),
    % Each temporary has one interval, so the pairs have distinct keys
    % and make the assoc at once, not by an insertion per temporary.
    allocate(Intervals, [], [], 0, NS, 0, NP, Pairs, WidePairs),
    foldl(wide_slot, Wides, []-0-WidePairs, _-NW-[]),
    list_to_assoc(Pairs, Aliases).

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

temp_interval(Lo, Hi, N-K, range(Start, End, Pool, N)) :-
    get_assoc(N, Lo, Start), get_assoc(N, Hi, End),
    class_pool(K, Pool).

class_pool(p, pointer).
class_pool(w, scalar).
class_pool(l, scalar).
class_pool(s, scalar).
class_pool(d, scalar).
class_pool(x, wide).

allocate([], _, _, NS, NS, NP, NP, Ps, Ps).
allocate([range(Start, End, Pool, N)|Rs], SS0, PS0, NS0, NS, NP0, NP,
         [N-storage(Pool, I)|Ps0], Ps) :-
    pool_slot(Pool, Start, End, SS0, SS, PS0, PS, NS0, NS1, NP0, NP1, I),
    allocate(Rs, SS, PS, NS1, NS, NP1, NP, Ps0, Ps).

pool_slot(scalar, S, E, SS0, SS, PS, PS, NS0, NS, NP, NP, I) :-
    reuse_slot(SS0, S, E, NS0, NS, SS, I).
pool_slot(pointer, S, E, SS, SS, PS0, PS, NS, NS, NP0, NP, I) :-
    reuse_slot(PS0, S, E, NP0, NP, PS, I).

% One end point per physical slot, not an interference graph. Reuse only
% strictly disjoint intervals: results cannot overwrite their operands.
reuse_slot([], _, E, N0, N, [slot(N0, E)], N0) :- N is N0 + 1.
reuse_slot([slot(I0, E0)|Ss0], S, E, N0, N, Ss, I) :-
    (   E0 < S
    ->  Ss = [slot(I0, E)|Ss0], I = I0, N = N0
    ;   Ss = [slot(I0, E0)|Tail],
        reuse_slot(Ss0, S, E, N0, N, Tail, I)
    ).
