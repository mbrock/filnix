/* Conservative stack-slot allocation. Closed intervals include every write
   (even dead results), instruction use and CFG live-in/out boundary. Thus
   one lowered instruction, including all its helper calls, is indivisible.
   Pointer payloads and lowers share one allocation; scalars never use it.
   Setjmp functions must not call this allocator (docs/setjmp.md). */
:- module(frame_slots, [temp_slots/6]).
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(pairs)).
:- use_module(cfg).

% temp_slots(+Params, +Blocks, +Temps, -Aliases, -ScalarCount, -PtrCount).
% Aliases maps each temp name to physical storage(Pool, Index).
temp_slots(Params, Blocks, Temps, Aliases, NS, NP) :-
    temp_liveness(Blocks, In, Out),
    foldl(param_point, Params, [], R1),
    block_ranges(Blocks, In, Out, 1, End, R1, R2),
    % va_args reads this backend-only parameter implicitly. Reserve both
    % its address and lower for the entire invocation.
    (   memberchk(par(p, t(hidden(va_snapshot))), Params)
    ->  touch(hidden(va_snapshot), End, R2, Points)
    ;   Points = R2
    ),
    % Batch the points rather than updating a persistent tree for every
    % use. Trealla otherwise retains gigabytes of intermediate trees on
    % large functions. Grouping computes exactly the same convex hulls.
    keysort(Points, Sorted), group_pairs_by_key(Sorted, Groups),
    maplist(group_range, Groups, Pairs), list_to_assoc(Pairs, Ranges),
    maplist(temp_interval(Ranges), Temps, Intervals0),
    sort(Intervals0, Intervals),
    empty_assoc(A0),
    allocate(Intervals, [], [], 0, NS, 0, NP, A0, Aliases).

param_point(par(_, t(N)), R0, R) :- touch(N, 0, R0, R).

touch(N, P, R, [N-P|R]).

group_range(N-Ps, N-(Lo-Hi)) :- min_list(Ps, Lo), max_list(Ps, Hi).

points([], _, R, R).
points([N|Ns], P, R0, R) :-
    touch(N, P, R0, R1), points(Ns, P, R1, R).

block_ranges([], _, _, P, P, R, R).
block_ranges([blk(L, Phis, Insts, Jump)|Bs], In, Out, P, End, R0, R) :-
    get_assoc(L, In, LiveIn), points(LiveIn, P, R0, R1),
    phi_points(Phis, P, R1, R2),
    P1 is P + 1,
    inst_ranges(Insts, P1, Exit, R2, R3),
    jump_uses(Jump, Uses), points(Uses, Exit, R3, R4),
    get_assoc(L, Out, LiveOut), points(LiveOut, Exit, R4, R5),
    Next is Exit + 1,
    block_ranges(Bs, In, Out, Next, End, R5, R).

phi_points([], _, R, R).
phi_points([phi(t(N), _, _)|Ps], P, R0, R) :-
    touch(N, P, R0, R1), phi_points(Ps, P, R1, R).

inst_ranges([], P, P, R, R).
inst_ranges([I|Is], P, End, R0, R) :-
    inst_uses(I, Uses), points(Uses, P, R0, R1),
    findall(N, inst_def(I, N), Defs), points(Defs, P, R1, R2),
    Next is P + 1,
    inst_ranges(Is, Next, End, R2, R).

temp_interval(Ranges, N-K, range(Start, End, Pool, N)) :-
    get_assoc(N, Ranges, Start-End),
    class_pool(K, Pool).

class_pool(p, pointer).
class_pool(w, scalar).
class_pool(l, scalar).
class_pool(s, scalar).
class_pool(d, scalar).

allocate([], _, _, NS, NS, NP, NP, A, A).
allocate([range(Start, End, Pool, N)|Rs], SS0, PS0, NS0, NS, NP0, NP, A0, A) :-
    pool_slot(Pool, Start, End, SS0, SS, PS0, PS, NS0, NS1, NP0, NP1, I),
    put_assoc(N, A0, storage(Pool, I), A1),
    allocate(Rs, SS, PS, NS1, NS, NP1, NP, A1, A).

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
