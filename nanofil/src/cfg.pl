/*  Control-flow analyses over one function's blocks, as pure functions
    from IR terms to assocs keyed by block label.

    func_cfg/2 builds cfg(Entry, Rpo, Succs, Preds), which the other
    analyses take: dominators (cfg_idoms/2, dom_children/3,
    cfg_frontiers/3, dominates/3, dom_intervals/3, dominates_by_interval/3),
    natural loops (natural_loops/3), and backward liveness (liveness/5,
    and temp_liveness/3 over temps). Each export documents its relation
    below.

    The PLAN asks for these as tabled relations. cfg_tabled.pl has that
    version; docs/m5.md has the measurement that made this one the one
    passes use.

    Variable conventions: L, B, S and P are labels (a block, a successor,
    a predecessor), Ls, Ss and Ps lists of them; T and D are temp names.
*/
:- module(cfg, [func_cfg/2, cfg_idoms/2, dom_children/3, cfg_frontiers/3,
                dominates/3, dom_intervals/3, dominates_by_interval/3,
                natural_loops/3,
                liveness/5, temp_liveness/3, blocks_gen_kill/2,
                phi_edge_uses/2, inst_uses/2, inst_def/2, jump_uses/2,
                jump_succs/2, edge_label/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).

%% CFG

%! jump_succs(+Jump, -Succs) is det.
%
%  Succs is the ordset of labels Jump can branch to.

jump_succs(jmp(T), [L]) :-
    edge_label(T, L).
jump_succs(jnz(_, T1, T2), Ls) :-
    edge_label(T1, L1),
    edge_label(T2, L2),
    sort([L1, L2], Ls).
jump_succs(ret(_), []).
jump_succs(ret, []).
jump_succs(rets(_), []).
jump_succs(hlt, []).

%! edge_label(+Target, -L) is det.
%
%  A jump's Target is the label L, or poll(L): a pollcheck on the edge,
%  then L (ir.pl). A label is any other term, so the cut commits to
%  poll/1.

edge_label(poll(L), L) :- !.
edge_label(L, L).

%! func_cfg(+Blocks, -Cfg) is det.
%
%  Cfg = cfg(Entry, Rpo, Succs, Preds) is the control-flow graph of
%  Blocks, whose first block is the entry:
%
%    - Rpo: the reachable labels in reverse postorder, Entry first;
%    - Succs: assoc Label -> ordset of successor labels (every block);
%    - Preds: assoc Label -> ordset of predecessor labels (every block,
%      including unreachable predecessors, as phis must list them).

func_cfg(Blocks, cfg(Entry, Rpo, Succs, Preds)) :-
    Blocks = [blk(Entry, _, _, _)|_],
    findall(Label-Ss,
            ( member(blk(Label, _, _, Jump), Blocks),
              jump_succs(Jump, Ss)
            ),
            SuccPairs),
    list_to_assoc(SuccPairs, Succs),
    findall(Label-[], member(Label-_, SuccPairs), NoPreds),
    list_to_assoc(NoPreds, Preds0),
    foldl(succ_pair_preds, SuccPairs, Preds0, Preds1),
    assoc_to_list(Preds1, PredPairs0),
    findall(Label-Ps,
            ( member(Label-Ps0, PredPairs0),
              sort(Ps0, Ps)
            ),
            PredPairs),
    list_to_assoc(PredPairs, Preds),
    empty_assoc(Seen0),
    reverse_postorder([Entry], Succs, Seen0, _, [], Rpo).

% succ_pair_preds(+Pred-Ss, +Preds0, -Preds): Preds is Preds0
% with Pred in the (unsorted) predecessor list of each label in Ss.
succ_pair_preds(Pred-Ss, Preds0, Preds) :-
    foldl(pred_succ_preds(Pred), Ss, Preds0, Preds).

pred_succ_preds(Pred, Succ, Preds0, Preds) :-
    get_assoc(Succ, Preds0, Ps),
    put_assoc(Succ, Preds0, [Pred|Ps], Preds).

% reverse_postorder(+Ls, +Succs, +Seen0, -Seen, +Post0, -Post): Post
% is a reverse postorder, in front of Post0, of the labels reachable
% from Ls (depth first, each of Ls in turn) without passing through
% Seen0; Seen is Seen0 with those labels.
reverse_postorder([], _, Seen, Seen, Post, Post).
reverse_postorder([L|Ls], Succs, Seen0, Seen, Post0, Post) :-
    (   get_assoc(L, Seen0, _)
    ->  reverse_postorder(Ls, Succs, Seen0, Seen, Post0, Post)
    ;   put_assoc(L, Seen0, t, Seen1),
        get_assoc(L, Succs, Ss),
        reverse_postorder(Ss, Succs, Seen1, Seen2, Post0, Post1),
        reverse_postorder(Ls, Succs, Seen2, Seen, [L|Post1], Post)
    ).

%% Dominators

%! cfg_idoms(+Cfg, -Idom) is det.
%
%  Idom is the assoc Label -> immediate dominator, for the reachable
%  labels other than the entry (Cooper, Harvey and Kennedy, "A Simple,
%  Fast Dominance Algorithm").

cfg_idoms(cfg(Entry, Rpo, _, Preds), Idom) :-
    labels_numbered(Rpo, 0, Numbered),
    list_to_assoc(Numbered, Num),
    empty_assoc(Idom0),
    put_assoc(Entry, Idom0, Entry, Idom1),
    Rpo = [_|Rest],
    idom_fixpoint(Rest, Preds, Num, Idom1, Idom2),
    del_assoc(Entry, Idom2, _, Idom).

% labels_numbered(+Labels, +N0, -Pairs): Pairs is Label-N for each of
% Labels, counting from N0.
labels_numbered([], _, []).
labels_numbered([L|Ls], N, [L-N|Ps]) :-
    N1 is N + 1,
    labels_numbered(Ls, N1, Ps).

% idom_fixpoint(+Labels, +Preds, +Num, +Idom0, -Idom): Idom is the
% fixed point, from Idom0, of sweeps over Labels in reverse postorder.
idom_fixpoint(Labels, Preds, Num, Idom0, Idom) :-
    foldl(label_idoms(Preds, Num), Labels, Idom0-false,
          Idom1-Changed),
    changed_idom_fixpoint(Changed, Labels, Preds, Num, Idom1, Idom).

% changed_idom_fixpoint(+Changed, +Labels, +Preds, +Num, +Idom0, -Idom):
% as idom_fixpoint/5, after a sweep that changed an idom (Changed is
% true) or none (false).
changed_idom_fixpoint(true, Labels, Preds, Num, Idom0, Idom) :-
    idom_fixpoint(Labels, Preds, Num, Idom0, Idom).
changed_idom_fixpoint(false, _, _, _, Idom, Idom).

% label_idoms(+Preds, +Num, +B, +Idom0-Changed0, -Idom-Changed):
% in Idom, the idom of B is the nearest common dominator of those of its
% predecessors that have an idom in Idom0. Changed is true if that
% differs from B's idom in Idom0, and Changed0 if not.
label_idoms(Preds, Num, B, Idom0-Changed0, Idom-Changed) :-
    get_assoc(B, Preds, Ps),
    include(has_idom(Idom0), Ps, Processed),
    Processed = [First|Others],
    foldl(common_dominator(Num, Idom0), Others, First, New),
    (   get_assoc(B, Idom0, Old),
        Old == New
    ->  Idom = Idom0,
        Changed = Changed0
    ;   put_assoc(B, Idom0, New, Idom),
        Changed = true
    ).

has_idom(Idom, L) :-
    get_assoc(L, Idom, _).

% common_dominator(+Num, +Idom, +A, +B, -Common): Common is the nearest
% common dominator of A and B: A if they are equal, and otherwise the
% nearest common dominator of the earlier one in reverse postorder and
% the idom of the later one.
common_dominator(Num, Idom, A, B, Common) :-
    (   A == B
    ->  Common = A
    ;   get_assoc(A, Num, NA),
        get_assoc(B, Num, NB),
        (   NA > NB
        ->  get_assoc(A, Idom, A1),
            common_dominator(Num, Idom, A1, B, Common)
        ;   get_assoc(B, Idom, B1),
            common_dominator(Num, Idom, A, B1, Common)
        )
    ).

%! dom_children(+Cfg, +Idom, -Kids) is det.
%
%  Kids is the assoc Label -> the children of Label in the dominator
%  tree, in reverse postorder, for every reachable label.

dom_children(cfg(_, Rpo, _, _), Idom, Kids) :-
    findall(L-[], member(L, Rpo), NoKids),
    list_to_assoc(NoKids, Kids0),
    reverse(Rpo, Reversed),
    foldl(label_kids(Idom), Reversed, Kids0, Kids).

% label_kids(+Idom, +L, +Kids0, -Kids): Kids is Kids0 with L in
% front of the children of its idom, if it has one.
label_kids(Idom, L, Kids0, Kids) :-
    (   get_assoc(L, Idom, Parent)
    ->  get_assoc(Parent, Kids0, Cs),
        put_assoc(Parent, Kids0, [L|Cs], Kids)
    ;   Kids = Kids0
    ).

%! dominates(+Idom, +A, +B) is semidet.
%
%  A dominates B (both reachable): A is B, or A dominates the idom of B.

dominates(Idom, A, B) :-
    (   A == B
    ->  true
    ;   get_assoc(B, Idom, D),
        dominates(Idom, A, D)
    ).

%! dom_intervals(+Cfg, +Idom, -Intervals) is det.
%
%  Intervals is the assoc Label -> Pre-Last for every reachable label:
%  Pre is the preorder number of Label in the dominator tree, and Last
%  the last one in its subtree.

dom_intervals(Cfg, Idom, Intervals) :-
    Cfg = cfg(Entry, _, _, _),
    dom_children(Cfg, Idom, Kids),
    empty_assoc(Intervals0),
    subtree_intervals(Entry, Kids, 0, _, Intervals0, Intervals).

% subtree_intervals(+L, +Kids, +N0, -N, +Intervals0, -Intervals):
% Intervals is Intervals0 with the intervals of the dominator subtree at
% L, numbered in preorder from N0; N is the next free number.
subtree_intervals(L, Kids, N0, N, Intervals0, Intervals) :-
    get_assoc(L, Kids, Ks),
    N1 is N0 + 1,
    foldl(kid_intervals(Kids), Ks, N1-Intervals0, N-Intervals1),
    Last is N - 1,
    put_assoc(L, Intervals1, N0-Last, Intervals).

kid_intervals(Kids, K, N0-Intervals0, N-Intervals) :-
    subtree_intervals(K, Kids, N0, N, Intervals0, Intervals).

%! dominates_by_interval(+Intervals, +A, +B) is semidet.
%
%  A dominates B, in constant time, given Intervals from
%  dom_intervals/3.

dominates_by_interval(Intervals, A, B) :-
    get_assoc(A, Intervals, PreA-LastA),
    get_assoc(B, Intervals, PreB-_),
    PreA =< PreB,
    PreB =< LastA.

%! cfg_frontiers(+Cfg, +Idom, -DF) is det.
%
%  DF is the assoc Label -> ordset of the labels in its dominance
%  frontier, for every reachable label. As in CHK, a join point is in
%  the frontier of each label on the idom path from each of its
%  predecessors up to (not including) its own idom.

cfg_frontiers(cfg(_, Rpo, _, Preds), Idom, DF) :-
    findall(L-[], member(L, Rpo), Empty),
    list_to_assoc(Empty, DF0),
    foldl(join_frontiers(Preds, Idom), Rpo, DF0, DF1),
    assoc_to_list(DF1, Pairs0),
    findall(L-S,
            ( member(L-Xs, Pairs0),
              sort(Xs, S)
            ),
            Pairs),
    list_to_assoc(Pairs, DF).

% join_frontiers(+Preds, +Idom, +B, +DF0, -DF): DF is DF0 with B in the
% frontiers it joins, if it has two or more reachable predecessors. DF0
% has a key for every reachable label, so it also tells which
% predecessors are reachable.
join_frontiers(Preds, Idom, B, DF0, DF) :-
    get_assoc(B, Preds, Ps0),
    include(has_frontier(DF0), Ps0, Ps),
    (   Ps = [_, _|_],
        get_assoc(B, Idom, IdomB)
    ->  foldl(runner_frontiers(Idom, IdomB, B), Ps, DF0, DF)
    ;   DF = DF0
    ).

has_frontier(DF, L) :-
    get_assoc(L, DF, _).

% runner_frontiers(+Idom, +Stop, +B, +Runner, +DF0, -DF): DF is DF0 with
% B in the frontier of every label on the idom path from Runner up to
% (not including) Stop.
runner_frontiers(Idom, Stop, B, Runner, DF0, DF) :-
    (   Runner == Stop
    ->  DF = DF0
    ;   get_assoc(Runner, DF0, Xs),
        put_assoc(Runner, DF0, [B|Xs], DF1),
        get_assoc(Runner, Idom, Up),
        runner_frontiers(Idom, Stop, B, Up, DF1, DF)
    ).

%% Natural loops

%! natural_loops(+Cfg, +Idom, -Loops) is det.
%
%  Loops is the assoc Header -> loop(Latches, Body), both ordsets of
%  labels. A latch has an edge to a header that dominates it. Body is
%  the union of their natural loops. Only reachable blocks participate.
%  Nested loops have separate entries; an irreducible cycle without a
%  dominating header is NOT a natural loop. Empty does not mean
%  acyclic, and this analysis alone cannot justify removing polls.

natural_loops(Cfg, Idom, Loops) :-
    Cfg = cfg(_, Rpo, Succs, Preds),
    dom_intervals(Cfg, Idom, Intervals),
    findall(Header-Latch,
            ( member(Latch, Rpo),
              get_assoc(Latch, Succs, Ss),
              member(Header, Ss),
              dominates_by_interval(Intervals, Header, Latch)
            ),
            Edges0),
    sort(Edges0, Edges),
    group_pairs_by_key(Edges, Headers),
    maplist(natural_loop(Preds, Intervals), Headers, Pairs),
    list_to_assoc(Pairs, Loops).

natural_loop(Preds, Intervals, H-Latches, H-loop(Latches, Body)) :-
    empty_assoc(Empty),
    % Mark the header before walking: its predecessors are outside the
    % natural loop (also essential for a one-block self loop).
    put_assoc(H, Empty, true, Seen0),
    loop_body(Latches, Preds, Intervals, Seen0, Seen),
    assoc_to_keys(Seen, Body).

% loop_body(+Pending, +Preds, +Intervals, +Seen0, -Seen): Seen is Seen0
% with the reachable labels from which a label in Pending is reached
% without passing through Seen0; a label without an interval is
% unreachable. Invariant: Seen0 holds the header and the body blocks
% found so far, and every reachable predecessor of a body block in Seen0
% is in Seen0 or Pending.
loop_body([], _, _, Seen, Seen).
loop_body([B|Pending], Preds, Intervals, Seen0, Seen) :-
    (   get_assoc(B, Seen0, _)
    ->  loop_body(Pending, Preds, Intervals, Seen0, Seen)
    ;   \+ get_assoc(B, Intervals, _)
    ->  loop_body(Pending, Preds, Intervals, Seen0, Seen)
    ;   put_assoc(B, Seen0, true, Seen1),
        get_assoc(B, Preds, Ps),
        append(Ps, Pending, More),
        loop_body(More, Preds, Intervals, Seen1, Seen)
    ).

%% Liveness

%! liveness(+Cfg, +GenKill, +EdgeUses, -LiveIn, -LiveOut) is det.
%
%  LiveIn and LiveOut are the assocs Label -> ordset of the names live
%  on entry to and exit from each block (every block, reachable or not),
%  the least solution of the backward dataflow equations
%
%    LiveOut(B) = union over successors S of LiveIn(S) and EdgeUses(B-S)
%    LiveIn(B)  = Gen(B) ∪ (LiveOut(B) \ Kill(B))
%
%  GenKill is the assoc Label -> Gen-Kill (ordsets: the names read
%  before any write in the block, and the names written). EdgeUses is the
%  assoc (Pred-Succ) -> ordset of the names read on that edge only (phi
%  arguments). Names are anything ordsets can hold, so the same relation
%  serves temps (temp_liveness/3) and promote's memory slots.

liveness(cfg(_, Rpo, Succs, Preds), GenKill, EdgeUses, LiveIn, LiveOut) :-
    assoc_to_keys(Succs, All),
    subtract(All, Rpo, Unreached),
    reverse(Rpo, Post),
    append(Post, Unreached, Order),
    labels_numbered(Order, 0, Numbered),
    list_to_assoc(Numbered, Num),
    findall(N-L, member(L-N, Numbered), Pending),
    findall(L-[], member(L, All), Empty),
    list_to_assoc(Empty, LiveIn0),
    liveness_worklist(Pending, Num, Succs, Preds, GenKill, EdgeUses,
                      LiveIn0, LiveIn),
    findall(L-Out,
            ( member(L, All),
              live_out(L, Succs, EdgeUses, LiveIn, Out)
            ),
            OutPairs),
    list_to_assoc(OutPairs, LiveOut).

% liveness_worklist(+Pending, +Num, +Succs, +Preds, +GenKill, +EdgeUses,
% +LiveIn0, -LiveIn): LiveIn is the least solution above LiveIn0, given
% that only the blocks in Pending may violate the equations. Pending is
% an ordset of N-L, N the position of L in postorder, so the pending
% block first in postorder is next; when a block's live-in set grows,
% its predecessors are pending again.
liveness_worklist([], _, _, _, _, _, LiveIn, LiveIn).
liveness_worklist([_-L|Pending0], Num, Succs, Preds, GenKill, EdgeUses,
                  LiveIn0, LiveIn) :-
    live_out(L, Succs, EdgeUses, LiveIn0, Out),
    get_assoc(L, GenKill, Gen-Kill),
    ord_subtract(Out, Kill, Through),
    ord_union(Gen, Through, New),
    (   get_assoc(L, LiveIn0, Old),
        Old == New
    ->  liveness_worklist(Pending0, Num, Succs, Preds, GenKill, EdgeUses,
                          LiveIn0, LiveIn)
    ;   put_assoc(L, LiveIn0, New, LiveIn1),
        get_assoc(L, Preds, PredLabels),
        findall(N-P,
                ( member(P, PredLabels),
                  get_assoc(P, Num, N)
                ),
                Requeued0),
        sort(Requeued0, Requeued),
        ord_union(Pending0, Requeued, Pending),
        liveness_worklist(Pending, Num, Succs, Preds, GenKill, EdgeUses,
                          LiveIn1, LiveIn)
    ).

% live_out(+L, +Succs, +EdgeUses, +LiveIn, -Out): Out is the live-out
% set of L, given the live-in sets LiveIn.
live_out(L, Succs, EdgeUses, LiveIn, Out) :-
    get_assoc(L, Succs, Ss),
    foldl(succ_live(L, EdgeUses, LiveIn), Ss, [], Out).

succ_live(L, EdgeUses, LiveIn, S, Out0, Out) :-
    get_assoc(S, LiveIn, SuccIn),
    ord_union(Out0, SuccIn, Out1),
    (   get_assoc(L-S, EdgeUses, Us)
    ->  ord_union(Out1, Us, Out)
    ;   Out = Out1
    ).

%% Temps

%! temp_liveness(+Blocks, -LiveIn, -LiveOut) is det.
%
%  LiveIn and LiveOut are liveness/5 of Blocks over temp names. A phi
%  defines its temp at block entry (in Kill, never in LiveIn) and reads
%  its argument on the edge.

temp_liveness(Blocks, LiveIn, LiveOut) :-
    func_cfg(Blocks, Cfg),
    blocks_gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    liveness(Cfg, GenKill, EdgeUses, LiveIn, LiveOut).

%! blocks_gen_kill(+Blocks, -GenKill) is det.
%
%  GenKill is the assoc Label -> Gen-Kill for each block: Gen is the
%  ordset of temps read before they are written in it, and Kill the
%  ordset of temps written (phi destinations included).

blocks_gen_kill(Blocks, GenKill) :-
    findall(L-(Gen-Kill),
            ( member(B, Blocks),
              B = blk(L, _, _, _),
              block_gen_kill(B, Gen, Kill)
            ),
            Pairs),
    list_to_assoc(Pairs, GenKill).

block_gen_kill(blk(_, Phis, Insts, Jump), Gen, Kill) :-
    findall(D, member(phi(t(D), _, _), Phis), PhiDefs),
    sort(PhiDefs, Kill0),
    foldl(inst_gen_kill, Insts, []-Kill0, Gen1-Kill),
    jump_uses(Jump, JumpUses),
    ord_subtract(JumpUses, Kill, JumpGen),
    ord_union(Gen1, JumpGen, Gen).

inst_gen_kill(I, Gen0-Kill0, Gen-Kill) :-
    inst_uses(I, Us),
    ord_subtract(Us, Kill0, New),
    ord_union(Gen0, New, Gen),
    findall(D, inst_def(I, D), Ds0),
    sort(Ds0, Ds),
    ord_union(Kill0, Ds, Kill).

%! phi_edge_uses(+Blocks, -EdgeUses) is det.
%
%  EdgeUses is the assoc (Pred-Succ) -> ordset of the temps that the
%  phis of Succ read on the edge from Pred, for the edges that have any.

phi_edge_uses(Blocks, EdgeUses) :-
    findall((P-S)-T,
            ( member(blk(S, Phis, _, _), Blocks),
              member(phi(_, _, Args), Phis),
              member(P-t(T), Args)
            ),
            Pairs0),
    keysort(Pairs0, Pairs1),
    group_pairs_by_key(Pairs1, Groups),
    findall(Edge-S,
            ( member(Edge-Ts, Groups),
              sort(Ts, S)
            ),
            Pairs),
    list_to_assoc(Pairs, EdgeUses).

%! inst_uses(+Inst, -Uses) is det.
%
%  Uses is the ordset of temps that the instruction Inst reads.

inst_uses(ins(_, _, _, Args), Us) :-
    temps(Args, Us).
inst_uses(store(_, V, A), Us) :-
    temps([V, A], Us).
inst_uses(st(_, _, V, A), Us) :-
    temps([V, A], Us).
inst_uses(call(_, F, Args), Us) :-
    findall(V, member(arg(_, V), Args), Vs),
    temps([F|Vs], Us).
inst_uses(loc(_, _), []).

%! inst_def(+Inst, -Temp) is nondet.
%
%  The instruction Inst defines Temp (a call can define several).

inst_def(ins(t(D), _, _, _), D).
inst_def(call(to(t(D), _), _, _), D).
inst_def(call(tuple(Rs), _, _), D) :-
    member(to(t(D), _), Rs).

%! jump_uses(+Jump, -Uses) is det.
%
%  Uses is the ordset of temps that Jump reads.

jump_uses(jmp(_), []).
jump_uses(jnz(V, _, _), Us) :-
    temps([V], Us).
jump_uses(ret(V), Us) :-
    temps([V], Us).
jump_uses(ret, []).
jump_uses(rets(Vs), Us) :-
    temps(Vs, Us).
jump_uses(hlt, []).

% temps(+Values, -Names): Names is the ordset of temp names among
% Values.
temps(Vs, Ts) :-
    findall(T, member(t(T), Vs), Ts0),
    sort(Ts0, Ts).
