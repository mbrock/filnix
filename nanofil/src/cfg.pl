/*  Control-flow analyses over one function's blocks, as pure functions
    from IR terms to assocs keyed by block label.

    fn_cfg(+Blocks, -Cfg)
      Cfg = cfg(Entry, Rpo, Succs, Preds)
      Rpo    reachable labels in reverse postorder, Entry first
      Succs  assoc Label -> ordset of successor labels (every block)
      Preds  assoc Label -> ordset of predecessor labels (every block,
             including unreachable predecessors, as phis must list them)

    dominators(+Cfg, -Idom)
      assoc Label -> immediate dominator, for reachable labels other than
      Entry (Cooper, Harvey and Kennedy, "A Simple, Fast Dominance
      Algorithm").

    dom_children(+Cfg, +Idom, -Kids)   assoc Label -> children, Rpo order
    frontiers(+Cfg, +Idom, -DF)        assoc Label -> ordset, reachable labels
    dominates(+Idom, +A, +B)           A dominates B (both reachable)
    dom_intervals(+Cfg, +Idom, -Iv)    assoc Label -> Pre-Last, the preorder
                                       number of Label in the dominator tree
                                       and the last one in its subtree
    dominates_iv(+Iv, +A, +B)          A dominates B, in constant time

    natural_loops(+Cfg, +Idom, -Loops)
      Assoc Header -> loop(Latches, Body), both ordsets of labels.
      A latch has an edge to a header that dominates it. Body is the
      union of their natural loops. Only reachable blocks participate.
      Nested loops have separate entries; an irreducible cycle without
      a dominating header is NOT a natural loop. Empty does not mean
      acyclic, and this analysis alone cannot justify removing polls.

    liveness(+Cfg, +GenKill, +EdgeUses, -LiveIn, -LiveOut)
      Backward dataflow over every block. GenKill: assoc Label -> Gen-Kill
      (ordsets: names read before any write in the block, and names
      written). EdgeUses: assoc (Pred-Succ) -> ordset read on that edge
      only (phi arguments). LiveOut(B) is the union over successors S of
      LiveIn(S) and EdgeUses(B-S); LiveIn(B) = Gen ∪ (LiveOut \ Kill).
      Names are anything ordsets can hold, so the same relation serves
      temps (temp_liveness/3) and promote's memory slots.

    temp_liveness(+Blocks, -LiveIn, -LiveOut)
      liveness/5 over temp names. A phi defines its temp at block entry
      (in Kill, never in LiveIn) and reads its argument on the edge.

    The PLAN asks for these as tabled relations. cfg_tabled.pl has that
    version; docs/m5.md has the measurement that made this one the one
    passes use.
*/
:- module(cfg, [fn_cfg/2, dominators/2, dom_children/3, frontiers/3,
                dominates/3, dom_intervals/3, dominates_iv/3, natural_loops/3,
                liveness/5, temp_liveness/3, gen_kill/2,
                phi_edge_uses/2, inst_uses/2, inst_def/2, jump_uses/2,
                jump_succs/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).

%% CFG

jump_succs(jmp(L), [L]).
jump_succs(jnz(_, L1, L2), Ls) :- sort([L1, L2], Ls).
jump_succs(ret(_), []).
jump_succs(ret, []).
jump_succs(rets(_), []).
jump_succs(hlt, []).

fn_cfg(Blocks, cfg(Entry, Rpo, Succs, Preds)) :-
    Blocks = [blk(Entry, _, _, _)|_],
    findall(Label-Ss,
            ( member(blk(Label, _, _, Jump), Blocks), jump_succs(Jump, Ss) ),
            SuccPairs),
    list_to_assoc(SuccPairs, Succs),
    findall(Label-[], member(Label-_, SuccPairs), NoPreds),
    list_to_assoc(NoPreds, Preds0),
    foldl(add_preds, SuccPairs, Preds0, Preds1),
    assoc_to_list(Preds1, PredPairs0),
    findall(Label-Ps,
            ( member(Label-Ps0, PredPairs0), sort(Ps0, Ps) ),
            PredPairs),
    list_to_assoc(PredPairs, Preds),
    empty_assoc(Seen0),
    reverse_postorder([Entry], Succs, Seen0, _, [], Rpo).

add_preds(Pred-Ss, Preds0, Preds) :- foldl(add_pred(Pred), Ss, Preds0, Preds).

add_pred(Pred, Succ, Preds0, Preds) :-
    get_assoc(Succ, Preds0, Ps),
    put_assoc(Succ, Preds0, [Pred|Ps], Preds).

% Depth-first, pushing each label after its successors: the result is
% reverse postorder.
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

dominators(cfg(Entry, Rpo, _, Preds), Idom) :-
    number_labels(Rpo, 0, Numbered),
    list_to_assoc(Numbered, Num),
    empty_assoc(Idom0),
    put_assoc(Entry, Idom0, Entry, Idom1),
    Rpo = [_|Rest],
    idom_fixpoint(Rest, Preds, Num, Idom1, Idom2),
    del_assoc(Entry, Idom2, _, Idom).

% number_labels(+Labels, +N0, -Pairs): Label-N, counting from N0.
number_labels([], _, []).
number_labels([L|Ls], N, [L-N|Ps]) :- N1 is N + 1, number_labels(Ls, N1, Ps).

% Sweep the labels in reverse postorder until no idom changes.
idom_fixpoint(Labels, Preds, Num, Idom0, Idom) :-
    foldl(update_idom(Preds, Num), Labels, Idom0-false, Idom1-Changed),
    (   Changed == true
    ->  idom_fixpoint(Labels, Preds, Num, Idom1, Idom)
    ;   Idom = Idom1
    ).

% The new idom of B is the intersection of its processed predecessors.
update_idom(Preds, Num, B, Idom0-Changed0, Idom-Changed) :-
    get_assoc(B, Preds, Ps),
    include(has_idom(Idom0), Ps, Processed),
    Processed = [First|Others],
    foldl(intersect(Num, Idom0), Others, First, New),
    (   get_assoc(B, Idom0, Old), Old == New
    ->  Idom = Idom0, Changed = Changed0
    ;   put_assoc(B, Idom0, New, Idom), Changed = true
    ).

has_idom(Idom, L) :- get_assoc(L, Idom, _).

% intersect(+Num, +Idom, +A, +B, -Common): the nearest common dominator
% of A and B, walking up whichever is later in reverse postorder.
intersect(Num, Idom, A, B, Common) :-
    (   A == B
    ->  Common = A
    ;   get_assoc(A, Num, NA),
        get_assoc(B, Num, NB),
        (   NA > NB
        ->  get_assoc(A, Idom, A1),
            intersect(Num, Idom, A1, B, Common)
        ;   get_assoc(B, Idom, B1),
            intersect(Num, Idom, A, B1, Common)
        )
    ).

dom_children(cfg(_, Rpo, _, _), Idom, Kids) :-
    findall(L-[], member(L, Rpo), NoKids),
    list_to_assoc(NoKids, Kids0),
    reverse(Rpo, Reversed),
    foldl(add_child(Idom), Reversed, Kids0, Kids).

add_child(Idom, L, Kids0, Kids) :-
    (   get_assoc(L, Idom, Parent)
    ->  get_assoc(Parent, Kids0, Cs),
        put_assoc(Parent, Kids0, [L|Cs], Kids)
    ;   Kids = Kids0
    ).

dominates(_, A, A) :- !.
dominates(Idom, A, B) :- get_assoc(B, Idom, D), dominates(Idom, A, D).

dom_intervals(Cfg, Idom, Intervals) :-
    Cfg = cfg(Entry, _, _, _),
    dom_children(Cfg, Idom, Kids),
    empty_assoc(Intervals0),
    number_tree(Entry, Kids, 0, _, Intervals0, Intervals).

% Number the dominator subtree at L in preorder from N0; N is the next
% free number.
number_tree(L, Kids, N0, N, Intervals0, Intervals) :-
    get_assoc(L, Kids, Ks),
    N1 is N0 + 1,
    foldl(number_kid(Kids), Ks, N1-Intervals0, N-Intervals1),
    Last is N - 1,
    put_assoc(L, Intervals1, N0-Last, Intervals).

number_kid(Kids, K, N0-Intervals0, N-Intervals) :-
    number_tree(K, Kids, N0, N, Intervals0, Intervals).

dominates_iv(Intervals, A, B) :-
    get_assoc(A, Intervals, PreA-LastA),
    get_assoc(B, Intervals, PreB-_),
    PreA =< PreB,
    PreB =< LastA.

% CHK: walk up from each predecessor of a join point to its idom.
frontiers(cfg(_, Rpo, _, Preds), Idom, DF) :-
    findall(L-[], member(L, Rpo), Empty),
    list_to_assoc(Empty, DF0),
    foldl(join_frontier(Preds, Idom), Rpo, DF0, DF1),
    assoc_to_list(DF1, Pairs0),
    findall(L-S, ( member(L-Xs, Pairs0), sort(Xs, S) ), Pairs),
    list_to_assoc(Pairs, DF).

% DF has a key for every reachable label, so it also tells which
% predecessors are reachable.
join_frontier(Preds, Idom, B, DF0, DF) :-
    get_assoc(B, Preds, Ps0),
    include(has_frontier(DF0), Ps0, Ps),
    (   Ps = [_, _|_], get_assoc(B, Idom, IdomB)
    ->  foldl(add_to_frontiers(Idom, IdomB, B), Ps, DF0, DF)
    ;   DF = DF0
    ).

has_frontier(DF, L) :- get_assoc(L, DF, _).

% B joins every frontier from Runner up to (not including) Stop.
add_to_frontiers(Idom, Stop, B, Runner, DF0, DF) :-
    (   Runner == Stop
    ->  DF = DF0
    ;   get_assoc(Runner, DF0, Xs),
        put_assoc(Runner, DF0, [B|Xs], DF1),
        get_assoc(Runner, Idom, Up),
        add_to_frontiers(Idom, Stop, B, Up, DF1, DF)
    ).

%% Natural loops

natural_loops(Cfg, Idom, Loops) :-
    Cfg = cfg(_, Rpo, Succs, Preds),
    dom_intervals(Cfg, Idom, Intervals),
    findall(Header-Latch,
            ( member(Latch, Rpo),
              get_assoc(Latch, Succs, Ss),
              member(Header, Ss),
              dominates_iv(Intervals, Header, Latch) ),
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

% Walk predecessors back from the latches; a label without an interval
% is unreachable.
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

liveness(cfg(_, Rpo, Succs, Preds), GenKill, EdgeUses, LiveIn, LiveOut) :-
    assoc_to_keys(Succs, All),
    subtract(All, Rpo, Unreached),
    reverse(Rpo, Post),
    append(Post, Unreached, Order),
    number_labels(Order, 0, Numbered),
    list_to_assoc(Numbered, Num),
    findall(N-L, member(L-N, Numbered), Pending),
    findall(L-[], member(L, All), Empty),
    list_to_assoc(Empty, LiveIn0),
    liveness_worklist(Pending, Num, Succs, Preds, GenKill, EdgeUses,
                      LiveIn0, LiveIn),
    findall(L-Out,
            ( member(L, All), live_out(L, Succs, EdgeUses, LiveIn, Out) ),
            OutPairs),
    list_to_assoc(OutPairs, LiveOut).

% Worklist in postorder: always take the pending block that comes first,
% and requeue the predecessors of a block whose live-in set grew.
liveness_worklist([], _, _, _, _, _, LiveIn, LiveIn).
liveness_worklist([_-L|Pending0], Num, Succs, Preds, GenKill, EdgeUses,
                  LiveIn0, LiveIn) :-
    live_out(L, Succs, EdgeUses, LiveIn0, Out),
    get_assoc(L, GenKill, Gen-Kill),
    ord_subtract(Out, Kill, Through),
    ord_union(Gen, Through, New),
    (   get_assoc(L, LiveIn0, Old), Old == New
    ->  liveness_worklist(Pending0, Num, Succs, Preds, GenKill, EdgeUses,
                          LiveIn0, LiveIn)
    ;   put_assoc(L, LiveIn0, New, LiveIn1),
        get_assoc(L, Preds, PredLabels),
        findall(N-P,
                ( member(P, PredLabels), get_assoc(P, Num, N) ),
                Requeued0),
        sort(Requeued0, Requeued),
        ord_union(Pending0, Requeued, Pending),
        liveness_worklist(Pending, Num, Succs, Preds, GenKill, EdgeUses,
                          LiveIn1, LiveIn)
    ).

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

temp_liveness(Blocks, LiveIn, LiveOut) :-
    fn_cfg(Blocks, Cfg),
    gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    liveness(Cfg, GenKill, EdgeUses, LiveIn, LiveOut).

% gen_kill(+Blocks, -GenKill): per block, temps read before written, and
% temps written (phi destinations included).
gen_kill(Blocks, GenKill) :-
    findall(L-(Gen-Kill),
            ( member(B, Blocks),
              B = blk(L, _, _, _),
              block_gen_kill(B, Gen, Kill) ),
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

phi_edge_uses(Blocks, EdgeUses) :-
    findall((P-S)-T,
            ( member(blk(S, Phis, _, _), Blocks),
              member(phi(_, _, Args), Phis),
              member(P-t(T), Args) ),
            Pairs0),
    keysort(Pairs0, Pairs1),
    group_pairs_by_key(Pairs1, Groups),
    findall(Edge-S, ( member(Edge-Ts, Groups), sort(Ts, S) ), Pairs),
    list_to_assoc(Pairs, EdgeUses).

inst_uses(ins(_, _, _, Args), Us) :- temps(Args, Us).
inst_uses(store(_, V, A), Us) :- temps([V, A], Us).
inst_uses(call(_, F, Args), Us) :-
    findall(V, member(arg(_, V), Args), Vs),
    temps([F|Vs], Us).

inst_def(ins(t(D), _, _, _), D).
inst_def(call(to(t(D), _), _, _), D).
inst_def(call(tuple(Rs), _, _), D) :- member(to(t(D), _), Rs).

jump_uses(jnz(V, _, _), Us) :- !, temps([V], Us).
jump_uses(ret(V), Us) :- !, temps([V], Us).
jump_uses(rets(Vs), Us) :- !, temps(Vs, Us).
jump_uses(_, []).

% temps(+Values, -Names): the ordset of temp names among Values.
temps(Vs, Ts) :- findall(T, member(t(T), Vs), Ts0), sort(Ts0, Ts).
