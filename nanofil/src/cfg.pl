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
                dominates/3, dom_intervals/3, dominates_iv/3, liveness/5, temp_liveness/3, gen_kill/2,
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
    findall(L-Ss, ( member(blk(L, _, _, J), Blocks), jump_succs(J, Ss) ), SPs),
    list_to_assoc(SPs, Succs),
    findall(L-[], member(L-_, SPs), E0),
    list_to_assoc(E0, P0),
    foldl(add_preds, SPs, P0, P1),
    assoc_to_list(P1, PL0),
    findall(L-S, ( member(L-Ps0, PL0), sort(Ps0, S) ), PL),
    list_to_assoc(PL, Preds),
    empty_assoc(Seen0),
    dfs([Entry], Succs, Seen0, _, [], Rpo).

add_preds(P-Ss, A0, A) :- foldl(add_pred(P), Ss, A0, A).
add_pred(P, S, A0, A) :- get_assoc(S, A0, Ps), put_assoc(S, A0, [P|Ps], A).

% Depth-first, pushing each label after its successors: the result is
% reverse postorder.
dfs([], _, Seen, Seen, Post, Post).
dfs([L|Ls], Succs, Seen0, Seen, Post0, Post) :-
    (   get_assoc(L, Seen0, _)
    ->  dfs(Ls, Succs, Seen0, Seen, Post0, Post)
    ;   put_assoc(L, Seen0, t, Seen1),
        get_assoc(L, Succs, Ss),
        dfs(Ss, Succs, Seen1, Seen2, Post0, Post1),
        dfs(Ls, Succs, Seen2, Seen, [L|Post1], Post)
    ).

%% Dominators

dominators(cfg(Entry, Rpo, _, Preds), Idom) :-
    numbered(Rpo, 0, NPs),
    list_to_assoc(NPs, Num),
    empty_assoc(I0),
    put_assoc(Entry, I0, Entry, I1),
    Rpo = [_|Rest],
    dom_fix(Rest, Preds, Num, I1, I2),
    del_assoc(Entry, I2, _, Idom).

numbered([], _, []).
numbered([L|Ls], N, [L-N|Ps]) :- N1 is N + 1, numbered(Ls, N1, Ps).

dom_fix(Ls, Preds, Num, I0, I) :-
    foldl(dom_step(Preds, Num), Ls, I0-false, I1-Changed),
    (   Changed == true -> dom_fix(Ls, Preds, Num, I1, I) ; I = I1 ).

dom_step(Preds, Num, B, I0-C0, I-C) :-
    get_assoc(B, Preds, Ps),
    include(processed(I0), Ps, Done),
    Done = [P|Others],
    foldl(intersect(Num, I0), Others, P, New),
    (   get_assoc(B, I0, Old), Old == New
    ->  I = I0, C = C0
    ;   put_assoc(B, I0, New, I), C = true
    ).

processed(I, P) :- get_assoc(P, I, _).

intersect(Num, I, A, B, R) :-
    (   A == B -> R = A
    ;   get_assoc(A, Num, NA), get_assoc(B, Num, NB),
        (   NA > NB -> get_assoc(A, I, A1), intersect(Num, I, A1, B, R)
        ;   get_assoc(B, I, B1), intersect(Num, I, A, B1, R)
        )
    ).

dom_children(cfg(_, Rpo, _, _), Idom, Kids) :-
    findall(L-[], member(L, Rpo), E),
    list_to_assoc(E, K0),
    reverse(Rpo, Rev),
    foldl(add_child(Idom), Rev, K0, Kids).

add_child(Idom, L, K0, K) :-
    (   get_assoc(L, Idom, D)
    ->  get_assoc(D, K0, Cs), put_assoc(D, K0, [L|Cs], K)
    ;   K = K0
    ).

dominates(_, A, A) :- !.
dominates(Idom, A, B) :- get_assoc(B, Idom, D), dominates(Idom, A, D).

dom_intervals(Cfg, Idom, Iv) :-
    Cfg = cfg(Entry, _, _, _),
    dom_children(Cfg, Idom, Kids),
    empty_assoc(I0),
    number_tree(Entry, Kids, 0, _, I0, Iv).

number_tree(L, Kids, N0, N, I0, I) :-
    get_assoc(L, Kids, Ks),
    N1 is N0 + 1,
    foldl(number_kid(Kids), Ks, N1-I0, N-I1),
    Last is N - 1,
    put_assoc(L, I1, N0-Last, I).

number_kid(Kids, K, N0-I0, N-I) :- number_tree(K, Kids, N0, N, I0, I).

dominates_iv(Iv, A, B) :-
    get_assoc(A, Iv, PA-LA), get_assoc(B, Iv, PB-_),
    PA =< PB, PB =< LA.

% CHK: walk up from each predecessor of a join point to its idom.
frontiers(cfg(_, Rpo, _, Preds), Idom, DF) :-
    findall(L-[], member(L, Rpo), E),
    list_to_assoc(E, D0),
    foldl(join_frontier(Preds, Idom), Rpo, D0, D1),
    assoc_to_list(D1, Ps0),
    findall(L-S, ( member(L-Xs, Ps0), sort(Xs, S) ), Ps),
    list_to_assoc(Ps, DF).

join_frontier(Preds, Idom, B, D0, D) :-
    get_assoc(B, Preds, Ps0),
    include(reachable(Idom, D0), Ps0, Ps),
    (   Ps = [_, _|_], get_assoc(B, Idom, IB)
    ->  foldl(runner(Idom, IB, B), Ps, D0, D)
    ;   D = D0
    ).

reachable(_, D, P) :- get_assoc(P, D, _).

runner(Idom, Stop, B, R, D0, D) :-
    (   R == Stop -> D = D0
    ;   get_assoc(R, D0, Xs), put_assoc(R, D0, [B|Xs], D1),
        get_assoc(R, Idom, R1),
        runner(Idom, Stop, B, R1, D1, D)
    ).

%% Liveness

liveness(cfg(_, Rpo, Succs, Preds), GenKill, EdgeUses, LiveIn, LiveOut) :-
    assoc_to_keys(Succs, All),
    subtract(All, Rpo, Unreached),
    reverse(Rpo, Post),
    append(Post, Unreached, Order),
    numbered(Order, 0, LNs),
    list_to_assoc(LNs, Num),
    findall(N-L, member(L-N, LNs), Pending),
    findall(L-[], member(L, All), E),
    list_to_assoc(E, In0),
    live_work(Pending, Num, Succs, Preds, GenKill, EdgeUses, In0, LiveIn),
    findall(L-Out,
            ( member(L, All), live_out(L, Succs, EdgeUses, LiveIn, Out) ),
            OPs),
    list_to_assoc(OPs, LiveOut).

% Worklist in postorder: always take the pending block that comes first,
% and requeue the predecessors of a block whose live-in set grew.
live_work([], _, _, _, _, _, In, In).
live_work([_-L|Ps0], Num, Succs, Preds, GK, EU, In0, In) :-
    live_out(L, Succs, EU, In0, Out),
    get_assoc(L, GK, Gen-Kill),
    ord_subtract(Out, Kill, Through),
    ord_union(Gen, Through, New),
    (   get_assoc(L, In0, Old), Old == New
    ->  live_work(Ps0, Num, Succs, Preds, GK, EU, In0, In)
    ;   put_assoc(L, In0, New, In1),
        get_assoc(L, Preds, PLs),
        findall(N-P, ( member(P, PLs), get_assoc(P, Num, N) ), Ws0),
        sort(Ws0, Ws),
        ord_union(Ps0, Ws, Ps),
        live_work(Ps, Num, Succs, Preds, GK, EU, In1, In)
    ).

live_out(L, Succs, EU, In, Out) :-
    get_assoc(L, Succs, Ss),
    foldl(succ_live(L, EU, In), Ss, [], Out).

succ_live(L, EU, In, S, O0, O) :-
    get_assoc(S, In, SIn),
    ord_union(O0, SIn, O1),
    (   get_assoc(L-S, EU, Us) -> ord_union(O1, Us, O) ; O = O1 ).

%% Temps

temp_liveness(Blocks, LiveIn, LiveOut) :-
    fn_cfg(Blocks, Cfg),
    gen_kill(Blocks, GK),
    phi_edge_uses(Blocks, EU),
    liveness(Cfg, GK, EU, LiveIn, LiveOut).

% gen_kill(+Blocks, -GK): per block, temps read before written, and
% temps written (phi destinations included).
gen_kill(Blocks, GK) :-
    findall(L-(Gen-Kill), ( member(B, Blocks), B = blk(L, _, _, _), block_gen_kill(B, Gen, Kill) ), Ps),
    list_to_assoc(Ps, GK).

block_gen_kill(blk(_, Phis, Insts, J), Gen, Kill) :-
    findall(D, member(phi(t(D), _, _), Phis), K0),
    sort(K0, Kill0),
    foldl(gk_inst, Insts, []-Kill0, Gen1-Kill),
    jump_uses(J, JU),
    ord_subtract(JU, Kill, JG),
    ord_union(Gen1, JG, Gen).

gk_inst(I, G0-K0, G-K) :-
    inst_uses(I, Us),
    ord_subtract(Us, K0, New),
    ord_union(G0, New, G),
    findall(D, inst_def(I, D), Ds0), sort(Ds0, Ds),
    ord_union(K0, Ds, K).

phi_edge_uses(Blocks, EU) :-
    findall((P-S)-T,
            ( member(blk(S, Phis, _, _), Blocks),
              member(phi(_, _, Args), Phis),
              member(P-t(T), Args) ),
            Ps0),
    keysort(Ps0, Ps1),
    group_pairs_by_key(Ps1, Gs),
    findall(K-S, ( member(K-Ts, Gs), sort(Ts, S) ), Ps),
    list_to_assoc(Ps, EU).

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

temps(Vs, Ts) :- findall(T, member(t(T), Vs), Ts0), sort(Ts0, Ts).
