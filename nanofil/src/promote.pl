/*  promote: memory slots to SSA temporaries (QBE's promote and ssa,
    LLVM's mem2reg).

    promote_module(+M0, -M)
    promote_func(+Mode, +F0, -F)
      Mode is module_mode/2 of the module being promoted.

    A slot is one fixed (offset, width) of an alloc that escape.pl calls
    local. An alloc is promoted, all its slots at once, when
      - it is in the entry block, so it runs exactly once per call (the
        validator forbids jumps to the entry block) and its fresh contents
        are the only initial state;
      - its size is a constant and every slot lies inside it, so no access
        could trap or be undefined;
      - its slots do not overlap and each offset has one width, so every
        load reads exactly the bytes one earlier store wrote;
      - in filc mode, p slots are 8-aligned (allocs are 16-aligned), so no
        loadp or storep could trap as misaligned.
    The function must also be in strict SSA form (each temp defined once,
    every definition dominating its uses); otherwise a stored temp could
    be redefined before the load that promote would turn into its copy.
    A function that is not is left alone.

    Loads become copies or extensions of the slot's current value, stores
    disappear, and phis are placed on the iterated dominance frontier of
    the stores where the slot is live (pruned SSA, Cytron et al.). Before
    any store a slot holds 0: Fil-C allocations are zeroed, and in plain
    mode the bytes are unknown, so 0 is one of the values they could have.

    Values keep the class of the store: a storeb of a w value stores the
    whole value, and each load narrows or extends it again, exactly as the
    bytes would.
*/
:- module(promote, [promote_module/2, promote_func/3, promotable/3,
                    alloc_count/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir).
:- use_module(cfg).
:- use_module(escape).

promote_module(module(Items0), module(Items)) :-
    module_mode(module(Items0), Mode),
    maplist(promote_item(Mode), Items0, Items).

promote_item(Mode, F0, F) :- F0 = func(_, _, _, _, _), !, promote_func(Mode, F0, F).
promote_item(_, D, D).

alloc_count(module(Items), N) :-
    findall(x, ( member(func(_, _, _, _, Bs), Items), member(blk(_, _, Is, _), Bs),
                 member(ins(_, _, alloc(_), _), Is) ), Xs),
    length(Xs, N).

promote_func(Mode, F0, F) :-
    F0 = func(Name, Lk, Ret, Params, Blocks0),
    fn_cfg(Blocks0, Cfg),
    dominators(Cfg, Idom),
    (   promotable(Mode, F0, Roots), Roots \== [], strict_ssa(F0, Cfg, Idom)
    ->  promote_roots(Roots, F0, Cfg, Idom, Blocks),
        F = func(Name, Lk, Ret, Params, Blocks)
    ;   F = F0
    ).

/* promotable(+Mode, +F, -Roots): Roots is [A-Slots] for the allocs that
   can be promoted, Slots an ordset of acc(Off, Width). */
promotable(Mode, F, Roots) :-
    F = func(_, _, _, _, [blk(_, _, EntryInsts, _)|_]),
    alloc_classes(F, Classes),
    findall(A-Accs,
            ( member(A-local(c(Size), Accs), Classes),
              memberchk(ins(t(A), _, alloc(_), _), EntryInsts),
              slots_ok(Mode, Size, Accs) ),
            Roots).

slots_ok(Mode, Size, Accs) :-
    maplist(slot_ok(Mode, Size), Accs),
    disjoint(Accs).

slot_ok(Mode, Size, acc(Off, W)) :-
    width_bytes(W, N),
    Off >= 0, Off + N =< Size,
    (   W == p, Mode == filc -> Off mod 8 =:= 0 ; true ).

% Accs is sorted by offset, so it is enough to compare neighbours. Two
% widths at one offset overlap too.
disjoint([]).
disjoint([_]).
disjoint([acc(O1, W1), acc(O2, W2)|As]) :-
    width_bytes(W1, N1),
    O1 + N1 =< O2,
    disjoint([acc(O2, W2)|As]).

/* strict_ssa(+F, +Cfg, +Idom): in the blocks reachable from the entry,
   every temp has one definition, which dominates each use (a phi
   argument is used at the end of its predecessor). */
strict_ssa(F, cfg(_, Rpo, _, _), Idom) :-
    def_counts(F, Counts),
    \+ ( gen_assoc(_, Counts, N), N > 1 ),
    F = func(_, _, _, Params, Blocks),
    Rpo = [Entry|_],
    findall(T-def(Entry, 0), member(par(_, t(T)), Params), D0),
    findall(T-def(L, I),
            ( member(blk(L, Phis, Is, _), Blocks),
              (   member(phi(t(T), _, _), Phis), I = 0
              ;   nth1(I, Is, Ins), inst_def(Ins, T)
              ) ),
            D1),
    append(D0, D1, Ds),
    list_to_assoc(Ds, Defs),
    list_to_assoc([], E), foldl(mark, Rpo, E, Reach),
    dom_intervals(cfg(Entry, Rpo, x, x), Idom, Iv),
    % Collect the uses first: a goal that mentions the big assocs, run by
    % forall/2 once per block, copies them every time.
    findall(L-Phis-Is-J, member(blk(L, Phis, Is, J), Blocks), BLs),
    include(reached(Reach), BLs, Live),
    findall(U, ( member(B, Live), block_use(B, U) ), Uses),
    include(reached_use(Reach), Uses, Checked),
    maplist(defined_at(Defs, Iv), Checked).

reached(Reach, L-_-_-_) :- get_assoc(L, Reach, _).
reached_use(Reach, use(_, L, _)) :- get_assoc(L, Reach, _).

mark(L, A0, A) :- put_assoc(L, A0, t, A).

% use(T, L, At): T is read at position At of block L; a phi argument is
% read at the end (inf) of its predecessor.
block_use(_-Phis-_-_, use(T, P, inf)) :-
    member(phi(_, _, Args), Phis), member(P-t(T), Args).
block_use(L-_-Is-_, use(T, L, I)) :-
    nth1(I, Is, Ins), inst_uses(Ins, Us), member(T, Us).
block_use(L-_-Is-J, use(T, L, N1)) :-
    jump_uses(J, Us), member(T, Us),
    length(Is, N), N1 is N + 1.

% T is defined before position At of block L (inf: the block's end).
defined_at(Defs, Iv, use(T, L, At)) :-
    get_assoc(T, Defs, def(DL, DI)),
    (   DL == L -> ( At == inf -> true ; DI < At )
    ;   dominates_iv(Iv, DL, L)
    ).

%% Rewriting

promote_roots(Roots, F0, Cfg, Idom, Blocks) :-
    F0 = func(_, _, _, _, Blocks0),
    address_temps(F0, Addrs0),
    % Only addresses of promoted allocs matter from here on.
    findall(X-(A-O), ( gen_assoc(X, Addrs0, A-O), memberchk(A-_, Roots) ), APs),
    list_to_assoc(APs, Addrs),
    findall((A-O)-W, ( member(A-Accs, Roots), member(acc(O, W), Accs) ), VWs),
    list_to_assoc(VWs, Widths),
    pairs_keys(VWs, Vars),
    % Liveness of slots: a load reads one, a store writes it.
    findall(L-GK, ( member(B, Blocks0), B = blk(L, _, _, _), slot_gen_kill(B, Addrs, GK) ), GKs),
    list_to_assoc(GKs, GenKill),
    empty_assoc(NoEdges),
    liveness(Cfg, GenKill, NoEdges, LiveIn, _),
    frontiers(Cfg, Idom, DF),
    Cfg = cfg(Entry, _, _, _),
    def_counts(F0, Counts),
    assoc_to_keys(Counts, Used),
    foldl(place_phis(Blocks0, Addrs, DF, LiveIn, Entry), Vars, []-(0-Used), Placed0-_),
    keysort(Placed0, Placed1),
    group_pairs_by_key(Placed1, Placed),      % Label -> [Var-Temp]
    list_to_assoc(Placed, PhiAt),
    findall(V-c(0), member(V, Vars), Zs),
    list_to_assoc(Zs, Zero),
    Ctx = ctx(Addrs, PhiAt),
    blocks_by_label(Blocks0, ByLabel),
    dom_children(Cfg, Idom, Kids),
    rename(Entry, Zero, Ctx, ByLabel, Kids, Cfg, []-[], Out1),
    % Unreachable blocks never run; their slot reads see 0 so that they
    % stay valid, and they still give each successor's phis an argument.
    Cfg = cfg(_, Rpo, _, _),
    findall(L, ( member(blk(L, _, _, _), Blocks0), \+ memberchk(L, Rpo) ), Dead),
    foldl(rename_alone(Zero, Ctx, ByLabel, Cfg), Dead, Out1, New-PhiArgs0),
    list_to_assoc(New, NewBlocks),
    keysort(PhiArgs0, PhiArgs1),
    group_pairs_by_key(PhiArgs1, PhiArgs),    % (Label-Var) -> [Pred-Value]
    list_to_assoc(PhiArgs, ArgsAt),
    maplist(assemble(NewBlocks, Placed, ArgsAt, Widths), Blocks0, Blocks).

slot_gen_kill(blk(_, _, Is, _), Addrs, Gen-Kill) :-
    foldl(slot_gk(Addrs), Is, []-[], Gen-Kill).

slot_gk(Addrs, I, G0-K0, G-K) :-
    (   I = ins(_, _, load(_), [t(X)]), get_assoc(X, Addrs, Var)
    ->  ( ord_memberchk(Var, K0) -> G = G0 ; ord_add_element(G0, Var, G) ), K = K0
    ;   I = store(_, _, t(X)), get_assoc(X, Addrs, Var)
    ->  G = G0, ord_add_element(K0, Var, K)
    ;   G = G0, K = K0
    ).

/* place_phis: the iterated dominance frontier of the blocks that store
   to Var, keeping only blocks where Var is live on entry. Each placed phi
   counts as a store for the iteration. Unreachable stores are ignored:
   they never run. */
place_phis(Blocks, Addrs, DF, LiveIn, Entry, Var, P0-(N0-Used), P-(N-Used)) :-
    findall(L, ( member(blk(L, _, Is, _), Blocks), get_assoc(L, DF, _),
                 member(store(_, _, t(X)), Is), get_assoc(X, Addrs, V), V == Var ), Ls0),
    sort([Entry|Ls0], Ls),
    idf(Ls, Var, DF, LiveIn, [], Phis),
    foldl(new_phi(Var, Used), Phis, P0-N0, P-N).

idf([], _, _, _, Placed, Placed).
idf([L|Ls], Var, DF, LiveIn, Placed0, Placed) :-
    get_assoc(L, DF, Fs),
    foldl(idf_add(Var, LiveIn), Fs, Placed0-Ls, Placed1-Ls1),
    idf(Ls1, Var, DF, LiveIn, Placed1, Placed).

idf_add(Var, LiveIn, Y, P0-W0, P-W) :-
    (   \+ ord_memberchk(Y, P0), get_assoc(Y, LiveIn, In), ord_memberchk(Var, In)
    ->  ord_add_element(P0, Y, P), W = [Y|W0]
    ;   P = P0, W = W0
    ).

new_phi(Var, Used, L, P0-N0, [L-(Var-T)|P0]-N) :- fresh(Used, N0, T, N).

fresh(Used, N0, T, N) :-
    N1 is N0 + 1,
    number_codes(N1, Ds), atom_codes(T0, [0'p, 0'r, 0'.|Ds]),
    (   ord_memberchk(T0, Used) -> fresh(Used, N1, T, N) ; T = T0, N = N1 ).

blocks_by_label(Blocks, A) :-
    findall(L-B, ( member(B, Blocks), B = blk(L, _, _, _) ), Ps),
    list_to_assoc(Ps, A).

% Walk the dominator tree, carrying each slot's current value.
rename(L, Cur0, Ctx, ByLabel, Kids, Cfg, Out0, Out) :-
    rename_block(L, Cur0, Ctx, ByLabel, Cfg, Cur, Out0, Out1),
    get_assoc(L, Kids, Ks),
    foldl(rename_kid(Cur, Ctx, ByLabel, Kids, Cfg), Ks, Out1, Out).

rename_kid(Cur, Ctx, ByLabel, Kids, Cfg, K, Out0, Out) :-
    rename(K, Cur, Ctx, ByLabel, Kids, Cfg, Out0, Out).

rename_alone(Zero, Ctx, ByLabel, Cfg, L, Out0, Out) :-
    rename_block(L, Zero, Ctx, ByLabel, Cfg, _, Out0, Out).

rename_block(L, Cur0, ctx(Addrs, PhiAt), ByLabel, cfg(_, _, Succs, _), Cur,
             New0-Args0, [L-blk(L, Phis, Is, J)|New0]-Args) :-
    get_assoc(L, ByLabel, blk(L, Phis, Is0, J)),
    (   get_assoc(L, PhiAt, VTs) -> true ; VTs = [] ),
    foldl(phi_current, VTs, Cur0, Cur1),
    foldl(rewrite(Addrs), Is0, Is1-Cur1, []-Cur),
    Is = Is1,
    get_assoc(L, Succs, Ss),
    findall((S-Var)-(L-Val),
            ( member(S, Ss), get_assoc(S, PhiAt, SVTs), member(Var-_, SVTs),
              get_assoc(Var, Cur, Val) ),
            As),
    append(As, Args0, Args).

phi_current(Var-T, C0, C) :- put_assoc(Var, C0, t(T), C).

% rewrite(+Addrs, +Ins, Is0-Cur0, Is-Cur): a difference list of the
% rewritten instructions, threading the current values.
rewrite(Addrs, I, Is0-Cur0, Is-Cur) :-
    (   I = ins(t(D), _, _, _), get_assoc(D, Addrs, _)
    ->  Is0 = Is, Cur = Cur0                  % the alloc or a derived address
    ;   I = ins(D, K, load(T), [t(X)]), get_assoc(X, Addrs, Var)
    ->  get_assoc(Var, Cur0, V),
        load_op(T, K, Op),
        Is0 = [ins(D, K, Op, [V])|Is], Cur = Cur0
    ;   I = store(_, V, t(X)), get_assoc(X, Addrs, Var)
    ->  Is0 = Is, put_assoc(Var, Cur0, V, Cur)
    ;   Is0 = [I|Is], Cur = Cur0
    ).

% What a load at class K of type T computes from the value last stored
% at its width (see the header).
load_op(l, _, copy).
load_op(p, _, copy).
load_op(sw, K, Op) :- ( K == w -> Op = copy ; Op = ext(sw) ).
load_op(uw, K, Op) :- ( K == w -> Op = copy ; Op = ext(uw) ).
load_op(sh, _, ext(sh)).
load_op(uh, _, ext(uh)).
load_op(sb, _, ext(sb)).
load_op(ub, _, ext(ub)).

slot_class(l, l).
slot_class(p, p).
slot_class(w, w).
slot_class(h, w).
slot_class(b, w).

assemble(NewBlocks, Placed, ArgsAt, Widths, blk(L, _, _, _), blk(L, Phis, Is, J)) :-
    get_assoc(L, NewBlocks, blk(L, Phis0, Is, J)),
    (   memberchk(L-VTs, Placed) -> true ; VTs = [] ),
    findall(phi(t(T), K, Args),
            ( member(Var-T, VTs), get_assoc(Var, Widths, W), slot_class(W, K),
              get_assoc(L-Var, ArgsAt, Args0), sort(Args0, Args) ),
            New),
    append(Phis0, New, Phis).
