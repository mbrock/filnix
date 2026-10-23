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
                    alloc_count/2, strict_ssa/3]).

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

promote_item(Mode, Item0, Item) :-
    Item0 = func(_, _, _, _, _), !,
    promote_func(Mode, Item0, Item).
promote_item(_, Item, Item).

alloc_count(module(Items), N) :-
    findall(x,
            ( member(func(_, _, _, _, Blocks), Items),
              member(blk(_, _, Insts, _), Blocks),
              member(ins(_, _, alloc(_), _), Insts) ),
            Allocs),
    length(Allocs, N).

promote_func(Mode, F0, F) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    func_cfg(Blocks0, Cfg),
    dominators(Cfg, Idom),
    (   promotable(Mode, F0, Roots),
        Roots \== [],
        strict_ssa(F0, Cfg, Idom)
    ->  promote_roots(Roots, F0, Cfg, Idom, Blocks),
        F = func(Name, Linkage, Ret, Params, Blocks)
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
    slots_disjoint(Accs).

slot_ok(Mode, Size, acc(Off, Width)) :-
    width_bytes(Width, Bytes),
    Off >= 0,
    Off + Bytes =< Size,
    (   Width == p, Mode == filc
    ->  Off mod 8 =:= 0
    ;   true
    ).

% Accs is sorted by offset, so it is enough to compare neighbours. Two
% widths at one offset overlap too.
slots_disjoint([]).
slots_disjoint([_]).
slots_disjoint([acc(Off1, Width1), acc(Off2, Width2)|Accs]) :-
    width_bytes(Width1, Bytes1),
    Off1 + Bytes1 =< Off2,
    slots_disjoint([acc(Off2, Width2)|Accs]).

/* strict_ssa(+F, +Cfg, +Idom): in the blocks reachable from the entry,
   every temp has one definition, which dominates each use (a phi
   argument is used at the end of its predecessor). */
strict_ssa(F, cfg(_, Rpo, _, _), Idom) :-
    def_counts(F, Counts),
    \+ ( gen_assoc(_, Counts, N), N > 1 ),
    F = func(_, _, _, Params, Blocks),
    Rpo = [Entry|_],
    % def(Label, Pos): defined at position Pos of block Label (0 for
    % parameters and phis).
    findall(T-def(Entry, 0), member(par(_, t(T)), Params), ParamDefs),
    findall(T-def(L, Pos),
            ( member(blk(L, Phis, Insts, _), Blocks),
              (   member(phi(t(T), _, _), Phis), Pos = 0
              ;   nth1(Pos, Insts, Ins), inst_def(Ins, T)
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, DefPairs),
    list_to_assoc(DefPairs, Defs),
    list_to_assoc([], Empty),
    foldl(mark_reached, Rpo, Empty, Reach),
    dom_intervals(cfg(Entry, Rpo, x, x), Idom, Intervals),
    % Collect the uses first: a goal that mentions the big assocs, run by
    % forall/2 once per block, copies them every time.
    findall(L-Phis-Insts-Jump,
            member(blk(L, Phis, Insts, Jump), Blocks),
            Parts),
    include(block_reached(Reach), Parts, Reached),
    findall(U, ( member(B, Reached), block_use(B, U) ), Uses),
    include(use_reached(Reach), Uses, Checked),
    maplist(defined_at(Defs, Intervals), Checked).

block_reached(Reach, L-_-_-_) :- get_assoc(L, Reach, _).

use_reached(Reach, use(_, L, _)) :- get_assoc(L, Reach, _).

mark_reached(L, Reach0, Reach) :- put_assoc(L, Reach0, t, Reach).

% use(T, L, At): T is read at position At of block L; a phi argument is
% read at the end (inf) of its predecessor.
block_use(_-Phis-_-_, use(T, P, inf)) :-
    member(phi(_, _, Args), Phis),
    member(P-t(T), Args).
block_use(L-_-Insts-_, use(T, L, Pos)) :-
    nth1(Pos, Insts, Ins),
    inst_uses(Ins, Us),
    member(T, Us).
block_use(L-_-Insts-Jump, use(T, L, JumpPos)) :-
    jump_uses(Jump, Us),
    member(T, Us),
    length(Insts, N),
    JumpPos is N + 1.

% T is defined before position At of block L (inf: the block's end).
defined_at(Defs, Intervals, use(T, L, At)) :-
    get_assoc(T, Defs, def(DefL, DefPos)),
    (   DefL == L
    ->  ( At == inf -> true ; DefPos < At )
    ;   dominates_by_interval(Intervals, DefL, L)
    ).

%% Rewriting

promote_roots(Roots, F0, Cfg, Idom, Blocks) :-
    F0 = func(_, _, _, _, Blocks0),
    address_temps(F0, AllAddrs),
    % Only addresses of promoted allocs matter from here on.
    findall(X-(A-Off),
            ( gen_assoc(X, AllAddrs, A-Off), memberchk(A-_, Roots) ),
            AddrPairs),
    list_to_assoc(AddrPairs, Addrs),
    % A slot (Var) is A-Off; Widths maps it to its access width.
    findall((A-Off)-Width,
            ( member(A-Accs, Roots), member(acc(Off, Width), Accs) ),
            VarWidths),
    list_to_assoc(VarWidths, Widths),
    pairs_keys(VarWidths, Vars),
    % Liveness of slots: a load reads one, a store writes it.
    findall(L-GenKill,
            ( member(B, Blocks0),
              B = blk(L, _, _, _),
              slot_gen_kill(B, Addrs, GenKill) ),
            GenKillPairs),
    list_to_assoc(GenKillPairs, GenKill),
    empty_assoc(NoEdges),
    liveness(Cfg, GenKill, NoEdges, LiveIn, _),
    frontiers(Cfg, Idom, DF),
    Cfg = cfg(Entry, _, _, _),
    def_counts(F0, Counts),
    assoc_to_keys(Counts, Used),
    % Index the reachable stores once, rather than scanning all blocks
    % and instructions again for every slot.
    findall(Var-L,
            ( member(blk(L, _, Insts, _), Blocks0),
              get_assoc(L, DF, _),
              member(store(_, _, t(X)), Insts),
              get_assoc(X, Addrs, Var) ),
            Stores0),
    keysort(Stores0, Stores1),
    group_pairs_by_key(Stores1, StorePairs),
    list_to_assoc(StorePairs, Stores),
    foldl(place_phis(Stores, DF, LiveIn, Entry), Vars,
          []-(0-Used), Placed0-_),
    keysort(Placed0, Placed1),
    group_pairs_by_key(Placed1, Placed),      % Label -> [Var-Temp]
    list_to_assoc(Placed, PhiAt),
    findall(Var-c(0), member(Var, Vars), Zeros),
    list_to_assoc(Zeros, Zero),
    Ctx = ctx(Addrs, PhiAt),
    blocks_by_label(Blocks0, ByLabel),
    dom_children(Cfg, Idom, Kids),
    rename_tree(Entry, Zero, Ctx, ByLabel, Kids, Cfg, []-[], Renamed),
    % Unreachable blocks never run; their slot reads see 0 so that they
    % stay valid, and they still give each successor's phis an argument.
    Cfg = cfg(_, Rpo, _, _),
    findall(L,
            ( member(blk(L, _, _, _), Blocks0), \+ memberchk(L, Rpo) ),
            Dead),
    foldl(rename_unreachable(Zero, Ctx, ByLabel, Cfg), Dead,
          Renamed, New-PhiArgs0),
    list_to_assoc(New, NewBlocks),
    keysort(PhiArgs0, PhiArgs1),
    group_pairs_by_key(PhiArgs1, PhiArgs),    % (Label-Var) -> [Pred-Value]
    list_to_assoc(PhiArgs, ArgsAt),
    maplist(assemble_block(NewBlocks, PhiAt, ArgsAt, Widths), Blocks0, Blocks).

slot_gen_kill(blk(_, _, Insts, _), Addrs, Gen-Kill) :-
    foldl(slot_inst_gen_kill(Addrs), Insts, []-[], Gen-Kill).

slot_inst_gen_kill(Addrs, I, Gen0-Kill0, Gen-Kill) :-
    (   I = ins(_, _, load(_), [t(X)]), get_assoc(X, Addrs, Var)
    ->  (   ord_memberchk(Var, Kill0)
        ->  Gen = Gen0
        ;   ord_add_element(Gen0, Var, Gen)
        ),
        Kill = Kill0
    ;   I = store(_, _, t(X)), get_assoc(X, Addrs, Var)
    ->  Gen = Gen0,
        ord_add_element(Kill0, Var, Kill)
    ;   Gen = Gen0,
        Kill = Kill0
    ).

/* place_phis: the iterated dominance frontier of the blocks that store
   to Var, keeping only blocks where Var is live on entry. Each placed phi
   counts as a store for the iteration. Unreachable stores are ignored:
   they never run. The accumulator is Placed-(N-Used): the Label-(Var-Temp)
   phis so far, the last fresh temp number, and the names already taken. */
place_phis(Stores, DF, LiveIn, Entry, Var,
           Placed0-(N0-Used), Placed-(N-Used)) :-
    (   get_assoc(Var, Stores, Labels0) -> true ; Labels0 = [] ),
    sort([Entry|Labels0], Labels),
    iterated_frontier(Labels, Var, DF, LiveIn, [], PhiLabels),
    foldl(new_phi(Var, Used), PhiLabels, Placed0-N0, Placed-N).

% Worklist over Labels, collecting the ordset of frontier labels where
% Var is live; each new one is pushed back on the worklist.
iterated_frontier([], _, _, _, Placed, Placed).
iterated_frontier([L|Ls], Var, DF, LiveIn, Placed0, Placed) :-
    get_assoc(L, DF, Frontier),
    foldl(add_live_frontier(Var, LiveIn), Frontier,
          Placed0-Ls, Placed1-Ls1),
    iterated_frontier(Ls1, Var, DF, LiveIn, Placed1, Placed).

add_live_frontier(Var, LiveIn, Y, Placed0-Work0, Placed-Work) :-
    (   \+ ord_memberchk(Y, Placed0),
        get_assoc(Y, LiveIn, In),
        ord_memberchk(Var, In)
    ->  ord_add_element(Placed0, Y, Placed),
        Work = [Y|Work0]
    ;   Placed = Placed0,
        Work = Work0
    ).

new_phi(Var, Used, L, Placed0-N0, [L-(Var-T)|Placed0]-N) :-
    fresh_temp(Used, N0, T, N).

% fresh_temp(+Used, +N0, -T, -N): T is pr.N, the first such name after
% N0 that is not in Used.
fresh_temp(Used, N0, T, N) :-
    N1 is N0 + 1,
    number_codes(N1, Ds),
    atom_codes(T0, [0'p, 0'r, 0'.|Ds]),
    (   ord_memberchk(T0, Used)
    ->  fresh_temp(Used, N1, T, N)
    ;   T = T0,
        N = N1
    ).

blocks_by_label(Blocks, ByLabel) :-
    findall(L-B, ( member(B, Blocks), B = blk(L, _, _, _) ), Pairs),
    list_to_assoc(Pairs, ByLabel).

% Walk the dominator tree, carrying each slot's current value. Out is
% NewBlocks-PhiArgs: Label-blk pairs, and (Succ-Var)-(Label-Value) phi
% arguments.
rename_tree(L, Cur0, Ctx, ByLabel, Kids, Cfg, Out0, Out) :-
    rename_block(L, Cur0, Ctx, ByLabel, Cfg, Cur, Out0, Out1),
    get_assoc(L, Kids, Ks),
    foldl(rename_kid(Cur, Ctx, ByLabel, Kids, Cfg), Ks, Out1, Out).

rename_kid(Cur, Ctx, ByLabel, Kids, Cfg, K, Out0, Out) :-
    rename_tree(K, Cur, Ctx, ByLabel, Kids, Cfg, Out0, Out).

rename_unreachable(Zero, Ctx, ByLabel, Cfg, L, Out0, Out) :-
    rename_block(L, Zero, Ctx, ByLabel, Cfg, _, Out0, Out).

rename_block(L, Cur0, ctx(Addrs, PhiAt), ByLabel, cfg(_, _, Succs, _), Cur,
             New0-Args0, [L-blk(L, Phis, Insts, Jump)|New0]-Args) :-
    get_assoc(L, ByLabel, blk(L, Phis, Insts0, Jump)),
    (   get_assoc(L, PhiAt, VarTemps) -> true ; VarTemps = [] ),
    foldl(phi_current, VarTemps, Cur0, Cur1),
    foldl(rewrite_inst(Addrs), Insts0, Insts-Cur1, []-Cur),
    get_assoc(L, Succs, Ss),
    findall((S-Var)-(L-Val),
            ( member(S, Ss),
              get_assoc(S, PhiAt, SuccVarTemps),
              member(Var-_, SuccVarTemps),
              get_assoc(Var, Cur, Val) ),
            Args1),
    append(Args1, Args0, Args).

phi_current(Var-T, Cur0, Cur) :- put_assoc(Var, Cur0, t(T), Cur).

% rewrite_inst(+Addrs, +Ins, Insts0-Cur0, Insts-Cur): a difference list
% of the rewritten instructions, threading the current values.
rewrite_inst(Addrs, I, Insts0-Cur0, Insts-Cur) :-
    (   I = ins(t(D), _, _, _), get_assoc(D, Addrs, _)
    ->  Insts0 = Insts,                       % the alloc or a derived address
        Cur = Cur0
    ;   I = ins(D, K, load(T), [t(X)]), get_assoc(X, Addrs, Var)
    ->  get_assoc(Var, Cur0, V),
        load_op(T, K, Op),
        Insts0 = [ins(D, K, Op, [V])|Insts],
        Cur = Cur0
    ;   I = store(_, V, t(X)), get_assoc(X, Addrs, Var)
    ->  Insts0 = Insts,
        put_assoc(Var, Cur0, V, Cur)
    ;   Insts0 = [I|Insts],
        Cur = Cur0
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

% The class of a slot's phi, from the slot's width.
slot_class(l, l).
slot_class(p, p).
slot_class(w, w).
slot_class(h, w).
slot_class(b, w).

% The renamed block, with the slots' phis appended to its own.
assemble_block(NewBlocks, PhiAt, ArgsAt, Widths, blk(L, _, _, _),
               blk(L, Phis, Insts, Jump)) :-
    get_assoc(L, NewBlocks, blk(L, Phis0, Insts, Jump)),
    (   get_assoc(L, PhiAt, VarTemps) -> true ; VarTemps = [] ),
    findall(phi(t(T), K, Args),
            ( member(Var-T, VarTemps),
              get_assoc(Var, Widths, Width),
              slot_class(Width, K),
              get_assoc(L-Var, ArgsAt, Args0),
              sort(Args0, Args) ),
            SlotPhis),
    append(Phis0, SlotPhis, Phis).
