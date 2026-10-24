/*  promote: memory slots to SSA temporaries, by promote_module/2 and
    promote_func/3. Prior art: QBE's promote and ssa passes, LLVM's
    mem2reg.

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
        load(p) or store(p, ...) could trap as misaligned.
    The function must also be in strict SSA form (each temp defined once,
    every definition dominating its uses); otherwise a stored temp could
    be redefined before the load that promote would turn into its copy.
    A function that is not is left alone.

    Loads become copies or extensions of the slot's current value, stores
    disappear, and phis are placed on the iterated dominance frontier of
    the stores where the slot is live (pruned SSA, Cytron et al.). Before
    any store a slot holds 0: Fil-C allocations are zeroed, and in plain
    mode the bytes are unknown, so 0 is one of the values they could have.

    Values keep the class of the store: a store(b, ...) of a w value
    keeps the whole value, and each load narrows or extends it again,
    exactly as the bytes would.
*/
:- module(promote, [promote_module/2, promote_func/3, promotable/3,
                    alloc_count/2, strict_ssa/3]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(library(dcgs)).
:- use_module(ir).
:- use_module(cfg).
:- use_module(escape).

%! promote_module(+M0, -M) is det.
%
%  M is the module M0 with the promotable allocs of each function
%  promoted.

promote_module(module(Items0), module(Items)) :-
    module_mode(module(Items0), Mode),
    maplist(promote_item(Mode), Items0, Items).

% promote_item(+Mode, +Item0, -Item): Item is the module item Item0,
% promoted if it is a function.
promote_item(Mode, Item0, Item) :-
    item_mode_promoted(Item0, Mode, Item).

item_mode_promoted(func(Name, Linkage, Ret, Params, Blocks), Mode, F) :-
    promote_func(Mode, func(Name, Linkage, Ret, Params, Blocks), F).
item_mode_promoted(data(Name, Linkage, Align, Items), _,
                   data(Name, Linkage, Align, Items)).

%! alloc_count(+M, -N) is det.
%
%  N is the number of alloc instructions in the functions of module M.

alloc_count(module(Items), N) :-
    findall(x,
            ( member(func(_, _, _, _, Blocks), Items),
              member(block(_, _, Insts, _), Blocks),
              member(let(_, _, alloc(_), _), Insts) ),
            Allocs),
    length(Allocs, N).

%! promote_func(+Mode, +F0, -F) is det.
%
%  F is the function F0 with its promotable allocs promoted, or F0 if
%  it has none or is not in strict SSA form. Mode is module_mode/2 of
%  the module being promoted.

promote_func(_, F, F) :- setjmp_func(F), !.
promote_func(Mode, F0, F) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    func_cfg(Blocks0, Cfg),
    cfg_idoms(Cfg, Idom),
    (   promotable(Mode, F0, Roots),
        Roots \== [],
        strict_ssa(F0, Cfg, Idom)
    ->  promote_roots(Roots, F0, Cfg, Idom, Blocks),
        F = func(Name, Linkage, Ret, Params, Blocks)
    ;   F = F0
    ).

%! promotable(+Mode, +F, -Roots) is det.
%
%  Roots is [A-Slots] for the allocs A of F that can be promoted, in
%  order, Slots an ordset of acc(Off, Width).

promotable(_, F, []) :- setjmp_func(F), !.
promotable(Mode, F, Roots) :-
    F = func(_, _, _, _, [block(_, _, EntryInsts, _)|_]),
    alloc_classes(F, Classes),
    findall(A-Accs,
            ( member(A-local(const(Size), Accs), Classes),
              memberchk(let(tmp(A), _, alloc(_), _), EntryInsts),
              slots_ok(Mode, Size, Accs) ),
            Roots).

slots_ok(Mode, Size, Accs) :-
    maplist(slot_ok(Mode, Size), Accs),
    slots_disjoint(Accs).

slot_ok(Mode, Size, acc(Off, Width)) :-
    width_bytes(Width, Bytes),
    Off >= 0,
    Off + Bytes =< Size,
    width_mode_aligned(Width, Mode, Off).

% width_mode_aligned(+Width, +Mode, +Off): a slot of Width at Off is
% aligned enough in Mode: only p slots in filc mode need 8.
width_mode_aligned(b, _, _).
width_mode_aligned(h, _, _).
width_mode_aligned(w, _, _).
width_mode_aligned(l, _, _).
width_mode_aligned(p, Mode, Off) :-
    mode_pointer_aligned(Mode, Off).

mode_pointer_aligned(plain, _).
mode_pointer_aligned(filc, Off) :-
    Off mod 8 =:= 0.

% slots_disjoint(+Accs): no two of Accs overlap.
% Accs is sorted by offset, so it is enough to compare neighbours. Two
% widths at one offset overlap too.
slots_disjoint([]).
slots_disjoint([Acc|Accs]) :-
    slots_disjoint_(Accs, Acc).

% slots_disjoint_(+Accs, +Acc): Acc, then Accs, do not overlap.
slots_disjoint_([], _).
slots_disjoint_([acc(Off2, Width2)|Accs], acc(Off1, Width1)) :-
    width_bytes(Width1, Bytes1),
    Off1 + Bytes1 =< Off2,
    slots_disjoint_(Accs, acc(Off2, Width2)).

%! strict_ssa(+F, +Cfg, +Idom) is semidet.
%
%  F is in strict SSA form: every temp has one definition, and in the
%  blocks reachable from the entry each definition dominates each use (a
%  phi argument is used at the end of its predecessor). Cfg and Idom are
%  those of F.

strict_ssa(F, cfg(_, Rpo, _, _), Idom) :-
    def_counts(F, Counts),
    \+ ( gen_assoc(_, Counts, N), N > 1 ),
    F = func(_, _, _, Params, Blocks),
    Rpo = [Entry|_],
    % def(Label, Pos): defined at position Pos of block Label (0 for
    % parameters and phis).
    findall(T-def(Entry, 0), member(param(_, tmp(T)), Params), ParamDefs),
    findall(T-def(L, Pos),
            ( member(block(L, Phis, Insts, _), Blocks),
              (   member(phi(tmp(T), _, _), Phis), Pos = 0
              ;   nth1(Pos, Insts, Ins), inst_def(Ins, T)
              ) ),
            BlockDefs),
    append(ParamDefs, BlockDefs, DefPairs),
    list_to_assoc(DefPairs, Defs),
    list_to_assoc([], Empty),
    foldl(label_reach, Rpo, Empty, Reach),
    dom_intervals(cfg(Entry, Rpo, x, x), Idom, Intervals),
    % Collect the uses first: a goal that mentions the big assocs, run by
    % forall/2 once per block, copies them every time.
    findall(L-Phis-Insts-Jump,
            member(block(L, Phis, Insts, Jump), Blocks),
            Parts),
    include(block_reached(Reach), Parts, Reached),
    findall(U, ( member(B, Reached), block_use(B, U) ), Uses),
    include(use_reached(Reach), Uses, Checked),
    maplist(defined_at(Defs, Intervals), Checked).

block_reached(Reach, L-_-_-_) :-
    get_assoc(L, Reach, _).

use_reached(Reach, use(_, L, _)) :-
    get_assoc(L, Reach, _).

label_reach(L, Reach0, Reach) :-
    put_assoc(L, Reach0, t, Reach).

% block_use(+Block, -Use): Block, given as L-Phis-Insts-Jump, reads a
% temp as Use = use(T, L, At): T is read in block L at At, which is
% at(Pos) for position Pos, or end for the end of the block; a phi
% argument is read at the end of its predecessor.
block_use(_-Phis-_-_, use(T, P, end)) :-
    member(phi(_, _, Args), Phis),
    member(P-tmp(T), Args).
block_use(L-_-Insts-_, use(T, L, at(Pos))) :-
    nth1(Pos, Insts, Ins),
    inst_uses(Ins, Us),
    member(T, Us).
block_use(L-_-Insts-Jump, use(T, L, at(JumpPos))) :-
    jump_uses(Jump, Us),
    member(T, Us),
    length(Insts, N),
    JumpPos is N + 1.

% defined_at(+Defs, +Intervals, +Use): the temp of Use = use(T, L, At)
% is defined before At in block L, or in a block that dominates L.
defined_at(Defs, Intervals, use(T, L, At)) :-
    get_assoc(T, Defs, def(DefL, DefPos)),
    (   DefL == L
    ->  at_after(At, DefPos)
    ;   dominates_by_interval(Intervals, DefL, L)
    ).

% at_after(+At, +Pos): At (at(N) or end) is after position Pos.
at_after(end, _).
at_after(at(N), Pos) :-
    Pos < N.

%% Rewriting

% promote_roots(+Roots, +F0, +Cfg, +Idom, -Blocks): Blocks are the blocks
% of F0 with every slot of Roots promoted.
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
              B = block(L, _, _, _),
              slot_gen_kill(B, Addrs, GenKill) ),
            GenKillPairs),
    list_to_assoc(GenKillPairs, GenKill),
    empty_assoc(NoEdges),
    liveness(Cfg, GenKill, NoEdges, LiveIn, _),
    cfg_frontiers(Cfg, Idom, DF),
    Cfg = cfg(Entry, _, Succs, _),
    def_counts(F0, Counts),
    assoc_to_keys(Counts, Used),
    % Index the reachable stores once, rather than scanning all blocks
    % and instructions again for every slot.
    findall(Var-L,
            ( member(block(L, _, Insts, _), Blocks0),
              get_assoc(L, DF, _),
              member(store(_, _, tmp(X)), Insts),
              get_assoc(X, Addrs, Var) ),
            Stores0),
    keysort(Stores0, Stores1),
    group_pairs_by_key(Stores1, StorePairs),
    list_to_assoc(StorePairs, Stores),
    maplist(slot_phi_labels(Stores, DF, LiveIn, Entry), Vars, PhiLabels),
    phrase(slots_phis(Vars, PhiLabels), Phis),
    % The semicontext of phis_temps//3 is the last fresh temp number.
    phrase(phis_temps(Phis, Used, Placed0), [0], [_]),
    reverse(Placed0, Placed1),
    keysort(Placed1, Placed2),
    group_pairs_by_key(Placed2, Placed),      % Label -> [Var-Temp]
    list_to_assoc(Placed, PhiAt),
    findall(Var-const(0), member(Var, Vars), Zeros),
    list_to_assoc(Zeros, Zero),
    blocks_by_label(Blocks0, ByLabel),
    dom_children(Cfg, Idom, Kids),
    Env = env(Addrs, PhiAt, ByLabel, Kids, Succs),
    % Unreachable blocks never run; their slot reads see 0 so that they
    % stay valid, and they still give each successor's phis an argument.
    Cfg = cfg(_, Rpo, _, _),
    findall(L,
            ( member(block(L, _, _, _), Blocks0), \+ memberchk(L, Rpo) ),
            Dead),
    phrase(subtree_renamed(Entry, Zero, Env), Renamed, Unreached),
    phrase(blocks_renamed(Dead, Zero, Env), Unreached),
    maplist(renamed_block_args, Renamed, New, PhiArgss),
    append(PhiArgss, PhiArgs0),
    list_to_assoc(New, NewBlocks),
    keysort(PhiArgs0, PhiArgs1),
    group_pairs_by_key(PhiArgs1, PhiArgs),    % (Label-Var) -> [Pred-Value]
    list_to_assoc(PhiArgs, ArgsAt),
    maplist(promoted_block(NewBlocks, PhiAt, ArgsAt, Widths), Blocks0, Blocks).

slot_gen_kill(block(_, _, Insts, _), Addrs, Gen-Kill) :-
    foldl(slot_inst_gen_kill(Addrs), Insts, []-[], Gen-Kill).

slot_inst_gen_kill(Addrs, I, Gen0-Kill0, Gen-Kill) :-
    (   I = let(_, _, load(_), [tmp(X)]), get_assoc(X, Addrs, Var)
    ->  (   ord_memberchk(Var, Kill0)
        ->  Gen = Gen0
        ;   ord_add_element(Gen0, Var, Gen)
        ),
        Kill = Kill0
    ;   I = store(_, _, tmp(X)), get_assoc(X, Addrs, Var)
    ->  Gen = Gen0,
        ord_add_element(Kill0, Var, Kill)
    ;   Gen = Gen0,
        Kill = Kill0
    ).

% slot_phi_labels(+Stores, +DF, +LiveIn, +Entry, +Var, -Labels): Labels
% is the ordset of the labels where Var needs a phi: the iterated
% dominance frontier of the entry and the blocks that store to Var,
% keeping only blocks where Var is live on entry. Each placed phi counts
% as a store for the iteration. Unreachable stores are not in Stores:
% they never run.
slot_phi_labels(Stores, DF, LiveIn, Entry, Var, PhiLabels) :-
    (   get_assoc(Var, Stores, Labels0) -> true ; Labels0 = [] ),
    sort([Entry|Labels0], Labels),
    iterated_frontier(Labels, Var, DF, LiveIn, [], PhiLabels).

% iterated_frontier(+Work, +Var, +DF, +LiveIn, +Placed0, -Placed):
% Placed is Placed0 with the frontier labels where Var is live, of the
% labels in Work and, in turn, of each new one. Invariant: Placed0 is
% the ordset of those labels found so far, and each of them has had its
% frontier scanned or is still in Work.
iterated_frontier([], _, _, _, Placed, Placed).
iterated_frontier([L|Ls], Var, DF, LiveIn, Placed0, Placed) :-
    get_assoc(L, DF, Frontier),
    foldl(label_placed(Var, LiveIn), Frontier,
          Placed0-Ls, Placed1-Ls1),
    iterated_frontier(Ls1, Var, DF, LiveIn, Placed1, Placed).

% label_placed(+Var, +LiveIn, +Y, +Placed0-Work0, -Placed-Work):
% if Var is live on entry to Y and Y is not in Placed0, Y is in Placed
% and in front of Work0.
label_placed(Var, LiveIn, Y, Placed0-Work0, Placed-Work) :-
    (   \+ ord_memberchk(Y, Placed0),
        get_assoc(Y, LiveIn, In),
        ord_memberchk(Var, In)
    ->  ord_add_element(Placed0, Y, Placed),
        Work = [Y|Work0]
    ;   Placed = Placed0,
        Work = Work0
    ).

% slots_phis(+Vars, +Labelss)//: the phis L-Var for each Var of Vars,
% in order, and each L of its ordset of labels in Labelss.
slots_phis([], []) --> [].
slots_phis([Var|Vars], [Ls|Lss]) -->
    slot_phis(Ls, Var),
    slots_phis(Vars, Lss).

slot_phis([], _) --> [].
slot_phis([L|Ls], Var) -->
    [L-Var],
    slot_phis(Ls, Var).

% phis_temps(+Phis, +Used, -Placed)//: Placed is Phis with each L-Var
% as L-(Var-T), T a fresh temp. The semicontext is the number of the
% last fresh temp.
phis_temps([], _, []) --> [].
phis_temps([L-Var|Phis], Used, [L-(Var-T)|Placed]) -->
    state(N0, N),
    { unused_temp(Used, N0, T, N) },
    phis_temps(Phis, Used, Placed).

state(S0, S), [S] --> [S0].

% unused_temp(+Used, +N0, -T, -N): T is pr.N, the first such name after
% N0 that is not in Used.
unused_temp(Used, N0, T, N) :-
    N1 is N0 + 1,
    number_codes(N1, Ds),
    atom_codes(T0, [0'p, 0'r, 0'.|Ds]),
    (   ord_memberchk(T0, Used)
    ->  unused_temp(Used, N1, T, N)
    ;   T = T0,
        N = N1
    ).

blocks_by_label(Blocks, ByLabel) :-
    findall(L-B, ( member(B, Blocks), B = block(L, _, _, _) ), Pairs),
    list_to_assoc(Pairs, ByLabel).

% subtree_renamed(+L, +Cur0, +Env)//: the renamed blocks of the
% dominator subtree at L, Cur0 being the slots' values on entry to L.
% Env is env(Addrs, PhiAt, ByLabel, Kids, Succs).
subtree_renamed(L, Cur0, Env) -->
    { block_renamed(L, Cur0, Env, Cur, Renamed),
      Env = env(_, _, _, Kids, _),
      get_assoc(L, Kids, Ks) },
    [Renamed],
    kids_renamed(Ks, Cur, Env).

kids_renamed([], _, _) --> [].
kids_renamed([K|Ks], Cur, Env) -->
    subtree_renamed(K, Cur, Env),
    kids_renamed(Ks, Cur, Env).

% blocks_renamed(+Ls, +Cur0, +Env)//: the renamed blocks Ls, each with
% the slots' values Cur0 on entry.
blocks_renamed([], _, _) --> [].
blocks_renamed([L|Ls], Cur0, Env) -->
    { block_renamed(L, Cur0, Env, _, Renamed) },
    [Renamed],
    blocks_renamed(Ls, Cur0, Env).

% block_renamed(+L, +Cur0, +Env, -Cur, -Renamed): Renamed is
% renamed(L-Blk, Args): Blk is block L with its slot accesses rewritten,
% given the slots' values Cur0 on entry (Cur on exit), and Args the
% (Succ-Var)-(L-Value) arguments it gives its successors' slot phis.
block_renamed(L, Cur0, env(Addrs, PhiAt, ByLabel, _, Succs), Cur,
              renamed(L-block(L, Phis, Insts, Jump), Args)) :-
    get_assoc(L, ByLabel, block(L, Phis, Insts0, Jump)),
    (   get_assoc(L, PhiAt, VarTemps) -> true ; VarTemps = [] ),
    foldl(phi_cur, VarTemps, Cur0, Cur1),
    phrase(insts_renamed(Insts0, Addrs, Cur1, Cur), Insts),
    get_assoc(L, Succs, Ss),
    findall((S-Var)-(L-Val),
            ( member(S, Ss),
              get_assoc(S, PhiAt, SuccVarTemps),
              member(Var-_, SuccVarTemps),
              get_assoc(Var, Cur, Val) ),
            Args).

renamed_block_args(renamed(LBlk, Args), LBlk, Args).

phi_cur(Var-T, Cur0, Cur) :-
    put_assoc(Var, Cur0, tmp(T), Cur).

% insts_renamed(+Insts0, +Addrs, +Cur0, -Cur)//: the instructions
% Insts0 with their slot accesses rewritten, Cur0 and Cur being the
% slots' values before and after them.
insts_renamed([], _, Cur, Cur) --> [].
insts_renamed([I|Is], Addrs, Cur0, Cur) -->
    inst_renamed(I, Addrs, Cur0, Cur1),
    insts_renamed(Is, Addrs, Cur1, Cur).

% inst_renamed(+I, +Addrs, +Cur0, -Cur)//: the alloc and the derived
% addresses are no instructions, a load of a slot is an operation on
% its current value, a store to a slot is none and sets its value, and
% any other instruction is itself.
inst_renamed(I, Addrs, Cur0, Cur) -->
    (   { I = let(tmp(D), _, _, _), get_assoc(D, Addrs, _) }
    ->  { Cur = Cur0 }
    ;   { I = let(D, K, load(T), [tmp(X)]), get_assoc(X, Addrs, Var) }
    ->  { get_assoc(Var, Cur0, V),
          load_op(T, K, Op),
          Cur = Cur0 },
        [let(D, K, Op, [V])]
    ;   { I = store(_, V, tmp(X)), get_assoc(X, Addrs, Var) }
    ->  { put_assoc(Var, Cur0, V, Cur) }
    ;   { Cur = Cur0 },
        [I]
    ).

% What a load at class K of type T computes from the value last stored
% at its width (see the header).
load_op(l, _, copy).
load_op(p, _, copy).
load_op(sw, K, Op) :-
    class_word_load_op(K, sw, Op).
load_op(uw, K, Op) :-
    class_word_load_op(K, uw, Op).
load_op(sh, _, ext(sh)).
load_op(uh, _, ext(uh)).
load_op(sb, _, ext(sb)).
load_op(ub, _, ext(ub)).

% class_word_load_op(+K, +T, -Op): a load of the word type T at class K
% (w or l, as ir.pl requires) is Op of the stored word.
class_word_load_op(w, _, copy).
class_word_load_op(l, T, ext(T)).

% The class of a slot's phi, from the slot's width.
slot_class(l, l).
slot_class(p, p).
slot_class(w, w).
slot_class(h, w).
slot_class(b, w).

% promoted_block(+NewBlocks, +PhiAt, +ArgsAt, +Widths, +Block0, -Block):
% Block is the renamed Block0, with the slots' phis appended to its own.
promoted_block(NewBlocks, PhiAt, ArgsAt, Widths, block(L, _, _, _),
               block(L, Phis, Insts, Jump)) :-
    get_assoc(L, NewBlocks, block(L, Phis0, Insts, Jump)),
    (   get_assoc(L, PhiAt, VarTemps) -> true ; VarTemps = [] ),
    findall(phi(tmp(T), K, Args),
            ( member(Var-T, VarTemps),
              get_assoc(Var, Widths, Width),
              slot_class(Width, K),
              get_assoc(L-Var, ArgsAt, Args0),
              sort(Args0, Args) ),
            SlotPhis),
    append(Phis0, SlotPhis, Phis).
