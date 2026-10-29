/*  Promotion of memory slots to SSA temporaries, by promote_module/2
    and promote_func/3. Prior art: QBE's promote and ssa passes, LLVM's
    mem2reg.

    ## Which allocs

    A slot is one fixed offset and width, `acc(Off, Width)`, of an alloc
    that escape.pl calls local. An alloc is promoted, all its slots at
    once, when:

    - it is in any block, its every execution a fresh zeroed object:
      the alloc itself sets each slot to 0, and its block is a
      definition block for phi placement. Strict SSA makes every access
      go through the latest execution's address (an inlined callee's
      local, perf.md item 4, in a caller's loop is an alloc in a middle
      block);
    - its size is a constant and every slot lies inside it, so no access
      could trap or be undefined;
    - its slots do not overlap and each offset has one width, so every
      load reads exactly the bytes one earlier store wrote, except for
      punned reads: a `b` or `h` load, at an access never stored, inside
      a slot of width `h` or `w` (a union read through a narrower
      member, lz4's `LZ4_isLittleEndian`). It reads the slot's value
      shifted right by 8 times its byte offset (little-endian), then
      extended as any narrow load. `l` and `p` slots are never punned;
    - in filc mode, its `p` slots are 8-aligned (allocs are 16-aligned),
      so no `load(p)` or `store(p, V, A)` could trap as misaligned.

    The function must also be in strict SSA form: each temp defined
    once, every definition dominating its uses. Otherwise a stored temp
    could be redefined before the load that promote would turn into its
    copy. A function that is not, or that calls setjmp, is left alone.

    ## The rewrite

    Loads become copies or extensions of the slot's current value, and
    stores disappear. Phis are placed on the iterated dominance frontier
    of the entry and the reachable blocks that store to the slot or hold
    its alloc, where the slot is live (pruned SSA, Cytron et al.); their
    temps are named `pr.N`. After its alloc and before any store a slot
    holds 0: Fil-C allocations are zeroed, and in plain mode the bytes
    are unknown, so 0 is one of the values they could have. Unreachable
    blocks read 0 too.

    Values keep the class of the store: a `store(b, V, A)` of a `w`
    value keeps the whole value, and each load narrows or extends it
    again, exactly as the bytes would.

    | A load of | Becomes, on the slot's value |
    |---|---|
    | `l` or `p` | `copy` |
    | `sw` or `uw`, at class `w` | `copy` |
    | `sw` or `uw`, at class `l` | `ext(sw)` or `ext(uw)` |
    | `sh`, `uh`, `sb` or `ub` | the extension of that type, such as `ext(sb)` |

    A slot's phi has class `w` for widths `b`, `h` and `w`, and the
    slot's width, `l` or `p`, otherwise.
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
:- use_module(provenance).

%! promote_module(+M0, -M) is det.
%
%  M is the module M0 with the promotable allocs of each function
%  promoted.

promote_module(M0, module(Items)) :-
    legacy_context(M0, module(Items0)),
    module_mode(module(Items0), Mode),
    code_items(Items0, Code),
    context_index(Items0, Contexts),
    maplist(promote_item(Mode, Contexts), Code, Groups), append(Groups, Items).

% promote_item(+Mode, +Item0, -Item): Item is the module item Item0,
% promoted if it is a function.
% The cut: the item's clause is not indexed (Mode comes first), and a
% choicepoint per function would pin the module's trail until the pass ends.
promote_item(Mode, All, F0, Items) :-
    F0 = func(Name, _, _, _, _), !,
    context_records(All, Name, Rs0),
    promote_context(Mode, F0, Rs0, F, Rs), with_context(F, Rs, Items).
promote_item(_, _, data(N, L, A, Is), [data(N, L, A, Is)]).
promote_item(_, _, alias(N, L, T), [alias(N, L, T)]).

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

promote_func(Mode, F0, F) :- promote_context(Mode, F0, [], F, _).

promote_context(_, F, Rs, F, Rs) :- setjmp_func(F), !.
promote_context(Mode, F0, Rs0, F, Rs) :-
    F0 = func(Name, Linkage, Ret, Params, Blocks0),
    % Most functions have nothing to promote: look before building the
    % dominator tree.
    (   promotable(Mode, F0, Roots),
        Roots \== [],
        func_cfg(Blocks0, Cfg),
        cfg_idoms(Cfg, Idom),
        strict_ssa(F0, Cfg, Idom)
    ->  promote_roots(Roots, F0, Cfg, Idom, Blocks, Map, Placed, Addrs, Widths),
        F = func(Name, Linkage, Ret, Params, Blocks),
        remap_sites(Rs0, Map, Rs1),
        promoted_context(Rs0, Rs1, Blocks0, Placed, Addrs, Widths, Rs)
    ;   F = F0, Rs = Rs0
    ).

promoted_context([], Rs, _, _, _, _, Rs) :- !.
promoted_context(Before, Rs0, Bs, Placed, Addrs, Widths, Rs) :-
    site_index(Before, Sites), origin_ids(Before, Ids0),
    findall(T, member(_-(_-T), Placed), Temps),
    retire_values(Rs0, Temps, Ids0, Ids1, Kept),
    findall(A-Os, member(value(A, _, Os), Before), VPairs), list_to_assoc(VPairs, Values),
    findall(A-Ty, member(binding(A, _, Ty, _), Before), BPairs), list_to_assoc(BPairs, Bindings),
    findall(Slot-Os,
            ( member(block(L, _, Is, _), Bs), nth0(I, Is, store(_, _, tmp(X))),
              get_assoc(X, Addrs, Slot), site_origins(Sites, inst(L, I), Os) ), StorePairs),
    keysort(StorePairs, Sorted), group_pairs_by_key(Sorted, Groups),
    maplist(slot_parents, Groups, ParentPairs), list_to_assoc(ParentPairs, Stores),
    findall(Slot, member(_-(Slot-_), Placed), Slots0), sort(Slots0, Slots),
    slot_records(Slots, Values, Stores, Ids1, Ids2, SummaryPairs, Summaries),
    list_to_assoc(SummaryPairs, SummaryIds),
    phi_records(Placed, Bindings, Widths, SummaryIds, Ids2, _, Phis),
    append([Kept, Summaries, Phis], Rs).

slot_parents(Slot-Lists, Slot-Parents) :- append(Lists, Os), sort(Os, Parents).

% A single shared summary per slot avoids repeating all stores for every
% phi. These are conservative contributors, not reaching-definition facts.
slot_records([], _, _, Ids, Ids, [], []).
slot_records([A-Off|Slots], Values, Stores, Ids0, Ids, [A-Off-Summary|Pairs],
             [origin(Initial, none, generated(promote, initial_zero), AllocOs),
              origin(Summary, none, generated(promote, slot_stores(A, Off)), [Initial|Parents])|Rs]) :-
    ( get_assoc(A, Values, AllocOs) -> true ; AllocOs = [] ),
    ( get_assoc(A-Off, Stores, Parents) -> true ; Parents = [] ),
    fresh_origin(initial(A, Off), Ids0, Ids1, Initial),
    fresh_origin(stores(A, Off), Ids1, Ids2, Summary),
    slot_records(Slots, Values, Stores, Ids2, Ids, Pairs, Rs).

phi_records([], _, _, _, Ids, Ids, []).
phi_records([_-((A-Off)-T)|Placed], Bindings, Widths, Summaries, Ids0, Ids,
            [origin(Id, none, generated(promote, slot(A, Off, Width)), [Summary]),
             value(T, Hint, [Id]), site(phi(T), [Id])|Rs]) :-
    get_assoc(A-Off, Widths, Width), get_assoc(A-Off, Summaries, Summary),
    ( Off =:= 0, get_assoc(A, Bindings, Type), type_slot(Type, Width)
    -> Hint = named(A, value) ; Hint = none ),
    fresh_origin(promote(T), Ids0, Ids1, Id),
    phi_records(Placed, Bindings, Widths, Summaries, Ids1, Ids, Rs).

% Only a scalar whole-object slot inherits its declaration's name.
type_slot(qualified(_, T), W) :- !, type_slot(T, W).
type_slot(T, W) :- memberchk(T-W, [char-b, schar-b, uchar-b, bool-b,
    short-h, ushort-h, int-w, uint-w, long-l, ulong-l, llong-l, ullong-l]).
type_slot(ptr(_), p).

%! promotable(+Mode, +F, -Roots) is det.
%
%  Roots is [A-Slots] for the allocs A of F that can be promoted, in
%  order, Slots an ordset of acc(Off, Width).

promotable(_, F, []) :- setjmp_func(F), !.
% Without an alloc, skip escape analysis.
promotable(_, func(_, _, _, _, Blocks), []) :-
    \+ ( member(block(_, _, Insts, _), Blocks),
         memberchk(let(_, _, alloc(_), _), Insts) ), !.
promotable(Mode, F, Roots) :-
    alloc_classes(F, Classes),
    stored_accs(F, Stored),
    findall(A-Slots,
            ( member(A-local(const(Size), Accs), Classes),
              ( get_assoc(A, Stored, Ws) -> true ; Ws = [] ),
              punned_slots(Accs, Ws, Slots),
              slots_ok(Mode, Size, Slots) ),
            Roots).

% stored_accs(+F, -Stored): Stored maps each alloc to the accesses that
% store to it.
stored_accs(F, Stored) :-
    F = func(_, _, _, _, Blocks),
    address_temps(F, Addrs),
    findall(A-acc(Off, W),
            ( member(block(_, _, Is, _), Blocks), member(store(W, _, tmp(X)), Is),
              get_assoc(X, Addrs, A-Off) ),
            Ps0),
    keysort(Ps0, Ps1), group_pairs_by_key(Ps1, Ps),
    list_to_assoc(Ps, Stored).

% punned_slots(+Accs, +Stored, -Slots): Slots are the accesses of Accs
% that no other one contains. Each other access is a punned read: a
% load of b or h, never stored, inside a slot of width h or w (a union
% read through a narrower member; its bytes are a shift and an
% extension of the slot's value, little-endian). Fails otherwise.
punned_slots(Accs, Stored, Slots) :-
    partition(inner_acc(Accs), Accs, Inner, Slots),
    forall(member(Acc, Inner), punned_read(Acc, Slots, Stored)).

inner_acc(Accs, Acc) :- member(Outer, Accs), Outer \== Acc, acc_inside(Acc, Outer), !.

acc_inside(acc(O, W), acc(SO, SW)) :-
    width_bytes(W, B), width_bytes(SW, SB),
    SO =< O, O + B =< SO + SB.

punned_read(acc(O, W), Slots, Stored) :-
    memberchk(W, [b, h]),
    \+ memberchk(acc(O, W), Stored),
    member(acc(SO, SW), Slots), acc_inside(acc(O, W), acc(SO, SW)), !,
    memberchk(SW, [h, w]).

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
    findall(L-t, member(L, Rpo), ReachPairs), list_to_assoc(ReachPairs, Reach),
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
promote_roots(Roots, F0, Cfg, Idom, Blocks, Map, Placed0, Addrs, Widths) :-
    F0 = func(_, _, _, _, Blocks0),
    address_temps(F0, AllAddrs),
    % Only addresses of promoted allocs matter from here on.
    % A punned read's address names its slot; Shifts holds its byte
    % offset in the slot when that is not 0.
    findall(X-(A-SOff)-Shift,
            ( gen_assoc(X, AllAddrs, A-Off), memberchk(A-Slots, Roots),
              (   member(acc(SOff, SW), Slots), width_bytes(SW, SB),
                  SOff =< Off, Off < SOff + SB
              ->  Shift is Off - SOff
              ;   SOff = Off, Shift = 0
              ) ),
            AddrShifts),
    findall(X-Var, member(X-Var-_, AddrShifts), AddrPairs),
    list_to_assoc(AddrPairs, Addrs),
    findall(X-Shift, ( member(X-_-Shift, AddrShifts), Shift =\= 0 ), ShiftPairs),
    list_to_assoc(ShiftPairs, Shifts),
    % A slot (Var) is A-Off; Widths maps it to its access width.
    findall((A-Off)-Width,
            ( member(A-Accs, Roots), member(acc(Off, Width), Accs) ),
            VarWidths),
    list_to_assoc(VarWidths, Widths),
    pairs_keys(VarWidths, Vars),
    % Liveness of slots: a load reads one, a store writes it.
    % An alloc writes 0 to each of its slots.
    findall(A-AVars, ( member(A-Accs, Roots), alloc_vars(A, Accs, AVars) ), AllocVarPairs),
    list_to_assoc(AllocVarPairs, AllocVars),
    findall(L-GenKill,
            ( member(B, Blocks0),
              B = block(L, _, _, _),
              slot_gen_kill(B, Addrs, AllocVars, GenKill) ),
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
              (   member(store(_, _, tmp(X)), Insts),
                  get_assoc(X, Addrs, Var)
              ;   member(let(tmp(A), _, alloc(_), _), Insts),
                  get_assoc(A, AllocVars, AVs), member(Var, AVs) ) ),
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
    Env = env(Addrs-AllocVars-Shifts, PhiAt, ByLabel, Kids, Succs),
    % Unreachable blocks never run; their slot reads see 0 so that they
    % stay valid, and they still give each successor's phis an argument.
    Cfg = cfg(_, Rpo, _, _),
    findall(L,
            ( member(block(L, _, _, _), Blocks0), \+ memberchk(L, Rpo) ),
            Dead),
    phrase(subtree_renamed(Entry, Zero, Env), Renamed, Unreached),
    phrase(blocks_renamed(Dead, Zero, Env), Unreached),
    maplist(renamed_block_args, Renamed, New, PhiArgss, Maps),
    append(Maps, Map),
    append(PhiArgss, PhiArgs0),
    list_to_assoc(New, NewBlocks),
    keysort(PhiArgs0, PhiArgs1),
    group_pairs_by_key(PhiArgs1, PhiArgs),    % (Label-Var) -> [Pred-Value]
    list_to_assoc(PhiArgs, ArgsAt),
    maplist(promoted_block(NewBlocks, PhiAt, ArgsAt, Widths), Blocks0, Blocks).

alloc_vars(A, Accs, Vars) :- findall(A-Off, member(acc(Off, _), Accs), Vars).

slot_gen_kill(block(_, _, Insts, _), Addrs, AllocVars, Gen-Kill) :-
    foldl(slot_inst_gen_kill(Addrs, AllocVars), Insts, []-[], Gen-Kill).

slot_inst_gen_kill(Addrs, AllocVars, I, Gen0-Kill0, Gen-Kill) :-
    (   I = let(tmp(A), _, alloc(_), _), get_assoc(A, AllocVars, AVs)
    ->  Gen = Gen0,
        list_to_ord_set(AVs, AVSet), ord_union(Kill0, AVSet, Kill)
    ;   I = let(_, _, load(_), [tmp(X)]), get_assoc(X, Addrs, Var)
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
              renamed(L-block(L, Phis, Insts, Jump), Args, Map)) :-
    get_assoc(L, ByLabel, block(L, Phis, Insts0, Jump)),
    (   get_assoc(L, PhiAt, VarTemps) -> true ; VarTemps = [] ),
    foldl(phi_cur, VarTemps, Cur0, Cur1),
    phrase(insts_renamed(Insts0, Addrs, Cur1, Cur, L, 0, 0, Map), Insts),
    get_assoc(L, Succs, Ss),
    findall((S-Var)-(L-Val),
            ( member(S, Ss),
              get_assoc(S, PhiAt, SuccVarTemps),
              member(Var-_, SuccVarTemps),
              get_assoc(Var, Cur, Val) ),
            Args).

renamed_block_args(renamed(LBlk, Args, Map), LBlk, Args, Map).

phi_cur(Var-T, Cur0, Cur) :-
    put_assoc(Var, Cur0, tmp(T), Cur).

% insts_renamed(+Insts0, +Addrs, +Cur0, -Cur)//: the instructions
% Insts0 with their slot accesses rewritten, Cur0 and Cur being the
% slots' values before and after them.
insts_renamed([], _, Cur, Cur, _, _, _, []) --> [].
insts_renamed([I|Is], Addrs, Cur0, Cur, L, Old, New, Map) -->
    { phrase(inst_renamed(I, Addrs, Cur0, Cur1), Out),
      emission_sites(L, Old, New, Out, Map, Rest, Next), Old1 is Old + 1 },
    inst_list(Out),
    insts_renamed(Is, Addrs, Cur1, Cur, L, Old1, Next, Rest).

inst_list([]) --> [].
inst_list([I|Is]) --> [I], inst_list(Is).

% inst_renamed(+I, +Addrs, +Cur0, -Cur)//: the alloc and the derived
% addresses are no instructions, a load of a slot is an operation on
% its current value, a store to a slot is none and sets its value, and
% any other instruction is itself.
inst_renamed(I, Addrs-AllocVars-Shifts, Cur0, Cur) -->
    (   { I = let(tmp(A), _, alloc(_), _), get_assoc(A, AllocVars, AVs) }
    ->  { foldl(slot_zero, AVs, Cur0, Cur) }
    ;   { I = let(tmp(D), _, _, _), get_assoc(D, Addrs, _) }
    ->  { Cur = Cur0 }
    ;   { I = let(D, K, load(T), [tmp(X)]), get_assoc(X, Addrs, Var),
          get_assoc(X, Shifts, Shift) }
    ->  % A punned read of the slot's bytes at Shift: the value shifted
        % right by 8*Shift, then extended as any narrow load (punned_slots/3).
        { get_assoc(Var, Cur0, V),
          load_op(T, K, Op),
          D = tmp(N), atom_concat('pun.', N, P), Bits is 8*Shift,
          Cur = Cur0 },
        [let(tmp(P), w, shr, [V, const(Bits)]), let(D, K, Op, [tmp(P)])]
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

slot_zero(Var, Cur0, Cur) :- put_assoc(Var, Cur0, const(0), Cur).

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
