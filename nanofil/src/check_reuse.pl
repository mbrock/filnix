/*  Check reuse: a heap access check's proof covers later scalar accesses
    through the same pointer or a related one, in its block and along CFG
    edges (docs/m7.md).

    Pizlonation states one check per access, right before it. This pass
    deletes a check when an earlier proof already
    establishes what it would: the same pointer operand, or one related
    to it (both constant offsets, by single-definition flights with the
    same lower donor, from one root; round 3), at least its range, shifted
    by their distance, and rights, and nothing in between that could free the object
    or redefine either temporary. The covered access then reads the
    earlier proof. Nothing is moved, widened or added, so every
    remaining check fails exactly where it failed before.

    ## Facts

    | Fact | Means |
    |---|---|
    | `avail(P, Q, Lo, Hi, Rights, Align)` | `tmp(Q)` is a proof of P that P+[Lo, Hi) allows Rights at alignment Align |

    Blocks are walked once, in order. A block's entry facts are those
    every incoming edge carries: a plain edge from a block already walked
    carries its exit facts, a poll edge or an edge from a later block
    none. Only facts whose proof has one definition and whose pointer has
    at most one cross an edge, and a phi kills the facts naming its
    destination. A kept heap check adds its fact once its
    first access has run. An instruction that is `transparent/1` keeps
    the facts that do not mention the temporary it defines; any other
    instruction (a call, allocation, getter, pointer access, setjmp,
    va_arg, ...) removes them all.

    The pass is selected with `--checks=reuse`; the reference path keeps
    every check. ir.pl's validator accepts the result by its own rule,
    and `reuse_refines/2` checks that the only change is deleted checks
    whose access now reads a proof of the same or a related operand, at
    an offset changed by exactly their distance.
*/
:- module(check_reuse, [reuse_checks/2, reuse_refines/2, renew_checks/2, renew_refines/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir, [op_kind/2, pointer_memory_effects/2, temp_defs/3]).
:- use_module(cfg, [inst_def/2, inst_uses/2, func_cfg/2, cfg_idoms/2, dominates/3]).
:- use_module(provenance, [code_items/2, context_records/3, context_index/2, with_context/3,
                           remap_sites/3]).

%! reuse_checks(+M0, -M) is det.
%
%  M is the checked module M0 with each heap check that an available
%  proof covers deleted, and its access reading that proof. Context
%  sites follow the instructions; `alias(Q, tmp(Q1), none, Os)` records
%  that the access of the deleted proof Q reads Q1.

reuse_checks(module(Items0), module(Items)) :-
    code_items(Items0, Code),
    context_index(Items0, Contexts),
    maplist(reused_item(Contexts), Code, Groups), append(Groups, Items).

reused_item(All, func(N, L, R, Ps, Bs0), Items) :- !,
    names_info(Ps, Bs0, Info),
    incoming(Bs0, Incoming), empty_assoc(Exits0),
    reused_blocks(Bs0, Info, Incoming, Exits0, Bs, Map, Reused),
    context_records(All, N, Rs0),
    (   Rs0 == [] -> Rs = []
    ;   remap_sites(Rs0, Map, Rs1),
        % A proof read at another distance is not Q's equal: no alias.
        findall(alias(Q, tmp(Q1), none, Os),
                ( member(Q-Q1-0, Reused),
                  ( memberchk(value(Q, _, Os), Rs0) -> true ; Os = [] ) ),
                Aliases),
        append(Rs1, Aliases, Rs)
    ),
    with_context(func(N, L, R, Ps, Bs), Rs, Items).
reused_item(_, Item, [Item]).

% Blocks in order. Entry facts are those every incoming edge carries
% (exit facts on a plain edge from a block already walked; none on a
% poll edge or from a later block), kept only when the proof and its
% pointer are defined once in the function, less those a phi redefines.
reused_blocks([], _, _, _, [], [], []).
reused_blocks([block(L, Phis, Insts0, J)|Bs0], Info, Incoming, Exits0,
              [block(L, Phis, Insts, J)|Bs], Map, Reused) :-
    (   get_assoc(L, Incoming, Edges) -> true ; Edges = [] ),
    maplist(carried(Exits0), Edges, Sets),
    common(Sets, Facts0),
    include(single_names(Info), Facts0, Facts1),
    foldl(phi_kills, Phis, Facts1, Facts),
    facts_state(Info, Facts, St),
    reused_insts(Insts0, Info, St, L-0-0, Insts, Map0, Reused0, st(Exit, _, _)),
    put_assoc(L, Exits0, Exit, Exits),
    reused_blocks(Bs0, Info, Incoming, Exits, Bs, Map1, Reused1),
    append(Map0, Map1, Map), append(Reused0, Reused1, Reused).

incoming(Blocks, Incoming) :-
    findall(L-(From-Polled),
            ( member(block(From, _, _, Jump), Blocks),
              target(Jump, T),
              ( T = poll(L) -> Polled = yes ; L = T, Polled = no ) ),
            Pairs),
    empty_assoc(I0),
    foldl(add_incoming, Pairs, I0, Incoming).

target(goto(T), T).
target(branch(_, T, _), T).
target(branch(_, _, T), T).

add_incoming(L-E, I0, I) :-
    (   get_assoc(L, I0, Es) -> true ; Es = [] ),
    put_assoc(L, I0, [E|Es], I).

carried(_, _-yes, []) :- !.
carried(Exits, From-no, Facts) :-
    (   get_assoc(From, Exits, Facts) -> true ; Facts = [] ).

common([], []).
common([S|Ss], Facts) :- maplist(sort, Ss, Os), include(everywhere(Os), S, Facts).
everywhere(Os, F) :- forall(member(O, Os), ord_memberchk(F, O)).

/* Within a block the facts are st(Facts, Names, ByRoot): Facts newest
   first, as before; Names every name a fact mentions (perhaps more);
   ByRoot the facts of each root (base_of/4), newest first, each with its
   pointer's offset from the root, K-avail(...). The candidates for a
   check are exactly ByRoot's list for its pointer's root, in Facts'
   order, and a definition scans Facts only when Names has its name: a
   long block costs no more per check than its facts of one root. */
facts_state(Info, Facts, st(Facts, Names, ByRoot)) :-
    empty_assoc(E),
    foldl(avail_names, Facts, E, Names),
    findall(R-(K-F), ( member(F, Facts), F = avail(P, _, _, _, _, _),
                       base_of(Info, P, R, K) ), Pairs0),
    keysort(Pairs0, Pairs),
    group_pairs_by_key(Pairs, Groups),
    list_to_assoc(Groups, ByRoot).

avail_names(avail(P, Q, _, _, _, _), N0, N) :-
    put_assoc(Q, N0, true, N1),
    ( P = tmp(X) -> put_assoc(X, N1, true, N) ; N = N1 ).

state_add(Info, F, st(Fs, Ns0, B0), st([F|Fs], Ns, B)) :-
    avail_names(F, Ns0, Ns),
    F = avail(P, _, _, _, _, _),
    base_of(Info, P, R, K),
    ( get_assoc(R, B0, L) -> true ; L = [] ),
    put_assoc(R, B0, [K-F|L], B).

state_kill(Info, D, St0, St) :-
    St0 = st(Fs0, Ns, _),
    (   get_assoc(D, Ns, _)
    ->  exclude(mentions(D), Fs0, Fs), facts_state(Info, Fs, St)
    ;   St = St0
    ).

state_none(Info, St) :- facts_state(Info, [], St).

phi_kills(phi(tmp(D), _, _), Facts0, Facts) :-
    exclude(mentions(D), Facts0, Facts).

% names_info(+Params, +Blocks, -Info): Info is info(Defs, Uses), each
% temporary's number of definitions (parameters, phis and every
% instruction form) and of instructions reading it.
names_info(Params, Blocks, info(Defs, Uses, Bases)) :-
    temp_defs(Params, Blocks, DefList),
    findall(N, member(N-_, DefList), Ns), counts(Ns, Defs),
    findall(Q, ( member(block(_, _, Insts, _), Blocks), member(I, Insts),
                 inst_uses(I, Us), member(Q, Us) ), Qs),
    counts(Qs, Uses),
    findall(X-(B-K),
            ( member(block(_, _, Insts, _), Blocks), member(I, Insts),
              flight_offset(I, X, B, K),
              count(Defs, X, 1), B = tmp(BN), count(Defs, BN, 1) ),
            BasePairs),
    list_to_assoc(BasePairs, Bases).

flight_offset(flight(tmp(X), add, [address(B), const(K)], lower(B1)), X, B, K) :- B == B1.
flight_offset(flight(tmp(X), sub, [address(B), const(K0)], lower(B1)), X, B, K) :- B == B1, K is -K0.
flight_offset(flight(tmp(X), copy, [address(B)], lower(B1)), X, B, 0) :- B == B1.

% base_of(+Info, +P, -R, -K): P's address is R's plus K, with R's
% capability, by single-definition flights; R = P and K = 0 if P is no
% such flight or its chain has a cycle (possible in unreachable blocks).
base_of(Info, P, R, K) :-
    (   base_walk(Info, P, [], R0, K0) -> R = R0, K = K0 ; R = P, K = 0 ).

base_walk(info(_, _, Bases), tmp(N), Seen, R, K) :- get_assoc(N, Bases, B-K0), !,
    \+ memberchk(N, Seen),
    base_walk(info(_, _, Bases), B, [N|Seen], R, K1), K is K0 + K1.
base_walk(_, P, _, P, 0).

% related(+Info, +P, +P1, -D): P's address is P1's plus D, same capability.
related(_, P, P1, 0) :- P == P1, !.
related(Info, P, P1, D) :-
    % Roots are singly defined: names_info/3 records only flights from
    % singly defined bases.
    base_of(Info, P, R, K), base_of(Info, P1, R1, K1), R == R1,
    D is K - K1.

counts(Xs, Assoc) :-
    msort(Xs, Sorted), clumped_pairs(Sorted, Pairs), list_to_assoc(Pairs, Assoc).

clumped_pairs([], []).
clumped_pairs([X|Xs], [X-N|Ps]) :- same_run(X, Xs, 1, N, Rest), clumped_pairs(Rest, Ps).
same_run(X, [Y|Ys], N0, N, Rest) :- X == Y, !, N1 is N0 + 1, same_run(X, Ys, N1, N, Rest).
same_run(_, Rest, N, N, Rest).

count(Assoc, N, C) :- ( get_assoc(N, Assoc, C0) -> C = C0 ; C = 0 ).

% A fact crosses an edge only when its proof has one definition and its
% pointer at most one (the emitter reloads the pointer there).
single_names(info(Defs, _, _), avail(P, Q, _, _, _, _)) :-
    count(Defs, Q, 1),
    (   P = tmp(N) -> count(Defs, N, C), C =< 1 ; true ).

% single_proof(+Info, +Q): the proof tmp(Q) has one definition and one
% reader, the access that follows its check.
single_proof(info(Defs, Uses, _), Q) :- count(Defs, Q, 1), count(Uses, Q, 1).

% reused_insts(+Insts0, +Facts, +L-Old-New, -Insts, -Map, -Reused): Old
% and New index the next instruction of block L before and after; Map
% pairs their sites, and Reused pairs each deleted proof with its
% replacement.
reused_insts([], _, Facts, _, [], [], [], Facts).
reused_insts([let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts0],
             Info, Facts, L-Old-New, Insts, Map, Reused, Exit) :-
    scalar_access(Access0, Q), !,
    Old1 is Old + 1, Old2 is Old + 2,
    base_of(Info, P, R, K),
    Facts = st(_, _, ByRoot),
    (   get_assoc(R, ByRoot, Cands),
        member(K1-avail(_, Q1, Lo1, Hi1, Rights1, Align1), Cands),
        D is K - K1,
        LoD is Lo + D, HiD is Hi + D,
        subsumes(Lo1, Hi1, Rights1, Align1, LoD, HiD, Rights, Align),
        single_proof(Info, Q)
    ->  renamed_access(Access0, Q1, D, Access), Insts = [Access|Insts1],
        Map = [inst(L, Old1)-inst(L, New)|Map1], New2 is New + 1,
        Reused = [Q-Q1-D|Reused1], Facts1 = Facts
    ;   Insts = [let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts1],
        New1 is New + 1, New2 is New + 2,
        Map = [inst(L, Old)-inst(L, New), inst(L, Old1)-inst(L, New1)|Map1],
        state_kill(Info, Q, Facts, Facts0),
        Reused = Reused1, state_add(Info, avail(P, Q, Lo, Hi, Rights, Align), Facts0, Facts1)
    ),
    after_def(Info, Access0, Facts1, Facts2),
    reused_insts(Insts0, Info, Facts2, L-Old2-New2, Insts1, Map1, Reused1, Exit).
reused_insts([Inst|Insts0], Info, Facts0, L-Old-New, [Inst|Insts],
             [inst(L, Old)-inst(L, New)|Map], Reused, Exit) :-
    (   transparent(Inst) -> after_def(Info, Inst, Facts0, Facts) ; state_none(Info, Facts) ),
    Old1 is Old + 1, New1 is New + 1,
    reused_insts(Insts0, Info, Facts, L-Old1-New1, Insts, Map, Reused, Exit).

%! reuse_refines(+M0, +M) is semidet.
%
%  M is M0 except for deleted heap checks, each of whose single access
%  now reads an earlier proof of the same operand. This is
%  identity, not safety: that the earlier proof still covers the access
%  is ir.pl's rule, which valid_module/1 checks separately.

reuse_refines(module(Items0), module(Items)) :-
    code_items(Items0, Code0), code_items(Items, Code),
    maplist(item_refines, Code0, Code).

item_refines(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    names_info(Ps, Bs0, Info),
    findall(Q-checked(P, check(Lo, Hi, Rs, Al)),
            ( member(block(_, _, Is, _), Bs0),
              member(let(tmp(Q), a, check(Lo, Hi, Rs, Al), [P]), Is),
              single_names(Info, avail(P, Q, Lo, Hi, Rs, Al)) ),
            Global),
    maplist(block_refines(Info, Global), Bs0, Bs).
item_refines(Item, Item).

block_refines(Info, Global, block(L, Phis, Insts0, J), block(L, Phis, Insts, J)) :-
    insts_refine(Insts0, Insts, r(Info, Global, [])).

% insts_refine(+Insts0, +Insts, +r(Info, Global, Proofs)): Proofs are
% Q-checked(P, Check) for the heap checks seen so far in the block,
% newest first; Global the same for every heap check in the function
% whose proof has one definition and its pointer at most one. A deleted
% check's proof had one definition and one reader, and the proof that
% replaces it checks the same operand and subsumes the deleted check.
% Whether it is available there is the validator's question.
insts_refine([], [], _).
insts_refine([Inst|Insts0], [Inst|Insts], r(Info, Global, Proofs)) :- !,
    (   Inst = let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P])
    ->  Proofs1 = [Q-checked(P, check(Lo, Hi, Rights, Align))|Proofs]
    ;   Proofs1 = Proofs
    ),
    insts_refine(Insts0, Insts, r(Info, Global, Proofs1)).
insts_refine([let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), Access0|Insts0],
             [Access|Insts], r(Info, Global, Proofs)) :-
    scalar_access(Access0, Q),
    renamed_access(Access0, Q1, D, Access),
    (   memberchk(Q1-Checked, Proofs) -> true ; memberchk(Q1-Checked, Global) ),
    Checked = checked(P1, check(Lo1, Hi1, Rights1, Align1)), related(Info, P, P1, D),
    LoD is Lo + D, HiD is Hi + D,
    subsumes(Lo1, Hi1, Rights1, Align1, LoD, HiD, Rights, Align),
    single_proof(Info, Q),
    insts_refine(Insts0, Insts, r(Info, Global, Proofs)).

% scalar_access(+Access, +Q): Access is a scalar raw access at tmp(Q).
scalar_access(let(_, _, raw_load(T, _), [tmp(Q)]), Q) :- T \== p.
scalar_access(raw_store(W, _, _, tmp(Q)), Q) :- W \== p.

renamed_access(let(R, K, raw_load(T, Off0), [_]), Q, D, let(R, K, raw_load(T, Off), [tmp(Q)])) :-
    ( var(D) -> D is Off - Off0 ; Off is Off0 + D ).
renamed_access(raw_store(W, Off0, V, _), Q, D, raw_store(W, Off, V, tmp(Q))) :-
    ( var(D) -> D is Off - Off0 ; Off is Off0 + D ).

% subsumes(+Lo1, +Hi1, +Rights1, +Align1, +Lo, +Hi, +Rights, +Align): a
% check of [Lo1, Hi1) with Rights1 at Align1 that succeeded implies that
% the check of [Lo, Hi) with Rights at Align, of the same pointer and
% object state, would succeed. Comparing with the deleted check, not just
% its access, keeps a wider or stronger check's trap.
subsumes(Lo1, Hi1, Rights1, Align1, Lo, Hi, Rights, Align) :-
    Lo1 =< Lo, Hi =< Hi1,
    rights_include(Rights1, Rights),
    Align1 mod Align =:= 0, (Lo - Lo1) mod Align =:= 0.

rights_include(write, _).
rights_include(read, read).

% after_def(+Info, +Inst, +Facts0, -Facts): Facts are those of Facts0 that do
% not mention the temporary Inst defines.
after_def(Info, Inst, Facts0, Facts) :-
    (   inst_def(Inst, D)
    ->  state_kill(Info, D, Facts0, Facts)
    ;   Facts = Facts0
    ).

mentions(D, avail(P, Q, _, _, _, _)) :- ( Q == D ; P == tmp(D) ).

% transparent(+Inst): Inst cannot free, reallocate or relabel an object,
% and reaches no safepoint: arithmetic, comparisons, conversions, pure
% pointer construction, checks, scalar raw accesses and raw pointer loads
% (which read aux and box words, calling no helper).
transparent(loc(_, _)).
transparent(flight(_, _, _, _)).
transparent(raw_store(W, _, _, _)) :- W \== p.
transparent(let(_, p, raw_load_pointer(_, Es), _)) :-
    ( pointer_memory_effects(load, Es) ; pointer_memory_effects(local_load, Es) ), !.
transparent(let(_, _, Op, Args)) :-
    op_kind(Op, Kind),
    transparent_kind(Kind, Args).

transparent_kind(additive, _).
transparent_kind(alu, _).
transparent_kind(shift, _).
transparent_kind(neg, _).
transparent_kind(cmp, _).
transparent_kind(ext, _).
transparent_kind(float_convert, _).
transparent_kind(float_to_int, _).
transparent_kind(int_to_float, _).
transparent_kind(cast, _).
transparent_kind(ptoi, _).
transparent_kind(check, _).
transparent_kind(ld, _).
transparent_kind(check_local, _).
transparent_kind(copy, Args) :- \+ memberchk(global(_), Args).

%! renew_checks(+M0, -M) is det.
%
%  M is the checked module M0 with each heap check replaced by a renew
%  (docs/m7.md, round 4) when an earlier heap check of a pointer related
%  to it at distance 0 dominates it and covers its bounds and alignment,
%  rights aside, and both that check's proof and pointer have one
%  definition. The renew reads that proof, the topmost such check on
%  the dominator chain: no check that covers it dominates it, so it stays
%  a check. Functions with a setjmp are unchanged. Every instruction keeps
%  its index, so context sites are unchanged.

renew_checks(module(Items0), module(Items)) :-
    maplist(renewed_item, Items0, Items).

renewed_item(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    (   member(block(_, _, Is, _), Bs0), member(let(_, _, setjmp(_), _), Is)
    ->  Bs = Bs0
    ;   names_info(Ps, Bs0, Info),
        func_cfg(Bs0, Cfg), cfg_idoms(Cfg, Idom), Cfg = cfg(Entry, _, _, _),
        renew_sources(Info, Bs0, Entry, Idom, Sources),
        maplist(renewed_block(Info, Entry, Idom, Sources), Bs0, Bs1),
        renew_selection(N, Bs0, Bs1, Bs)
    ).
renewed_item(Item, Item).

/* renew_selection(+Fn, +Blocks0, +Blocks1, -Blocks): for measurement,
   NANOFIL_RENEW_SITES=Fn:From-To keeps only Fn's renews numbered From to
   To - 1 in block order (Fn alone keeps all of Fn's), and every other
   function's checks; unset or empty, Blocks is Blocks1. Any subset of renews is
   valid IR: a check left in place is the reference. */
renew_selection(Fn, Bs0, Bs1, Bs) :-
    (   getenv('NANOFIL_RENEW_SITES', Spec), Spec \== ''
    ->  (   atomic_list_concat([F, Range], ':', Spec)
        ->  atomic_list_concat([A, B], '-', Range), atom_number(A, From), atom_number(B, To)
        ;   F = Spec, From = 0, To = inf
        ),
        (   F == Fn
        ->  foldl(selected_block(From, To), Bs0, Bs1, Bs, 0, _)
        ;   Bs = Bs0
        )
    ;   Bs = Bs1
    ).

selected_block(From, To, block(L, Ph, Is0, J), block(L, Ph, Is1, J), block(L, Ph, Is, J), K0, K) :-
    foldl(selected_inst(From, To), Is0, Is1, Is, K0, K).

selected_inst(From, To, I0, I1, I, K0, K) :-
    (   I1 = let(_, a, renew(_, _, _, _), _)
    ->  K is K0 + 1, ( K0 >= From, ( To == inf ; K0 < To ) -> I = I1 ; I = I0 )
    ;   K = K0, I = I1
    ).

% renew_sources(+Info, +Blocks, +Entry, +Idom, -Sources): Sources maps
% Root-K, a root and an offset from it, to s(Depth, L, I, Q1, check) for
% each reachable heap check of a pointer at K from Root whose proof and
% pointer have one definition, sorted by dominator depth and index.
renew_sources(Info, Blocks, Entry, Idom, Sources) :-
    findall((R-K)-s(Depth, L, I, Q1, check(Lo1, Hi1, Al1)),
            ( member(block(L, _, Is, _), Blocks),
              dom_depth(Idom, Entry, L, Depth),
              nth0(I, Is, let(tmp(Q1), a, check(Lo1, Hi1, _, Al1), [P1])),
              single_source(Info, Q1, P1),
              base_of(Info, P1, R, K) ),
            Pairs0),
    keysort(Pairs0, Pairs1),
    group_pairs_by_key(Pairs1, Groups0),
    findall(Key-Ss, ( member(Key-Ss0, Groups0), msort(Ss0, Ss) ), Groups),
    list_to_assoc(Groups, Sources).

single_source(info(Defs, _, _), Q1, tmp(N1)) :-
    count(Defs, Q1, 1), count(Defs, N1, 1).

% dom_depth(+Idom, +Entry, +L, -Depth): L is reachable, at Depth
% dominators below Entry.
dom_depth(_, Entry, Entry, 0) :- !.
dom_depth(Idom, Entry, L, Depth) :-
    get_assoc(L, Idom, D), dom_depth(Idom, Entry, D, Depth0), Depth is Depth0 + 1.

renewed_block(Info, Entry, Idom, Sources, block(L, Phis, Is0, J), block(L, Phis, Is, J)) :-
    (   dom_depth(Idom, Entry, L, _)
    ->  renewed_insts(Is0, 0, L, Info, Idom, Sources, Is)
    ;   Is = Is0
    ).

renewed_insts([], _, _, _, _, _, []).
renewed_insts([Inst0|Is0], I, L, Info, Idom, Sources, [Inst|Is]) :-
    (   Inst0 = let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]),
        Is0 = [Access|_], renewable_access(Access, Q),
        base_of(Info, P, R, K),
        get_assoc(R-K, Sources, Ss),
        member(s(_, L1, I1, Q1, check(Lo1, Hi1, Al1)), Ss),
        (   L1 == L -> I1 < I ; dominates(Idom, L1, L) ),
        subsumes(Lo1, Hi1, write, Al1, Lo, Hi, Rights, Align)
    ->  Inst = let(tmp(Q), a, renew(Lo, Hi, Rights, Align), [tmp(Q1)])
    ;   Inst = Inst0
    ),
    I1n is I + 1,
    renewed_insts(Is0, I1n, L, Info, Idom, Sources, Is).

% A renew's access: scalar or an ordinary pointer access; not a cas.
renewable_access(Access, Q) :- scalar_access(Access, Q).
renewable_access(let(_, p, raw_load_pointer(_, Es), [tmp(Q)]), Q) :-
    pointer_memory_effects(load, Es).
renewable_access(raw_store_pointer(_, _, tmp(Q), Es), Q) :-
    pointer_memory_effects(store, Es).

%! renew_refines(+M0, +M) is semidet.
%
%  M is M0 except for heap checks replaced by renews of the same range,
%  rights and alignment, each reading a single-definition heap check's
%  proof of a single-definition pointer related to the replaced check's
%  at distance 0. This is identity, not safety: dominance and coverage
%  are the validator's (ir.pl), which valid_module/1 checks separately.

renew_refines(module(Items0), module(Items)) :-
    maplist(item_renews, Items0, Items).

item_renews(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    names_info(Ps, Bs0, Info),
    findall(Q1-P1, ( member(block(_, _, Is, _), Bs0),
                     member(let(tmp(Q1), a, check(_, _, _, _), [P1]), Is),
                     single_source(Info, Q1, P1) ), Pairs),
    list_to_assoc(Pairs, Checks),
    maplist(block_renews(Info, Checks), Bs0, Bs).
item_renews(Item, Item).

block_renews(Info, Checks, block(L, Ph, Is0, J), block(L, Ph, Is, J)) :-
    maplist(inst_renews(Info, Checks), Is0, Is).

inst_renews(_, _, Inst, Inst) :- !.
inst_renews(Info, Checks, let(tmp(Q), a, check(Lo, Hi, Rs, Al), [P]),
            let(tmp(Q), a, renew(Lo, Hi, Rs, Al), [tmp(Q1)])) :-
    get_assoc(Q1, Checks, P1), related(Info, P, P1, 0).
