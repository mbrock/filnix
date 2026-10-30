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
:- module(check_reuse, [reuse_checks/2, reuse_refines/2, renew_checks/2, renew_refines/2,
                        guard_checks/2, guard_refines/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(library(pairs)).
:- use_module(ir, [op_kind/2, pointer_memory_effects/2, temp_defs/3, single_definitions/3,
                   guard_chain/3, same_pointer/3]).
:- use_module(cfg, [inst_def/2, inst_uses/2, func_cfg/2, cfg_idoms/2, dominates/3,
                    natural_loops/3]).
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

%! names_info(+Params, +Blocks, -Info) is det.
%
%  Info is info(Defs, Uses, Bases): each temporary's number of
%  definitions (parameters, phis and every instruction form) and of
%  instructions reading it, and Bases, the assoc from each
%  single-definition flight X to B-K when X's address is B's plus the
%  constant K with B's capability, B defined once too (base_of/4).
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

%! base_of(+Info, +P, -R, -K) is det.
%
%  P's address is R's plus K, with R's capability, by single-definition
%  flights; R = P and K = 0 if P is no such flight or its chain has a
%  cycle (possible in unreachable blocks).
base_of(Info, P, R, K) :-
    (   base_walk(Info, P, [], R0, K0) -> R = R0, K = K0 ; R = P, K = 0 ).

base_walk(info(_, _, Bases), tmp(N), Seen, R, K) :- get_assoc(N, Bases, B-K0), !,
    \+ memberchk(N, Seen),
    base_walk(info(_, _, Bases), B, [N|Seen], R, K1), K is K0 + K1.
base_walk(_, P, _, P, 0).

%! related(+Info, +P, +P1, -D) is semidet.
%
%  P's address is P1's plus D, same capability.
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

%! single_proof(+Info, +Q) is semidet.
%
%  The proof tmp(Q) has one definition and one reader, the access that
%  follows its check.
single_proof(info(Defs, Uses, _), Q) :- count(Defs, Q, 1), count(Uses, Q, 1).

%! reused_insts(+Insts0, +Facts, +L-Old-New, -Insts, -Map, -Reused) is det.
%
%  Old and New index the next instruction of block L before and after;
%  Map pairs their sites, and Reused pairs each deleted proof with its
%  replacement.
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
% A vector's full-width check and its touch (docs/vector-access.md) stay,
% and make a fact that the chunk accesses after them may reuse. V1 does
% not reuse the full-width check itself.
reused_insts([let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), touch(T)|Insts0],
             Info, Facts0, L-Old-New, [let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]), touch(T)|Insts],
             [inst(L, Old)-inst(L, New), inst(L, Old1)-inst(L, New1)|Map], Reused, Exit) :-
    T == tmp(Q), !,
    Old1 is Old + 1, Old2 is Old + 2, New1 is New + 1, New2 is New + 2,
    state_kill(Info, Q, Facts0, Facts1),
    state_add(Info, avail(P, Q, Lo, Hi, Rights, Align), Facts1, Facts),
    reused_insts(Insts0, Info, Facts, L-Old2-New2, Insts, Map, Reused, Exit).
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

%! insts_refine(+Insts0, +Insts, +r(Info, Global, Proofs)) is semidet.
%
%  Proofs are Q-checked(P, Check) for the heap checks seen so far in the
%  block, newest first; Global the same for every heap check in the
%  function whose proof has one definition and its pointer at most one.
%  A deleted check's proof had one definition and one reader, and the
%  proof that replaces it checks the same operand and subsumes the
%  deleted check. Whether it is available there is the validator's
%  question.
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

%! scalar_access(+Access, +Q) is semidet.
%
%  Access is a scalar raw access at tmp(Q).
scalar_access(let(_, _, raw_load(T, _), [tmp(Q)]), Q) :- T \== p.
scalar_access(raw_store(W, _, _, tmp(Q)), Q) :- W \== p.

renamed_access(let(R, K, raw_load(T, Off0), [_]), Q, D, let(R, K, raw_load(T, Off), [tmp(Q)])) :-
    ( var(D) -> D is Off - Off0 ; Off is Off0 + D ).
renamed_access(raw_store(W, Off0, V, _), Q, D, raw_store(W, Off, V, tmp(Q))) :-
    ( var(D) -> D is Off - Off0 ; Off is Off0 + D ).

%! subsumes(+Lo1, +Hi1, +Rights1, +Align1, +Lo, +Hi, +Rights, +Align) is semidet.
%
%  A check of [Lo1, Hi1) with Rights1 at Align1 that succeeded implies
%  that the check of [Lo, Hi) with Rights at Align, of the same pointer
%  and object state, would succeed. Comparing with the deleted check,
%  not just its access, keeps a wider or stronger check's trap.
subsumes(Lo1, Hi1, Rights1, Align1, Lo, Hi, Rights, Align) :-
    Lo1 =< Lo, Hi =< Hi1,
    rights_include(Rights1, Rights),
    Align1 mod Align =:= 0, (Lo - Lo1) mod Align =:= 0.

rights_include(write, _).
rights_include(read, read).

%! after_def(+Info, +Inst, +Facts0, -Facts) is det.
%
%  Facts are those of Facts0 that do not mention the temporary Inst
%  defines.
after_def(Info, Inst, Facts0, Facts) :-
    (   inst_def(Inst, D)
    ->  state_kill(Info, D, Facts0, Facts)
    ;   Facts = Facts0
    ).

mentions(D, avail(P, Q, _, _, _, _)) :- ( Q == D ; P == tmp(D) ).

%! transparent(+Inst) is semidet.
%
%  Inst cannot free, reallocate or relabel an object, and reaches no
%  safepoint: arithmetic, comparisons, conversions, pure pointer
%  construction, checks, scalar raw accesses and raw pointer loads
%  (which read aux and box words, calling no helper).
transparent(loc(_, _)).
transparent(touch(_)).
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
        single_definitions(Ps, Bs0, Once),
        maplist(renewed_block(Info-Once, Entry, Idom, Sources), Bs0, Bs1),
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

%! renew_sources(+Info, +Blocks, +Entry, +Idom, -Sources) is det.
%
%  Sources maps Root-K, a root and an offset from it, to s(Depth, L, I,
%  Q1, check, P1) for each reachable heap check of a pointer at K from
%  Root whose proof and pointer have one definition, sorted by dominator
%  depth and index.
renew_sources(Info, Blocks, Entry, Idom, Sources) :-
    findall((R-K)-s(Depth, L, I, Q1, check(Lo1, Hi1, Al1), P1),
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

%! dom_depth(+Idom, +Entry, +L, -Depth) is semidet.
%
%  L is reachable, at Depth dominators below Entry.
dom_depth(_, Entry, Entry, 0) :- !.
dom_depth(Idom, Entry, L, Depth) :-
    get_assoc(L, Idom, D), dom_depth(Idom, Entry, D, Depth0), Depth is Depth0 + 1.

renewed_block(Info, Entry, Idom, Sources, block(L, Phis, Is0, J), block(L, Phis, Is, J)) :-
    (   dom_depth(Idom, Entry, L, _)
    ->  renewed_insts(Is0, 0, L, Info, Idom, Sources, Is)
    ;   Is = Is0
    ).

renewed_insts([], _, _, _, _, _, []).
renewed_insts([Inst0|Is0], I, L, Info-Once, Idom, Sources, [Inst|Is]) :-
    (   Inst0 = let(tmp(Q), a, check(Lo, Hi, Rights, Align), [P]),
        Is0 = [Access|_], renewable_access(Access, Q),
        base_of(Info, P, R, K),
        get_assoc(R-K, Sources, Ss),
        member(s(_, L1, I1, Q1, check(Lo1, Hi1, Al1), P1), Ss),
        (   L1 == L -> I1 < I ; dominates(Idom, L1, L) ),
        subsumes(Lo1, Hi1, write, Al1, Lo, Hi, Rights, Align),
        % The validator's identity rule (ir.pl), which bounds its walk:
        % the pass renews only what it accepts.
        same_pointer(Once, P, P1)
    ->  Inst = let(tmp(Q), a, renew(Lo, Hi, Rights, Align), [tmp(Q1), P])
    ;   Inst = Inst0
    ),
    I1n is I + 1,
    renewed_insts(Is0, I1n, L, Info-Once, Idom, Sources, Is).

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
            let(tmp(Q), a, renew(Lo, Hi, Rs, Al), [tmp(Q1), P])) :-
    get_assoc(Q1, Checks, P1), related(Info, P, P1, 0).

%! guard_checks(+M0, -M) is det.
%
%  Range guards (docs/m7.md, round 5, slice A). M is the checked module
%  M0 with each heap check in a natural loop, followed by a renewable
%  access, whose pointer is a base defined outside its innermost loop
%  plus an offset with a constant interval (ir.pl's guard_chain/3),
%  replaced by renew_if of that pointer and a guard: one span_test per
%  loop and base, appended to the end of the loop header's immediate
%  dominator, spanning every byte the group's checks can reach. Nothing
%  else moves, so existing context sites are unchanged; a guard has no
%  site and cannot trap. Functions with a setjmp are unchanged.

guard_checks(module(Items0), module(Items)) :-
    maplist(guarded_item, Items0, Items).

guarded_item(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    (   member(block(_, _, Is, _), Bs0), member(let(_, _, setjmp(_), _), Is)
    ->  Bs = Bs0
    ;   func_cfg(Bs0, Cfg), cfg_idoms(Cfg, Idom), natural_loops(Cfg, Idom, Loops0),
        assoc_to_list(Loops0, Loops), Loops \== [],
        single_definitions(Ps, Bs0, Once),
        findall(D-L0, ( member(block(L0, Phs, Is, _), Bs0),
                        ( member(phi(tmp(D), _, _), Phs) ; member(I0, Is), inst_def(I0, D) ) ),
                DLs0),
        sort(1, @<, DLs0, DLs), list_to_assoc(DLs, DefBlocks),
        Cfg = cfg(Entry, _, _, _),
        block_loops(Loops, Idom, BlockLoops),
        findall(L0-H0, ( gen_assoc(L0, BlockLoops, Ls0), last(Ls0, H0-_-_) ), LoopOf0),
        list_to_assoc(LoopOf0, LoopOf),
        Place = place(Entry, DefBlocks, LoopOf),
        findall(C, ( member(block(L1, _, Is, _), Bs0),
                     get_assoc(L1, BlockLoops, Outward),
                     guard_candidates(Is, 0, L1, Outward, Once-DefBlocks, Idom, C) ),
                Cs),
        Cs \== []
    ->  guard_places(Cs, Place, Idom, Places),
        findall((X-B-K)-(Lo1-Hi1), ( member(c(IH, B, K, _, _, Lo1, Hi1), Cs),
                                     get_assoc(B-K-IH, Places, X) ), KVs0),
        msort(KVs0, KVs), group_pairs_by_key(KVs, Groups0),
        findall(Key-Spans, ( member(Key-Spans0, Groups0), Key = _-_-Kind,
                             span_clusters(Kind, Spans0, Spans1), member(Spans, Spans1) ),
                Groups),
        empty_assoc(E),
        foldl(defined_name, DLs, E, Names0),
        foldl(param_name, Ps, Names0, Names),
        fresh_guards(Groups, Names, 0, Guards),
        foldl(placed_guard, Guards, Bs0, Bs1),
        findall((L2-I2)-G, ( member(c(IH, B, K, L2, I2, Lo2, Hi2), Cs),
                             get_assoc(B-K-IH, Places, X),
                             once(( member(g(G, X, B, K, GLo, GHi), Guards),
                                    GLo =< Lo2, Hi2 =< GHi )) ),
                Sites0),
        list_to_assoc(Sites0, Sites),
        maplist(guarded_block(Sites), Bs1, Bs)
    ;   Bs = Bs0
    ).
guarded_item(Item, Item).

defined_name(D-_, N0, N) :- put_assoc(D, N0, true, N).

param_name(param(_, tmp(D)), N0, N) :- !, put_assoc(D, N0, true, N).
param_name(_, N, N).

%! guard_candidates(+Insts, +I, +L, +Outward, +Defs, +Idom, -C) is nondet.
%
%  C is c(IH, B, K, L, J, Lo, Hi) for a heap check at index J >= I of
%  block L, followed by a renewable access, whose pointer is base B plus
%  an offset whose accesses cover [Lo, Hi) of B, B defined before the
%  loop whose header's immediate dominator is IH: the outermost of the
%  loops around L for which B is. K is const for a constant offset, else
%  ranged.
guard_candidates([Inst, Access|Is], I, L, Outward, Defs, Idom, C) :-
    (   Inst = let(tmp(Q), a, check(0, Hi, _, _), [P]),
        renewable_access(Access, Q),
        Defs = Once-_, guard_chain(Once, P, Chain),
        member(_-Body-IH, Outward),
        guard_base(Chain, Defs, Body, Idom, IH, B, OLo, OHi)
    ->  Hi1 is OHi + Hi,
        ( OLo =:= OHi -> K = const ; K = ranged ),
        (   guard_worth(K, OLo, Hi1), C = c(IH, B, K, L, I, OLo, Hi1)
        ;   I2 is I + 2, guard_candidates(Is, I2, L, Outward, Defs, Idom, C)
        )
    ;   I1 is I + 1, guard_candidates([Access|Is], I1, L, Outward, Defs, Idom, C)
    ).

/* guard_places(+Cs, +Place, +Idom, -Places): Places maps B-K-IH to X,
   the block at whose end the guard of base B and offset kind K for the
   loops whose headers' immediate dominators are IH goes. The IHs of one
   base and kind that lie in the same loop (or in none) share one place:
   their nearest common dominator, or B's definition block (the entry
   for a parameter) when that is deeper. So one guard serves several
   loops (bzip2's BZ2_decompress has dozens of bit-reading loops, each
   run once or twice, on one state pointer), yet runs only where every
   path to those loops runs: at mainGtU's entry it would run on each
   call, though its loop is reached by few. A place in another loop than
   its IHs (a definition inside an inner loop) falls back to each IH. */
guard_places(Cs, place(Entry, DefBlocks, LoopOf), Idom, Places) :-
    findall((B-K-LK)-IH, ( member(c(IH, B, K, _, _, _, _), Cs), loop_of(LoopOf, IH, LK) ), Ps0),
    sort(Ps0, Ps), group_pairs_by_key(Ps, Groups),
    findall((B-K-IH)-X,
            ( member((B-K-LK)-IHs, Groups),
              IHs = [IH0|IHs1], foldl(common_dominator(Idom), IHs1, IH0, X0),
              B = tmp(N), ( get_assoc(N, DefBlocks, DL) -> true ; DL = Entry ),
              ( DL \== X0, dominates(Idom, X0, DL) -> X1 = DL ; X1 = X0 ),
              member(IH, IHs),
              ( loop_of(LoopOf, X1, LK) -> X = X1 ; X = IH ) ),
            Pairs),
    list_to_assoc(Pairs, Places).

loop_of(LoopOf, L, H) :- ( get_assoc(L, LoopOf, H0) -> H = H0 ; H = none ).

%! common_dominator(+Idom, +A, +B, -D) is det.
%
%  D is the deepest block that dominates both A and B.
common_dominator(Idom, A, B, D) :-
    (   dominates(Idom, B, A) -> D = B
    ;   get_assoc(B, Idom, B1) -> common_dominator(Idom, A, B1, D)
    ;   D = B
    ).

%! guard_worth(+Kind, +Lo, +Hi) is semidet.
%
%  A guard of [Lo, Hi) may pass. A span test fails as a whole, and then
%  each access it guards pays its full check plus the test of G. A
%  ranged span over 256 KiB is a type's bound times a stride (a byte or
%  short index into a row of a table), which objects rarely hold:
%  bzip2's s->len[t][v], for a byte t, spans 1 MB of a 55 KB state. A
%  table that large (bzip2's ftab, 256 KiB) still fits. A span_test's
%  ends are signed 64-bit (ir.pl's valid_op); a span past them is no
%  guard at all, and merged clusters stay within each part's.
guard_worth(const, Lo, Hi) :- span_fits(Lo, Hi).
guard_worth(ranged, Lo, Hi) :- span_fits(Lo, Hi), Hi - Lo =< 262144.

span_fits(Lo, Hi) :- Lo >= -(1 << 63), Hi =< (1 << 63) - 1.

%! block_loops(+Loops, +Idom, -BlockLoops) is det.
%
%  BlockLoops maps each block in some natural loop whose header has an
%  immediate dominator to its loops' H-Body-IH, outermost first (nested
%  loops' bodies are nested). Built by walking the loops outermost first
%  and each body once, so the cost is the bodies' total size, not blocks
%  times loops.
block_loops(Loops, Idom, BlockLoops) :-
    findall(N-(H-B-IH), ( member(H-loop(_, B), Loops), get_assoc(H, Idom, IH),
                          length(B, N0), N is -N0 ), Ls),
    keysort(Ls, Sorted), pairs_values(Sorted, Outermost),
    findall(L-Lp, ( member(Lp, Outermost), Lp = _-B-_, member(L, B) ), LLs),
    sort(1, @=<, LLs, ByBlock), group_pairs_by_key(ByBlock, Groups),
    list_to_assoc(Groups, BlockLoops).

/* span_clusters(+Kind, +Spans, -Clusters): the Lo-Hi Spans of one base
   in one loop, in clusters, each one span test. A span test passes or
   fails as a whole, so a span the object cannot hold must not take
   others down with it. An offset that varies is bounded by its type and
   masks, not by the array it indexes (a byte index into a six-row
   table), so each distinct ranged span gets its own test; constant
   offsets, fields, merge where they overlap or lie within 64 bytes. */
span_clusters(ranged, Spans0, Clusters) :-
    sort(Spans0, Spans),
    findall([S], member(S, Spans), Clusters).
span_clusters(const, Spans0, Clusters) :-
    msort(Spans0, Spans),
    Spans = [Lo-Hi|Rest],
    merged_spans(Rest, Lo, Hi, Clusters).

merged_spans([], Lo, Hi, [[Lo-Hi]]).
merged_spans([Lo1-Hi1|Rest], Lo, Hi, Clusters) :-
    (   Lo1 =< Hi + 64
    ->  Hi2 is max(Hi, Hi1), merged_spans(Rest, Lo, Hi2, Clusters)
    ;   Clusters = [[Lo-Hi]|Clusters1], merged_spans(Rest, Lo1, Hi1, Clusters1)
    ).

%! guard_base(+Chain, +Once-DefBlocks, +Body, +Idom, +IH, -B, -OLo, -OHi) is semidet.
%
%  B is the farthest base on the chain whose single definition is
%  outside the loop Body and dominates its header's immediate dominator
%  IH, so a guard at IH's end may read it.
guard_base(Chain, Once-DefBlocks, Body, Idom, IH, B, OLo, OHi) :-
    reverse(Chain, Far),
    member(B-i(OLo, OHi), Far),
    B = tmp(N), get_assoc(N, Once, Def),
    (   Def == param -> true
    ;   get_assoc(N, DefBlocks, DL), \+ ord_memberchk(DL, Body), dominates(Idom, DL, IH)
    ), !.

%! fresh_guards(+Groups, +Names, +K, -Guards) is det.
%
%  A name no instruction or phi defines per group, g(Name, H, B, K, Lo,
%  Hi).
fresh_guards([], _, _, []).
fresh_guards([(H-B-K)-Spans|Gs], Names, K0, [g(Name, H, B, K, Lo, Hi)|Guards]) :-
    pairs_keys_values(Spans, Los, His), min_list(Los, Lo), max_list(His, Hi),
    fresh_name(Names, K0, Name, K1),
    fresh_guards(Gs, Names, K1, Guards).

fresh_name(Names, K0, Name, K) :-
    format(atom(Name0), 'guard.~w', [K0]), K1 is K0 + 1,
    (   get_assoc(Name0, Names, _) -> fresh_name(Names, K1, Name, K)
    ;   Name = Name0, K = K1
    ).

names_mentioned(Bs, Name) :-
    member(block(_, _, Is, _), Bs), member(I, Is),
    ( inst_def(I, Name) ; inst_uses(I, Us), memberchk(Name, Us) ), !.

placed_guard(g(Name, X, B, _, Lo, Hi), Bs0, Bs) :-
    append(Pre, [block(X, Ph, Is, J)|Post], Bs0), !,
    append(Is, [let(tmp(Name), w, span_test(Lo, Hi), [B])], Is1),
    append(Pre, [block(X, Ph, Is1, J)|Post], Bs).

guarded_block(Sites, block(L, Ph, Is0, J), block(L, Ph, Is, J)) :-
    guarded_insts(Is0, 0, L, Sites, Is).

guarded_insts([], _, _, _, []).
guarded_insts([Inst0|Is0], I, L, Sites, [Inst|Is]) :-
    (   get_assoc(L-I, Sites, G),
        Inst0 = let(Q, a, check(Lo, Hi, Rights, Align), [P])
    ->  Inst = let(Q, a, renew_if(Lo, Hi, Rights, Align), [P, tmp(G)])
    ;   Inst = Inst0
    ),
    I1 is I + 1,
    guarded_insts(Is0, I1, L, Sites, Is).

%! guard_refines(+M0, +M) is semidet.
%
%  M is M0 except for span_test lets of fresh names appended at block
%  ends, and heap checks replaced in place by renew_if of the same
%  pointer, range, rights and alignment, reading one of those guards.
%  This is identity, not safety: that the guard covers the access is the
%  validator's rule (ir.pl).

guard_refines(module(Items0), module(Items)) :-
    maplist(item_guards, Items0, Items).

item_guards(func(N, L, R, Ps, Bs0), func(N, L, R, Ps, Bs)) :- !,
    maplist(block_guards, Bs0, Bs, Gss), append(Gss, Gs),
    msort(Gs, Sorted), length(Gs, NG), sort(Gs, Set), length(Set, NG),
    \+ ( member(G, Sorted), names_mentioned(Bs0, G) ),
    \+ ( member(G, Sorted), member(param(_, tmp(G1)), Ps), G1 == G ),
    maplist(guard_reads_ok(Set), Bs, Bs0).
item_guards(Item, Item).

block_guards(block(L, Ph, Is0, J), block(L, Ph, Is, J), Gs) :-
    length(Is0, N), length(Pre, N), append(Pre, Extra, Is),
    findall(G, member(let(tmp(G), w, span_test(_, _), [_]), Extra), Gs),
    length(Extra, NE), length(Gs, NE),
    maplist(inst_guarded, Is0, Pre).

inst_guarded(Inst, Inst) :- !.
inst_guarded(let(Q, a, check(Lo, Hi, Rs, Al), [P]),
             let(Q, a, renew_if(Lo, Hi, Rs, Al), [P, tmp(_)])).

% Each renew_if that replaced a check reads one of the fresh guards.
guard_reads_ok(Set, block(_, _, Is, _), block(_, _, Is0, _)) :-
    guard_reads(Is0, Is, Set).

guard_reads([], _, _).
guard_reads([I0|Is0], [I|Is], Set) :-
    (   I0 = let(_, a, check(_, _, _, _), _), I = let(_, a, renew_if(_, _, _, _), [_, tmp(G)])
    ->  ord_memberchk(G, Set)
    ;   true
    ),
    guard_reads(Is0, Is, Set).
