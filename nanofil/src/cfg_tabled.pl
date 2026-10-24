/*  The analyses of cfg.pl as tabled relations over IR facts, in the two
    styles the handoff proposed. They exist to answer PLAN's open
    question by measurement (tests/bench-cfg.pl, docs/m5.md); passes use
    cfg.pl.

    | Style | Loads the facts | Relations |
    |---|---|---|
    | versioned facts | assert_version/2, retract_version/1 | version_live_in/3, version_live_out/3, version_dominates/3, version_idoms/2, version_frontier/3 |
    | incremental tabling | incremental_load/1, incremental_update/1, incremental_clear/0 | incremental_live_in/2, incremental_live_out/2 |

    ## Versioned facts

    assert_version/2 asserts the function's edges, entry, blocks,
    per-block gen and kill sets and phi edge uses as facts tagged with a
    version V. The relations over them take V as an argument, so every
    version has its own tables. retract_version/1 drops a version's
    facts and abolishes every table.

    ## Incremental tabling

    incremental_load/1 asserts unversioned facts that are declared
    incremental. incremental_update/1 replaces the gen, kill and phi
    edge-use facts that differ from those of the new blocks, and leaves
    the edges as they are; the host then invalidates only the tables
    that depend on the changed facts. incremental_clear/0 retracts every
    incremental fact.

    ## Common ground

    Both styles take the gen and kill sets from cfg.pl, which computes
    them by a local scan of each block: tabling that would only add
    table overhead.

    Facts are asserted and retracted here, which is the "versioned facts
    at pass boundaries" exception in PLAN's rules. The negations
    (`\+ kill`, `\+ avoid`) are called with ground arguments only, so
    they are sound.
*/
:- module(cfg_tabled, [assert_version/2, retract_version/1,
                       version_live_in/3, version_live_out/3,
                       version_dominates/3, version_idoms/2,
                       version_frontier/3,
                       incremental_load/1, incremental_update/1,
                       incremental_clear/0,
                       incremental_live_in/2, incremental_live_out/2]).

% SWI-Prolog has tabling built in (its library(tabling) is deprecated) and
% declares incremental dynamic predicates through dynamic/2.
:- if(\+ current_prolog_flag(dialect, swi)).
:- use_module(library(tabling)).
:- endif.
:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(cfg).

:- dynamic(vf_edge/3).     % vf_edge(From, To, V)
:- dynamic(vf_pred/3).     % vf_pred(To, From, V)
:- dynamic(vf_entry/2).    % vf_entry(V, Entry)
:- dynamic(vf_block/2).    % vf_block(B, V)
:- dynamic(vf_gen/3).      % vf_gen(B, T, V)
:- dynamic(vf_kill/3).     % vf_kill(B, T, V)
:- dynamic(vf_euse/4).     % vf_euse(B, Succ, T, V): T read on edge B->Succ

%% Versioned facts

%! assert_version(+V, +Blocks) is det.
%
%  Assert the edges, entry, blocks, gen/kill sets and phi edge uses of
%  the function Blocks as facts tagged V.

assert_version(V, Blocks) :-
    Blocks = [block(Entry, _, _, _)|_],
    assertz(vf_entry(V, Entry)),
    blocks_gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    forall(member(block(B, _, _, Jump), Blocks),
           ( assertz(vf_block(B, V)),
             forall(( jump_succs(Jump, Ss), member(S, Ss) ),
                    ( assertz(vf_edge(B, S, V)),
                      assertz(vf_pred(S, B, V)) )),
             get_assoc(B, GenKill, Gen-Kill),
             forall(member(T, Gen), assertz(vf_gen(B, T, V))),
             forall(member(T, Kill), assertz(vf_kill(B, T, V))) )),
    forall(( gen_assoc(B-S, EdgeUses, Ts), member(T, Ts) ),
           assertz(vf_euse(B, S, T, V))).

%! retract_version(+V) is det.
%
%  Retract version V's facts and abolish every table (Trealla's
%  abolish_table/1 drops all variants of a predicate, so old tables
%  cannot be dropped one version at a time).

retract_version(V) :-
    retractall(vf_entry(V, _)),
    retractall(vf_block(_, V)),
    retractall(vf_edge(_, _, V)),
    retractall(vf_pred(_, _, V)),
    retractall(vf_gen(_, _, V)),
    retractall(vf_kill(_, _, V)),
    retractall(vf_euse(_, _, _, V)),
    abolish_all_tables.

% Every call below is a variant of an open version_live_in(V, _, _) or
% version_live_out(V, _, _), so each version has two tables in all.
:- table version_live_in/3, version_live_out/3.

%! version_live_in(+V, ?B, ?T) is nondet.
%
%  Temp T is live on entry to block B in version V.

version_live_in(V, B, T) :-
    vf_gen(B, T, V).
version_live_in(V, B, T) :-
    version_live_out(V, B, T),
    v_not_killed(B, T, V).

% Trealla 12f4cbd: a \+ or if-then-else written inline after a tabled
% call in a tabled clause gives wrong answers (it lets version_live_in(start,
% T) through for a T that start defines); the same negation in its own
% predicate is right. docs/m5.md has the reproduction.
v_not_killed(B, T, V) :-
    \+ vf_kill(B, T, V).

%! version_live_out(+V, ?B, ?T) is nondet.
%
%  Temp T is live on exit from block B in version V.

version_live_out(V, B, T) :-
    version_live_in(V, S, T),
    vf_pred(S, B, V).
version_live_out(V, B, T) :-
    vf_euse(B, _, T, V).

% avoid(V, Avoid, B): B is reachable from the entry in version V on a
% path that does not pass through the label of Avoid: some(D) avoids D,
% and none gives plain reachability. One table per Avoid.
:- table avoid/3.

avoid(V, Avoid, B) :-
    vf_entry(V, B),
    not_avoided(Avoid, B).
avoid(V, Avoid, B) :-
    avoid(V, Avoid, P),
    vf_edge(P, B, V),
    not_avoided(Avoid, B).

% not_avoided(+Avoid, +B): B is not the label that Avoid avoids.
not_avoided(none, _).
not_avoided(some(D), B) :-
    B \== D.

%! version_dominates(+V, ?D, ?B) is nondet.
%
%  D dominates B in version V (both reachable).

version_dominates(V, D, B) :-
    avoid(V, none, D),
    avoid(V, none, B),
    % Not \+ avoid(V, some(D), B): that call is a new variant, and so a
    % new reachability table, for every B.
    \+ ( avoid(V, some(D), X), X == B ).

%! version_idoms(+V, -Pairs) is det.
%
%  Pairs is the list B-Idom of the reachable blocks B of version V other
%  than the entry and their immediate dominators, from
%  version_dominates/3: the immediate dominator of B is the strict
%  dominator with the most dominators of its own.

version_idoms(V, Pairs) :-
    findall(B-Doms,
            ( avoid(V, none, B),
              findall(D, version_dominates(V, D, B), Doms)
            ),
            BlockDoms),
    findall(B-N,
            ( member(B-Doms, BlockDoms),
              length(Doms, N)
            ),
            Counts),
    list_to_assoc(Counts, Count),
    findall(B-Idom,
            ( member(B-Doms, BlockDoms),
              Doms = [_, _|_],
              findall(C-D,
                      ( member(D, Doms),
                        D \== B,
                        get_assoc(D, Count, C)
                      ),
                      Counted),
              msort(Counted, Sorted),
              last(Sorted, _-Idom)
            ),
            Pairs).

%! version_frontier(+V, ?X, ?Y) is nondet.
%
%  Y is in the dominance frontier of X in version V. A Y can be found
%  once per predecessor that X dominates.

version_frontier(V, X, Y) :-
    vf_edge(P, Y, V),
    avoid(V, none, P),
    version_dominates(V, X, P),
    \+ ( version_dominates(V, X, Y), X \== Y ).

%% Incremental tabling

% if_pred(To, From), if_gen(B, T), if_kill(B, T), if_euse(B, T)
:- if(current_prolog_flag(dialect, swi)).
:- dynamic([if_pred/2, if_gen/2, if_kill/2, if_euse/2], [incremental(true)]).
:- else.
:- dynamic(if_pred/2).
:- dynamic(if_gen/2).
:- dynamic(if_kill/2).
:- dynamic(if_euse/2).
:- incremental((if_pred/2, if_gen/2, if_kill/2, if_euse/2)).
:- endif.

:- table incremental_live_in/2 as incremental.
:- table incremental_live_out/2 as incremental.

%! incremental_live_in(?B, ?T) is nondet.
%
%  Temp T is live on entry to block B of the loaded function.

incremental_live_in(B, T) :-
    if_gen(B, T).
incremental_live_in(B, T) :-
    incremental_live_out(B, T),
    i_not_killed(B, T).

% See v_not_killed/3.
i_not_killed(B, T) :-
    \+ if_kill(B, T).

%! incremental_live_out(?B, ?T) is nondet.
%
%  Temp T is live on exit from block B of the loaded function.

incremental_live_out(B, T) :-
    incremental_live_in(S, T),
    if_pred(S, B).
incremental_live_out(B, T) :-
    if_euse(B, T).

%! incremental_clear is det.
%
%  Retract every incremental fact.

incremental_clear :-
    retractall(if_pred(_, _)),
    retractall(if_gen(_, _)),
    retractall(if_kill(_, _)),
    retractall(if_euse(_, _)).

%! incremental_load(+Blocks) is det.
%
%  Assert the incremental facts (edges, gen/kill sets, phi edge uses) of
%  the function Blocks.

incremental_load(Blocks) :-
    forall(( member(block(B, _, _, Jump), Blocks),
             jump_succs(Jump, Ss),
             member(S, Ss) ),
           assertz(if_pred(S, B))),
    block_facts(Blocks, Facts),
    forall(member(F, Facts), assertz(F)).

%! incremental_update(+Blocks) is det.
%
%  Make the gen, kill and phi edge-use facts those of Blocks: retract
%  the facts no block has any more and assert the new ones. Edges
%  (if_pred/2) are left as they are.

incremental_update(Blocks) :-
    block_facts(Blocks, New),
    findall(F,
            ( member(F, [if_gen(_, _), if_kill(_, _), if_euse(_, _)]),
              call(F) ),
            Old0),
    sort(Old0, Old),
    ord_subtract(Old, New, Gone),
    ord_subtract(New, Old, Added),
    forall(member(F, Gone), retract(F)),
    forall(member(F, Added), assertz(F)).

% block_facts(+Blocks, -Facts): the sorted if_gen, if_kill and if_euse
% facts of Blocks.
block_facts(Blocks, Facts) :-
    blocks_gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    findall(F,
            ( member(block(B, _, _, _), Blocks),
              get_assoc(B, GenKill, Gen-Kill),
              (   member(T, Gen), F = if_gen(B, T)
              ;   member(T, Kill), F = if_kill(B, T)
              ) ),
            GenKillFacts),
    findall(if_euse(B, T),
            ( gen_assoc(B-_, EdgeUses, Ts), member(T, Ts) ),
            EdgeFacts),
    append(GenKillFacts, EdgeFacts, Facts0),
    sort(Facts0, Facts).
