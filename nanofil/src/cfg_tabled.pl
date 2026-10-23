/*  The analyses of cfg.pl as tabled relations over IR facts, in the two
    styles the handoff proposed. They exist to answer PLAN's open
    question by measurement (tests/bench-cfg.pl, docs/m5.md); passes use
    cfg.pl.

    Versioned facts. assert_version(+V, +Blocks) asserts the function's
    edges and per-block gen/kill as facts tagged V; the tables take V as
    an argument, so every version has its own tables.
    retract_version(+V) drops version V's facts and every table
    (Trealla's abolish_table/1 drops all variants of a predicate, so old
    tables cannot be dropped one version at a time).

      v_live_in(V, B, T)     temp T is live on entry to B
      v_live_out(V, B, T)
      v_dom(V, D, B)         D dominates B (both reachable)
      v_idoms(V, Pairs)      [B-IDom] from v_dom
      v_frontier(V, X, Y)    Y is in the dominance frontier of X

    Incremental tabling. inc_load(+Blocks) asserts unversioned facts that
    are declared incremental, and inc_update(+Blocks) replaces the
    gen/kill/phi facts of the blocks whose facts differ; Trealla then
    invalidates exactly the tables that consulted them.

      i_live_in(B, T), i_live_out(B, T)

    Both styles take the gen/kill sets from cfg.pl, which is a local scan
    of each block: tabling it would only add table overhead.

    Impurity: facts are asserted and retracted here, which is the
    "versioned facts at pass boundaries" exception in PLAN's rules. The
    negations (\+ kill, \+ avoid) are called with ground arguments only,
    so they are sound.
*/
:- module(cfg_tabled, [assert_version/2, retract_version/1,
                       v_live_in/3, v_live_out/3, v_dom/3, v_idoms/2,
                       v_frontier/3,
                       inc_load/1, inc_update/1, inc_clear/0,
                       i_live_in/2, i_live_out/2]).

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

assert_version(V, Blocks) :-
    Blocks = [blk(Entry, _, _, _)|_],
    assertz(vf_entry(V, Entry)),
    gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    forall(member(blk(B, _, _, Jump), Blocks),
           ( assertz(vf_block(B, V)),
             forall(( jump_succs(Jump, Ss), member(S, Ss) ),
                    ( assertz(vf_edge(B, S, V)),
                      assertz(vf_pred(S, B, V)) )),
             get_assoc(B, GenKill, Gen-Kill),
             forall(member(T, Gen), assertz(vf_gen(B, T, V))),
             forall(member(T, Kill), assertz(vf_kill(B, T, V))) )),
    forall(( gen_assoc(B-S, EdgeUses, Ts), member(T, Ts) ),
           assertz(vf_euse(B, S, T, V))).

retract_version(V) :-
    retractall(vf_entry(V, _)),
    retractall(vf_block(_, V)),
    retractall(vf_edge(_, _, V)),
    retractall(vf_pred(_, _, V)),
    retractall(vf_gen(_, _, V)),
    retractall(vf_kill(_, _, V)),
    retractall(vf_euse(_, _, _, V)),
    abolish_all_tables.

% Every call below is a variant of an open v_live_in(V, _, _) or
% v_live_out(V, _, _), so each version has two tables in all.
:- table v_live_in/3, v_live_out/3.

v_live_in(V, B, T) :- vf_gen(B, T, V).
v_live_in(V, B, T) :- v_live_out(V, B, T), v_not_killed(B, T, V).

% Trealla 12f4cbd: a \+ or if-then-else written inline after a tabled
% call in a tabled clause gives wrong answers (it lets v_live_in(start,
% T) through for a T that start defines); the same negation in its own
% predicate is right. docs/m5.md has the reproduction.
v_not_killed(B, T, V) :- \+ vf_kill(B, T, V).

v_live_out(V, B, T) :- v_live_in(V, S, T), vf_pred(S, B, V).
v_live_out(V, B, T) :- vf_euse(B, _, T, V).

% avoid(V, D, B): B is reachable from the entry on a path that does not
% pass through D. One table per D; D = none gives plain reachability.
:- table avoid/3.

avoid(V, D, B) :- vf_entry(V, B), B \== D.
avoid(V, D, B) :- avoid(V, D, P), vf_edge(P, B, V), B \== D.

v_dom(V, D, B) :-
    avoid(V, none, D),
    avoid(V, none, B),
    % Not \+ avoid(V, D, B): that call is a new variant, and so a new
    % reachability table, for every B.
    \+ ( avoid(V, D, X), X == B ).

% The immediate dominator of B is the strict dominator with the most
% dominators of its own.
v_idoms(V, Pairs) :-
    findall(B-Doms,
            ( avoid(V, none, B), findall(D, v_dom(V, D, B), Doms) ),
            BlockDoms),
    findall(B-N, ( member(B-Doms, BlockDoms), length(Doms, N) ), Counts),
    list_to_assoc(Counts, Count),
    findall(B-Idom,
            ( member(B-Doms, BlockDoms),
              Doms = [_, _|_],
              findall(C-D,
                      ( member(D, Doms), D \== B, get_assoc(D, Count, C) ),
                      Counted),
              msort(Counted, Sorted),
              last(Sorted, _-Idom) ),
            Pairs).

v_frontier(V, X, Y) :-
    vf_edge(P, Y, V),
    avoid(V, none, P),
    v_dom(V, X, P),
    \+ ( v_dom(V, X, Y), X \== Y ).

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

:- table i_live_in/2 as incremental.
:- table i_live_out/2 as incremental.

i_live_in(B, T) :- if_gen(B, T).
i_live_in(B, T) :- i_live_out(B, T), i_not_killed(B, T).

i_not_killed(B, T) :- \+ if_kill(B, T).    % see v_not_killed/3

i_live_out(B, T) :- i_live_in(S, T), if_pred(S, B).
i_live_out(B, T) :- if_euse(B, T).

inc_clear :-
    retractall(if_pred(_, _)),
    retractall(if_gen(_, _)),
    retractall(if_kill(_, _)),
    retractall(if_euse(_, _)).

inc_load(Blocks) :-
    forall(( member(blk(B, _, _, Jump), Blocks),
             jump_succs(Jump, Ss),
             member(S, Ss) ),
           assertz(if_pred(S, B))),
    block_facts(Blocks, Facts),
    forall(member(F, Facts), assertz(F)).

% Retract the facts no block has any more, assert the new ones.
inc_update(Blocks) :-
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
    gen_kill(Blocks, GenKill),
    phi_edge_uses(Blocks, EdgeUses),
    findall(F,
            ( member(blk(B, _, _, _), Blocks),
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
