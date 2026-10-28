/*  Inlining of small static functions (docs/perf.md item 4), on
    unchecked IR before promotion, selected with `--inline=small`.

    A call `call(Res, global(F), Args)` to a function F of the module is
    replaced by F's blocks when F is eligible and so is the caller. The
    calling block is split at the call: its first part copies the
    arguments into F's renamed parameters and jumps to F's renamed entry;
    each `ret(V)` of F jumps to a join block, whose phi takes V, and the
    join block holds the rest of the calling block and its jump. F's
    blocks are placed right after the first part, so edges into and out
    of the body are forward and pizlonation, which polls by block order,
    polls exactly the cycles it polled before. Every allocation stays
    where it was, a fresh object at each execution; promotion takes the
    ones that do not escape (promote.pl promotes in any block).

    ## Eligibility

    | Callee F | Why |
    |---|---|
    | `local` linkage | an exported definition can be interposed |
    | no call to a function of the module (a leaf) | no recursion; two rounds give depth 2 |
    | no `va_args`, no setjmp, no tuple return | its own entry's argument snapshot, returns twice, two words |
    | a `ret`, strict SSA | the join needs a predecessor; promotion needs strict SSA |
    | every alloc of constant size at most 256, promotable or escaping (filc), promotable (plain) | a local one that could not promote would become a heap object per call; a plain stack alloc would outlive the call |
    | at most 120 instructions and jumps | size |

    | Caller | Why |
    |---|---|
    | no setjmp | reference selection, temporaries live across returns-twice |
    | in no cycle of direct calls | recursion depth before stack overflow is unchanged |
    | at most 2000 instructions, growing by at most half its size or 120, whichever is more | frame size and compile time |

    Function objects, getters and entries of inlined functions stay, so
    their addresses are unchanged. Names are fresh in the caller:
    `iR_N.X` for round R and instance N, with N raised past any
    collision. Source contexts follow: callee records are renamed (origin
    and binding identities wrapped as `inl(R, N, Id)`), and the split
    block's sites are re-indexed.
*/
:- module(inline, [inline_module/2]).

:- use_module(library(lists)).
:- use_module(library(assoc)).
:- use_module(library(ordsets)).
:- use_module(ir, [setjmp_func/1, module_mode/2]).
:- use_module(cfg, [func_cfg/2, cfg_idoms/2, inst_def/2]).
:- use_module(escape, [alloc_classes/2]).
:- use_module(promote, [promotable/3, strict_ssa/3]).
:- use_module(provenance, [legacy_context/2, code_items/2, context_index/2,
                           context_records/3, with_context/3]).

callee_limit(120).
caller_limit(2000).

%! inline_module(+M0, -M) is det.
%
%  M is M0 with two rounds of inlining of eligible calls.
inline_module(M0, M) :-
    legacy_context(M0, M1),
    M1 = module(Items1),
    findall(N-S, ( member(func(N, _, _, _, Bs), Items1), func_size(Bs, S) ), Sizes0),
    list_to_assoc(Sizes0, Sizes),
    inline_round(1, Sizes, M1, M2),
    release_stacks,
    inline_round(2, Sizes, M2, M).

% release_stacks: as main.pl's, collect the first round's garbage and
% return the stack memory before the second. SWI's limit counts what is
% allocated: without it, sqlite3.c overflows 1 GB with 200 MB live, and
% peaks 0.7 GB above `--inline=none` under the 4 GB limit its builds use.
release_stacks :-
    catch(garbage_collect, error(existence_error(_, _), _), true),
    catch(trim_stacks, error(existence_error(_, _), _), true).

% Sizes holds each function's size before the first round: both caps on
% a caller are on that size, so the second round cannot reset them.
inline_round(Round, Sizes, module(Items0), module(Items)) :-
    module_mode(module(Items0), Mode),
    code_items(Items0, Code),
    context_index(Items0, Contexts),
    findall(N, member(func(N, _, _, _, _), Code), Ns), name_set(Ns, Defined),
    % include/3 shares the callees' terms; findall/3 would copy them and
    % their records, hundreds of MB on SQLite.
    include(eligible_callee(Mode, Defined), Code, CalleeFs),
    maplist(callee_pair(Contexts), CalleeFs, CalleePairs),
    list_to_assoc(CalleePairs, Callees),
    cyclic_functions(Code, Defined, Cyclic0), name_set(Cyclic0, Cyclic),
    maplist(inlined_item(Round, Sizes, Callees, Cyclic, Contexts), Code, Groups),
    append(Groups, Items).

% name_set(+Names, -Set): Set is an assoc with key each of Names, for
% lookups in SQLite's 3,000 functions and its large callers' names.
name_set(Names, Set) :-
    sort(Names, Sorted), findall(N-true, member(N, Sorted), Pairs),
    ord_list_to_assoc(Pairs, Set).

callee_pair(Contexts, F, N-callee(F, Rs)) :-
    F = func(N, _, _, _, _), context_records(Contexts, N, Rs).

inlined_item(Round, Sizes, Callees, Cyclic, Contexts, F0, Items) :-
    F0 = func(Name, _, _, _, _), !,
    context_records(Contexts, Name, Rs0),
    get_assoc(Name, Sizes, Orig),
    (   eligible_caller(Cyclic, Orig, F0)
    ->  inline_func(Round, Orig, Callees, F0, Rs0, F, Rs)
    ;   F = F0, Rs = Rs0
    ),
    with_context(F, Rs, Items).
inlined_item(_, _, _, _, _, Item, [Item]).

%% Eligibility

eligible_callee(Mode, Defined, F) :-
    F = func(_, local, Ret, _, Bs),
    Ret \= tuple(_),
    \+ setjmp_func(F),
    func_size(Bs, S), callee_limit(Max), S =< Max,
    member(block(_, _, _, J), Bs), returns(J), !,
    \+ ( member(block(_, _, Is, J1), Bs),
         ( J1 = rets(_) ; member(I, Is), excluded_inst(Defined, I) ) ),
    allocs_ok(Mode, F),
    func_cfg(Bs, Cfg), cfg_idoms(Cfg, Idom), strict_ssa(F, Cfg, Idom).

returns(ret).
returns(ret(_)).

excluded_inst(Defined, call(_, global(G), _)) :- get_assoc(G, Defined, _).
excluded_inst(_, let(_, _, va_args, _)).
excluded_inst(_, let(_, p, alloc(_), [V])) :- \+ ( V = const(N), N =< 256 ).

% In filc mode every alloc either promotes or escapes, to a heap object
% per execution as before. In plain mode every alloc promotes: a stack
% alloc that stayed would live until the caller returns.
allocs_ok(filc, F) :-
    alloc_classes(F, Classes),
    promotable(filc, F, Roots),
    forall(member(A-local(_, _), Classes), memberchk(A-_, Roots)).
allocs_ok(plain, F) :-
    promotable(plain, F, Roots),
    F = func(_, _, _, _, Bs),
    forall(( member(block(_, _, Is, _), Bs), member(let(tmp(A), p, alloc(_), _), Is) ),
           memberchk(A-_, Roots)).

eligible_caller(Cyclic, Orig, F) :-
    F = func(Name, _, _, _, _),
    \+ setjmp_func(F),
    \+ get_assoc(Name, Cyclic, _),
    caller_limit(Max), Orig =< Max.

func_size(Bs, S) :- foldl(block_size, Bs, 0, S).
block_size(block(_, _, Is, _), S0, S) :- length(Is, N), S is S0 + N + 1.

% cyclic_functions(+Code, +Defined, -Cyclic): the ordset of functions on
% a cycle of direct calls between functions of the module. Functions
% that reach no cycle or that no cycle reaches are peeled off first;
% each remaining one is on a cycle if it reaches itself among them.
cyclic_functions(Code, Defined, Cyclic) :-
    findall(N-Cs, ( member(func(N, _, _, _, Bs), Code), direct_callees(Defined, Bs, Cs) ),
            Pairs),
    peel(Pairs, Core0),
    findall(C-N, ( member(N-Cs, Core0), member(C, Cs) ), Rev0),
    reverse_graph(Core0, Rev0, Rev),
    peel(Rev, CoreR),
    findall(N, member(N-_, CoreR), Ns0), sort(Ns0, Keep),
    findall(N-Cs, ( member(N-Cs0, Core0), ord_memberchk(N, Keep),
                    ord_intersection(Cs0, Keep, Cs) ), Core),
    list_to_assoc(Core, Graph),
    include(on_cycle(Graph), Keep, Cyclic).

direct_callees(Defined, Bs, Cs) :-
    findall(G, ( member(block(_, _, Is, _), Bs), member(call(_, global(G), _), Is),
                 get_assoc(G, Defined, _) ), Cs0),
    sort(Cs0, Cs).

% peel(+Graph, -Core): Core is Graph less, repeatedly, the nodes with no
% edge to a remaining node.
peel(Graph, Core) :-
    findall(N, ( member(N-Cs, Graph), Cs == [] ), Sinks0), sort(Sinks0, Sinks),
    (   Sinks == [] -> Core = Graph
    ;   findall(N-Cs, ( member(N-Cs0, Graph), \+ ord_memberchk(N, Sinks),
                        ord_subtract(Cs0, Sinks, Cs) ), Graph1),
        peel(Graph1, Core)
    ).

reverse_graph(Graph, Rev0, Rev) :-
    findall(N-Ps, ( member(N-_, Graph),
                    findall(P, member(N-P, Rev0), Ps0), sort(Ps0, Ps) ), Rev).

on_cycle(Graph, N) :-
    get_assoc(N, Graph, Cs),
    empty_assoc(Seen), reaches(Graph, Cs, N, Seen).

reaches(_, [N|_], N, _) :- !.
reaches(Graph, [C|Cs], N, Seen) :-
    (   get_assoc(C, Seen, _) -> reaches(Graph, Cs, N, Seen)
    ;   put_assoc(C, Seen, true, Seen1),
        ( get_assoc(C, Graph, Next) -> true ; Next = [] ),
        append(Next, Cs, Work),
        reaches(Graph, Work, N, Seen1)
    ).

%% The transformation

% inline_func(+Round, +Orig, +Callees, +F0, +Rs0, -F, -Rs): F is F0 with
% its eligible calls inlined while it stays within its original size
% Orig plus half of Orig, or plus one callee limit for a small caller.
% Splits and callee records are collected as the blocks are walked and
% applied to the caller's records once at the end: SQLite's largest
% functions inline hundreds of calls over tens of thousands of records.
inline_func(Round, Orig, Callees, F0, Rs0, F, Rs) :-
    F0 = func(Name, L, R, Ps, Bs0),
    (   once(( member(block(_, _, Is, _), Bs0), member(call(_, global(G), _), Is),
               get_assoc(G, Callees, _) ))
    ->  used_names(F0, Used0), name_set(Used0, Used),
        func_size(Bs0, S0), callee_limit(Floor),
        Budget is max(Orig // 2, Floor) - (S0 - Orig),
        blocks_inlined(Bs0, Callees, Used, Bs1, Moves,
                       st(Round, 1, Budget, [], []), st(_, _, _, Splits, Ctxs)),
        list_to_assoc(Moves, MoveIndex),
        maplist(moved_phis(MoveIndex), Bs1, Bs),
        F = func(Name, L, R, Ps, Bs),
        list_to_assoc(Splits, SplitIndex),
        reverse(Ctxs, Ctxs1), append(Ctxs1, CtxRs),
        % One copy of the caller's records, ending in the callees'.
        foldl(split_record(SplitIndex, MoveIndex), Rs0, Rs, CtxRs)
    ;   F = F0, Rs = Rs0
    ).

used_names(func(_, _, _, Ps, Bs), Used) :-
    findall(X, ( member(param(_, tmp(X)), Ps)
               ; member(block(X, _, _, _), Bs)
               ; member(block(_, Phis, _, _), Bs), member(phi(tmp(X), _, _), Phis)
               ; member(block(_, _, Is, _), Bs), member(I, Is), inst_def(I, X) ), Xs),
    list_to_ord_set(Xs, Used).

% blocks_inlined(+Bs0, +Callees, +Used, -Bs, -Moves, +St0, -St): Moves
% pairs each split block's label with the label of its last piece, which
% its successors' phis must now name. Used holds the caller's names
% before this round; the round's own names cannot collide with each
% other, since `iR_N.` determines N.
blocks_inlined([], _, _, [], [], St, St).
blocks_inlined([B|Bs0], Callees, Used, Bs, Moves, St0, St) :-
    B = block(L, _, _, _),
    block_inlined(B, Callees, Used, Out, Last, St0, St1),
    ( Last == L -> Moves = Moves1 ; Moves = [L-Last|Moves1] ),
    blocks_inlined(Bs0, Callees, Used, Bs1, Moves1, St1, St),
    append(Out, Bs1, Bs).

% block_inlined(+Block, +Callees, +Used, -Blocks, -Last, +St0, -St):
% Block with its first eligible call inlined, and the rest of it
% recursively; Last is the label of the last piece. St collects each
% split as L-split(NPre, NCopies, Join) and each instance's records.
block_inlined(block(L, Phis, Is, J), Callees, Used, Out, Last, St0, St) :-
    St0 = st(Round, N0, Budget0, Splits0, Ctxs0),
    (   append(Pre, [call(Res, global(G), Args)|Post], Is),
        get_assoc(G, Callees, callee(Callee, CRs)),
        Callee = func(_, _, _, _, CBs0),
        func_size(CBs0, CS), CS =< Budget0
    ->  Budget is Budget0 - CS,
        fresh_prefix(Round, N0, Callee, Used, N, P, Join),
        renamed_callee(P, Join, Callee, CBs, CPs, Rets),
        CBs = [block(Entry, _, _, _)|_],
        maplist(param_copy, CPs, Args, Copies),
        append(Pre, Copies, PreIs),
        join_phis(Res, Rets, JPhis),
        length(Pre, NPre), length(Copies, NC),
        callee_context(r(Round, N, P), CRs, CtxRs),
        N1 is N + 1,
        block_inlined(block(Join, JPhis, Post, J), Callees, Used, JoinOut, Last,
                      st(Round, N1, Budget, [L-split(NPre, NC, Join)|Splits0],
                         [CtxRs|Ctxs0]), St),
        append([[block(L, Phis, PreIs, goto(Entry))], CBs, JoinOut], Out)
    ;   Out = [block(L, Phis, Is, J)], Last = L, St = St0
    ).

% fresh_prefix(+Round, +N0, +Callee, +Used, -N, -P, -Join): P is
% `iR_N.` for the first N from N0 at which no renamed callee name is in
% Used, and Join is P before the first of join, join_, ... that is
% neither a callee name nor, with P, in Used.
fresh_prefix(Round, N0, Callee, Used, N, P, Join) :-
    format(atom(P0), 'i~w_~w.', [Round, N0]),
    used_names(Callee, Names),
    (   \+ ( member(X, Names), atom_concat(P0, X, Y), get_assoc(Y, Used, _) )
    ->  N = N0, P = P0, join_label(P0, Names, Used, join, Join)
    ;   N1 is N0 + 1, fresh_prefix(Round, N1, Callee, Used, N, P, Join)
    ).

join_label(P, Names, Used, Base, Join) :-
    atom_concat(P, Base, J0),
    (   \+ ord_memberchk(Base, Names), \+ get_assoc(J0, Used, _)
    ->  Join = J0
    ;   atom_concat(Base, '_', Base1), join_label(P, Names, Used, Base1, Join)
    ).

param_copy(param(K, tmp(X)), arg(_, V), let(tmp(X), K, copy, [V])).

% renamed_callee(+P, +Join, +Callee, -Blocks, -Params, -Rets): the
% callee's blocks and parameters with P before every temp and label,
% each return a jump to Join, Rets the join phi's arguments.
renamed_callee(P, Join, func(_, _, _, Ps0, Bs0), Bs, Ps, Rets) :-
    maplist(renamed_param(P), Ps0, Ps),
    maplist(renamed_block(P, Join), Bs0, Bs, Retss),
    append(Retss, Rets).

renamed_param(P, param(K, tmp(X)), param(K, tmp(Y))) :- atom_concat(P, X, Y).

renamed_block(P, Join, block(L, Phis, Is, J0), block(L1, Phis1, Is1, J), Rets) :-
    atom_concat(P, L, L1),
    maplist(renamed_phi(P), Phis, Phis1),
    maplist(renamed_temps(P), Is, Is1),
    (   J0 = ret(V) -> renamed_temps(P, V, V1), J = goto(Join), Rets = [L1-V1]
    ;   J0 == ret -> J = goto(Join), Rets = [L1-none]
    ;   renamed_jump(P, J0, J), Rets = []
    ).

renamed_phi(P, phi(D, K, Ins), phi(D1, K, Ins1)) :-
    renamed_temps(P, D, D1),
    maplist(renamed_phi_arg(P), Ins, Ins1).
renamed_phi_arg(P, L-V, L1-V1) :- atom_concat(P, L, L1), renamed_temps(P, V, V1).

renamed_jump(P, goto(T), goto(T1)) :- !, renamed_target(P, T, T1).
renamed_jump(P, branch(V, A, B), branch(V1, A1, B1)) :- !,
    renamed_temps(P, V, V1), renamed_target(P, A, A1), renamed_target(P, B, B1).
renamed_jump(P, J, J1) :- renamed_temps(P, J, J1).

renamed_target(P, poll(L), poll(L1)) :- !, atom_concat(P, L, L1).
renamed_target(P, L, L1) :- atom_concat(P, L, L1).

renamed_temps(P, tmp(X), tmp(Y)) :- !, atom_concat(P, X, Y).
renamed_temps(P, T, T1) :-
    compound(T), !,
    T =.. [F|As], maplist(renamed_temps(P), As, As1), T1 =.. [F|As1].
renamed_temps(_, T, T).

% A void callee's returns give no values: no phi.
join_phis(void, _, []).
join_phis(result(D, K), Rets, [phi(D, K, Rets)]).

moved_phis(Moves, block(L, Phis0, Is, J), block(L, Phis, Is, J)) :-
    maplist(moved_phi(Moves), Phis0, Phis).
moved_phi(Moves, phi(D, K, Ins0), phi(D, K, Ins)) :-
    maplist(moved_arg(Moves), Ins0, Ins).
moved_arg(Moves, F-V, T-V) :- ( get_assoc(F, Moves, T0) -> T = T0 ; T = F ).

%% Source contexts

% split_record(+Splits, +Moves, +R)// : the caller's records for R after
% every split. A split of block L at a call with NPre instructions before
% it keeps the sites before the call, gives the call's origins to each
% of the NC parameter copies, and moves the rest to Join, shifted, where
% a later split of Join applies in turn. A split block's jump site moves
% to its last piece. (The callees' records name no split block.)
split_record(Splits, Moves, site(inst(L, I), Os)) --> { get_assoc(L, Splits, Split) }, !,
    split_site(Split, Splits, Moves, L, I, Os).
split_record(_, Moves, site(jump(L), Os)) --> { get_assoc(L, Moves, T) }, !,
    [site(jump(T), Os)].
split_record(_, _, R) --> [R].

split_site(split(NPre, NC, Join), Splits, Moves, L, I, Os) -->
    (   { I < NPre } -> [site(inst(L, I), Os)]
    ;   { I =:= NPre } -> copy_sites(0, NC, L, NPre, Os)
    ;   { I1 is I - NPre - 1 }, split_record(Splits, Moves, site(inst(Join, I1), Os))
    ).

copy_sites(K, NC, _, _, _) --> { K >= NC }, !.
copy_sites(K, NC, L, NPre, Os) -->
    { I is NPre + K, K1 is K + 1 }, [site(inst(L, I), Os)],
    copy_sites(K1, NC, L, NPre, Os).


% callee_context(+r(Round, N, P), +CRs, -Rs): the callee's records
% renamed into the caller: temps and labels prefixed with P, origin and
% binding identities wrapped as inl(Round, N, Id). A return's jump site
% stays at its block, whose jump is now the goto to the join.
callee_context(R, CRs, Rs) :- maplist(context_record(R), CRs, Rs).

context_record(R, binding(B, Nm, Ty, Loc), binding(Id, Nm, Ty, Loc)) :- !, ctx_id(R, B, Id).
context_record(R, origin(Id0, Loc, D, Ps0), origin(Id, Loc, D, Ps)) :- !,
    ctx_id(R, Id0, Id), maplist(ctx_id(R), Ps0, Ps).
context_record(R, value(T0, H0, Os0), value(T, H, Os)) :- !,
    ctx_temp(R, T0, T), ctx_hint(R, H0, H), maplist(ctx_id(R), Os0, Os).
context_record(R, alias(T0, V0, H0, Os0), alias(T, V, H, Os)) :- !,
    ctx_temp(R, T0, T), ctx_value(R, V0, V), ctx_hint(R, H0, H), maplist(ctx_id(R), Os0, Os).
context_record(R, history(Id0, T0, H0, Os0, Rep0), history(Id, T, H, Os, Rep)) :- !,
    ctx_id(R, Id0, Id), ctx_temp(R, T0, T), ctx_hint(R, H0, H), maplist(ctx_id(R), Os0, Os),
    ( Rep0 = replaced(V0) -> ctx_value(R, V0, V), Rep = replaced(V) ; Rep = Rep0 ).
context_record(R, site(S0, Os0), site(S, Os)) :- !,
    ctx_site(R, S0, S), maplist(ctx_id(R), Os0, Os).
context_record(_, Rec, Rec).

ctx_id(r(Round, N, _), Id, inl(Round, N, Id)).
ctx_temp(r(_, _, P), T0, T) :- atom_concat(P, T0, T).
ctx_hint(R, named(B, Role), named(Id, Role)) :- !, ctx_id(R, B, Id).
ctx_hint(_, H, H).
ctx_value(R, tmp(T0), tmp(T)) :- !, ctx_temp(R, T0, T).
ctx_value(R, historical(Id0), historical(Id)) :- !, ctx_id(R, Id0, Id).
ctx_value(_, V, V).
ctx_site(r(_, _, P), inst(L0, I), inst(L, I)) :- atom_concat(P, L0, L).
ctx_site(r(_, _, P), phi(T0), phi(T)) :- atom_concat(P, T0, T).
ctx_site(r(_, _, P), jump(L0), jump(L)) :- atom_concat(P, L0, L).
