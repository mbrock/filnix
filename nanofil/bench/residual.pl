/* Campaign 0's read-only query over provenance-bearing checked modules.
   Run from src: ../bin/nanofil --script ../bench/residual.pl FILE.term...
   Each input is outcomes' single module/1 term, with no run lines.
   --sites-only skips the cost model (Cost is unmeasured), including
   named-local sites whose emitter sequence has no Campaign 0 cost.
   The classifications are syntactic observations, not discharge proofs.
   docs/residual.md defines the precedence, limitations and cost model. */
:- use_module('../src/ir', [single_definitions/3, pointer_distance/4]).
:- use_module('../src/cfg').
:- use_module('../src/provenance').
:- use_module('../src/filc_amd64', []).
:- use_module(library(assoc)).
:- use_module(library(lists)).
:- use_module(library(pairs)).
:- initialization(main).

main :-
    catch((census -> halt(0) ; halt(1)), E, (print_message(error, E), halt(1))).

census :-
    current_prolog_flag(argv, Args),
    ( Args = ['--sites-only'|Files] -> Mode = sites ; Files = Args, Mode = costs ),
    maplist(file_sites(Mode), Files, Groups), append(Groups, Sites),
    forall(member(S, Sites), (write_canonical(S), write('.'), nl)),
    findall(form(F), member(site(_, _, _, _, F, _, _, _, _, _), Sites), Forms),
    findall(shape(S), member(site(_, _, _, _, _, S, _, _, _, _), Sites), Shapes),
    findall(cross(F, S), member(site(_, _, _, _, F, S, _, _, _, _), Sites), Cross),
    findall(loop(F, L), member(site(_, _, _, _, F, _, L, _, _, _), Sites), Loops),
    findall(after(F, A), member(site(_, _, _, _, F, _, _, A, _, _), Sites), After),
    append([Forms, Shapes, Cross, Loops, After], Keys),
    msort(Keys, Sorted), clumped(Sorted, Counts),
    forall(member(K-N, Counts), format('~q.~n', [count(K, N)])),
    ( Mode == costs -> cost_totals(Sites) ; true ),
    length(Files, NF), length(Sites, NS), format('total(~d,~d).~n', [NF, NS]).

cost_totals(Sites) :-
    findall(shape(S)-C, member(site(_, _, _, _, _, S, _, _, _, C), Sites), SCosts),
    findall(form(F)-C, member(site(_, _, _, _, F, _, _, _, _, C), Sites), FCosts),
    append(SCosts, FCosts, Costs), keysort(Costs, SortedCosts),
    group_pairs_by_key(SortedCosts, CostGroups),
    forall(member(K-Cs, CostGroups), (sum_list(Cs, Sum), format('~q.~n', [instructions(K, Sum)]))).

file_sites(File, Sites) :-
    file_sites(costs, File, Sites).

file_sites(Mode, File, Sites) :-
    setup_call_cleanup(open(File, read, S),
                       (read_term(S, M, []), read_term(S, end_of_file, [])), close(S)),
    M = module(Items), context_index(Items, Contexts),
    findall(FSites,
            ( member(func(N, _, _, Ps, Bs), Items),
              single_definitions(Ps, Bs, Defs),
              func_cfg(Bs, Cfg), cfg_idoms(Cfg, Idoms), natural_loops(Cfg, Idoms, LoopMap),
              assoc_to_values(LoopMap, Natural),
              context_records(Contexts, N, Rs), site_index(Rs, SiteMap),
              findall(Id-origin(Loc, Parents), member(origin(Id, Loc, _, Parents), Rs), OPairs),
              list_to_assoc(OPairs, Origins),
              findall(site(File, N, L, I, Form, Shape, Loop, After, Locs, Cost),
                      ( member(block(L, _, Is, _), Bs), nth0(I, Is, Inst),
                        check_form(Inst, Form, P),
                        site_cost(Mode, Inst, Cost),
                        shape(Form, P, Defs, Items, Shape),
                        loop_shape(L, P, Natural, Bs, Defs, Loop),
                        after_event(L, I, Is, Bs, After),
                        site_origins(SiteMap, inst(L, I), Os),
                        locations(Os, Origins, [], Ls), sort(Ls, Locs)
                      ), FSites)
            ), Groups),
    append(Groups, Sites),
    % A new class-a opcode or a failed classification must not silently
    % disappear from this census. Count the input independently.
    findall(1, (member(func(_, _, _, _, Bs), Items), member(block(_, _, Is, _), Bs),
                member(let(_, a, _, _), Is)), Checks),
    length(Checks, Count), length(Sites, Count).

site_cost(sites, _, unmeasured).
site_cost(costs, Inst, Cost) :- core_instructions(Inst, Cost).

check_form(let(_, a, check(_, _, _, _), [P]), full, P).
check_form(let(_, a, renew(_, _, _, _), [_, P]), renew, P).
check_form(let(_, a, half_check(B, _, _, _, _), [_, P]), half(B), P).
check_form(let(_, a, check_local(N, O, _, _, _), []), local, local(N, O)).

% Count the emitter's unshared, split-bounds check core, not pointer
% preparation, the raw access, aux handling or failure paths. Combined
% emits only full, renew and half checks in the measured Lua corpus.
core_instructions(let(_, a, Op, _), Count) :-
    ( phrase(core(Op), Asm) -> length(Asm, Count)
    ; throw(error(domain_error(campaign_check, Op), residual)) ).
core(check(0, Size, Rights, Align)) -->
    { write_bit(Rights, W) },
    filc_amd64:bounds_check(split, local, Size, fail),
    filc_amd64:write_check(W, fail), filc_amd64:align_check(Align, fail).
core(renew(_, _, Rights, _)) -->
    { write_bit(Rights, W) }, filc_amd64:flags_check(W, fail).
core(half_check(Bound, 0, Size, Rights, Align)) -->
    { write_bit(Rights, W) }, filc_amd64:half_bounds(Bound, local, Size, W, fail),
    filc_amd64:align_check(Align, fail).
write_bit(read, 0).
write_bit(write, 1).

% Capability origins retain root identities, not merely root categories.
% On a phi cycle, an already visited node contributes no new roots.
roots(P, _, Seen, []) :- memberchk(P, Seen), !.
roots(tmp(T), Ds, Seen, Roots) :-
    get_assoc(T, Ds, D), !,
    definition_roots(D, tmp(T), Ds, [tmp(T)|Seen], Roots).
roots(P, _, _, [unknown(P)]).

definition_roots(flight(_, _, _, lower(P)), _, Ds, Seen, Rs) :- !,
    roots(P, Ds, Seen, Rs).
definition_roots(flight(_, _, _, none), T, _, _, [integer(T)]) :- !.
definition_roots(phi(_, p, Pairs), _, Ds, Seen, Rs) :- !,
    pairs_values(Pairs, Ps), maplist(pointer_roots(Ds, Seen), Ps, Groups), append(Groups, Rs).
definition_roots(let(_, p, raw_load_pointer(_, _), _), T, _, _, [loaded(T)]) :- !.
definition_roots(let(_, p, copy, [global(N)]), _, _, _, [global(N)]) :- !.
definition_roots(let(_, p, alloc(_), [const(Size)]), T, _, _, [allocated(T, Size)]) :- !.
definition_roots(param, T, _, _, [parameter(T)]) :- !.
definition_roots(call(_, _, _), T, _, _, [returned(T)]) :- !.
definition_roots(raw_call(_, _, _), T, _, _, [returned(T)]) :- !.
definition_roots(D, T, _, _, [other(T, D)]).
pointer_roots(Ds, Seen, P, Rs) :- roots(P, Ds, Seen, Rs).

shape(local, _, _, _, static_local) :- !.
shape(_, P, Ds, Items, Shape) :-
    roots(P, Ds, [], Rs0), sort(Rs0, Rs),
    ( Rs = [_, _|_] -> Shape = mixed_roots
    ; Rs = [integer(_)] -> Shape = integer_derived
    ; Rs = [loaded(_)] -> Shape = pointer_chase
    ; Rs = [global(N)], memberchk(data(N, _, _, _), Items),
      root_pointer(P, Ds, [], Base), Base = tmp(T),
      get_assoc(T, Ds, let(_, p, copy, [global(N)])), pointer_distance(Ds, P, Base, _)
    -> Shape = static_global
    ; Rs = [allocated(Base, _)], pointer_distance(Ds, P, Base, _)
    -> Shape = static_allocation
    ; Rs = [allocated(_, _)] -> Shape = allocation_dynamic_offset
    ; Rs = [parameter(_)] -> Shape = parameter
    ; Rs = [returned(_)] -> Shape = call_result
    ; Rs = [global(_)] -> Shape = global_dynamic_or_external
    ; Shape = other
    ).

root_pointer(P, _, Seen, _) :- memberchk(P, Seen), !, fail.
root_pointer(tmp(T), Ds, Seen, Root) :-
    get_assoc(T, Ds, flight(_, _, _, lower(P))), !,
    root_pointer(P, Ds, [tmp(T)|Seen], Root).
root_pointer(P, _, _, P).

% An affine candidate is address arithmetic using a scalar induction
% phi in the same natural loop. It is NOT a proof of no wrap or bounds.
loop_shape(L, P, Loops, Bs, Ds, Shape) :-
    ( affine_loop(L, P, Loops, Bs, Ds, Body, V), visible_bound(Body, Bs, Ds, V)
    -> Shape = affine_parameter_bound
    ; affine_loop(L, P, Loops, Bs, Ds, _, _) -> Shape = affine_candidate
    ; member(loop(_, Body), Loops), memberchk(L, Body) -> Shape = other_loop
    ; Shape = outside_loop ).

affine_loop(L, P, Loops, Bs, Ds, Body, V) :-
    member(loop(_, Body), Loops), memberchk(L, Body),
    induction_address(P, Ds, [], V),
    member(block(PL, Phis, _, _), Bs), memberchk(PL, Body),
    member(phi(V, K, Pairs), Phis), memberchk(K, [w, l]),
    member(_-Next, Pairs), affine(Next, V, Ds, [], 1, Step), Step =\= 0.

induction_address(P, _, Seen, _) :- memberchk(P, Seen), !, fail.
induction_address(tmp(T), Ds, Seen, V) :-
    get_assoc(T, Ds, flight(_, _, Args, _)),
    member(A, Args),
    ( A = address(B) -> induction_address(B, Ds, [tmp(T)|Seen], V)
    ; scalar_phi(A, Ds, [], V), affine(A, V, Ds, [], Scale, _), Scale =\= 0 ).

scalar_phi(P, _, Seen, _) :- memberchk(P, Seen), !, fail.
scalar_phi(tmp(T), Ds, Seen, V) :-
    get_assoc(T, Ds, D),
    ( D = phi(V, K, _), memberchk(K, [w, l])
    ; D = let(_, _, Op, Args), memberchk(Op, [add, sub, mul, shl, copy, ext(sw), ext(uw)]),
      member(A, Args), scalar_phi(A, Ds, [tmp(T)|Seen], V) ).

affine(V, V, _, _, 1, 0) :- !.
affine(const(N), _, _, _, 0, N) :- !.
affine(tmp(T), V, Ds, Seen, A, B) :-
    \+ memberchk(T, Seen), get_assoc(T, Ds, let(_, _, Op, Args)),
    affine_op(Op, Args, V, Ds, [T|Seen], A, B).
affine_op(Op, [X], V, Ds, S, A, B) :-
    memberchk(Op, [copy, ext(sw), ext(uw)]), affine(X, V, Ds, S, A, B).
affine_op(Op, [X, Y], V, Ds, S, A, B) :-
    memberchk(Op, [add, sub]),
    affine(X, V, Ds, S, AX, BX), affine(Y, V, Ds, S, AY, BY),
    ( Op == add -> A is AX + AY, B is BX + BY ; A is AX - AY, B is BX - BY ).
affine_op(mul, [X, const(N)], V, Ds, S, A, B) :-
    affine(X, V, Ds, S, AX, BX), A is AX * N, B is BX * N.
affine_op(shl, [X, const(N)], V, Ds, S, A, B) :-
    N >= 0, N < 64, affine(X, V, Ds, S, AX, BX), A is AX << N, B is BX << N.

visible_bound(Body, Bs, Ds, V) :-
    member(block(L, _, Is, _), Bs), memberchk(L, Body),
    member(let(_, _, cmp(Cond, _), [X, Y]), Is),
    memberchk(Cond, [slt, sle, ult, ule, eq, ne, sgt, sge, ugt, uge]),
    ( affine(X, V, Ds, [], A, _), A =\= 0, parameter_value(Y, Ds, [])
    ; affine(Y, V, Ds, [], A, _), A =\= 0, parameter_value(X, Ds, []) ).
parameter_value(tmp(T), Ds, Seen) :-
    \+ memberchk(T, Seen), get_assoc(T, Ds, D),
    ( D == param
    ; D = let(_, _, Op, [X]), memberchk(Op, [copy, ext(sw), ext(uw)]),
      parameter_value(X, Ds, [T|Seen]) ).

% This reports a nearby event, not all-path safepoint causality. For a
% poll incoming edge, no earlier check may occur in the target block.
after_event(L, I, Is, Bs, After) :-
    length(Prefix, I), append(Prefix, _, Is), reverse(Prefix, Rev),
    ( nearest_event(Rev, E) -> After = E
    ; \+ (member(X, Prefix), check_form(X, _, _)),
      member(block(_, _, _, J), Bs), sub_term(poll(L), J)
    -> After = poll_edge
    ; After = none ).
nearest_event([I|_], call) :- ( I = call(_, _, _) ; I = raw_call(_, _, _) ), !.
nearest_event([I|_], check) :- check_form(I, _, _), !.
nearest_event([_|Is], E) :- nearest_event(Is, E).

locations([], _, _, []).
locations([O|Os], Origins, Seen, Ls) :-
    ( memberchk(O, Seen) -> locations(Os, Origins, Seen, Ls)
    ; get_assoc(O, Origins, origin(Loc, Parents)),
      append(Parents, Os, Todo), locations(Todo, Origins, [O|Seen], Rest),
      ( Loc == none -> Ls = Rest ; Ls = [Loc|Rest] ) ).
