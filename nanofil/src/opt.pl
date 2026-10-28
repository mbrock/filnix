/*  The middle end's entry points for the driver, and the comparison the
    interpreter uses to validate it.

    optimize/3 runs the passes at a level, or an explicit ordered subset:

    ```diagram
    o0:  M0 ─────────────────────────────────────▶ M
    o1:  M0 ─▶ promote ─▶ copy ─▶ local_storage ─▶ M
    ```

    `optimization_passes/2` names that sequence. `optimize_pass/3` runs
    one member, so the playground can time it and show its actual output
    without implementing another optimizer. `passes([promote, copy])`,
    for example, leaves local storage off. Ordering stays fixed: local
    storage introduces a vocabulary the earlier passes do not consume.

    refines/2 relates the outcome of a program to the outcome of its
    optimized version. The driver's difftest and the unit tests validate
    the optimized IR, rather than repeating that work on every
    compilation. These passes consume unchecked IR only. A checked
    module supplied directly (even with -O) is left unchanged: promotion
    and substitution do not understand proofs or flight projections.
*/
:- module(opt, [optimize/3, optimization_passes/2, optimize_pass/3, refines/2]).

:- use_module(inline).
:- use_module(promote).
:- use_module(copy).
:- use_module(local_storage).
:- use_module(ir, [module_stage/2, local_objects/2]).
:- use_module(library(lists)).

%! optimize(+Options, +M0, -M) is semidet.
%
%  Options is o0 (the reference path), o1 (all three passes), o1(small)
%  (inlining of small static functions first, `--inline=small`), or
%  passes(Names), an ordered subset of o1(small). Invalid selections fail.
%  Checked or already-local IR stays unchanged.

optimize(Options, M0, M) :-
    optimization_passes(Options, Passes),
    foldl(optimize_pass, Passes, M0, M).

%! optimization_passes(+Options, -Passes) is semidet.
%
%  Passes is the selected sequence. A selection can omit passes but
%  cannot reorder or repeat them, or name an unknown pass.
optimization_passes(o0, []).
optimization_passes(o1, [promote, copy, local_storage]).
optimization_passes(o1(small), [inline, promote, copy, local_storage]).
optimization_passes(passes(Passes), Passes) :-
    optimization_passes(o1(small), All),
    ordered_passes(Passes, All).

ordered_passes([], _).
ordered_passes([P|Ps], All) :-
    append(_, [P|Rest], All),
    ordered_passes(Ps, Rest).

%! optimize_pass(+Name, +M0, -M) is semidet.
%
%  Run one named transformation on unchecked, ordinary-address IR.
%  Each pass transports its source contexts alongside executable IR.
%  Unknown names fail; all guards remain in the existing pass modules.
optimize_pass(Name, M0, M) :-
    pass_predicate(Name, Goal),
    (   ( module_stage(M0, checked) ; has_local_storage(M0) )
    ->  M = M0
    ;   call(Goal, M0, M)
    ).

pass_predicate(inline, inline_module).
pass_predicate(promote, promote_module).
pass_predicate(copy, copy_module).
pass_predicate(local_storage, local_storage_module).

% Named local objects are already the storage pass's product. Earlier
% passes consume ordinary addresses, not this lowered vocabulary.
has_local_storage(module(Items)) :-
    member(F, Items), F = func(_, _, _, _, _),
    local_objects(F, [_|_]).

%! refines(+Before, +After) is semidet.
%
%  After is an outcome the original program allows, given that the
%  original's outcome was Before, both from interp:run/5 on the same
%  inputs:
%
%    - undefined behaviour allows anything;
%    - an unknown result (read of uninitialized bytes in plain mode)
%      allows any value consistent with its constraints;
%    - otherwise the outcomes must be equal. A pointer into an alloc
%      compares by its offset in the object, because removing allocs
%      moves the ones left; data and function addresses do not move.

refines(ub(_), _) :- !.
refines(Before0, After0) :-
    outcome_key(Before0, Before),
    outcome_key(After0, After),
    (   ground(Before)
    ->  Before == After
    ;   \+ \+ Before = After
    ).

% outcome_key(+Outcome, -Key): Key is Outcome, except that a returned
% pointer into an alloc is keyed by its offset in the object.
outcome_key(ret(P), ret(obj_ptr(Off))) :-
    nonvar(P),
    P = ptr(Addr, obj(Base)),
    integer(Addr),
    !,
    Off is Addr - Base.
outcome_key(Outcome, Outcome).
