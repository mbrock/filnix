/*  The middle end's entry points, for the driver, and the comparison the
    interpreter uses to validate it: optimize/3 runs the passes at a
    level, and refines/2 relates the outcome of a program to the outcome
    of its optimized version. The driver's difftest and unit tests
    validate the optimized IR, rather than repeating that work on every
    compilation.
*/
:- module(opt, [optimize/3, refines/2]).

:- use_module(promote).
:- use_module(copy).

%! optimize(+Level, +M0, -M) is det.
%
%  M is the module M0 optimized at Level: o0 leaves M0 unchanged (the
%  reference path); o1 runs promote followed by copy elimination.

optimize(o0, M, M).
optimize(o1, M0, M) :-
    promote_module(M0, Promoted),
    copy_module(Promoted, M).

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
