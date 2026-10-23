/*  The middle end's entry points, for the driver, and the comparison the
    interpreter uses to validate it.

    optimize(+Level, +M0, -M)
      Level o0 returns M0 unchanged (the reference path); o1 runs
      promote. The result is not re-validated here: valid_module/1 is
      quadratic in the number of blocks (8 s on a 1557-block function),
      so the driver's difftest and the unit tests do it instead.

    refines(+Before, +After)
      After is an outcome the original program allows, given that the
      original's outcome was Before, both from interp:run/5 on the same
      inputs:
        - undefined behaviour allows anything;
        - an unknown result (read of uninitialized bytes in plain mode)
          allows any value consistent with its constraints;
        - otherwise the outcomes must be equal. A pointer into an alloc
          compares by its offset in the object, because removing allocs
          moves the ones left; data and function addresses do not move.
*/
:- module(opt, [optimize/3, refines/2]).

:- use_module(promote).

optimize(o0, M, M).
optimize(o1, M0, M) :-
    promote_module(M0, M).

refines(ub(_), _) :- !.
refines(B0, A0) :-
    outcome_key(B0, B),
    outcome_key(A0, A),
    (   ground(B) -> B == A
    ;   \+ \+ B = A
    ).

outcome_key(ret(P), ret(obj_ptr(Off))) :-
    nonvar(P), P = ptr(A, obj(Base)), integer(A), !,
    Off is A - Base.
outcome_key(O, O).
