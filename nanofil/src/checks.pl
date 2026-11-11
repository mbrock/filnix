/*  The check passes after pizlonation, as `--checks` selects them
    (docs/m7.md, docs/forward.md, docs/half.md): checks_module/3 runs
    one selection on a checked module, and opt_checks/2 names the one
    each optimization level uses. The driver (main.pl) and the
    playground (web/play/play.pl) both run them from here, so the
    playground's -O shows the module the compiler gives its backend.

    | Checks | Passes |
    |---|---|
    | `reference` | none: pizlonate's check before every access |
    | `reuse` | reuse |
    | `renew`, `guard`, `hoist`, `schedule`, `half` | reuse, renewal, then that pass |
    | `forward` | forward reuse, renewal at any distance |
    | `combined` (`-O`) | forward, then half checks |
    | `hull`, `getter`, `extended` | combined with renewal by two checks' hull, facts across repeated getters, or both |

    Each pass's result must pass its `*_refines` identity check against
    its input, and valid_module/1 checks the result's evidence again on
    its own; a refused result throws `nanofil_error(Msg)`.
*/
:- module(checks, [checks_module/3, opt_checks/2]).

:- use_module(ir, [valid_module/1]).
:- use_module(check_reuse).
:- use_module(schedule).
:- use_module(half_check).

%! opt_checks(?Opt, ?Checks) is nondet.
%
%  Checks is the check selection of optimization level Opt (o0 or o1):
%  without -O every access keeps its full check; -O combines forward
%  facts and half checks (docs/forward.md, docs/half.md).
opt_checks(o0, reference).
opt_checks(o1, combined).

%! checks_module(+Checks, +Checked0, -Checked) is det.
%
%  Checked is the checked module Checked0 after the check passes of
%  Checks (--checks; docs/m7.md): reference keeps pizlonate's naive
%  checks; reuse deletes a check an earlier live one covers; renew
%  also replaces a dominated check by a test of only the
%  free and read-only flags; guard also puts a span test before a loop
%  and makes its checks renew_if; combined, the -O default, is forward
%  facts followed by half checks; hull, getter and extended add
%  renew_hull and facts across repeated getters (docs/forward.md). Each pass's result must pass its
%  *_refines identity check against its input, and the validator
%  (valid_module/1) then checks the result's evidence again on its own.
checks_module(reference, Checked, Checked).
checks_module(reuse, Checked0, Checked) :-
    reused_module(Checked0, Checked),
    once(valid_module(Checked)).

% Renew (docs/m7.md, round 4) runs after reuse: what reuse keeps, a
% dominating check may renew. Only the result is validated: a renew
% keeps its check's proof and index, so reuse's output is valid if it is.
checks_module(renew, Checked0, Checked) :-
    renewed_module(Checked0, Checked),
    once(valid_module(Checked)).

% Guards (docs/m7.md, round 5) run after renewal: a check renewal left
% in a loop may become a guarded renewal. Only the result is validated.
checks_module(guard, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(guard_checks(Checked1, Checked)),
    (   guard_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('range guards changed more than checks'))
    ),
    once(valid_module(Checked)).

% Hoisted bounds (docs/bounds.md) run after renewal: a full check
% renewal left in a loop may test its bounds against a limit taken
% before the loop. Only the result is validated.
checks_module(hoist, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(hoist_checks(Checked1, Checked)),
    (   hoist_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('hoisted bounds changed more than checks'))
    ),
    once(valid_module(Checked)).

% Scheduled checks (docs/schedule.md) run after renewal: a check widens
% over the bytes every path ahead needs from its base, and the checks it
% then covers are renewed at a distance. Only the result is validated.
checks_module(schedule, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(schedule_checks(Checked1, Checked)),
    (   schedule_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('scheduled checks changed more than checks'))
    ),
    once(valid_module(Checked)).

% Half checks (docs/half.md) run after renewal: a full check renewal left
% whose object an earlier check covers at one end tests only the other.
% Only the result is validated.
checks_module(half, Checked0, Checked) :-
    renewed_module(Checked0, Checked1),
    once(half_checks(Checked1, Checked)),
    (   half_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('half checks changed more than checks'))
    ),
    once(valid_module(Checked)).

% Forward facts (docs/forward.md): reuse that also serves heap pointer
% loads and covers a check by the hull of its object's live facts, then
% renewal at any distance (docs/schedule.md's renew from a related
% pointer's check). No trap moves. Only the result is validated.
checks_module(forward, Checked0, Checked) :-
    forwarded_module(forward, any, Checked0, Checked),
    once(valid_module(Checked)).

% Combined: forward facts, then half checks for what renewal left. Each
% stage keeps its own refines check. Only the result is validated.
checks_module(combined, Checked0, Checked) :-
    combined_module(forward, any, Checked0, Checked).
% Combined with renewal by the hull of two checks (hull), with facts kept
% across repeated getter calls (getter), or both (extended), opt-in
% (docs/forward.md). Each stage keeps its own refines check.
checks_module(hull, Checked0, Checked) :-
    combined_module(forward, hull, Checked0, Checked).
checks_module(getter, Checked0, Checked) :-
    combined_module(getter, any, Checked0, Checked).
checks_module(extended, Checked0, Checked) :-
    combined_module(getter, hull, Checked0, Checked).

combined_module(Reuse, Renew, Checked0, Checked) :-
    forwarded_module(Reuse, Renew, Checked0, Checked1),
    once(half_checks(Checked1, Checked)),
    (   half_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('half checks changed more than checks'))
    ),
    once(valid_module(Checked)).

forwarded_module(Reuse, Renew, Checked0, Checked) :-
    once(reuse_checks(Reuse, Checked0, Checked1)),
    (   reuse_refines(Reuse, Checked0, Checked1) -> true
    ;   throw(nanofil_error('forward reuse changed more than proofs'))
    ),
    once(renew_checks(Renew, Checked1, Checked)),
    (   renew_refines(Renew, Checked1, Checked) -> true
    ;   throw(nanofil_error('check renewal changed more than checks'))
    ).

renewed_module(Checked0, Checked) :-
    reused_module(Checked0, Checked1),
    once(renew_checks(Checked1, Checked)),
    (   renew_refines(Checked1, Checked) -> true
    ;   throw(nanofil_error('check renewal changed more than checks'))
    ).

reused_module(Checked0, Checked) :-
    once(reuse_checks(Checked0, Checked)),
    (   reuse_refines(Checked0, Checked) -> true
    ;   throw(nanofil_error('check reuse changed more than proofs'))
    ).
