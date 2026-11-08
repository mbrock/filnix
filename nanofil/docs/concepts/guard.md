# guard

Range guards, `--checks=guard`: a [[span_test|span test]] before a loop proves its accesses' bounds once, and the loop's checks become [[renew_if]], which tests only the flags and alignment when the guard passed and runs the full check out of line otherwise (`check_reuse:guard_checks/2`, [m7.md, Range guards (round 5)](../m7.md#range-guards-round-5-contract-reviewed)).

The validator accepts each renew_if through `ir:guard_covers/5`; Rocq transcribes [guard_covers], and Guard.v proves that no run of a valid module makes one `unchecked` ([run_guard_checked]).
