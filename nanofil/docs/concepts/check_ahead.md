# check_ahead / scheduled check

**nanofil** · the check scheduler hoists and merges checks, `filc-optimize-checks` ([compiler](https://fil-c.org/compiler), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp))

`check_ahead(Lo, Hi, Rights, Align, AHi)` is a check of `[Lo, Hi)` whose own access needs only `[Lo, AHi)`: the bytes `[AHi, Hi)` are checked early for later accesses through the same base, as filcc's check scheduler does. It may trap earlier than the reference program, but only on runs that would trap later anyway.

- Made by `schedule:schedule_checks/2` under `--checks=schedule` (opt-in); emitted as a plain check of the whole range.
- Accepted by `ir:ahead_justified/3` where, right after its access, the [[need]] of P's [[exact-base|exact base]] B (P = B + K) is at least K + Hi, the access is [[ahead-transparent]], K and K + Lo are [[near-offset|near offsets]], and the function has no setjmp. Rocq: [ahead_justified] in Validate.v, read back by Ahead.v's [ahead_accepted].
- interp.pl tests `[Lo, AHi)` first and traps as a check would; if only the rest fails, the frame is [[doomed]].

The subtlety: the bound on K + Lo came from a counterexample in which the check's start wrapped onto the need's end modulo 2^64 ([rocq.md, A need past 2^64](../rocq.md#a-need-past-264)).

See [schedule.md](../schedule.md).
