# check

**Fil-C** · [GIMSO](https://fil-c.org/gimso), [compiler](https://fil-c.org/compiler), [FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp)

An access check: `check(Lo, Hi, Rights, Align)` of a pointer P traps unless P's [[capability]] permits [[rights|Rights]] on `[P+Lo, P+Hi)` with P+Lo Align-aligned, and otherwise yields P as a [[proof]] of class `a`. `check_local` does the same for a named local, and `check_function` yields a function proof of class `f` (`ir:op_kind/2`, `pizlonate:checked_access/4`).

- Rocq: the ops [Check], [CheckLocal] and [CheckFunction] in Syntax.v; the test itself is [cap_access_res] (`interp:cap_access_res/7`).
- A check is followed at once by the access it covers ([[covered-access|coverage]]); later accesses may reuse it while its [[live-fact|live fact]] holds, and the [[reuse]] forms trust it longer.

Upstream FilPizlonator schedules bounds checks and removes redundant ones; nanofil's [[reuse]] forms and [[check_ahead]] are its versions, each accepted only by the [[validator]].

Because a [[trap]] is terminal, a check is a pure assertion: one proved never to fail can be deleted.
