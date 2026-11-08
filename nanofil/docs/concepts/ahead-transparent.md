# ahead-transparent

**nanofil** · the check scheduler, `filc-optimize-checks` ([FilPizlonator.cpp](https://github.com/pizlonator/fil-c/blob/deluge/llvm/lib/Transforms/Instrumentation/FilPizlonator.cpp))

An instruction is ahead-transparent when it may stand between a [[check_ahead]] and the access whose [[need]] it checks early: it reaches no safepoint, calls nothing, cannot free, and is not a division, whose fault would end the program other than by a Fil-C trap.

- `ir:ahead_transparent/1` is `ir:evidence_preserving/1` less `div`, `udiv`, `rem` and `urem`; Syntax.v's [ahead_transparent] is the same table. Not transparent: calls, allocation, getters, pointer stores, atomics, setjmp, va_arg. Poll edges, edges back and returns also end the scheduled region.
- A [[doomed]] frame that reaches a non-transparent instruction is `unchecked(ahead(Why))`, in `interp:insts_result/5` and in [step].

Why it is enough: what an early trap skips are scalar stores, loads and arithmetic, which nobody in the process observes once it has trapped ([schedule.md, nanofil's contract](../schedule.md#nanofils-contract)).

The subtlety: the check's own access counts too, so a check whose access is a pointer store or an atomic is never widened, where filcc would widen it.
