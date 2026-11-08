# flight

**nanofil** · the [[flight-pointer|flight pointer]], a lower and an intval in SSA ([InvisiCaps](https://fil-c.org/invisicaps#flightptr))

A flight builds a pointer from two independent sources: `flight(D, Op, Args, Lower)` computes D's address with `copy`, `add` or `sub` over `l` values and pointer addresses, and takes its [[capability]] from the pointer Lower names, or none (`pizlonate:flight_inst/2`). Making the pair proves nothing about access; no check, getter, memory access or safepoint happens inside it.

- Rocq: the instruction [Flight]; [flight_cap] reads its capability. A flight is [replayable]: its capability is its lower donor's ([[replay]]).
- Chains of flights are what the validator follows: [[guard-chain|guard chains]] and [[lower-chain|lower chains]].
