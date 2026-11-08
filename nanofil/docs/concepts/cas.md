# cas

**nanofil** · an atomic pointer lives in an atomic box ([InvisiCaps](https://fil-c.org/invisicaps))

Compare-and-exchange, the one atomic read-modify-write term in the IR: `cas(T)` reads the T at an address and, if it equals Expected, writes New there, as one sequentially consistent step. Every other atomic operation is a loop of it (`c_lower:rmw//7`).

Its checked form `raw_cas(T, Off)` always keeps its own [[check]], and every cas ends every [[live-fact|live fact]]. For `p` it compares addresses only, so a New may replace a pointer of another [[capability]], as Fil-C's `filc_strong_cas_ptr` does. Atomics are outside the [[core-subset|core subset]]: the Rocq model has no cas.
