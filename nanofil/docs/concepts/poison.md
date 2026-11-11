# poison / zegarmistrz

**Fil-C** · [projects/zegarmistrz](https://github.com/pizlonator/fil-c/tree/deluge/projects/zegarmistrz)

Poison is Zegarmistrz's byte- and value-level secret tracking for catching cryptographic timing side channels. Each byte in memory carries an 8-bit poison mask (`cannot-load`, `cannot-store`, `cannot-branch`, `cannot-index`, `cannot-var-time-op`, and three `clear-*-on-store` bits); each register or [[temporary]] carries the three value taint bits (`cannot-branch`, `cannot-index`, `cannot-var-time-op`), propagated by bitwise OR through arithmetic and cleared by self-zeroing idioms (`xor r, r`, `sub r, r`).

A poisoned run faults as soon as a value marked `cannot-branch` drives control flow (or a Fil-C bounds [[check]]), a value marked `cannot-index` enters a memory address, or a value marked `cannot-var-time-op` enters a variable-latency instruction (`div`, `rem`, floating point).

- In nanofil's Rocq spike ([Poison.v](../../rocq/spikes/Poison.v)), [pstep] pairs Campaign 1's [Semantics.step] with a shadow state [pstate] over [m_bytes], [m_aux] and the [[ssa|SSA]] environment, erasing to [Semantics.step] on every non-trapping transition ([pstep_erases]).
- When secrets are marked with all three value bits ([taint_all]) and `pol_check_branches` is enabled, one non-trapping poisoned run witnesses two-run constant-time noninterference across every secret input ([prun_ct_sound], applied to AES `SubBytes` in [subbytes_ct_constant_time]).

See [How zegarmistrz works](../zegarmistrz.md) and [Poison and constant time in Rocq](../poison.md).
