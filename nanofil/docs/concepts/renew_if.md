# renew_if

**nanofil**

A [[renew]] whose bounds come from a [[guard]]: `renew_if(Lo, Hi, Rights, Align)` of `[P, G]` is exactly a check of P, but where the [[span_test|span test]] G passed it natively tests only the flags and alignment, and where G failed it runs the full check out of line. The validator accepts it through `ir:guard_covers/5`, following P's [[guard-chain|guard chain]] (`ir:guard_chain/3`).

Rocq: the op [RenewIf]; Guard.v's [renew_if_not_unchecked] and, along runs, [run_guard_checked].
