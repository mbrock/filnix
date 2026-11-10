# touch

**nanofil**

A touch uses a vector check's [[proof]] without accessing anything: `touch(tmp(Q))` follows the [[check]] that an [[access]] pizlonates to, so the check has its covering use (`pizlonate:checked_access/4`). It is `ir:evidence_preserving/1` and in the [[core-subset|core subset]]: the model steps it as `interp.pl` does, doing nothing (Semantics.v's `inst_step`, `Touch`).
