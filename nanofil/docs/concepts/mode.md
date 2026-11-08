# mode

A module's mode is plain or filc: filc if it uses anything Fil-C-specific (a `p`, a call to an external function, ...), plain otherwise, read off its contents (`ir:module_mode/2`).

Plain mode is C without capabilities: an access outside every live allocation is `ub`, not a [[trap]]. The Rocq model covers filc mode only; plain mode is outside the [[core-subset|core subset]].
