# asm_fixed

An inline asm statement of one fixed-register instruction: `asm_fixed(M, Ins, Outs)` runs M (`cpuid`, `xgetbv`, `rdtsc`, `rdtscp`, or the operand-free `lfence`, `sfence` and `pause`) on `w` inputs in the registers M reads, defining `w` temporaries from the registers it writes (`ir:asm_fixed_regs/3`, [asm-fixed.md](../asm-fixed.md)).

Other inline asm is a blank-template barrier (its operands are evaluated, nothing else), a call to `zsafety_error` where filcc would refuse it at run time, or refused. The [[interpreter]] stops at `unknown(asm(M, Xs))`, since only the machine knows the results; it is outside the [[core-subset|core subset]].
