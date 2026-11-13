From Nanofil Require Import Runtime Logic.
From Glibc Require Import GetoptLongMiss PrintfBufferOverflowHeapCaller.
Module LG := Logic InterpRuntime.
Module M := GetoptLongMissOn InterpRuntime LG.
Module C := PrintfBufferOverflowHeapCallerOn InterpRuntime LG.
Print Assumptions M.wp_long_miss.
Print Assumptions M.LOM.wp_long_miss_only.
Print Assumptions M.LOM.LU.wp_long_unrec.
Print Assumptions C.wp_printf_overflow_heap_caller.
Check M.wp_long_miss.
Check C.wp_printf_overflow_heap_caller.
