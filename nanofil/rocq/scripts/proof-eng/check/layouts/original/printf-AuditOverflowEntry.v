From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferOverflowEntry.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferOverflowEntryOn InterpRuntime LG.
Print Assumptions C.wp_printf_overflow_entry.
Check C.wp_printf_overflow_entry.
