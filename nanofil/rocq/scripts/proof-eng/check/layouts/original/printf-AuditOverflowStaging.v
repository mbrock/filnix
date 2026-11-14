From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferOverflowStaging.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferOverflowStagingOn InterpRuntime LG.
Print Assumptions C.wp_printf_overflow_staging.
Check C.wp_printf_overflow_staging.
