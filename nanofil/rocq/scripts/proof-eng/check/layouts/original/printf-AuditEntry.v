From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnEntry.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnEntryOn InterpRuntime LG.
Print Assumptions C.wp_printf_xsputn_entry.
Check C.wp_printf_xsputn_entry.
