From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnCaller.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnCallerOn InterpRuntime LG.
Print Assumptions C.wp_printf_xsputn_caller.
Check C.wp_printf_xsputn_caller.
