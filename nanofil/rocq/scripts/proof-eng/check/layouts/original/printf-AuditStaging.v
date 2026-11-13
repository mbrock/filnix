From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnStaging.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnStagingOn InterpRuntime LG.
Print Assumptions C.wp_printf_xsputn_staging.
Check C.wp_printf_xsputn_staging.
