From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnSwitch.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnSwitchOn InterpRuntime LG.
Print Assumptions C.wp_printf_xsputn_switch_null.
Check C.wp_printf_xsputn_switch_null.
Print Assumptions C.wp_printf_xsputn_switch_owned.
Check C.wp_printf_xsputn_switch_owned.
