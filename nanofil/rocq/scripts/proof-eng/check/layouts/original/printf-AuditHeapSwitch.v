From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnHeapSwitch.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnHeapSwitchOn InterpRuntime LG.
Print Assumptions C.wp_printf_xsputn_heap_switch.
Check C.wp_printf_xsputn_heap_switch.
