From Nanofil Require Import Runtime Logic.
From Glibc Require Import GetoptLongArg PrintfBufferOverflowHeapSwitch.
Module LG := Logic InterpRuntime.
Module A := GetoptLongArgOn InterpRuntime LG.
Module P := A.LP.
Module E := P.LQE.
Module Q := E.LQ.
Module T := Q.LL.
Module S := T.LT.
Module D := S.LD.
Module X := D.LE.
Module N := X.LS.
Module HS := PrintfBufferOverflowHeapSwitchOn InterpRuntime LG.
Print Assumptions A.wp_long_found.
Print Assumptions P.wp_long_pre.
Print Assumptions E.wp_long_eq.
Print Assumptions Q.wp_long_req.
Print Assumptions T.wp_long_next.
Print Assumptions T.wp_long_miss_tail.
Print Assumptions S.wp_long_store.
Print Assumptions S.int_at_store.
Print Assumptions D.wp_getopt_ldiag_noarg.
Print Assumptions D.wp_getopt_ldiag_missing.
Print Assumptions X.wp_long_exact_loop.
Print Assumptions N.wp_getopt_long_scan.
Print Assumptions N.wp_long_scan_loop.
Print Assumptions N.wp_half_check_read_dq.
Print Assumptions HS.wp_printf_overflow_heap_switch.
