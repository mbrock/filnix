From Nanofil Require Import Runtime Logic.
From Glibc Require Import GetoptLongArg PrintfBufferOverflowHeapSwitch.
From Glibc Require GetoptLongArg GetoptLongDiag GetoptLongEq GetoptLongExact GetoptLongPre GetoptLongReq GetoptLongScan GetoptLongStore GetoptLongTail PrintfBufferOverflowHeapSwitch.
From Glibc Require Import Fix.
Module HLG := LG0.
Print Assumptions GetoptLongArg.wp_long_found.
Print Assumptions GetoptLongPre.wp_long_pre.
Print Assumptions GetoptLongEq.wp_long_eq.
Print Assumptions GetoptLongReq.wp_long_req.
Print Assumptions GetoptLongTail.wp_long_next.
Print Assumptions GetoptLongTail.wp_long_miss_tail.
Print Assumptions GetoptLongStore.wp_long_store.
Print Assumptions GetoptLongStore.int_at_store.
Print Assumptions GetoptLongDiag.wp_getopt_ldiag_noarg.
Print Assumptions GetoptLongDiag.wp_getopt_ldiag_missing.
Print Assumptions GetoptLongExact.wp_long_exact_loop.
Print Assumptions GetoptLongScan.wp_getopt_long_scan.
Print Assumptions GetoptLongScan.wp_long_scan_loop.
Print Assumptions GetoptLongScan.wp_half_check_read_dq.
Print Assumptions PrintfBufferOverflowHeapSwitch.wp_printf_overflow_heap_switch.
