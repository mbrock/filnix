From Nanofil Require Import Runtime Logic.
From Glibc Require Import GetoptLongMiss PrintfBufferOverflowHeapCaller.
From Glibc Require GetoptLongMiss GetoptLongMissOnly GetoptLongUnrec PrintfBufferOverflowHeapCaller.
From Glibc Require Import Fix.
Module HLG := LG0.
Print Assumptions GetoptLongMiss.wp_long_miss.
Print Assumptions GetoptLongMissOnly.wp_long_miss_only.
Print Assumptions GetoptLongUnrec.wp_long_unrec.
Print Assumptions PrintfBufferOverflowHeapCaller.wp_printf_overflow_heap_caller.
Check GetoptLongMiss.wp_long_miss.
Check PrintfBufferOverflowHeapCaller.wp_printf_overflow_heap_caller.
