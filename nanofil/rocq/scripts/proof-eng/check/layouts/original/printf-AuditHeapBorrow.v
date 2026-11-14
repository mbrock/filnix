From Nanofil Require Import Runtime Logic.
From Glibc Require Import PrintfBufferXsputnHeapBorrow.
Module LG := Logic InterpRuntime.
Module C := PrintfBufferXsputnHeapBorrowOn InterpRuntime LG.
Print Assumptions C.printf_heap_vtable_borrow.
Check C.printf_heap_vtable_borrow.
