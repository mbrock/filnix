From Stdlib Require Import ZArith List.
From Nanofil Require Import Runtime.
From Glibc Require Import HelloGlibcJoin HiAtexitSafe.
Set Printing Depth 10000.
Set Printing Implicit.
Declare Module AuditRuntime : Runtime.
Module AuditHello := HelloGlibcJoin AuditRuntime.
Check AuditHello.hello_never_panics.
Print Assumptions AuditHello.hello_never_panics.
Check hi_atexit_initialized_entry.
Check hi_atexit_never_panics.
Print Assumptions hi_atexit_initialized_entry.
Print Assumptions hi_atexit_never_panics.
