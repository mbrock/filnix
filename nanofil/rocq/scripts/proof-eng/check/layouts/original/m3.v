From Nanofil Require Import Runtime.
From Glibc Require Import HiAtexitSafe HelloGlibcJoin.
Print Assumptions hi_atexit_initialized_entry.
Print Assumptions hi_atexit_never_panics.
Declare Module AuditRuntime : Runtime.
Module AuditHello := HelloGlibcJoin AuditRuntime.
Check AuditHello.hello_never_panics.
Print Assumptions AuditHello.hello_never_panics.
