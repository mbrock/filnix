From Nanofil Require Import Runtime.
From Glibc Require Import HiAtexitSafe HelloGlibcJoin.
From Glibc Require HelloGlibcJoin.
Print Assumptions hi_atexit_initialized_entry.
Print Assumptions hi_atexit_never_panics.
Declare Module AuditRuntime : Runtime.
Check HelloGlibcJoin.hello_never_panics.
Print Assumptions HelloGlibcJoin.hello_never_panics.
