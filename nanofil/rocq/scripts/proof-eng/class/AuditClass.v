From Stdlib Require Import ZArith List.
From Nanofil Require Import Runtime.
From Glibc Require Import HelloGlibcJoin HiAtexitSafe.
Set Printing Depth 10000.
Set Printing Implicit.
Check @hello_never_panics.
Print Assumptions hello_never_panics.
Section SecondRuntime.
Context (other : R.RuntimeClass).
Definition hello_other := @hello_never_panics other.
End SecondRuntime.
Print Assumptions hello_other.
Definition hello_interp := @hello_never_panics interp_runtime.
Print Assumptions hello_interp.
Declare Module AuditRuntime : Runtime.
Module AuditClass := ClassOf AuditRuntime.
Definition hello_abstract := @hello_never_panics AuditClass.instance.
Print Assumptions hello_abstract.
Check hi_atexit_initialized_entry.
Check hi_atexit_never_panics.
Print Assumptions hi_atexit_initialized_entry.
Print Assumptions hi_atexit_never_panics.
