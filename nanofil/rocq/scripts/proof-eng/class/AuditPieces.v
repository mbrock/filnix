From Nanofil Require Import Runtime.
From Glibc Require Import GlibcLogic.
Check @pieces_never_panics.
Print Assumptions pieces_never_panics.
Definition pieces_interp := @pieces_never_panics interp_runtime.
Print Assumptions pieces_interp.
Declare Module AuditRuntime : Runtime.
Module AuditClass := ClassOf AuditRuntime.
Definition pieces_abstract := @pieces_never_panics AuditClass.instance.
Print Assumptions pieces_abstract.
