(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.


Module HiAtexitSrcFiles.

Definition file_0 : string := "../nptl/descr.h".

Definition file_1 : string := "../stdlib/stdbit.h".

Definition file_2 : string := "../sysdeps/nptl/pthreadP.h".

Definition file_3 : string := "../sysdeps/unix/sysv/linux/_exit.c".

Definition file_4 : string := "../sysdeps/unix/sysv/linux/close_nocancel.c".

Definition file_5 : string := "../sysdeps/unix/sysv/linux/fstat64.c".

Definition file_6 : string := "../sysdeps/unix/sysv/linux/isatty_nostatus.c".

Definition file_7 : string := "../sysdeps/unix/sysv/linux/lseek64.c".

Definition file_8 : string := "../sysdeps/unix/sysv/linux/write.c".

Definition file_9 : string := "../sysdeps/unix/sysv/linux/write_nocancel.c".

Definition file_10 : string := "./libioP.h".

Definition file_11 : string := "rocq/glibc/hi_atexit.c".

Definition file_12 : string := "__fpending.c".

Definition file_13 : string := "atexit.c".

Definition file_14 : string := "cxa_atexit.c".

Definition file_15 : string := "cxa_thread_atexit_impl.c".

Definition file_16 : string := "exit.c".

Definition file_17 : string := "ferror.c".

Definition file_18 : string := "filedoalloc.c".

Definition file_19 : string := "fileops.c".

Definition file_20 : string := "genops.c".

Definition file_21 : string := "iofclose.c".

Definition file_22 : string := "ioputs.c".

Definition file_23 : string := "libc-cleanup.c".

Definition file_24 : string := "makedev.c".

Definition file_25 : string := "malloc.c".

Definition file_26 : string := "memcpy.c".

Definition file_27 : string := "mempcpy.c".

Definition file_28 : string := "stdfiles.c".

Definition file_29 : string := "strlen.c".

Definition file_30 : string := "vtables.c".

End HiAtexitSrcFiles.
