(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to the decoded function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


Module HiAtexitSrcFiles.

Definition file_0 : string := "../bits/stdlib-bsearch.h".

Definition file_1 : string := "../csu/libc-start.c".

Definition file_2 : string := "../nptl/descr.h".

Definition file_3 : string := "../stdlib/stdbit.h".

Definition file_4 : string := "../sysdeps/generic/hugepages.h".

Definition file_5 : string := "../sysdeps/generic/string-fza.h".

Definition file_6 : string := "../sysdeps/generic/string-shift.h".

Definition file_7 : string := "../sysdeps/nptl/dl-tls_init_tp.c".

Definition file_8 : string := "../sysdeps/nptl/futex-internal.h".

Definition file_9 : string := "../sysdeps/nptl/libc_start_call_main.h".

Definition file_10 : string := "../sysdeps/nptl/pthreadP.h".

Definition file_11 : string := "../sysdeps/nptl/pthread_early_init.h".

Definition file_12 : string := "../sysdeps/unix/sysv/linux/_exit.c".

Definition file_13 : string := "../sysdeps/unix/sysv/linux/clock_gettime.c".

Definition file_14 : string := "../sysdeps/unix/sysv/linux/close_nocancel.c".

Definition file_15 : string := "../sysdeps/unix/sysv/linux/fstat64.c".

Definition file_16 : string := "../sysdeps/unix/sysv/linux/getrandom.c".

Definition file_17 : string := "../sysdeps/unix/sysv/linux/getrlimit64.c".

Definition file_18 : string := "../sysdeps/unix/sysv/linux/internal-signals.h".

Definition file_19 : string := "../sysdeps/unix/sysv/linux/isatty_nostatus.c".

Definition file_20 : string := "../sysdeps/unix/sysv/linux/lseek64.c".

Definition file_21 : string := "../sysdeps/unix/sysv/linux/write.c".

Definition file_22 : string := "../sysdeps/unix/sysv/linux/write_nocancel.c".

Definition file_23 : string := "../sysdeps/unix/sysv/linux/x86/dl-hwcap2.h".

Definition file_24 : string := "../sysdeps/unix/sysv/linux/x86/dl-minsigstacksize.h".

Definition file_25 : string := "../sysdeps/unix/sysv/linux/x86_64/dl-plt-rewrite.h".

Definition file_26 : string := "../sysdeps/x86/cacheinfo.h".

Definition file_27 : string := "../sysdeps/x86/cpu-features.c".

Definition file_28 : string := "../sysdeps/x86/dl-cacheinfo.h".

Definition file_29 : string := "../sysdeps/x86/get-isa-level.h".

Definition file_30 : string := "./arena.c".

Definition file_31 : string := "./dl-tunable-types.h".

Definition file_32 : string := "./dl-tunables.h".

Definition file_33 : string := "./libioP.h".

Definition file_34 : string := "rocq/glibc/hi_atexit.c".

Definition file_35 : string := "__fpending.c".

Definition file_36 : string := "atexit.c".

Definition file_37 : string := "ctype-info.c".

Definition file_38 : string := "cxa_atexit.c".

Definition file_39 : string := "cxa_thread_atexit_impl.c".

Definition file_40 : string := "dl-tunables.c".

Definition file_41 : string := "exit.c".

Definition file_42 : string := "ferror.c".

Definition file_43 : string := "filedoalloc.c".

Definition file_44 : string := "fileops.c".

Definition file_45 : string := "genops.c".

Definition file_46 : string := "init-first.c".

Definition file_47 : string := "init-misc.c".

Definition file_48 : string := "iofclose.c".

Definition file_49 : string := "ioputs.c".

Definition file_50 : string := "libc-cleanup.c".

Definition file_51 : string := "libc-tls.c".

Definition file_52 : string := "libc_early_init.c".

Definition file_53 : string := "makedev.c".

Definition file_54 : string := "malloc.c".

Definition file_55 : string := "memcpy.c".

Definition file_56 : string := "mempcpy.c".

Definition file_57 : string := "memrchr.c".

Definition file_58 : string := "nptl_deallocate_tsd.c".

Definition file_59 : string := "pthread_mutex_conf.c".

Definition file_60 : string := "stdfiles.c".

Definition file_61 : string := "strlen.c".

Definition file_62 : string := "strrchr.c".

Definition file_63 : string := "vtables.c".

End HiAtexitSrcFiles.
