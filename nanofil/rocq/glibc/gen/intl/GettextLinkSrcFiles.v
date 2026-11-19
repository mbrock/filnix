(** These tables connect checked function bodies to C declarations and source lines.
    Names and locations support annotations and diagnostic messages, not soundness premises.
    Natural-loop headers provide optional cuts for symbolic execution; any cut list is sound.
    Live sets and memory footprints guide execution but cannot justify a memory access.
    Computation checks that every recorded block label belongs to its function.
    The code generator reproduces this file from the capture; do not edit it. *)

From Stdlib Require Import String List Bool NArith ZArith.
From Glibc Require Import CodePrelude.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.


Module GettextLinkSrcFiles.

Definition file_0 : string := "../bits/byteswap.h".

Definition file_1 : string := "../include/time.h".

Definition file_2 : string := "../sysdeps/nptl/futex-internal.h".

Definition file_3 : string := "./eval-plural.h".

Definition file_4 : string := "./pthread_rwlock_common.c".

Definition file_5 : string := "dcgettext.c".

Definition file_6 : string := "dcigettext.c".

Definition file_7 : string := "localename.c".

Definition file_8 : string := "memcpy.c".

Definition file_9 : string := "mempcpy.c".

Definition file_10 : string := "pthread_rwlock_rdlock.c".

Definition file_11 : string := "pthread_rwlock_unlock.c".

Definition file_12 : string := "stpcpy.c".

Definition file_13 : string := "tsearch.c".

End GettextLinkSrcFiles.
