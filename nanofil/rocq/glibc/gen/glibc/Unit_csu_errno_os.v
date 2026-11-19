(** This file defines checked IR from glibc’s `csu/errno.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___libc_errno : item :=
  (IAlias (a "__libc_errno") (a "export") (a "errno")).

Definition item_errno : item :=
  (IData (a "errno") (LTls (a "export")) 4 [(Zero 4)]).
