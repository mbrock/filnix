(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn_glibc_libc_start'23errno_handler : func :=
  mkFunc (a "glibc_libc_start#errno_handler") (a "local") RVoid [(W, (a "v0"))] [(mkBlock (a "start") [] [(Let (a "v2") P Copy [(Global (a "__libc_errno"))]);
      (Let (a "chk0") A (Check 0 4 Write 1) [(t "v2")]);
      (RawStore Ww 0 (t "v0") (t "chk0"))] JRetVoid)].
