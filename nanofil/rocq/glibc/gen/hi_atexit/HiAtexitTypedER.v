(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_fn_glibc_libc_start'23errno_handler : func :=
  ir_fn{ "local" "glibc_libc_start#errno_handler"(W %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk0" + 0] <- %"v0"
    => ret void
} }.
