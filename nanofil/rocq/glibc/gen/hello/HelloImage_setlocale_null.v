(** This file defines checked IR from the `setlocale_null` object of HelloImage.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn_setlocale_null_r : func :=
  ir_fn{ "export" "setlocale_null_r"(W %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    call %"v9" : W = $"setlocale_null_r_unlocked"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.
