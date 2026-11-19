(** This file defines checked IR from the `c32isprint` object of HelloImage.
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

Definition fn_c32isprint : func :=
  ir_fn{ "export" "c32isprint"(W %"v0") -> (RClass W) {
  @"start":
    call %"v3" : W = $"iswprint"(W %"v0")
    => ret %"v3"
} }.
