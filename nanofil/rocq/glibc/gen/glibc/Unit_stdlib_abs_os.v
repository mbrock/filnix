(** This file defines checked IR from glibc’s `stdlib/abs.os` object.
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

Definition fn_abs : func :=
  ir_fn{ "export" "abs"(W %"v0") -> (RClass W) {
  @"start":
    %"v6" : W = (Cmp Slt W) %"v0", #0
    => br %"v6" ? "L2" : "L4";
  @"L2":
    %"v8" : W = Neg %"v0"
    => goto "L4";
  @"L4" [%"v10" : W = phi("L2" => %"v8", "start" => %"v0")]:
    => ret %"v10"
} }.
