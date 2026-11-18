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

Definition hello_image_fn___GI_abort : func :=
  ir_fn{ "export" "__GI_abort"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_abort#str.268";
    call void $"zerror"(P %"v0")
    => goto "L2";
  @"L2":
    %"v4" : P = Copy $"glibc_abort#str.269";
    call void $"zsafety_error"(P %"v4")
    => goto poll "L2"
} }.

Definition hello_image_fn_abs : func :=
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
