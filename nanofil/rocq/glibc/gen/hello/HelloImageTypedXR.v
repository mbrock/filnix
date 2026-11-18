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

Definition hello_image_fn_xrealloc : func :=
  ir_fn{ "export" "xrealloc"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"realloc"(P %"v0", L %"v2");
    %"iw_1.v6" : L = Ptoi %"v6";
    %"iw_1.v8" : W = (Cmp Eq L) %"iw_1.v6", #0
    => br %"iw_1.v8" ? "iw_1.L2" : "iw_1.join";
  @"iw_1.L2":
    call void $"xalloc_die"()
    => goto "iw_1.join";
  @"iw_1.join":
    => ret %"v6"
} }.
