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

Definition hello_image_fn_xcharalloc : func :=
  ir_fn{ "export" "xcharalloc"(L %"v0") -> (RClass P) {
  @"start":
    call %"v7" : P = $"xmalloc"(L %"v0")
    => ret %"v7"
} }.
