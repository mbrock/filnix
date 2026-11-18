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

Definition hello_image_fn___lseek64 : func :=
  ir_fn{ "export" "__lseek64"(W %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_lseek"(W %"v0", L %"v2", W %"v4")
    => ret %"v9"
} }.
