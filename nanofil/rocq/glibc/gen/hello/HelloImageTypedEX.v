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

Definition hello_image_fn___GI__exit : func :=
  ir_fn{ "export" "__GI__exit"(W %"v0") -> RVoid {
  @"start":
    call void $"zsys_exit_hard"(W %"v0")
    => ret void
} }.

Definition hello_image_fn___GI_exit : func :=
  ir_fn{ "export" "__GI_exit"(W %"v0") -> RVoid {
  @"start":
    %"v3" : P = Copy $"__exit_funcs";
    call void $"__run_exit_handlers"(W %"v0", P %"v3", W #1, W #1)
    => ret void
} }.
