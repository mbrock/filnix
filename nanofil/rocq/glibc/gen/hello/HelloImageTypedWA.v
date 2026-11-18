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

Definition hello_image_fn___GI___wait4 : func :=
  ir_fn{ "export" "__GI___wait4"(W %"v0", P %"v2", W %"v4", P %"v6") -> (RClass W) {
  @"start":
    call %"v12" : W = $"zsys_wait4"(W %"v0", P %"v2", W %"v4", P %"v6")
    => ret %"v12"
} }.

Definition hello_image_fn___GI___waitpid : func :=
  ir_fn{ "export" "__GI___waitpid"(W %"v0", P %"v2", W %"v4") -> (RClass W) {
  @"start":
    call %"v9" : W = $"__GI___wait4"(W %"v0", P %"v2", W %"v4", P #0)
    => ret %"v9"
} }.
