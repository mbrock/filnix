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

Definition hi_fn___GI___cxa_atexit : func :=
  ir_fn{ "export" "__GI___cxa_atexit"(P %"v0", P %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"v9" : P = Copy $"__exit_funcs";
    call %"v10" : W = $"__internal_atexit"(P %"v0", P %"v2", P %"v4", P %"v9")
    => ret %"v10"
} }.
