(** This file defines checked IR from glibc’s `stdlib/atexit.oS` object.
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

Definition fn_atexit : func :=
  ir_fn{ "export" "atexit"(P %"v0") -> (RClass W) {
  @"start":
    call %"v3" : W = $"__cxa_atexit"(P %"v0", P #0, P #0)
    => ret %"v3"
} }.
