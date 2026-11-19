(** This file defines checked IR from glibc’s `debug/readonly-area.os` object.
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

Definition fn___readonly_area : func :=
  ir_fn{ "export" "__readonly_area"(P %"v0", L %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"__readonly_area_fallback"(P %"v0", L %"v2")
    => ret %"v6"
} }.
