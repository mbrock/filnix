(** This file defines checked IR from the `mbszero` object of HelloImage.
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

Definition fn_mbszero : func :=
  ir_fn{ "export" "mbszero"(P %"v0") -> RVoid {
  @"start":
    call %"v3" : P = $"memset"(P %"v0", W #0, L #8)
    => ret void
} }.
