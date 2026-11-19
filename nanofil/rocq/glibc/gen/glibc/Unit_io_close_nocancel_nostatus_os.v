(** This file defines checked IR from glibc’s `io/close_nocancel_nostatus.os` object.
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

Definition fn___GI___close_nocancel_nostatus : func :=
  ir_fn{ "export" "__GI___close_nocancel_nostatus"(W %"v0") -> RVoid {
  @"start":
    call %"v3" : W = $"zsys_close"(W %"v0")
    => ret void
} }.
