(** This file defines checked IR from glibc’s `string/strcpy.os` object.
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

Definition fn___GI_strcpy : func :=
  ir_fn{ "export" "__GI_strcpy"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"__GI___stpcpy"(P %"v0", P %"v2")
    => ret %"v0"
} }.
