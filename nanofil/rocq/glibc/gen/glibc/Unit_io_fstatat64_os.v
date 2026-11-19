(** This file defines checked IR from glibc’s `io/fstatat64.os` object.
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

Definition fn___GI___fstatat64 : func :=
  ir_fn{ "export" "__GI___fstatat64"(W %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    call %"v12" : W = $"zsys_fstatat"(W %"v0", P %"v2", P %"v4", W %"v6")
    => ret %"v12"
} }.
