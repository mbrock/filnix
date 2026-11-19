(** This file defines checked IR from glibc’s `io/stat64.os` object.
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

Definition fn___GI___stat64 : func :=
  ir_fn{ "export" "__GI___stat64"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v7" : W = $"__GI___fstatat64"(W #4294967196, P %"v0", P %"v2", W #0)
    => ret %"v7"
} }.
