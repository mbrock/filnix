(** This file defines checked IR from glibc’s `io/read.os` object.
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

Definition fn___GI___libc_read : func :=
  ir_fn{ "export" "__GI___libc_read"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : L = $"zsys_read"(W %"v0", P %"v2", L %"v4")
    => ret %"v9"
} }.

Definition item___GI___read : item :=
  (IAlias (a "__GI___read") (a "export") (a "__GI___libc_read")).
