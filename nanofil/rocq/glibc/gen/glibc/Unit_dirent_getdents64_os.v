(** This file defines checked IR from glibc’s `dirent/getdents64.os` object.
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

Definition fn___GI___getdents64 : func :=
  ir_fn{ "export" "__GI___getdents64"(W %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call %"v9" : W = $"zsys_getdents"(W %"v0", P %"v2", L %"v4");
    %"v10" : L = (Ext Sw) %"v9"
    => ret %"v10"
} }.
