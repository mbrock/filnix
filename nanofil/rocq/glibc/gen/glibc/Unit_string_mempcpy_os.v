(** This file defines checked IR from glibc’s `string/mempcpy.os` object.
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

Definition fn___GI___mempcpy : func :=
  ir_fn{ "export" "__GI___mempcpy"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    call %"v9" : P = $"__GI_memcpy"(P %"v0", P %"v2", L %"v4");
    %"v11" = %"v9" +p %"v4"
    => ret %"v11"
} }.

Definition item___GI_mempcpy : item :=
  (IAlias (a "__GI_mempcpy") (a "export") (a "__GI___mempcpy")).

Definition item_mempcpy : item :=
  (IAlias (a "mempcpy") (a "export") (a "__GI___mempcpy")).
