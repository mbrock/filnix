(** This file defines checked IR from glibc’s `string/memset.os` object.
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

Definition fn___GI_memset : func :=
  ir_fn{ "export" "__GI_memset"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    call void $"zmemset"(P %"v0", W %"v2", L %"v4")
    => ret %"v0"
} }.

Definition item_memset : item :=
  (IAlias (a "memset") (a "export") (a "__GI_memset")).
