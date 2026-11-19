(** This file defines checked IR from glibc’s `string/strrchr.os` object.
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

Definition fn___GI_strrchr : func :=
  ir_fn{ "export" "__GI_strrchr"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI_strlen"(P %"v0");
    %"v8" : L = Add %"v7", #1;
    call %"v9" : P = $"__GI___memrchr"(P %"v0", W %"v2", L %"v8")
    => ret %"v9"
} }.

Definition item_strrchr : item :=
  (IAlias (a "strrchr") (a "export") (a "__GI_strrchr")).
