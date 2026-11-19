(** This file defines checked IR from glibc’s `string/strdup.os` object.
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

Definition fn___GI___strdup : func :=
  ir_fn{ "export" "__GI___strdup"(P %"v0") -> (RClass P) {
  @"start":
    call %"v4" : L = $"__GI_strlen"(P %"v0");
    %"v5" : L = Add %"v4", #1;
    call %"v8" : P = $"malloc"(L %"v5");
    %"v13" : L = Ptoi %"v8";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L11";
  @"L9":
    => ret #0;
  @"L11":
    call %"v20" : P = $"__GI_memcpy"(P %"v8", P %"v0", L %"v5")
    => ret %"v20"
} }.

Definition item_strdup : item :=
  (IAlias (a "strdup") (a "weak") (a "__GI___strdup")).
