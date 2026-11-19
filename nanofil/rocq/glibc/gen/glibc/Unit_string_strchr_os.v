(** This file defines checked IR from glibc’s `string/strchr.os` object.
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

Definition fn___GI_strchr : func :=
  ir_fn{ "export" "__GI_strchr"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    call %"v7" : P = $"__GI___strchrnul"(P %"v0", W %"v2");
    %"chk0" : A = (Check 0 1 Read 1) %"v7";
    %"v12" : W = (RawLoad (LdNarrow Ub) 0) %"chk0";
    %"v14" : W = (Ext Ub) %"v2";
    %"v15" : W = (Cmp Eq W) %"v12", %"v14"
    => br %"v15" ? "L10" : "L9";
  @"L9":
    => goto "L10";
  @"L10" [%"v17" : P = phi("L9" => #0, "start" => %"v7")]:
    => ret %"v17"
} }.

Definition item_strchr : item :=
  (IAlias (a "strchr") (a "export") (a "__GI_strchr")).
