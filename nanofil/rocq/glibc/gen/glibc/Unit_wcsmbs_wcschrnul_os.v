(** This file defines checked IR from glibc’s `wcsmbs/wcschrnul.os` object.
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

Definition fn___wcschrnul : func :=
  ir_fn{ "export" "__wcschrnul"(P %"v0", W %"v2") -> (RClass P) {
  @"start":
    => goto "L4";
  @"L4" [%"pr.1" : P = phi("start" => %"v0", "L11" => %"v19")]:
    %"chk0" : A = (Check 0 4 Read 1) %"pr.1";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = (Cmp Ne W) %"v8", #0
    => br %"v9" ? "L5" : "L6";
  @"L5":
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v16" : W = (Cmp Eq W) %"v14", %"v2"
    => br %"v16" ? "L6" : "L11";
  @"L11":
    %"v19" = %"pr.1" +p #4
    => goto poll "L4";
  @"L6":
    => ret %"pr.1"
} }.
