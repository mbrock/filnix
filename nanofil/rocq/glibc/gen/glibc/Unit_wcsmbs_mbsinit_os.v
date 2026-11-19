(** This file defines checked IR from glibc’s `wcsmbs/mbsinit.os` object.
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

Definition fn___mbsinit : func :=
  ir_fn{ "export" "__mbsinit"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" : L = Ptoi %"v0";
    %"v4" : L = Ptoi #0;
    %"v5" : W = (Cmp Eq L) %"v3", %"v4"
    => br %"v5" ? "L7" : "L6";
  @"L6":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => goto "L7";
  @"L7" [%"v12" : W = phi("start" => #1, "L6" => %"v10")]:
    => ret %"v12"
} }.

Definition item_mbsinit : item :=
  (IAlias (a "mbsinit") (a "weak") (a "__mbsinit")).
