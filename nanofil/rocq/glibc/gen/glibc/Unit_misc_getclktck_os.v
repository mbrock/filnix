(** This file defines checked IR from glibc’s `misc/getclktck.os` object.
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

Definition fn___getclktck : func :=
  ir_fn{ "export" "__getclktck"() -> (RClass W) {
  @"start":
    %"v0" : P = Copy $"_dl_clktck";
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v1" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => br %"v1" ? "L4" : "L3";
  @"L3":
    => goto "L4";
  @"L4" [%"v5" : W = phi("L3" => #100, "start" => %"v1")]:
    => ret %"v5"
} }.
