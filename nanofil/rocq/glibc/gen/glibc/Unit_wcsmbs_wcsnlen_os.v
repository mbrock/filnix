(** This file defines checked IR from glibc’s `wcsmbs/wcsnlen.os` object.
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

Definition fn___wcsnlen : func :=
  ir_fn{ "export" "__wcsnlen"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    call %"v7" : P = $"__GI___wmemchr"(P %"v0", W #0, L %"v2");
    %"v12" : L = Ptoi %"v7";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L8" : "L10";
  @"L8":
    %"v17" : L = Ptoi %"v0";
    %"v18" : L = Sub %"v12", %"v17";
    %"v19" : L = Div %"v18", #4
    => goto "L10";
  @"L10" [%"pr.1" : L = phi("L8" => %"v19", "start" => %"v2")]:
    => ret %"pr.1"
} }.
