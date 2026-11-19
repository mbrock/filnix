(** This file defines checked IR from the `strnlen1` object of HelloImage.
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

Definition fn_strnlen1 : func :=
  ir_fn{ "export" "strnlen1"(P %"v0", L %"v2") -> (RClass L) {
  @"start":
    call %"v7" : P = $"memchr"(P %"v0", W #0, L %"v2");
    %"v12" : L = Ptoi %"v7";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Ne L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L9";
  @"L8":
    %"v18" : L = Ptoi %"v0";
    %"v19" : L = Sub %"v12", %"v18";
    %"v20" : L = Add %"v19", #1
    => ret %"v20";
  @"L9":
    => ret %"v2"
} }.
