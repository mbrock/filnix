(** This file defines checked IR from the `streq` object of HelloImage.
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

Definition fn_streq : func :=
  ir_fn{ "export" "streq"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"strcmp"(P %"v0", P %"v2");
    %"v7" : W = (Cmp Eq W) %"v6", #0
    => ret %"v7"
} }.
