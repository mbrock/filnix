(** This file defines checked IR from glibc’s `wcsmbs/wmemmove.os` object.
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

Definition fn___wmemmove : func :=
  ir_fn{ "export" "__wmemmove"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v9" : L = Shl %"v4", #2;
    call %"v10" : P = $"__GI_memmove"(P %"v0", P %"v2", L %"v9")
    => ret %"v10"
} }.
