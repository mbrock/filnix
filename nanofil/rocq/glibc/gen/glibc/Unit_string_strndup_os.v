(** This file defines checked IR from glibc’s `string/strndup.os` object.
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

Definition fn___GI___strndup : func :=
  ir_fn{ "export" "__GI___strndup"(P %"v0", L %"v2") -> (RClass P) {
  @"start":
    call %"v7" : L = $"__GI___strnlen"(P %"v0", L %"v2");
    %"v10" : L = Add %"v7", #1;
    call %"v11" : P = $"malloc"(L %"v10");
    %"v16" : L = Ptoi %"v11";
    %"v17" : L = Ptoi #0;
    %"v18" : W = (Cmp Eq L) %"v16", %"v17"
    => br %"v18" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"v22" = %"v11" +p %"v7";
    %"chk0" : A = (Check 0 1 Write 1) %"v22";
    store Wb [%"chk0" + 0] <- #0;
    call %"v26" : P = $"__GI_memcpy"(P %"v11", P %"v0", L %"v7")
    => ret %"v26"
} }.
