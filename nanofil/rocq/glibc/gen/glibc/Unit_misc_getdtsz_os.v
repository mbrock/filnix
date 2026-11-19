(** This file defines checked IR from glibc’s `misc/getdtsz.os` object.
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

Definition fn___getdtablesize : func :=
  ir_fn{ "export" "__getdtablesize"() -> (RClass W) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #7, P %"v0");
    %"v5" : W = (Cmp Slt W) %"v4", #0
    => br %"v5" ? "L3" : "L2";
  @"L2":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v6" : L = (RawLoad LdL 0) %"chk0"
    => goto "L3";
  @"L3" [%"v7" : L = phi("L2" => %"v6", "start" => #256)]:
    => ret %"v7"
} }.
