(** This file defines checked IR from glibc’s `posix/get_child_max.os` object.
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

Definition fn___get_child_max : func :=
  ir_fn{ "export" "__get_child_max"() -> (RClass L) {
  @"start":
    %"v0" : P = (Alloc 8) #16;
    call %"v4" : W = $"__GI___getrlimit"(W #6, P %"v0");
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => br %"v5" ? "L6" : "L7";
  @"L6":
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v8" : L = (RawLoad LdL 0) %"chk0";
    %"v11" : W = (Cmp Ne L) %"v8", #18446744073709551615
    => goto "L7";
  @"L7" [%"v13" : W = phi("start" => #0, "L6" => %"v11")]:
    => br %"v13" ? "L1" : "L3";
  @"L1":
    %"chk1" : A = (Check 0 8 Read 1) %"v0";
    %"v14" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v14";
  @"L3":
    => ret #18446744073709551615
} }.
