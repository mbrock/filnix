(** This file defines checked IR from glibc’s `dirent/closedir.os` object.
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

Definition fn___closedir : func :=
  ir_fn{ "export" "__closedir"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" : L = Ptoi %"v0";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Eq L) %"v7", %"v8"
    => br %"v9" ? "L3" : "L5";
  @"L3":
    %"v10" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #22
    => ret #4294967295;
  @"L5":
    %"chk1" : A = (Check 0 4 Read 1) %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call void $"free"(P %"v0");
    call %"v17" : W = $"__GI___close_nocancel"(W %"v14")
    => ret %"v17"
} }.
