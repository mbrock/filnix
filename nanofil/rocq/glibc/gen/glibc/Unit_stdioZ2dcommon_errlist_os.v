(** This file defines checked IR from glibc’s `stdio-common/errlist.os` object.
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

Definition fn___get_errlist : func :=
  ir_fn{ "export" "__get_errlist"(W %"v0") -> (RClass P) {
  @"start":
    %"v8" : W = (Cmp Sge W) %"v0", #0
    => br %"v8" ? "L9" : "L10";
  @"L9":
    %"v12" : P = Copy $"_sys_errlist_internal_len";
    %"chk0" : A = (Check 0 8 Read 1) %"v12";
    %"v13" : L = (RawLoad LdL 0) %"chk0";
    %"v14" : L = (Ext Sw) %"v0";
    %"v15" : W = (Cmp Ult L) %"v14", %"v13"
    => goto "L10";
  @"L10" [%"v17" : W = phi("start" => #0, "L9" => %"v15")]:
    => br %"v17" ? "L4" : "L6";
  @"L4":
    %"v18" : P = Copy $"_sys_errlist_internal";
    %"v20" : L = (Ext Sw) %"v0";
    %"v21" : L = Shl %"v20", #3;
    %"v22" = %"v18" +p %"v21";
    %"chk1" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => ret %"v23";
  @"L6":
    => ret #0
} }.
