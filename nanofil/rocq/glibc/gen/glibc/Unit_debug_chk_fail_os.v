(** This file defines checked IR from glibc’s `debug/chk_fail.os` object.
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

Definition fn___GI___chk_fail : func :=
  ir_fn{ "export" "__GI___chk_fail"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_chk_fail#str.134";
    call void $"__GI___fortify_fail"(P %"v0")
    => ret void
} }.

Definition item_glibc_chk_fail'23str'2e134 : item :=
  (IData (a "glibc_chk_fail#str.134") (LRo (a "local")) 1 [(Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 32); (Item Wb 111); (Item Wb 118); (Item Wb 101); (Item Wb 114); (Item Wb 102); (Item Wb 108); (Item Wb 111); (Item Wb 119); (Item Wb 32); (Item Wb 100); (Item Wb 101); (Item Wb 116); (Item Wb 101); (Item Wb 99); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).
