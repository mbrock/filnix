(** This file defines checked IR from glibc’s `stdlib/abort.os` object.
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

Definition item___GI___abort_msg : item :=
  (IData (a "__GI___abort_msg") LExport 8 [(Zero 8)]).

Definition fn___GI_abort : func :=
  ir_fn{ "export" "__GI_abort"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"glibc_abort#str.268";
    call void $"zerror"(P %"v0")
    => goto "L2";
  @"L2":
    %"v4" : P = Copy $"glibc_abort#str.269";
    call void $"zsafety_error"(P %"v4")
    => goto poll "L2"
} }.

Definition item_abort : item :=
  (IAlias (a "abort") (a "export") (a "__GI_abort")).

Definition item_glibc_abort'23str'2e268 : item :=
  (IData (a "glibc_abort#str.268") (LRo (a "local")) 1 [(Item Wb 97); (Item Wb 98); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 40); (Item Wb 51); (Item Wb 41); (Item Wb 32); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 101); (Item Wb 100); (Item Wb 46); (Item Wb 0)]).

Definition item_glibc_abort'23str'2e269 : item :=
  (IData (a "glibc_abort#str.269") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109)] [(Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110); (Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 104); (Item Wb 108); (Item Wb 116); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 104); (Item Wb 108); (Item Wb 116); (Item Wb 0)])).
