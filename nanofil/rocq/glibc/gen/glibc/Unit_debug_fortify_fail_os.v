(** This file defines checked IR from glibc’s `debug/fortify_fail.os` object.
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

Definition fn___GI___fortify_fail : func :=
  ir_fn{ "export" "__GI___fortify_fail"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"glibc_fortify_fail#str.19";
    %"v3" : P = Copy $"glibc_fortify_fail#str.20";
    call void $"__libc_message_impl"(P %"v2", P %"v3", P %"v0")
    => ret void
} }.

Definition item_glibc_fortify_fail'23str'2e19 : item :=
  (IData (a "glibc_fortify_fail#str.19") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 58); (Item Wb 32); (Item Wb 102); (Item Wb 97); (Item Wb 116); (Item Wb 97); (Item Wb 108); (Item Wb 0)]).

Definition item_glibc_fortify_fail'23str'2e20 : item :=
  (IData (a "glibc_fortify_fail#str.20") (LRo (a "local")) 1 [(Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 32); (Item Wb 37); (Item Wb 115); (Item Wb 32); (Item Wb 42); (Item Wb 42); (Item Wb 42); (Item Wb 58); (Item Wb 32); (Item Wb 116); (Item Wb 101); (Item Wb 114); (Item Wb 109); (Item Wb 105); (Item Wb 110); (Item Wb 97); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 10); (Item Wb 0)]).
