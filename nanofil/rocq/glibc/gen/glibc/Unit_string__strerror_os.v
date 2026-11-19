(** This file defines checked IR from glibc’s `string/_strerror.os` object.
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

Definition fn___GI___strerror_r : func :=
  ir_fn{ "export" "__GI___strerror_r"(W %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    call %"v8" : P = $"__get_errlist"(W %"v0");
    %"v13" : L = Ptoi %"v8";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L11";
  @"L9":
    %"v20" : P = Copy $"glibc__strerror#str.136";
    %"v21" : P = Copy $"__GI__libc_intl_domainname";
    %"v22" : P = Copy $"glibc__strerror#str.137";
    call %"v23" : P = $"__GI___dcgettext"(P %"v21", P %"v22", W #5);
    call %"v25" : W = $"__GI___snprintf"(P %"v2", L %"v4", P %"v20", P %"v23", W %"v0")
    => ret %"v2";
  @"L11":
    %"v28" : P = Copy $"__GI__libc_intl_domainname";
    call %"v30" : P = $"__GI___dcgettext"(P %"v28", P %"v8", W #5)
    => ret %"v30"
} }.

Definition item_glibc__strerror'23str'2e136 : item :=
  (IData (a "glibc__strerror#str.136") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 37); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc__strerror'23str'2e137 : item :=
  (IData (a "glibc__strerror#str.137") (LRo (a "local")) 1 [(Item Wb 85); (Item Wb 110); (Item Wb 107); (Item Wb 110); (Item Wb 111); (Item Wb 119); (Item Wb 110); (Item Wb 32); (Item Wb 101); (Item Wb 114); (Item Wb 114); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 0)]).
