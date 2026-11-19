(** This file defines checked IR from glibc’s `misc/getpagesize.os` object.
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

Definition fn___GI___getpagesize : func :=
  ir_fn{ "export" "__GI___getpagesize"() -> (RClass W) {
  @"start":
    %"v3" : P = Copy $"_dl_pagesize";
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v5" : W = (Cmp Ne L) %"v4", #0
    => br %"v5" ? "L2" : "L1";
  @"L1":
    %"v6" : P = Copy $"glibc_getpagesize#str.279";
    %"v7" : P = Copy $"glibc_getpagesize#str.280";
    %"v8" : P = Copy $"glibc_getpagesize#str.281";
    call void $"__libc_assert_fail"(P %"v6", P %"v7", W #28, P %"v8")
    => goto "L2";
  @"L2":
    %"v9" : P = Copy $"_dl_pagesize";
    %"chk1" : A = (Check 0 8 Read 1) %"v9";
    %"v10" : L = (RawLoad LdL 0) %"chk1"
    => ret %"v10"
} }.

Definition item_glibc_getpagesize'23str'2e279 : item :=
  (IData (a "glibc_getpagesize#str.279") (LRo (a "local")) 1 [(Item Wb 71); (Item Wb 76); (Item Wb 82); (Item Wb 79); (Item Wb 40); (Item Wb 100); (Item Wb 108); (Item Wb 95); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 41); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_getpagesize'23str'2e280 : item :=
  (IData (a "glibc_getpagesize#str.280") (LRo (a "local")) 1 [(Item Wb 46); (Item Wb 46); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 100); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 47); (Item Wb 117); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 118); (Item Wb 47); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 117); (Item Wb 120); (Item Wb 47); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_getpagesize'23str'2e281 : item :=
  (IData (a "glibc_getpagesize#str.281") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 103); (Item Wb 101); (Item Wb 116); (Item Wb 112); (Item Wb 97); (Item Wb 103); (Item Wb 101); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 0)]).
