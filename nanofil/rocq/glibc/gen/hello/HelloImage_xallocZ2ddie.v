(** This file defines checked IR from the `xalloc-die` object of HelloImage.
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

Definition item_xalloc'2ddie'23str'2e41 : item :=
  (IData (a "xalloc-die#str.41") (LRo (a "local")) 1 [(Item Wb 37); (Item Wb 115); (Item Wb 0)]).

Definition item_xalloc'2ddie'23str'2e42 : item :=
  (IData (a "xalloc-die#str.42") (LRo (a "local")) 1 [(Item Wb 103); (Item Wb 110); (Item Wb 117); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 0)]).

Definition item_xalloc'2ddie'23str'2e43 : item :=
  (IData (a "xalloc-die#str.43") (LRo (a "local")) 1 [(Item Wb 109); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 114); (Item Wb 121); (Item Wb 32); (Item Wb 101); (Item Wb 120); (Item Wb 104); (Item Wb 97); (Item Wb 117); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 0)]).

Definition fn_xalloc_die : func :=
  ir_fn{ "export" "xalloc_die"() -> RVoid {
  @"start":
    %"v16" : P = Copy $"exit_failure";
    %"chk0" : A = (Check 0 4 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v19" : P = Copy $"xalloc-die#str.41";
    %"v20" : P = Copy $"xalloc-die#str.42";
    %"v21" : P = Copy $"xalloc-die#str.43";
    call void $"error"(W %"v17", W #0, P %"v19", P %"v21");
    %"v26" : W = (Cmp Ne W) %"v17", #0
    => br %"v26" ? "L22" : "L2";
  @"L22":
    => unreachable;
  @"L2":
    call void $"abort"()
    => ret void
} }.
