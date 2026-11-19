(** This file defines checked IR from the `hard-locale` object of HelloImage.
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

Definition item_hard'2dlocale'23str'2e31 : item :=
  (IData (a "hard-locale#str.31") (LRo (a "local")) 1 [(Item Wb 67); (Item Wb 0)]).

Definition item_hard'2dlocale'23str'2e32 : item :=
  (IData (a "hard-locale#str.32") (LRo (a "local")) 1 [(Item Wb 80); (Item Wb 79); (Item Wb 83); (Item Wb 73); (Item Wb 88); (Item Wb 0)]).

Definition fn_hard_locale : func :=
  ir_fn{ "export" "hard_locale"(W %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 4) #257;
    call %"v7" : W = $"setlocale_null_r"(W %"v0", P %"v2", L #257)
    => br %"v7" ? "L3" : "L5";
  @"L3":
    => ret #0;
  @"L5":
    %"v13" : P = Copy $"hard-locale#str.31";
    call %"v14" : W = $"streq"(P %"v2", P %"v13");
    %"v15" : W = (Ext Ub) %"v14"
    => br %"v15" ? "L17" : "L16";
  @"L16":
    %"v18" : P = Copy $"hard-locale#str.32";
    call %"v19" : W = $"streq"(P %"v2", P %"v18");
    %"v20" : W = (Ext Ub) %"v19";
    %"v21" : W = (Cmp Ne W) %"v20", #0
    => goto "L17";
  @"L17" [%"v22" : W = phi("L5" => #1, "L16" => %"v21")]:
    => br %"v22" ? "L12" : "L10";
  @"L10":
    => ret #1;
  @"L12":
    => ret #0
} }.
