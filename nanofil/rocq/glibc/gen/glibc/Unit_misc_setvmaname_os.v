(** This file defines checked IR from glibc’s `misc/setvmaname.os` object.
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

Definition fn___is_decorate_maps_enabled : func :=
  ir_fn{ "export" "__is_decorate_maps_enabled"() -> (RClass W) {
  @"start":
    %"v9" : P = (Alloc 4) #4;
    %"v0" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v1" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v29" : W = (Cmp Eq W) %"v1", #(-1)
    => br %"v29" ? "L4" : "L30";
  @"L4":
    call void $"__tunable_get_val"(W #26, P %"v9", P #0);
    %"chk1" : A = (Check 0 4 Read 1) %"v9";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v12" : W = (Cmp Ne W) %"v11", #0
    => br %"v12" ? "L13" : "L19";
  @"L13":
    %"v16" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk2" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk2" + 0] <- #1
    => ret #1;
  @"L19":
    %"v22" : P = Copy $"glibc_setvmaname#decorate_maps";
    %"chk3" : A = (Check 0 4 Write 1) %"v22";
    store Ww [%"chk3" + 0] <- #0
    => ret #0;
  @"L24":
    => ret #0;
  @"L26":
    => ret #1;
  @"L30":
    %"v31" : W = (Cmp Eq W) %"v1", #0
    => br %"v31" ? poll "L24" : "L32";
  @"L32":
    %"v33" : W = (Cmp Eq W) %"v1", #1
    => br %"v33" ? poll "L26" : "L3";
  @"L3":
    => unreachable
} }.

Definition fn___set_vma_name : func :=
  ir_fn{ "export" "__set_vma_name"(P %"v0", L %"v2", P %"v4") -> RVoid {
  @"start":
    call %"v9" : W = $"__is_decorate_maps_enabled"();
    %"v10" : W = (Ext Ub) %"v9"
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v38" : P = Copy $"glibc_setvmaname#str.282";
    call void $"zsafety_error"(P %"v38")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition item_glibc_setvmaname'23decorate_maps : item :=
  (IData (a "glibc_setvmaname#decorate_maps") LLocal 4 [(Item Ww (-1))]).

Definition item_glibc_setvmaname'23str'2e282 : item :=
  (IData (a "glibc_setvmaname#str.282") (LRo (a "local")) 1 (app [(Item Wb 99); (Item Wb 97); (Item Wb 110); (Item Wb 110); (Item Wb 111); (Item Wb 116); (Item Wb 32); (Item Wb 104); (Item Wb 97); (Item Wb 110); (Item Wb 100); (Item Wb 108); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 32); (Item Wb 40); (Item Wb 117); (Item Wb 110); (Item Wb 115); (Item Wb 117); (Item Wb 112); (Item Wb 112); (Item Wb 111); (Item Wb 114); (Item Wb 116); (Item Wb 101); (Item Wb 100); (Item Wb 32); (Item Wb 109); (Item Wb 110); (Item Wb 101); (Item Wb 109); (Item Wb 111); (Item Wb 110)] [(Item Wb 105); (Item Wb 99); (Item Wb 32); (Item Wb 102); (Item Wb 111); (Item Wb 114); (Item Wb 32); (Item Wb 115); (Item Wb 97); (Item Wb 102); (Item Wb 101); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 108); (Item Wb 105); (Item Wb 110); (Item Wb 101); (Item Wb 32); (Item Wb 97); (Item Wb 115); (Item Wb 109); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 41); (Item Wb 58); (Item Wb 32); (Item Wb 115); (Item Wb 121); (Item Wb 115); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 108); (Item Wb 10); (Item Wb 9); (Item Wb 0)])).
