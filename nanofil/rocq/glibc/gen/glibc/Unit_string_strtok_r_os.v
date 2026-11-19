(** This file defines checked IR from glibc’s `string/strtok_r.os` object.
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

Definition fn___GI___strtok_r : func :=
  ir_fn{ "export" "__GI___strtok_r"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v11" : L = Ptoi %"v0";
    %"v12" : L = Ptoi #0;
    %"v13" : W = (Cmp Eq L) %"v11", %"v12"
    => br %"v13" ? "L7" : "L9";
  @"L7":
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L9";
  @"L9" [%"pr.1" : P = phi("L7" => %"v15", "start" => %"v0")]:
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v20" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    %"chk2" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk2" + 0] <- %"pr.1"
    => ret #0;
  @"L18":
    call %"v28" : L = $"__GI_strspn"(P %"pr.1", P %"v2");
    %"v29" = %"pr.1" +p %"v28";
    %"chk3" : A = (Check 0 1 Read 1) %"v29";
    %"v34" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => br %"v35" ? "L30" : "L32";
  @"L30":
    %"chk4" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk4" + 0] <- %"v29"
    => ret #0;
  @"L32":
    call %"v42" : L = $"__GI_strcspn"(P %"v29", P %"v2");
    %"v43" = %"v29" +p %"v42";
    %"chk5" : A = (Check 0 1 Read 1) %"v43";
    %"v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v49" : W = (Cmp Eq W) %"v48", #0
    => br %"v49" ? "L44" : "L46";
  @"L44":
    %"chk6" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk6" + 0] <- %"v43"
    => ret %"v29";
  @"L46":
    %"chk7" : A = (Renew 0 1 Write 1) %"chk5", %"v43";
    store Wb [%"chk7" + 0] <- #0;
    %"v57" = %"v43" +p #1;
    %"chk8" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk8" + 0] <- %"v57"
    => ret %"v29"
} }.
