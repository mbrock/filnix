(** This file defines checked IR from glibc’s `stdlib/getenv.os` object.
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

Definition fn___GI_getenv : func :=
  ir_fn{ "export" "__GI_getenv"(P %"v0") -> (RClass P) {
  @"start":
    => goto "L3";
  @"L3":
    %"v6" : P = Copy $"__environ_counter";
    %"chk0" : A = (Check 0 8 Read 1) %"v6";
    %"v7" : L = (RawLoad LdL 0) %"chk0";
    %"v9" : P = Copy $"__environ";
    %"chk1" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 [AtomicRead]) %"chk1";
    %"v15" : L = Ptoi %"v10";
    %"v16" : L = Ptoi #0;
    %"v17" : W = (Cmp Eq L) %"v15", %"v16"
    => br %"v17" ? "L19" : "L18";
  @"L18":
    %"chk2" : A = (Check 0 1 Read 1) %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v23" : W = (Cmp Eq W) %"v22", #0
    => goto "L19";
  @"L19" [%"v25" : W = phi("L3" => #1, "L18" => %"v23")]:
    => br %"v25" ? "L11" : "L13";
  @"L11":
    => ret #0;
  @"L13":
    call %"v29" : L = $"__GI_strlen"(P %"v0")
    => goto "L32";
  @"L32" [%"pr.1" : P = phi("L13" => %"v10", "L34" => %"v81")]:
    %"chk3" : A = (Check 0 8 Read 8) %"pr.1";
    %"v38" : P = (RawLoadPointer 0 [AtomicRead]) %"chk3";
    %"v43" : L = Ptoi %"v38";
    %"v45" : W = (Cmp Eq L) %"v43", %"v16"
    => br %"v45" ? "L35" : "L41";
  @"L41":
    %"chk4" : A = (Check 0 1 Read 1) %"v0";
    %"v52" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"chk5" : A = (Check 0 1 Read 1) %"v38";
    %"v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v56" : W = (Cmp Eq W) %"v52", %"v55"
    => br %"v56" ? "L57" : "L58";
  @"L57":
    call %"v62" : W = $"__GI_strncmp"(P %"v0", P %"v38", L %"v29");
    %"v63" : W = (Cmp Eq W) %"v62", #0
    => goto "L58";
  @"L58" [%"v65" : W = phi("L41" => #0, "L57" => %"v63")]:
    => br %"v65" ? "L66" : "L67";
  @"L66":
    %"v70" = %"v38" +p %"v29";
    %"chk6" : A = (Check 0 1 Read 1) %"v70";
    %"v71" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v72" : W = (Cmp Eq W) %"v71", #61
    => goto "L67";
  @"L67" [%"v74" : W = phi("L58" => #0, "L66" => %"v72")]:
    => br %"v74" ? "L47" : "L34";
  @"L47":
    %"v77" = %"v38" +p %"v29";
    %"v78" = %"v77" +p #1
    => ret %"v78";
  @"L34":
    %"v81" = %"pr.1" +p #8
    => goto poll "L32";
  @"L35":
    %"v85" : P = Copy $"__environ_counter";
    %"chk7" : A = (Check 0 8 Read 1) %"v85";
    %"v86" : L = (RawLoad LdL 0) %"chk7";
    %"v88" : W = (Cmp Eq L) %"v86", %"v7"
    => br %"v88" ? "L82" : poll "L3";
  @"L82":
    => ret #0
} }.

Definition item_getenv : item :=
  (IAlias (a "getenv") (a "export") (a "__GI_getenv")).
