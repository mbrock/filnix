(** This file defines checked IR from glibc’s `stdlib/rshift.os` object.
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

Definition fn___mpn_rshift : func :=
  ir_fn{ "export" "__mpn_rshift"(P %"v0", P %"v2", L %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v18" : W = (Cmp Ne L) %"v4", #0
    => br %"v18" ? "L19" : "L20";
  @"L19":
    %"v22" : W = (Cmp Ne W) %"v6", #0
    => goto "L20";
  @"L20" [%"v24" : W = phi("start" => #0, "L19" => %"v22")]:
    => br %"v24" ? "L16" : "L15";
  @"L15":
    %"v25" : P = Copy $"glibc_rshift#str.62";
    %"v26" : P = Copy $"glibc_rshift#str.63";
    %"v27" : P = Copy $"glibc_rshift#str.64";
    call void $"__libc_assert_fail"(P %"v25", P %"v26", W #45, P %"v27")
    => goto "L16";
  @"L16":
    (Flight (a "v30") Sub [(FAddress (t "v0")); (FValue (Const 8))] (LowerOf (t "v0")));
    %"v32" : W = Sub #64, %"v6";
    %"chk0" : A = (Check 0 8 Read 1) %"v2";
    %"v35" : L = (RawLoad LdL 0) %"chk0";
    %"v38" : L = Shl %"v35", %"v32"
    => goto "L40";
  @"L40" [%"pr.2" : L = phi("L16" => #1, "L41" => %"v65"); %"pr.1" : L = phi("L16" => %"v35", "L41" => %"v51")]:
    %"v46" : W = (Cmp Slt L) %"pr.2", %"v4"
    => br %"v46" ? "L41" : "L43";
  @"L41":
    %"v49" : L = Shl %"pr.2", #3;
    %"v50" = %"v2" +p %"v49";
    %"chk1" : A = (Check 0 8 Read 1) %"v50";
    %"v51" : L = (RawLoad LdL 0) %"chk1";
    %"v55" = %"v30" +p %"v49";
    %"v58" : L = Shr %"pr.1", %"v6";
    %"v61" : L = Shl %"v51", %"v32";
    %"v62" : L = Or %"v58", %"v61";
    %"chk2" : A = (Check 0 8 Write 1) %"v55";
    store Wl [%"chk2" + 0] <- %"v62";
    %"v65" : L = Add %"pr.2", #1
    => goto poll "L40";
  @"L43":
    %"v68" : L = Shl %"pr.2", #3;
    %"v69" = %"v30" +p %"v68";
    %"v72" : L = Shr %"pr.1", %"v6";
    %"chk3" : A = (Check 0 8 Write 1) %"v69";
    store Wl [%"chk3" + 0] <- %"v72"
    => ret %"v38"
} }.

Definition item_glibc_rshift'23str'2e62 : item :=
  (IData (a "glibc_rshift#str.62") (LRo (a "local")) 1 [(Item Wb 117); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 99); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_rshift'23str'2e63 : item :=
  (IData (a "glibc_rshift#str.63") (LRo (a "local")) 1 [(Item Wb 114); (Item Wb 115); (Item Wb 104); (Item Wb 105); (Item Wb 102); (Item Wb 116); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_rshift'23str'2e64 : item :=
  (IData (a "glibc_rshift#str.64") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 109); (Item Wb 112); (Item Wb 110); (Item Wb 95); (Item Wb 114); (Item Wb 115); (Item Wb 104); (Item Wb 105); (Item Wb 102); (Item Wb 116); (Item Wb 0)]).
