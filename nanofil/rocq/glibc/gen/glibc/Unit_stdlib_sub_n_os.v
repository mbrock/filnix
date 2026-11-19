(** This file defines checked IR from glibc’s `stdlib/sub_n.os` object.
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

Definition fn___mpn_sub_n : func :=
  ir_fn{ "export" "__mpn_sub_n"(P %"v0", P %"v2", P %"v4", L %"v6") -> (RClass L) {
  @"start":
    %"v13" : L = Neg %"v6";
    %"v16" : L = Shl %"v13", #3;
    (Flight (a "v17") Sub [(FAddress (t "v2")); (FValue (t "v16"))] (LowerOf (t "v2")));
    (Flight (a "v21") Sub [(FAddress (t "v4")); (FValue (t "v16"))] (LowerOf (t "v4")));
    (Flight (a "v25") Sub [(FAddress (t "v0")); (FValue (t "v16"))] (LowerOf (t "v0")))
    => goto "L26";
  @"L26" [%"pr.2" : L = phi("L26" => %"v61", "start" => %"v13"); %"pr.1" : L = phi("L26" => %"v54", "start" => #0)]:
    %"v31" : L = Shl %"pr.2", #3;
    %"v32" = %"v21" +p %"v31";
    %"chk0" : A = (Check 0 8 Read 1) %"v32";
    %"v33" : L = (RawLoad LdL 0) %"chk0";
    %"v37" = %"v17" +p %"v31";
    %"chk1" : A = (Check 0 8 Read 1) %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk1";
    %"v41" : L = Add %"v33", %"pr.1";
    %"v44" : W = (Cmp Ult L) %"v41", %"pr.1";
    %"v45" : L = (Ext Sw) %"v44";
    %"v48" : L = Sub %"v38", %"v41";
    %"v51" : W = (Cmp Ugt L) %"v48", %"v38";
    %"v53" : L = (Ext Sw) %"v51";
    %"v54" : L = Add %"v53", %"v45";
    %"v58" = %"v25" +p %"v31";
    %"chk2" : A = (Check 0 8 Write 1) %"v58";
    store Wl [%"chk2" + 0] <- %"v48";
    %"v61" : L = Add %"pr.2", #1;
    %"v62" : W = (Cmp Ne L) %"v61", #0
    => br %"v62" ? poll "L26" : "L28";
  @"L28":
    => ret %"v54"
} }.
