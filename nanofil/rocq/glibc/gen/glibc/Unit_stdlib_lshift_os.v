(** This file defines checked IR from glibc’s `stdlib/lshift.os` object.
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

Definition fn___mpn_lshift : func :=
  ir_fn{ "export" "__mpn_lshift"(P %"v0", P %"v2", L %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v16" = %"v0" +p #8;
    %"v18" : W = Sub #64, %"v6";
    %"v20" : L = Sub %"v4", #1;
    %"v23" : L = Shl %"v20", #3;
    %"v24" = %"v2" +p %"v23";
    %"chk0" : A = (Check 0 8 Read 1) %"v24";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v28" : L = Shr %"v25", %"v18"
    => goto "L30";
  @"L30" [%"pr.2" : L = phi("L31" => %"v34", "start" => %"v20"); %"pr.1" : L = phi("L31" => %"v40", "start" => %"v25")]:
    %"v34" : L = Sub %"pr.2", #1;
    %"v35" : W = (Cmp Sge L) %"v34", #0
    => br %"v35" ? "L31" : "L32";
  @"L31":
    %"v38" : L = Shl %"v34", #3;
    %"v39" = %"v2" +p %"v38";
    %"chk1" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk1";
    %"v44" = %"v16" +p %"v38";
    %"v47" : L = Shl %"pr.1", %"v6";
    %"v50" : L = Shr %"v40", %"v18";
    %"v51" : L = Or %"v47", %"v50";
    %"chk2" : A = (Check 0 8 Write 1) %"v44";
    store Wl [%"chk2" + 0] <- %"v51"
    => goto poll "L30";
  @"L32":
    %"v55" : L = Shl %"v34", #3;
    %"v56" = %"v16" +p %"v55";
    %"v59" : L = Shl %"pr.1", %"v6";
    %"chk3" : A = (Check 0 8 Write 1) %"v56";
    store Wl [%"chk3" + 0] <- %"v59"
    => ret %"v28"
} }.
