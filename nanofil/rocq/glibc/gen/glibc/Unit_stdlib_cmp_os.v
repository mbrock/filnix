(** This file defines checked IR from glibc’s `stdlib/cmp.os` object.
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

Definition fn___mpn_cmp : func :=
  ir_fn{ "export" "__mpn_cmp"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v10" : L = Sub %"v4", #1
    => goto "L11";
  @"L11" [%"pr.1" : L = phi("L13" => %"v36", "start" => %"v10")]:
    %"v16" : W = (Cmp Sge L) %"pr.1", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    %"v19" : L = Shl %"pr.1", #3;
    %"v20" = %"v0" +p %"v19";
    %"chk0" : A = (Check 0 8 Read 1) %"v20";
    %"v21" : L = (RawLoad LdL 0) %"chk0";
    %"v25" = %"v2" +p %"v19";
    %"chk1" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk1";
    %"v32" : W = (Cmp Ne L) %"v21", %"v26"
    => br %"v32" ? "L33" : "L13";
  @"L13":
    %"v36" : L = Sub %"pr.1", #1
    => goto poll "L11";
  @"L14":
    => ret #0;
  @"L33":
    %"v42" : W = (Cmp Ugt L) %"v21", %"v26"
    => br %"v42" ? "L39" : "L38";
  @"L38":
    => goto "L39";
  @"L39" [%"v44" : W = phi("L38" => #4294967295, "L33" => #1)]:
    => ret %"v44"
} }.
