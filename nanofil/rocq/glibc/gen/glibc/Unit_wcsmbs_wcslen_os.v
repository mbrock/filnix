(** This file defines checked IR from glibc’s `wcsmbs/wcslen.os` object.
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

Definition fn___wcslen : func :=
  ir_fn{ "export" "__wcslen"(P %"v0") -> (RClass L) {
  @"start":
    => goto "L3";
  @"L3" [%"pr.1" : L = phi("L38" => %"v49", "start" => #0)]:
    %"v8" : L = Shl %"pr.1", #2;
    %"v9" = %"v0" +p %"v8";
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = (Cmp Ne W) %"v10", #0
    => br %"v11" ? "L4" : "L5";
  @"L4":
    %"v17" : L = Add %"pr.1", #1;
    %"v18" : L = Shl %"v17", #2;
    %"v19" = %"v0" +p %"v18";
    %"chk1" : A = (Check 0 4 Read 1) %"v19";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => br %"v21" ? "L12" : "L14";
  @"L12":
    => ret %"v17";
  @"L14":
    %"v29" : L = Add %"v17", #1;
    %"v30" : L = Shl %"v29", #2;
    %"v31" = %"v0" +p %"v30";
    %"chk2" : A = (Check 0 4 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v33" : W = (Cmp Eq W) %"v32", #0
    => br %"v33" ? "L24" : "L26";
  @"L24":
    => ret %"v29";
  @"L26":
    %"v41" : L = Add %"v29", #1;
    %"v42" : L = Shl %"v41", #2;
    %"v43" = %"v0" +p %"v42";
    %"chk3" : A = (Check 0 4 Read 1) %"v43";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v45" : W = (Cmp Eq W) %"v44", #0
    => br %"v45" ? "L36" : "L38";
  @"L36":
    => ret %"v41";
  @"L38":
    %"v49" : L = Add %"v41", #1
    => goto poll "L3";
  @"L5":
    => ret %"pr.1"
} }.
