(** This file defines checked IR from glibc’s `string/argz-ctsep.os` object.
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

Definition fn___argz_create_sep : func :=
  ir_fn{ "export" "__argz_create_sep"(P %"v0", W %"v2", P %"v4", P %"v6") -> (RClass W) {
  @"start":
    call %"v10" : L = $"__GI_strlen"(P %"v0");
    %"v11" : L = Add %"v10", #1;
    %"v16" : W = (Cmp Ugt L) %"v11", #1
    => br %"v16" ? "L12" : "L13";
  @"L12":
    call %"v21" : P = $"malloc"(L %"v11");
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"v21";
    %"chk1" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" : L = Ptoi %"v26";
    %"v28" : L = Ptoi #0;
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L22" : "L24";
  @"L22":
    => ret #12;
  @"L24":
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L34";
  @"L34" [%"pr.5" : P = phi("L24" => %"v33", "L39" => %"pr.6"); %"pr.4" : P = phi("L24" => %"v0", "L39" => %"v72"); %"pr.1" : L = phi("L24" => %"v11", "L39" => %"pr.2")]:
    %"chk3" : A = (Check 0 1 Read 1) %"pr.4";
    %"v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v43" : W = (Cmp Eq W) %"v41", %"v2"
    => br %"v43" ? "L37" : "L38";
  @"L37":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" : L = Ptoi %"pr.5";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ugt L) %"v50", %"v51"
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v58" = %"pr.5" +p #18446744073709551615;
    %"chk5" : A = (Check 0 1 Read 1) %"v58";
    %"v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v60" : W = (Cmp Ne W) %"v59", #0
    => goto "L54";
  @"L54" [%"v62" : W = phi("L37" => #0, "L53" => %"v60")]:
    => br %"v62" ? "L44" : "L45";
  @"L44":
    %"v64" = %"pr.5" +p #1;
    %"chk6" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk6" + 0] <- #0
    => goto "L39";
  @"L45":
    %"v66" : L = Sub %"pr.1", #1
    => goto "L39";
  @"L38":
    %"v68" = %"pr.5" +p #1;
    %"v70" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk8" + 0] <- %"v70"
    => goto "L39";
  @"L39" [%"pr.6" : P = phi("L38" => %"v68", "L44" => %"v64", "L45" => %"pr.5"); %"pr.2" : L = phi("L38" => %"pr.1", "L44" => %"pr.1", "L45" => %"v66")]:
    %"v72" = %"pr.4" +p #1;
    %"v73" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v74" : W = (Cmp Ne W) %"v73", #0
    => br %"v74" ? poll "L34" : "L36";
  @"L36":
    %"v79" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v79" ? "L75" : "L77";
  @"L75":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call void $"free"(P %"v81");
    %"chk11" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk11" + 0] <- #0;
    %"chk12" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk12" + 0] <- #0
    => goto "L77";
  @"L77":
    %"chk13" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk13" + 0] <- %"pr.2"
    => goto "L14";
  @"L13":
    %"chk14" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk14" + 0] <- #0;
    %"chk15" : A = (Check 0 8 Write 1) %"v6";
    store Wl [%"chk15" + 0] <- #0
    => goto "L14";
  @"L14":
    => ret #0
} }.
