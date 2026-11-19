(** This file defines checked IR from glibc’s `string/argz-addsep.os` object.
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

Definition fn___argz_add_sep : func :=
  ir_fn{ "export" "__argz_add_sep"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    call %"v10" : L = $"__GI_strlen"(P %"v4");
    %"v11" : L = Add %"v10", #1;
    %"v16" : W = (Cmp Ugt L) %"v11", #1
    => br %"v16" ? "L12" : "L14";
  @"L12":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 1) %"v2";
    %"v23" : L = (RawLoad LdL 0) %"chk1";
    %"v25" : L = Add %"v23", %"v11";
    call %"v26" : P = $"realloc"(P %"v21", L %"v25");
    %"v31" : L = Ptoi %"v26";
    %"v32" : L = Ptoi #0;
    %"v33" : W = (Cmp Eq L) %"v31", %"v32"
    => br %"v33" ? "L27" : "L29";
  @"L27":
    => ret #12;
  @"L29":
    %"chk2" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk2" + 0] <- %"v26";
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Renew 0 8 Read 1) %"chk1", %"v2";
    %"v40" : L = (RawLoad LdL 0) %"chk4";
    %"v41" = %"v38" +p %"v40"
    => goto "L43";
  @"L43" [%"pr.5" : P = phi("L29" => %"v41", "L48" => %"pr.6"); %"pr.4" : P = phi("L29" => %"v4", "L48" => %"v81"); %"pr.1" : L = phi("L29" => %"v11", "L48" => %"pr.2")]:
    %"chk5" : A = (Check 0 1 Read 1) %"pr.4";
    %"v50" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v52" : W = (Cmp Eq W) %"v50", %"v6"
    => br %"v52" ? "L46" : "L47";
  @"L46":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v0";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v59" : L = Ptoi %"pr.5";
    %"v60" : L = Ptoi %"v58";
    %"v61" : W = (Cmp Ugt L) %"v59", %"v60"
    => br %"v61" ? "L62" : "L63";
  @"L62":
    %"v67" = %"pr.5" +p #18446744073709551615;
    %"chk7" : A = (Check 0 1 Read 1) %"v67";
    %"v68" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"v69" : W = (Cmp Ne W) %"v68", #0
    => goto "L63";
  @"L63" [%"v71" : W = phi("L46" => #0, "L62" => %"v69")]:
    => br %"v71" ? "L53" : "L54";
  @"L53":
    %"v73" = %"pr.5" +p #1;
    %"chk8" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk8" + 0] <- #0
    => goto "L48";
  @"L54":
    %"v75" : L = Sub %"pr.1", #1
    => goto "L48";
  @"L47":
    %"v77" = %"pr.5" +p #1;
    %"v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"chk10" : A = (Check 0 1 Write 1) %"pr.5";
    store Wb [%"chk10" + 0] <- %"v79"
    => goto "L48";
  @"L48" [%"pr.6" : P = phi("L47" => %"v77", "L53" => %"v73", "L54" => %"pr.5"); %"pr.2" : L = phi("L47" => %"pr.1", "L53" => %"pr.1", "L54" => %"v75")]:
    %"v81" = %"pr.4" +p #1;
    %"v82" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v83" : W = (Cmp Ne W) %"v82", #0
    => br %"v83" ? poll "L43" : "L45";
  @"L45":
    %"chk12" : A = (Renew 0 8 Read 1) %"chk1", %"v2";
    %"v85" : L = (RawLoad LdL 0) %"chk12";
    %"v87" : L = Add %"v85", %"pr.2";
    %"chk13" : A = (Renew 0 8 Write 1) %"chk1", %"v2";
    store Wl [%"chk13" + 0] <- %"v87"
    => goto "L14";
  @"L14":
    => ret #0
} }.
