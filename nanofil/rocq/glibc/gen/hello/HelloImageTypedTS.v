(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___tsearch : func :=
  ir_fn{ "export" "__GI___tsearch"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v20" : L = Ptoi %"v2";
    %"v21" : L = Ptoi #0;
    %"v22" : W = (Cmp Eq L) %"v20", %"v21"
    => br %"v22" ? "L16" : "L18";
  @"L16":
    => ret #0;
  @"L18":
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v30" : L = Ptoi %"v25";
    %"v32" : W = (Cmp Ne L) %"v30", %"v21"
    => br %"v32" ? "L26" : "L42";
  @"L26":
    %"v34" = %"v25" +p #24;
    %"chk1" : A = (Check 0 4 Read 1) %"v34";
    %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v36" : W = And %"v35", #4294967294;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v34";
    store Ww [%"chk2" + 0] <- %"v36"
    => goto "L42";
  @"L42" [%"pr.9" : W = phi("L26" => #0, "L18" => #0, "L71" => %"pr.8"); %"pr.8" : W = phi("L26" => #0, "L18" => #0, "L71" => %"v56"); %"pr.6" : W = phi("L26" => #0, "L18" => #0, "L71" => %"v56"); %"pr.4" : P = phi("L26" => %"v2", "L18" => %"v2", "L71" => %"v78"); %"pr.3" : P = phi("L26" => %"v2", "L18" => %"v2", "L71" => %"v78"); %"pr.2" : P = phi("L26" => #0, "L18" => #0, "L71" => %"pr.1"); %"pr.1" : P = phi("L26" => #0, "L18" => #0, "L71" => %"pr.3")]:
    %"chk3" : A = (Check 0 8 Read 8) %"pr.4";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v47" : L = Ptoi %"v46";
    %"v49" : W = (Cmp Ne L) %"v47", %"v21"
    => br %"v49" ? "L43" : "L44";
  @"L43":
    %"chk4" : A = (Check 0 8 Read 8) %"pr.3";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v51";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v4";
    rawcall %"v56" : W = %"chk6"(P %"v0", P %"v55");
    %"v61" : W = (Cmp Eq W) %"v56", #0
    => br %"v61" ? "L57" : "L59";
  @"L57":
    => ret %"v51";
  @"L59":
    call void $"glibc_tsearch#maybe_split_for_insert"(P %"pr.3", P %"pr.1", P %"pr.2", W %"pr.8", W %"pr.9", W #0);
    %"v73" : W = (Cmp Slt W) %"v56", #0
    => br %"v73" ? "L69" : "L70";
  @"L69":
    %"v75" = %"v51" +p #8
    => goto "L71";
  @"L70":
    %"v77" = %"v51" +p #16
    => goto "L71";
  @"L71" [%"v78" : P = phi("L69" => %"v75", "L70" => %"v77")]:
    %"chk7" : A = (Check 0 8 Read 8) %"v78";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v84" : L = Ptoi %"v83";
    %"v86" : W = (Cmp Eq L) %"v84", %"v21"
    => br %"v86" ? "L44" : poll "L42";
  @"L44" [%"pr.7" : W = phi("L42" => %"pr.6", "L71" => %"v56"); %"pr.5" : P = phi("L42" => %"pr.4", "L71" => %"v78")]:
    call %"v93" : P = $"malloc"(L #32);
    %"v98" : L = Ptoi %"v93";
    %"v100" : W = (Cmp Ne L) %"v98", %"v21"
    => br %"v100" ? "L94" : "L96";
  @"L94":
    %"chk8" : A = (Check 0 8 Write 8) %"pr.5";
    store.ptr [%"chk8" + 0] <- %"v93";
    %"chk9" : A = (Check 0 8 Write 8) %"v93";
    store.ptr [%"chk9" + 0] <- %"v0";
    %"v106" = %"v93" +p #24;
    %"chk10" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v106";
    %"v107" : W = (RawLoad (LdNarrow Uw) 0) %"chk10";
    %"v108" : W = And %"v107", #4294967294;
    %"v110" : W = Or %"v108", #1;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk10", %"v106";
    store Ww [%"chk11" + 0] <- %"v110";
    %"v114" = %"v93" +p #8;
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk9", %"v114";
    store.ptr [%"chk12" + 0] <- #0;
    %"v116" = %"v93" +p #16;
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk9", %"v116";
    store.ptr [%"chk13" + 0] <- #0;
    %"v122" : L = Ptoi %"pr.5";
    %"v123" : L = Ptoi %"pr.3";
    %"v124" : W = (Cmp Ne L) %"v122", %"v123"
    => br %"v124" ? "L117" : "L96";
  @"L117":
    call void $"glibc_tsearch#maybe_split_for_insert"(P %"pr.5", P %"pr.3", P %"pr.1", W %"pr.7", W %"pr.8", W #1)
    => goto "L96";
  @"L96":
    => ret %"v93"
} }.
