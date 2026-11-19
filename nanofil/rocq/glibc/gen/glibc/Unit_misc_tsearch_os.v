(** This file defines checked IR from glibc’s `misc/tsearch.os` object.
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

Definition fn___GI___tfind : func :=
  ir_fn{ "export" "__GI___tfind"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v13" : L = Ptoi %"v2";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L11";
  @"L9":
    => ret #0;
  @"L11":
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L19";
  @"L19" [%"pr.1" : P = phi("L11" => %"v2", "L42" => %"v48", "L43" => %"v50")]:
    %"chk1" : A = (Check 0 8 Read 8) %"pr.1";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v24" : L = Ptoi %"v23";
    %"v26" : W = (Cmp Ne L) %"v24", %"v14"
    => br %"v26" ? "L20" : "L21";
  @"L20":
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk3" : A = (Check 0 8 Read 8) %"v28";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v4";
    rawcall %"v34" : W = %"chk4"(P %"v0", P %"v33");
    %"v39" : W = (Cmp Eq W) %"v34", #0
    => br %"v39" ? "L35" : "L37";
  @"L35":
    => ret %"v28";
  @"L37":
    %"v46" : W = (Cmp Slt W) %"v34", #0
    => br %"v46" ? "L42" : "L43";
  @"L42":
    %"v48" = %"v28" +p #8
    => goto poll "L19";
  @"L43":
    %"v50" = %"v28" +p #16
    => goto poll "L19";
  @"L21":
    => ret #0
} }.

Definition fn___GI___tsearch : func :=
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

Definition fn___GI___twalk_r : func :=
  ir_fn{ "export" "__GI___twalk_r"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v12" : L = Ptoi %"v0";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Ne L) %"v12", %"v13"
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v18" : L = Ptoi %"v2";
    %"v20" : W = (Cmp Ne L) %"v18", %"v13"
    => goto "L16";
  @"L16" [%"v22" : W = phi("start" => #0, "L15" => %"v20")]:
    => br %"v22" ? "L8" : "L10";
  @"L8":
    call void $"glibc_tsearch#trecurse_r"(P %"v0", P %"v2", P %"v4")
    => goto "L10";
  @"L10":
    => ret void
} }.

Definition fn_glibc_tsearch'23maybe_split_for_insert : func :=
  ir_fn{ "local" "glibc_tsearch#maybe_split_for_insert"(P %"v0", P %"v2", P %"v4", W %"v6", W %"v8", W %"v10") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" = %"v14" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v20";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" = %"v14" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v25";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v33" : W = (Cmp Eq W) %"v10", #1
    => br %"v33" ? "L35" : "L34";
  @"L34":
    %"v37" : L = Ptoi %"v23";
    %"v38" : L = Ptoi #0;
    %"v39" : W = (Cmp Ne L) %"v37", %"v38"
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" : L = Ptoi %"v28";
    %"v45" : W = (Cmp Ne L) %"v43", %"v38"
    => goto "L41";
  @"L41" [%"v47" : W = phi("L34" => #0, "L40" => %"v45")]:
    => br %"v47" ? "L48" : "L49";
  @"L48":
    %"v51" = %"v23" +p #24;
    %"chk3" : A = (Check 0 4 Read 1) %"v51";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = Shl %"v52", #31;
    %"v54" : W = Shr %"v53", #31;
    %"v55" : W = (Cmp Ne W) %"v54", #0
    => goto "L49";
  @"L49" [%"v56" : W = phi("L41" => #0, "L48" => %"v55")]:
    => br %"v56" ? "L57" : "L35";
  @"L57":
    %"v60" = %"v28" +p #24;
    %"chk4" : A = (Check 0 4 Read 1) %"v60";
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v62" : W = Shl %"v61", #31;
    %"v63" : W = Shr %"v62", #31;
    %"v64" : W = (Cmp Ne W) %"v63", #0
    => goto "L35";
  @"L35" [%"v67" : W = phi("start" => #1, "L49" => #0, "L57" => %"v64")]:
    => br %"v67" ? "L29" : "L31";
  @"L29":
    %"v69" = %"v14" +p #24;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"v69";
    %"v70" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v71" : W = And %"v70", #4294967294;
    %"v73" : W = Or %"v71", #1;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v69";
    store Ww [%"chk6" + 0] <- %"v73";
    %"v80" : L = Ptoi %"v23";
    %"v81" : W = (Cmp Ne L) %"v80", #0
    => br %"v81" ? "L76" : "L78";
  @"L76":
    %"v83" = %"v23" +p #24;
    %"chk7" : A = (Check 0 4 Read 1) %"v83";
    %"v84" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v85" : W = And %"v84", #4294967294;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v83";
    store Ww [%"chk8" + 0] <- %"v85"
    => goto "L78";
  @"L78":
    %"v94" : L = Ptoi %"v28";
    %"v95" : W = (Cmp Ne L) %"v94", #0
    => br %"v95" ? "L90" : "L92";
  @"L90":
    %"v97" = %"v28" +p #24;
    %"chk9" : A = (Check 0 4 Read 1) %"v97";
    %"v98" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"v99" : W = And %"v98", #4294967294;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v97";
    store Ww [%"chk10" + 0] <- %"v99"
    => goto "L92";
  @"L92":
    %"v108" : L = Ptoi %"v2";
    %"v109" : L = Ptoi #0;
    %"v110" : W = (Cmp Ne L) %"v108", %"v109"
    => br %"v110" ? "L111" : "L112";
  @"L111":
    %"chk11" : A = (Check 0 8 Read 8) %"v2";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v115" = %"v114" +p #24;
    %"chk12" : A = (Check 0 4 Read 1) %"v115";
    %"v116" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"v117" : W = Shl %"v116", #31;
    %"v118" : W = Shr %"v117", #31;
    %"v119" : W = (Cmp Ne W) %"v118", #0
    => goto "L112";
  @"L112" [%"v120" : W = phi("L92" => #0, "L111" => %"v119")]:
    => br %"v120" ? "L104" : "L31";
  @"L104":
    %"chk13" : A = (Check 0 8 Read 8) %"v4";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Read 8) %"v2";
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v131" : W = (Cmp Sgt W) %"v6", #0;
    %"v133" : W = (Cmp Sgt W) %"v8", #0;
    %"v134" : W = (Cmp Ne W) %"v131", %"v133"
    => br %"v134" ? "L127" : "L128";
  @"L127":
    %"v136" = %"v126" +p #24;
    %"chk15" : A = (Check 0 4 Read 1) %"v136";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"v138" : W = And %"v137", #4294967294;
    %"v140" : W = Or %"v138", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v136";
    store Ww [%"chk16" + 0] <- %"v140";
    %"v144" = %"v123" +p #24;
    %"chk17" : A = (Check 0 4 Read 1) %"v144";
    %"v145" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v146" : W = And %"v145", #4294967294;
    %"v148" : W = Or %"v146", #1;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v144";
    store Ww [%"chk18" + 0] <- %"v148";
    %"v152" = %"v14" +p #24;
    %"v153" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v154" : W = And %"v153", #4294967294;
    store Ww [%"chk6" + 0] <- %"v154";
    %"v163" : W = (Cmp Slt W) %"v6", #0
    => br %"v163" ? "L159" : "L160";
  @"L159":
    %"v165" = %"v126" +p #8;
    %"chk21" : A = (HalfCheck Lower 0 8 Write 8) %"chk15", %"v165";
    store.ptr [%"chk21" + 0] <- %"v23";
    %"chk22" : A = (Renew 0 8 Write 8) %"chk1", %"v20";
    store.ptr [%"chk22" + 0] <- %"v126";
    %"v170" = %"v123" +p #16;
    %"chk23" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"v170";
    store.ptr [%"chk23" + 0] <- %"v28";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk2", %"v25";
    store.ptr [%"chk24" + 0] <- %"v123"
    => goto "L161";
  @"L160":
    %"v175" = %"v126" +p #16;
    %"chk25" : A = (HalfCheck Lower 0 8 Write 8) %"chk15", %"v175";
    store.ptr [%"chk25" + 0] <- %"v28";
    %"chk26" : A = (Renew 0 8 Write 8) %"chk2", %"v25";
    store.ptr [%"chk26" + 0] <- %"v126";
    %"v180" = %"v123" +p #8;
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk17", %"v180";
    store.ptr [%"chk27" + 0] <- %"v23";
    %"chk28" : A = (Renew 0 8 Write 8) %"chk1", %"v20";
    store.ptr [%"chk28" + 0] <- %"v123"
    => goto "L161";
  @"L161":
    %"chk29" : A = (Renew 0 8 Write 8) %"chk13", %"v4";
    store.ptr [%"chk29" + 0] <- %"v14"
    => goto "L31";
  @"L128":
    %"chk30" : A = (Renew 0 8 Write 8) %"chk13", %"v4";
    store.ptr [%"chk30" + 0] <- %"v126";
    %"v189" = %"v126" +p #24;
    %"chk31" : A = (Check 0 4 Read 1) %"v189";
    %"v190" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v191" : W = And %"v190", #4294967294;
    %"chk32" : A = (Renew 0 4 Write 1) %"chk31", %"v189";
    store Ww [%"chk32" + 0] <- %"v191";
    %"v197" = %"v123" +p #24;
    %"chk33" : A = (Check 0 4 Read 1) %"v197";
    %"v198" : W = (RawLoad (LdNarrow Uw) 0) %"chk33";
    %"v199" : W = And %"v198", #4294967294;
    %"v201" : W = Or %"v199", #1;
    %"chk34" : A = (Renew 0 4 Write 1) %"chk33", %"v197";
    store Ww [%"chk34" + 0] <- %"v201";
    %"v208" : W = (Cmp Slt W) %"v6", #0
    => br %"v208" ? "L204" : "L205";
  @"L204":
    %"v210" = %"v123" +p #8;
    %"v212" = %"v126" +p #16;
    %"chk35" : A = (HalfCheck Lower 0 8 Read 8) %"chk31", %"v212";
    %"v213" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (HalfCheck Lower 0 8 Write 8) %"chk33", %"v210";
    store.ptr [%"chk36" + 0] <- %"v213";
    %"chk37" : A = (Renew 0 8 Write 8) %"chk35", %"v212";
    store.ptr [%"chk37" + 0] <- %"v123"
    => goto "L31";
  @"L205":
    %"v218" = %"v123" +p #16;
    %"v220" = %"v126" +p #8;
    %"chk38" : A = (HalfCheck Lower 0 8 Read 8) %"chk31", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (HalfCheck Lower 0 8 Write 8) %"chk33", %"v218";
    store.ptr [%"chk39" + 0] <- %"v221";
    %"chk40" : A = (Renew 0 8 Write 8) %"chk38", %"v220";
    store.ptr [%"chk40" + 0] <- %"v123"
    => goto "L31";
  @"L31":
    => ret void
} }.

Definition fn_glibc_tsearch'23trecurse_r : func :=
  ir_fn{ "local" "glibc_tsearch#trecurse_r"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v12" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v13";
    %"v15" : L = Ptoi #0;
    %"v16" : W = (Cmp Eq L) %"v14", %"v15"
    => br %"v16" ? "L17" : "L18";
  @"L17":
    %"v20" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" : L = Ptoi %"v21";
    %"v24" : W = (Cmp Eq L) %"v22", %"v15"
    => goto "L18";
  @"L18" [%"v26" : W = phi("start" => #0, "L17" => %"v24")]:
    => br %"v26" ? "L8" : "L9";
  @"L8":
    %"chk2" : F = CheckFunction %"v2";
    rawcall void %"chk2"(P %"v0", W #3, P %"v4")
    => goto "L10";
  @"L9":
    %"chk3" : F = CheckFunction %"v2";
    rawcall void %"chk3"(P %"v0", W #0, P %"v4");
    %"v37" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v39" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Ne L) %"v39", %"v15"
    => br %"v41" ? "L33" : "L35";
  @"L33":
    %"v43" = %"v0" +p #8;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk4";
    call void $"glibc_tsearch#trecurse_r"(P %"v44", P %"v2", P %"v4")
    => goto "L35";
  @"L35":
    %"chk6" : F = CheckFunction %"v2";
    rawcall void %"chk6"(P %"v0", W #1, P %"v4");
    %"v54" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v56" : L = Ptoi %"v55";
    %"v58" : W = (Cmp Ne L) %"v56", %"v15"
    => br %"v58" ? "L50" : "L52";
  @"L50":
    %"v60" = %"v0" +p #16;
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk7";
    call void $"glibc_tsearch#trecurse_r"(P %"v61", P %"v2", P %"v4")
    => goto "L52";
  @"L52":
    %"chk9" : F = CheckFunction %"v2";
    rawcall void %"chk9"(P %"v0", W #2, P %"v4")
    => goto "L10";
  @"L10":
    => ret void
} }.
