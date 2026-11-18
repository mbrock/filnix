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

Definition hi_fn_glibc_genops'23flush_cleanup : func :=
  ir_fn{ "local" "glibc_genops#flush_cleanup"(P %"v0") -> RVoid {
  @"start":
    %"v5" : P = Copy $"glibc_genops#run_fp";
    %"chk0" : A = (Check 0 8 Read 8) %"v5";
    %"v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" : L = Ptoi %"v6";
    %"v8" : L = Ptoi #0;
    %"v9" : W = (Cmp Ne L) %"v7", %"v8"
    => br %"v9" ? "L2" : "L101";
  @"L2":
    %"v13" : P = Copy $"glibc_genops#run_fp";
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 4 Read 1) %"v14";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v16" : W = And %"v15", #32768;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L18" : "L101";
  @"L18":
    %"v24" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v26" : W = (Cmp Ne W) %"v25", #0
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v29" : P = Copy $"glibc_genops#run_fp";
    %"chk4" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v31" = %"v30" +p #136;
    %"chk5" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v33" = %"v32" +p #4;
    %"chk6" : A = (Check 0 4 Read 1) %"v33";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => goto "L28";
  @"L28" [%"v37" : W = phi("L18" => #0, "L27" => %"v35")]:
    => br %"v37" ? "L21" : "L22";
  @"L21":
    %"v38" : P = Copy $"glibc_genops#run_fp";
    %"chk7" : A = (Check 0 8 Read 8) %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v40" = %"v39" +p #136;
    %"chk8" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v42" = %"v41" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk9" + 0] <- #0;
    %"v43" : P = Copy $"glibc_genops#run_fp";
    %"chk10" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v45" = %"v44" +p #136;
    %"chk11" : A = (Check 0 8 Read 8) %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v46";
    store Ww [%"chk12" + 0] <- #0
    => goto "L101";
  @"L22":
    %"v50" : P = Copy $"glibc_genops#run_fp";
    %"chk13" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v52" = %"v51" +p #136;
    %"chk14" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v54" = %"v53" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v54";
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v56" : W = (Cmp Eq W) %"v55", #0
    => br %"v56" ? "L47" : "L48";
  @"L47":
    %"v57" : P = Copy $"glibc_genops#run_fp";
    %"chk16" : A = (Check 0 8 Read 8) %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v59" = %"v58" +p #136;
    %"chk17" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v61" = %"v60" +p #8;
    %"chk18" : A = (Check 0 8 Write 8) %"v61";
    store.ptr [%"chk18" + 0] <- #0;
    %"v63" : P = Copy $"glibc_genops#run_fp";
    %"chk19" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v65" = %"v64" +p #136;
    %"chk20" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 4 Read 1) %"v66";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk21"
    => goto "L71";
  @"L71" [%"v73" : W = phi("L47" => %"v70", "L71" => %"v74")]:
    %"chk22" : A = (HalfCheck Lower 0 4 Write 4) %"chk21", %"v66";
    %"v74" : W = (RawCas (CasNarrow Sw) 0) %"chk22", %"v73", #0;
    %"v75" : W = (Cmp Eq W) %"v74", %"v73"
    => br %"v75" ? "L72" : poll "L71";
  @"L72":
    %"v80" : W = (Cmp Sgt W) %"v73", #1
    => br %"v80" ? "L83" : "L101";
  @"L83":
    call void $"__GI___lll_lock_wake_private"(P %"v66")
    => goto "L101";
  @"L48":
    %"v94" : P = Copy $"glibc_genops#run_fp";
    %"chk23" : A = (Check 0 8 Read 8) %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v96" = %"v95" +p #136;
    %"chk24" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v98" = %"v97" +p #4;
    %"chk25" : A = (Check 0 4 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v100" : W = Sub %"v99", #1;
    %"chk26" : A = (Renew 0 4 Write 1) %"chk25", %"v98";
    store Ww [%"chk26" + 0] <- %"v100"
    => goto "L101";
  @"L101":
    %"v107" : P = Copy $"__libc_single_threaded_internal";
    %"chk27" : A = (Check 0 1 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v109" : W = (Cmp Ne W) %"v108", #0
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"v112" : P = Copy $"glibc_genops#list_all_lock";
    %"v113" = %"v112" +p #4;
    %"chk28" : A = (Check 0 4 Read 1) %"v113";
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v115" : W = (Cmp Eq W) %"v114", #0
    => goto "L111";
  @"L111" [%"v117" : W = phi("L101" => #0, "L110" => %"v115")]:
    => br %"v117" ? "L104" : "L105";
  @"L104":
    %"v118" : P = Copy $"glibc_genops#list_all_lock";
    %"v119" = %"v118" +p #8;
    %"chk29" : A = (Check 0 8 Write 8) %"v119";
    store.ptr [%"chk29" + 0] <- #0;
    %"v120" : P = Copy $"glibc_genops#list_all_lock";
    %"chk30" : A = (Check 0 4 Write 1) %"v120";
    store Ww [%"chk30" + 0] <- #0
    => goto "L103";
  @"L105":
    %"v124" : P = Copy $"glibc_genops#list_all_lock";
    %"v125" = %"v124" +p #4;
    %"chk31" : A = (Check 0 4 Read 1) %"v125";
    %"v126" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v127" : W = (Cmp Eq W) %"v126", #0
    => br %"v127" ? "L121" : "L122";
  @"L121":
    %"v128" : P = Copy $"glibc_genops#list_all_lock";
    %"v129" = %"v128" +p #8;
    %"chk32" : A = (Check 0 8 Write 8) %"v129";
    store.ptr [%"chk32" + 0] <- #0;
    %"v131" : P = Copy $"glibc_genops#list_all_lock";
    %"chk33" : A = (Check 0 4 Read 1) %"v131";
    %"v135" : W = (RawLoad (LdNarrow Sw) 0) %"chk33"
    => goto "L136";
  @"L136" [%"v138" : W = phi("L121" => %"v135", "L136" => %"v139")]:
    %"chk34" : A = (HalfCheck Lower 0 4 Write 4) %"chk33", %"v131";
    %"v139" : W = (RawCas (CasNarrow Sw) 0) %"chk34", %"v138", #0;
    %"v140" : W = (Cmp Eq W) %"v139", %"v138"
    => br %"v140" ? "L137" : poll "L136";
  @"L137":
    %"v145" : W = (Cmp Sgt W) %"v138", #1
    => br %"v145" ? "L148" : "L103";
  @"L148":
    call void $"__GI___lll_lock_wake_private"(P %"v131")
    => goto "L103";
  @"L122":
    %"v159" : P = Copy $"glibc_genops#list_all_lock";
    %"v160" = %"v159" +p #4;
    %"chk35" : A = (Check 0 4 Read 1) %"v160";
    %"v161" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v162" : W = Sub %"v161", #1;
    %"chk36" : A = (Renew 0 4 Write 1) %"chk35", %"v160";
    store Ww [%"chk36" + 0] <- %"v162"
    => goto "L103";
  @"L103":
    => ret void
} }.
