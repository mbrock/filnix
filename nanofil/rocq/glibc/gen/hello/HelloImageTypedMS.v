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

Definition hello_image_fn_glibc_qsort'23msort_with_tmp : func :=
  ir_fn{ "local" "glibc_qsort#msort_with_tmp"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"v14" : W = (Cmp Ule L) %"v4", #1
    => br %"v14" ? "L10" : "L12";
  @"L10":
    => ret void;
  @"L12":
    %"v17" : L = Shr %"v4", #1;
    %"v20" : L = Sub %"v4", %"v17";
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v25" : L = (RawLoad LdL 0) %"chk0";
    %"v26" : L = Mul %"v17", %"v25";
    %"v27" = %"v2" +p %"v26";
    call void $"glibc_qsort#msort_with_tmp"(P %"v0", P %"v2", L %"v17");
    call void $"glibc_qsort#msort_with_tmp"(P %"v0", P %"v27", L %"v20");
    %"v36" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Renew 0 8 Read 1) %"chk0", %"v0";
    %"v40" : L = (RawLoad LdL 0) %"chk2";
    %"v43" = %"v0" +p #16;
    %"v44" : P = (RawLoadPointer (-16) load_effects) %"chk1";
    %"v47" = %"v0" +p #24;
    %"v48" : P = (RawLoadPointer (-8) load_effects) %"chk1";
    %"v50" = %"v0" +p #8;
    %"v51" : W = (RawLoad (LdNarrow Uw) 8) %"chk2";
    %"v207" : W = (Cmp Eq W) %"v51", #1
    => br %"v207" ? "L55" : "L208";
  @"L55" [%"pr.40" : P = phi("L68" => %"v90", "L12" => %"v37"); %"pr.33" : L = phi("L68" => %"pr.34", "L12" => %"v20"); %"pr.24" : L = phi("L68" => %"pr.25", "L12" => %"v17"); %"pr.15" : P = phi("L68" => %"pr.16", "L12" => %"v27"); %"pr.7" : P = phi("L68" => %"pr.8", "L12" => %"v2")]:
    %"v59" : W = (Cmp Ugt L) %"pr.24", #0
    => br %"v59" ? "L60" : "L61";
  @"L60":
    %"v63" : W = (Cmp Ugt L) %"pr.33", #0
    => goto "L61";
  @"L61" [%"v65" : W = phi("L55" => #0, "L60" => %"v63")]:
    => br %"v65" ? "L56" : "L53";
  @"L56":
    %"chk6" : F = CheckFunction %"v44";
    rawcall %"v73" : W = %"chk6"(P %"pr.7", P %"pr.15", P %"v48");
    %"v74" : W = (Cmp Sle W) %"v73", #0
    => br %"v74" ? "L66" : "L67";
  @"L66":
    %"chk7" : A = (Check 0 4 Read 1) %"pr.7";
    %"v77" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"chk8" : A = (Check 0 4 Write 1) %"pr.40";
    store Ww [%"chk8" + 0] <- %"v77";
    %"v79" = %"pr.7" +p #4;
    %"v81" : L = Sub %"pr.24", #1
    => goto "L68";
  @"L67":
    %"chk9" : A = (Check 0 4 Read 1) %"pr.15";
    %"v84" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"chk10" : A = (Check 0 4 Write 1) %"pr.40";
    store Ww [%"chk10" + 0] <- %"v84";
    %"v86" = %"pr.15" +p #4;
    %"v88" : L = Sub %"pr.33", #1
    => goto "L68";
  @"L68" [%"pr.34" : L = phi("L66" => %"pr.33", "L67" => %"v88"); %"pr.25" : L = phi("L66" => %"v81", "L67" => %"pr.24"); %"pr.16" : P = phi("L66" => %"pr.15", "L67" => %"v86"); %"pr.8" : P = phi("L66" => %"v79", "L67" => %"pr.7")]:
    %"v90" = %"pr.40" +p #4
    => goto poll "L55";
  @"L92" [%"pr.41" : P = phi("L105" => %"v127", "L208" => %"v37"); %"pr.35" : L = phi("L105" => %"pr.27", "L208" => %"v20"); %"pr.26" : L = phi("L105" => %"pr.18", "L208" => %"v17"); %"pr.17" : P = phi("L105" => %"pr.10", "L208" => %"v27"); %"pr.9" : P = phi("L105" => %"pr.1", "L208" => %"v2")]:
    %"v96" : W = (Cmp Ugt L) %"pr.26", #0
    => br %"v96" ? "L97" : "L98";
  @"L97":
    %"v100" : W = (Cmp Ugt L) %"pr.35", #0
    => goto "L98";
  @"L98" [%"v102" : W = phi("L92" => #0, "L97" => %"v100")]:
    => br %"v102" ? "L93" : "L53";
  @"L93":
    %"chk11" : F = CheckFunction %"v44";
    rawcall %"v110" : W = %"chk11"(P %"pr.9", P %"pr.17", P %"v48");
    %"v111" : W = (Cmp Sle W) %"v110", #0
    => br %"v111" ? "L103" : "L104";
  @"L103":
    %"chk12" : A = (Check 0 8 Read 1) %"pr.9";
    %"v114" : L = (RawLoad LdL 0) %"chk12";
    %"chk13" : A = (Check 0 8 Write 1) %"pr.41";
    store Wl [%"chk13" + 0] <- %"v114";
    %"v116" = %"pr.9" +p #8;
    %"v118" : L = Sub %"pr.26", #1
    => goto "L105";
  @"L104":
    %"chk14" : A = (Check 0 8 Read 1) %"pr.17";
    %"v121" : L = (RawLoad LdL 0) %"chk14";
    %"chk15" : A = (Check 0 8 Write 1) %"pr.41";
    store Wl [%"chk15" + 0] <- %"v121";
    %"v123" = %"pr.17" +p #8;
    %"v125" : L = Sub %"pr.35", #1
    => goto "L105";
  @"L105" [%"pr.27" : L = phi("L103" => %"pr.35", "L104" => %"v125"); %"pr.18" : L = phi("L103" => %"v118", "L104" => %"pr.26"); %"pr.10" : P = phi("L103" => %"pr.17", "L104" => %"v123"); %"pr.1" : P = phi("L103" => %"v116", "L104" => %"pr.9")]:
    %"v127" = %"pr.41" +p #8
    => goto poll "L92";
  @"L129" [%"pr.36" : P = phi("L142" => %"v166", "L210" => %"v37"); %"pr.28" : L = phi("L142" => %"pr.29", "L210" => %"v20"); %"pr.19" : L = phi("L142" => %"pr.20", "L210" => %"v17"); %"pr.11" : P = phi("L142" => %"pr.12", "L210" => %"v27"); %"pr.2" : P = phi("L142" => %"pr.3", "L210" => %"v2")]:
    %"v133" : W = (Cmp Ugt L) %"pr.19", #0
    => br %"v133" ? "L134" : "L135";
  @"L134":
    %"v137" : W = (Cmp Ugt L) %"pr.28", #0
    => goto "L135";
  @"L135" [%"v139" : W = phi("L129" => #0, "L134" => %"v137")]:
    => br %"v139" ? "L130" : "L53";
  @"L130":
    %"chk16" : A = (Check 0 8 Read 8) %"pr.2";
    %"v145" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 8) %"pr.11";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : F = CheckFunction %"v44";
    rawcall %"v149" : W = %"chk18"(P %"v145", P %"v147", P %"v48");
    %"v150" : W = (Cmp Sle W) %"v149", #0
    => br %"v150" ? "L140" : "L141";
  @"L140":
    %"chk19" : A = (Renew 0 8 Read 8) %"chk16", %"pr.2";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 8 Write 8) %"pr.36";
    store.ptr [%"chk20" + 0] <- %"v153";
    %"v155" = %"pr.2" +p #8;
    %"v157" : L = Sub %"pr.19", #1
    => goto "L142";
  @"L141":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk17", %"pr.11";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Check 0 8 Write 8) %"pr.36";
    store.ptr [%"chk22" + 0] <- %"v160";
    %"v162" = %"pr.11" +p #8;
    %"v164" : L = Sub %"pr.28", #1
    => goto "L142";
  @"L142" [%"pr.29" : L = phi("L140" => %"pr.28", "L141" => %"v164"); %"pr.20" : L = phi("L140" => %"v157", "L141" => %"pr.19"); %"pr.12" : P = phi("L140" => %"pr.11", "L141" => %"v162"); %"pr.3" : P = phi("L140" => %"v155", "L141" => %"pr.2")]:
    %"v166" = %"pr.36" +p #8
    => goto poll "L129";
  @"L168" [%"pr.37" : P = phi("L179" => %"v191", "L180" => %"v200", "L210" => %"v37"); %"pr.30" : L = phi("L179" => %"pr.30", "L180" => %"v205", "L210" => %"v20"); %"pr.21" : L = phi("L179" => %"v196", "L180" => %"pr.21", "L210" => %"v17"); %"pr.13" : P = phi("L179" => %"pr.13", "L180" => %"v203", "L210" => %"v27"); %"pr.4" : P = phi("L179" => %"v194", "L180" => %"pr.4", "L210" => %"v2")]:
    %"v172" : W = (Cmp Ugt L) %"pr.21", #0
    => br %"v172" ? "L173" : "L174";
  @"L173":
    %"v176" : W = (Cmp Ugt L) %"pr.30", #0
    => goto "L174";
  @"L174" [%"v178" : W = phi("L168" => #0, "L173" => %"v176")]:
    => br %"v178" ? "L169" : "L53";
  @"L169":
    %"chk23" : F = CheckFunction %"v44";
    rawcall %"v186" : W = %"chk23"(P %"pr.4", P %"pr.13", P %"v48");
    %"v187" : W = (Cmp Sle W) %"v186", #0
    => br %"v187" ? "L179" : "L180";
  @"L179":
    call %"v191" : P = $"__GI_mempcpy"(P %"pr.37", P %"pr.4", L %"v40");
    %"v194" = %"pr.4" +p %"v40";
    %"v196" : L = Sub %"pr.21", #1
    => goto poll "L168";
  @"L180":
    call %"v200" : P = $"__GI_mempcpy"(P %"pr.37", P %"pr.13", L %"v40");
    %"v203" = %"pr.13" +p %"v40";
    %"v205" : L = Sub %"pr.30", #1
    => goto poll "L168";
  @"L208":
    %"v209" : W = (Cmp Eq W) %"v51", #0
    => br %"v209" ? poll "L92" : "L210";
  @"L210":
    %"v211" : W = (Cmp Eq W) %"v51", #2
    => br %"v211" ? poll "L129" : poll "L168";
  @"L53" [%"pr.39" : P = phi("L61" => %"pr.40", "L98" => %"pr.41", "L135" => %"pr.36", "L174" => %"pr.37"); %"pr.32" : L = phi("L61" => %"pr.33", "L98" => %"pr.35", "L135" => %"pr.28", "L174" => %"pr.30"); %"pr.23" : L = phi("L61" => %"pr.24", "L98" => %"pr.26", "L135" => %"pr.19", "L174" => %"pr.21"); %"pr.6" : P = phi("L61" => %"pr.7", "L98" => %"pr.9", "L135" => %"pr.2", "L174" => %"pr.4")]:
    %"v217" : W = (Cmp Ugt L) %"pr.23", #0
    => br %"v217" ? "L213" : "L215";
  @"L213":
    %"v222" : L = Mul %"pr.23", %"v40";
    call %"v223" : P = $"__GI_memcpy"(P %"pr.39", P %"pr.6", L %"v222")
    => goto "L215";
  @"L215":
    %"v226" = %"v0" +p #32;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v230" : L = Sub %"v4", %"pr.32";
    %"v232" : L = Mul %"v230", %"v40";
    call %"v233" : P = $"__GI_memcpy"(P %"v2", P %"v227", L %"v232")
    => ret void
} }.
