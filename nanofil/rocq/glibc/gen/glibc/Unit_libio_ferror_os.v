(** This file defines checked IR from glibc’s `libio/ferror.os` object.
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

Definition fn__IO_ferror : func :=
  ir_fn{ "export" "_IO_ferror"(P %"v0") -> (RClass W) {
  @"start":
    %"v10" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Shl %"v11", #8;
    %"v13" : W = Sar %"v12", #8;
    %"v14" : W = And %"v13", #128;
    %"v16" : W = (Cmp Eq W) %"v14", #0
    => br %"v16" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v19" : W = And %"v18", #32;
    %"v20" : W = (Cmp Ne W) %"v19", #0
    => ret %"v20";
  @"L8":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v27" : W = And %"v26", #32768;
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L29" : "L24";
  @"L29":
    call %"v33" : P = $"zthread_self_cookie"();
    %"v37" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v39" : W = (Cmp Ne W) %"v38", #0
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" = %"v0" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v45" = %"v44" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v47" : L = Ptoi %"v46";
    %"v48" : L = Ptoi #0;
    %"v49" : W = (Cmp Eq L) %"v47", %"v48"
    => goto "L41";
  @"L41" [%"v51" : W = phi("L29" => #0, "L40" => %"v49")]:
    => br %"v51" ? "L34" : "L35";
  @"L34":
    %"v53" = %"v0" +p #136;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 4 Write 1) %"v54";
    store Ww [%"chk7" + 0] <- #1;
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v58" = %"v57" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v58";
    store.ptr [%"chk9" + 0] <- %"v33"
    => goto "L24";
  @"L35":
    %"v64" = %"v0" +p #136;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" = %"v65" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Ptoi %"v33";
    %"v71" : W = (Cmp Ne L) %"v69", %"v70"
    => br %"v71" ? "L60" : "L61";
  @"L60":
    %"v74" = %"v0" +p #136;
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Check 0 4 Write 4) %"v75";
    %"v82" : W = (RawCas (CasNarrow Sw) 0) %"chk13", #0, #1;
    %"v83" : W = (Cmp Eq W) %"v82", #0
    => br %"v83" ? "L85" : "L84";
  @"L84":
    => goto "L85";
  @"L85":
    %"v86" : W = (Cmp Ne W) %"v82", #0
    => br %"v86" ? "L89" : "L78";
  @"L89":
    call void $"__GI___lll_lock_wait_private"(P %"v75")
    => goto "L78";
  @"L78":
    %"v100" = %"v0" +p #136;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk10", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v102" = %"v101" +p #8;
    %"chk15" : A = (Check 0 8 Write 8) %"v102";
    store.ptr [%"chk15" + 0] <- %"v33"
    => goto "L24";
  @"L61":
    %"v105" = %"v0" +p #136;
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v107" = %"v106" +p #4;
    %"chk17" : A = (Check 0 4 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v109" : W = Add %"v108", #1;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v107";
    store Ww [%"chk18" + 0] <- %"v109"
    => goto "L24";
  @"L24":
    %"chk19" : A = (Renew 0 4 Read 1) %"chk2", %"v0";
    %"v111" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v112" : W = And %"v111", #32;
    %"v113" : W = (Cmp Ne W) %"v112", #0;
    %"v118" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v119" : W = And %"v118", #32768;
    %"v120" : W = (Cmp Eq W) %"v119", #0
    => br %"v120" ? "L121" : "L116";
  @"L121":
    %"v127" : P = Copy $"__libc_single_threaded_internal";
    %"chk21" : A = (Check 0 1 Read 1) %"v127";
    %"v128" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v129" : W = (Cmp Ne W) %"v128", #0
    => br %"v129" ? "L130" : "L131";
  @"L130":
    %"v133" = %"v0" +p #136;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v135" = %"v134" +p #4;
    %"chk23" : A = (Check 0 4 Read 1) %"v135";
    %"v136" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v137" : W = (Cmp Eq W) %"v136", #0
    => goto "L131";
  @"L131" [%"v139" : W = phi("L121" => #0, "L130" => %"v137")]:
    => br %"v139" ? "L124" : "L125";
  @"L124":
    %"v141" = %"v0" +p #136;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v141";
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v143" = %"v142" +p #8;
    %"chk25" : A = (Check 0 8 Write 8) %"v143";
    store.ptr [%"chk25" + 0] <- #0;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk24", %"v141";
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 4 Write 1) %"v146";
    store Ww [%"chk27" + 0] <- #0
    => goto "L116";
  @"L125":
    %"v151" = %"v0" +p #136;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v153" = %"v152" +p #4;
    %"chk29" : A = (Check 0 4 Read 1) %"v153";
    %"v154" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v155" : W = (Cmp Eq W) %"v154", #0
    => br %"v155" ? "L147" : "L148";
  @"L147":
    %"v157" = %"v0" +p #136;
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v159" = %"v158" +p #8;
    %"chk31" : A = (Check 0 8 Write 8) %"v159";
    store.ptr [%"chk31" + 0] <- #0;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk28", %"v157";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 4 Read 1) %"v163";
    %"v167" : W = (RawLoad (LdNarrow Sw) 0) %"chk33"
    => goto "L168";
  @"L168" [%"v170" : W = phi("L147" => %"v167", "L168" => %"v171")]:
    %"chk34" : A = (HalfCheck Lower 0 4 Write 4) %"chk33", %"v163";
    %"v171" : W = (RawCas (CasNarrow Sw) 0) %"chk34", %"v170", #0;
    %"v172" : W = (Cmp Eq W) %"v171", %"v170"
    => br %"v172" ? "L169" : poll "L168";
  @"L169":
    %"v177" : W = (Cmp Sgt W) %"v170", #1
    => br %"v177" ? "L180" : "L116";
  @"L180":
    call void $"__GI___lll_lock_wake_private"(P %"v163")
    => goto "L116";
  @"L148":
    %"v192" = %"v0" +p #136;
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v194" = %"v193" +p #4;
    %"chk36" : A = (Check 0 4 Read 1) %"v194";
    %"v195" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v196" : W = Sub %"v195", #1;
    %"chk37" : A = (Renew 0 4 Write 1) %"chk36", %"v194";
    store Ww [%"chk37" + 0] <- %"v196"
    => goto "L116";
  @"L116":
    => ret %"v113"
} }.

Definition item_ferror : item :=
  (IAlias (a "ferror") (a "weak") (a "_IO_ferror")).
