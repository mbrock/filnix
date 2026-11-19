(** This file defines checked IR from glibc’s `libio/ioputs.os` object.
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

Definition fn___GI__IO_puts : func :=
  ir_fn{ "export" "__GI__IO_puts"(P %"v0") -> (RClass W) {
  @"start":
    call %"v6" : L = $"__GI_strlen"(P %"v0");
    %"v11" : P = Copy $"stdout";
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 4 Read 1) %"v12";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v18" : W = And %"v17", #32768;
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => br %"v19" ? "L20" : "L109";
  @"L20":
    call %"v24" : P = $"zthread_self_cookie"();
    %"v28" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v30" : W = (Cmp Ne W) %"v29", #0
    => br %"v30" ? "L31" : "L32";
  @"L31":
    %"v34" = %"v12" +p #136;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v36" = %"v35" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v38" : L = Ptoi %"v37";
    %"v39" : L = Ptoi #0;
    %"v40" : W = (Cmp Eq L) %"v38", %"v39"
    => goto "L32";
  @"L32" [%"v42" : W = phi("L20" => #0, "L31" => %"v40")]:
    => br %"v42" ? "L25" : "L26";
  @"L25":
    %"v44" = %"v12" +p #136;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Write 1) %"v45";
    store Ww [%"chk6" + 0] <- #1;
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v49" = %"v48" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v49";
    store.ptr [%"chk8" + 0] <- %"v24"
    => goto "L109";
  @"L26":
    %"v55" = %"v12" +p #136;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v57" = %"v56" +p #8;
    %"chk10" : A = (Check 0 8 Read 8) %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v60" : L = Ptoi %"v58";
    %"v61" : L = Ptoi %"v24";
    %"v62" : W = (Cmp Ne L) %"v60", %"v61"
    => br %"v62" ? "L51" : "L52";
  @"L51":
    %"v65" = %"v12" +p #136;
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk12" : A = (Check 0 4 Write 4) %"v66";
    %"v73" : W = (RawCas (CasNarrow Sw) 0) %"chk12", #0, #1;
    %"v74" : W = (Cmp Eq W) %"v73", #0
    => br %"v74" ? "L76" : "L75";
  @"L75":
    => goto "L76";
  @"L76":
    %"v77" : W = (Cmp Ne W) %"v73", #0
    => br %"v77" ? "L80" : "L69";
  @"L80":
    call void $"__GI___lll_lock_wait_private"(P %"v66")
    => goto "L69";
  @"L69":
    %"v91" = %"v12" +p #136;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk9", %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v93" = %"v92" +p #8;
    %"chk14" : A = (Check 0 8 Write 8) %"v93";
    store.ptr [%"chk14" + 0] <- %"v24"
    => goto "L109";
  @"L52":
    %"v96" = %"v12" +p #136;
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v98" = %"v97" +p #4;
    %"chk16" : A = (Check 0 4 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v100" : W = Add %"v99", #1;
    %"chk17" : A = (Renew 0 4 Write 1) %"chk16", %"v98";
    store Ww [%"chk17" + 0] <- %"v100"
    => goto "L109";
  @"L109":
    %"v122" : P = Copy $"stdout";
    %"chk18" : A = (Check 0 8 Read 8) %"v122";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v124" = %"v123" +p #192;
    %"chk19" : A = (Check 0 4 Read 1) %"v124";
    %"v125" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v126" : W = (Cmp Eq W) %"v125", #0
    => br %"v126" ? "L119" : "L121";
  @"L119":
    %"v127" : P = Copy $"stdout";
    %"chk20" : A = (Check 0 8 Read 8) %"v127";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v129" = %"v128" +p #192;
    %"chk21" : A = (Check 0 4 Write 1) %"v129";
    store Ww [%"chk21" + 0] <- #4294967295
    => goto "L121";
  @"L121":
    %"v131" : P = Copy $"stdout";
    %"chk22" : A = (Check 0 8 Read 8) %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v133" = %"v132" +p #192;
    %"chk23" : A = (Check 0 4 Read 1) %"v133";
    %"v134" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v159" : W = (Cmp Eq W) %"v134", #4294967295
    => br %"v159" ? "L162" : "L163";
  @"L162":
    %"v164" : P = Copy $"stdout";
    %"chk24" : A = (Check 0 8 Read 8) %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v166" = %"v165" +p #216;
    %"chk25" : A = (Check 0 8 Read 8) %"v166";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v4" : L = Ptoi %"v167";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v169" = %"v167" +p #56;
    %"chk26" : A = (Check 0 8 Read 8) %"v169";
    %"v170" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v171" : P = Copy $"stdout";
    %"chk27" : A = (Check 0 8 Read 8) %"v171";
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : F = CheckFunction %"v170";
    rawcall %"v175" : L = %"chk28"(P %"v172", P %"v0", L %"v6");
    %"v177" : W = (Cmp Eq L) %"v175", %"v6"
    => goto "L163";
  @"L163" [%"v179" : W = phi("L121" => #0, "iw_1.join" => %"v177")]:
    => br %"v179" ? "L180" : "L181";
  @"L180":
    %"v185" : P = Copy $"stdout";
    %"chk29" : A = (Check 0 8 Read 8) %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v187" = %"v186" +p #40;
    %"chk30" : A = (Check 0 8 Read 8) %"v187";
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v189" : P = Copy $"stdout";
    %"chk31" : A = (Check 0 8 Read 8) %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v191" = %"v190" +p #48;
    %"chk32" : A = (Check 0 8 Read 8) %"v191";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v193" : L = Ptoi %"v188";
    %"v194" : L = Ptoi %"v192";
    %"v195" : W = (Cmp Uge L) %"v193", %"v194"
    => br %"v195" ? "L182" : "L183";
  @"L182":
    %"v198" : P = Copy $"stdout";
    %"chk33" : A = (Check 0 8 Read 8) %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk33";
    call %"v200" : W = $"__GI___overflow"(P %"v199", W #10)
    => goto "L184";
  @"L183":
    %"v201" : P = Copy $"stdout";
    %"chk34" : A = (Check 0 8 Read 8) %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v203" = %"v202" +p #40;
    %"chk35" : A = (Check 0 8 Read 8) %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v205" = %"v204" +p #1;
    %"chk36" : A = (Renew 0 8 Write 8) %"chk35", %"v203";
    store.ptr [%"chk36" + 0] <- %"v205";
    %"chk37" : A = (Check 0 1 Write 1) %"v204";
    store Wb [%"chk37" + 0] <- #10
    => goto "L184";
  @"L184" [%"v206" : W = phi("L182" => %"v200", "L183" => #10)]:
    %"v208" : W = (Cmp Ne W) %"v206", #4294967295
    => goto "L181";
  @"L181" [%"v210" : W = phi("L163" => #0, "L184" => %"v208")]:
    => br %"v210" ? "L101" : "L103";
  @"L101":
    %"v215" : L = Add %"v6", #1;
    %"v216" : W = (Cmp Ugt L) %"v215", #2147483647
    => br %"v216" ? "L103" : "L212";
  @"L212":
    => goto "L103";
  @"L103" [%"pr.1" : W = phi("L212" => %"v215", "L101" => #2147483647, "L181" => #4294967295)]:
    %"chk38" : A = (Renew 0 4 Read 1) %"chk1", %"v12";
    %"iw_2.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_2.v10" : W = And %"iw_2.v9", #32768;
    %"iw_2.v11" : W = (Cmp Eq W) %"iw_2.v10", #0
    => br %"iw_2.v11" ? "iw_2.L5" : "L9";
  @"iw_2.L5":
    %"iw_2.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_2.v17" : W = And %"iw_2.v16", #32768;
    %"iw_2.v18" : W = (Cmp Eq W) %"iw_2.v17", #0
    => br %"iw_2.v18" ? "iw_2.L19" : "L9";
  @"iw_2.L19":
    %"iw_2.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk40" : A = (Check 0 1 Read 1) %"iw_2.v25";
    %"iw_2.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk40";
    %"iw_2.v27" : W = (Cmp Ne W) %"iw_2.v26", #0
    => br %"iw_2.v27" ? "iw_2.L28" : "iw_2.L29";
  @"iw_2.L28":
    %"iw_2.v31" = %"v12" +p #136;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_2.v31";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_2.v33" = %"iw_2.v32" +p #4;
    %"chk42" : A = (Check 0 4 Read 1) %"iw_2.v33";
    %"iw_2.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"iw_2.v35" : W = (Cmp Eq W) %"iw_2.v34", #0
    => goto "iw_2.L29";
  @"iw_2.L29" [%"iw_2.v37" : W = phi("iw_2.L19" => #0, "iw_2.L28" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L22" : "iw_2.L23";
  @"iw_2.L22":
    %"iw_2.v39" = %"v12" +p #136;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_2.v39";
    %"iw_2.v40" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_2.v41" = %"iw_2.v40" +p #8;
    %"chk44" : A = (Check 0 8 Write 8) %"iw_2.v41";
    store.ptr [%"chk44" + 0] <- #0;
    %"chk45" : A = (Renew 0 8 Read 8) %"chk43", %"iw_2.v39";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"chk46" : A = (Check 0 4 Write 1) %"iw_2.v44";
    store Ww [%"chk46" + 0] <- #0
    => goto "L9";
  @"iw_2.L23":
    %"iw_2.v49" = %"v12" +p #136;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_2.v49";
    %"iw_2.v50" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"iw_2.v51" = %"iw_2.v50" +p #4;
    %"chk48" : A = (Check 0 4 Read 1) %"iw_2.v51";
    %"iw_2.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_2.v53" : W = (Cmp Eq W) %"iw_2.v52", #0
    => br %"iw_2.v53" ? "iw_2.L45" : "iw_2.L46";
  @"iw_2.L45":
    %"iw_2.v55" = %"v12" +p #136;
    %"iw_2.v56" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"iw_2.v57" = %"iw_2.v56" +p #8;
    %"chk50" : A = (Check 0 8 Write 8) %"iw_2.v57";
    store.ptr [%"chk50" + 0] <- #0;
    %"chk51" : A = (Renew 0 8 Read 8) %"chk47", %"iw_2.v55";
    %"iw_2.v61" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"chk52" : A = (Check 0 4 Read 1) %"iw_2.v61";
    %"iw_2.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk52"
    => goto "iw_2.L66";
  @"iw_2.L66" [%"iw_2.v68" : W = phi("iw_2.L45" => %"iw_2.v65", "iw_2.L66" => %"iw_2.v69")]:
    %"chk53" : A = (HalfCheck Lower 0 4 Write 4) %"chk52", %"iw_2.v61";
    %"iw_2.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk53", %"iw_2.v68", #0;
    %"iw_2.v70" : W = (Cmp Eq W) %"iw_2.v69", %"iw_2.v68"
    => br %"iw_2.v70" ? "iw_2.L67" : poll "iw_2.L66";
  @"iw_2.L67":
    %"iw_2.v75" : W = (Cmp Sgt W) %"iw_2.v68", #1
    => br %"iw_2.v75" ? "iw_2.L78" : "L9";
  @"iw_2.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_2.v61")
    => goto "L9";
  @"iw_2.L46":
    %"iw_2.v90" = %"v12" +p #136;
    %"iw_2.v91" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"iw_2.v92" = %"iw_2.v91" +p #4;
    %"chk55" : A = (Check 0 4 Read 1) %"iw_2.v92";
    %"iw_2.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk55";
    %"iw_2.v94" : W = Sub %"iw_2.v93", #1;
    %"chk56" : A = (Renew 0 4 Write 1) %"chk55", %"iw_2.v92";
    store Ww [%"chk56" + 0] <- %"iw_2.v94"
    => goto "L9";
  @"L9":
    => ret %"pr.1"
} }.

Definition item_puts : item :=
  (IAlias (a "puts") (a "export") (a "__GI__IO_puts")).
