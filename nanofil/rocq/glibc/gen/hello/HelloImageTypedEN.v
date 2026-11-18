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

Definition hello_image_fn_glibc_strops'23enlarge_userbuf : func :=
  ir_fn{ "local" "glibc_strops#enlarge_userbuf"(P %"v0", L %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v11" = %"v0" +p #64;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v0" +p #56;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" : L = Ptoi %"v12";
    %"v17" : L = Ptoi %"v15";
    %"v18" : L = Sub %"v16", %"v17";
    %"v19" : W = (Cmp Sle L) %"v2", %"v18"
    => br %"v19" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v23" = %"v0" +p #48;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v26" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v28" : L = Ptoi %"v24";
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Sub %"v28", %"v29";
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v36" : W = And %"v35", #1
    => br %"v36" ? "L31" : "L33";
  @"L31":
    => ret #1;
  @"L33":
    %"v40" : L = Add %"v2", #100;
    %"v43" = %"v0" +p #56;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v47" : P = $"malloc"(L %"v40");
    %"v52" : L = Ptoi %"v47";
    %"v53" : L = Ptoi #0;
    %"v54" : W = (Cmp Eq L) %"v52", %"v53"
    => br %"v54" ? "L48" : "L50";
  @"L48":
    => ret #1;
  @"L50":
    %"v60" : L = Ptoi %"v44";
    %"v62" : W = (Cmp Ne L) %"v60", %"v53"
    => br %"v62" ? "L56" : "L58";
  @"L56":
    %"v66" = %"v0" +p #64;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v69" = %"v0" +p #56;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v71" : L = Ptoi %"v67";
    %"v72" : L = Ptoi %"v70";
    %"v73" : L = Sub %"v71", %"v72";
    call %"v74" : P = $"__GI_memcpy"(P %"v47", P %"v44", L %"v73");
    call void $"free"(P %"v44");
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v69";
    store.ptr [%"chk8" + 0] <- #0
    => goto "L58";
  @"L58":
    %"v82" = %"v47" +p %"v40";
    call void $"__GI__IO_setb"(P %"v0", P %"v47", P %"v82", W #1)
    => br %"v4" ? "L83" : "L84";
  @"L83":
    %"v88" = %"v0" +p #32;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk3", %"v88";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v94" : L = Ptoi %"v92";
    %"v96" : L = Sub %"v94", %"v60";
    %"v97" = %"v47" +p %"v96";
    %"chk10" : A = (Renew 0 8 Write 8) %"chk3", %"v88";
    store.ptr [%"chk10" + 0] <- %"v97";
    %"v99" = %"v0" +p #40;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v99";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v105" : L = Ptoi %"v103";
    %"v107" : L = Sub %"v105", %"v60";
    %"v108" = %"v47" +p %"v107";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk11", %"v99";
    store.ptr [%"chk12" + 0] <- %"v108";
    %"v110" = %"v0" +p #48;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v110";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v116" : L = Ptoi %"v114";
    %"v118" : L = Sub %"v116", %"v60";
    %"v119" = %"v47" +p %"v118";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk2", %"v110";
    store.ptr [%"chk14" + 0] <- %"v119";
    %"v121" = %"v0" +p #8;
    %"chk15" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v121";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v127" : L = Ptoi %"v125";
    %"v129" : L = Sub %"v127", %"v60";
    %"v130" = %"v47" +p %"v129";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk15", %"v121";
    store.ptr [%"chk16" + 0] <- %"v130";
    %"v132" = %"v0" +p #24;
    %"chk17" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v132";
    store.ptr [%"chk17" + 0] <- %"v47";
    %"v135" = %"v0" +p #16;
    %"v137" = %"v0" +p #64;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v135";
    store.ptr [%"chk19" + 0] <- %"v138"
    => goto "L85";
  @"L84":
    %"v140" = %"v0" +p #24;
    %"chk20" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v140";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v146" : L = Ptoi %"v144";
    %"v148" : L = Sub %"v146", %"v60";
    %"v149" = %"v47" +p %"v148";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk20", %"v140";
    store.ptr [%"chk21" + 0] <- %"v149";
    %"v151" = %"v0" +p #8;
    %"chk22" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v151";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v157" : L = Ptoi %"v155";
    %"v159" : L = Sub %"v157", %"v60";
    %"v160" = %"v47" +p %"v159";
    %"chk23" : A = (Renew 0 8 Write 8) %"chk22", %"v151";
    store.ptr [%"chk23" + 0] <- %"v160";
    %"v162" = %"v0" +p #16;
    %"chk24" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v162";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v168" : L = Ptoi %"v166";
    %"v170" : L = Sub %"v168", %"v60";
    %"v171" = %"v47" +p %"v170";
    %"chk25" : A = (Renew 0 8 Write 8) %"chk24", %"v162";
    store.ptr [%"chk25" + 0] <- %"v171";
    %"v173" = %"v0" +p #40;
    %"chk26" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v173";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v179" : L = Ptoi %"v177";
    %"v181" : L = Sub %"v179", %"v60";
    %"v182" = %"v47" +p %"v181";
    %"chk27" : A = (Renew 0 8 Write 8) %"chk26", %"v173";
    store.ptr [%"chk27" + 0] <- %"v182";
    %"v184" = %"v0" +p #32;
    %"chk28" : A = (Renew 0 8 Write 8) %"chk3", %"v184";
    store.ptr [%"chk28" + 0] <- %"v47";
    %"v187" = %"v0" +p #48;
    %"v189" = %"v0" +p #64;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk2", %"v187";
    store.ptr [%"chk30" + 0] <- %"v190"
    => goto "L85";
  @"L85":
    %"v196" : W = (Cmp Sge L) %"v2", %"v30"
    => br %"v196" ? "L193" : "L192";
  @"L192":
    %"v197" : P = Copy $"glibc_strops#str.257";
    %"v198" : P = Copy $"glibc_strops#str.258";
    %"v199" : P = Copy $"glibc_strops#str.259";
    call void $"__libc_assert_fail"(P %"v197", P %"v198", W #225, P %"v199")
    => goto "L193";
  @"L193":
    => br %"v4" ? "L200" : "L201";
  @"L200":
    %"v205" = %"v0" +p #24;
    %"chk31" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v208" = %"v206" +p %"v30";
    %"v211" : L = Sub %"v2", %"v30";
    call %"v212" : P = $"__GI_memset"(P %"v208", W #0, L %"v211")
    => goto "L202";
  @"L201":
    %"v214" = %"v0" +p #32;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk3", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v217" = %"v215" +p %"v30";
    %"v220" : L = Sub %"v2", %"v30";
    call %"v221" : P = $"__GI_memset"(P %"v217", W #0, L %"v220")
    => goto "L202";
  @"L202":
    => ret #0
} }.

Definition hello_image_fn_glibc_wstrops'23enlarge_userbuf : func :=
  ir_fn{ "local" "glibc_wstrops#enlarge_userbuf"(P %"v0", L %"v2", W %"v4") -> (RClass W) {
  @"start":
    %"v11" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #56;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" = %"v17" +p #48;
    %"chk3" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v20" : L = Ptoi %"v14";
    %"v21" : L = Ptoi %"v19";
    %"v22" : L = Sub %"v20", %"v21";
    %"v23" : L = Div %"v22", #4;
    %"v24" : W = (Cmp Sle L) %"v2", %"v23"
    => br %"v24" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v28" = %"v0" +p #160;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v32" = %"v29" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v35" = %"v29" +p #24;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v37" : L = Ptoi %"v33";
    %"v38" : L = Ptoi %"v36";
    %"v39" : L = Sub %"v37", %"v38";
    %"v40" : L = Div %"v39", #4;
    %"v45" = %"v0" +p #116;
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v45";
    %"v46" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v47" : W = Shl %"v46", #8;
    %"v48" : W = Sar %"v47", #8;
    %"v49" : W = And %"v48", #8
    => br %"v49" ? "L41" : "L43";
  @"L41":
    => ret #1;
  @"L43":
    %"v53" : L = Add %"v2", #100;
    %"v59" : W = (Cmp Ugt L) %"v53", #4611686018427387903
    => br %"v59" ? "L54" : "L56";
  @"L54":
    => ret #1;
  @"L56":
    %"v65" = %"v29" +p #48;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk5", %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v69" : L = Shl %"v53", #2;
    call %"v70" : P = $"malloc"(L %"v69");
    %"v75" : L = Ptoi %"v70";
    %"v76" : L = Ptoi #0;
    %"v77" : W = (Cmp Eq L) %"v75", %"v76"
    => br %"v77" ? "L71" : "L73";
  @"L71":
    => ret #1;
  @"L73":
    %"v83" : L = Ptoi %"v66";
    %"v85" : W = (Cmp Ne L) %"v83", %"v76"
    => br %"v85" ? "L79" : "L81";
  @"L79":
    %"v89" = %"v0" +p #160;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk0", %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v91" = %"v90" +p #56;
    %"chk10" : A = (Check 0 8 Read 8) %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v96" = %"v95" +p #48;
    %"chk12" : A = (Check 0 8 Read 8) %"v96";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v98" : L = Ptoi %"v92";
    %"v99" : L = Ptoi %"v97";
    %"v100" : L = Sub %"v98", %"v99";
    %"v101" : L = Div %"v100", #4;
    call %"v102" : P = $"__wmemcpy"(P %"v70", P %"v66", L %"v101");
    call void $"free"(P %"v66");
    %"v105" = %"v29" +p #48;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk8", %"v105";
    store.ptr [%"chk13" + 0] <- #0
    => goto "L81";
  @"L81":
    %"v111" = %"v70" +p %"v69";
    call void $"__GI__IO_wsetb"(P %"v0", P %"v70", P %"v111", W #1)
    => br %"v4" ? "L112" : "L113";
  @"L112":
    %"v117" = %"v29" +p #24;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk6", %"v117";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v123" : L = Ptoi %"v121";
    %"v125" : L = Sub %"v123", %"v83";
    %"v126" : L = Div %"v125", #4;
    %"v127" : L = Shl %"v126", #2;
    %"v128" = %"v70" +p %"v127";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk6", %"v117";
    store.ptr [%"chk15" + 0] <- %"v128";
    %"v130" = %"v29" +p #32;
    %"chk16" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v130";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v136" : L = Ptoi %"v134";
    %"v138" : L = Sub %"v136", %"v83";
    %"v139" : L = Div %"v138", #4;
    %"v140" : L = Shl %"v139", #2;
    %"v141" = %"v70" +p %"v140";
    %"chk17" : A = (Renew 0 8 Write 8) %"chk16", %"v130";
    store.ptr [%"chk17" + 0] <- %"v141";
    %"v143" = %"v29" +p #40;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk5", %"v143";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v149" : L = Ptoi %"v147";
    %"v151" : L = Sub %"v149", %"v83";
    %"v152" : L = Div %"v151", #4;
    %"v153" : L = Shl %"v152", #2;
    %"v154" = %"v70" +p %"v153";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk5", %"v143";
    store.ptr [%"chk19" + 0] <- %"v154";
    %"chk20" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v29";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v160" : L = Ptoi %"v158";
    %"v162" : L = Sub %"v160", %"v83";
    %"v163" : L = Div %"v162", #4;
    %"v164" : L = Shl %"v163", #2;
    %"v165" = %"v70" +p %"v164";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk20", %"v29";
    store.ptr [%"chk21" + 0] <- %"v165";
    %"v167" = %"v29" +p #16;
    %"chk22" : A = (HalfCheck Lower 0 8 Write 8) %"chk5", %"v167";
    store.ptr [%"chk22" + 0] <- %"v70";
    %"v170" = %"v29" +p #8;
    %"v172" = %"v29" +p #56;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk5", %"v172";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (HalfCheck Lower 0 8 Write 8) %"chk5", %"v170";
    store.ptr [%"chk24" + 0] <- %"v173"
    => goto "L114";
  @"L113":
    %"v175" = %"v29" +p #16;
    %"chk25" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v175";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v181" : L = Ptoi %"v179";
    %"v183" : L = Sub %"v181", %"v83";
    %"v184" : L = Div %"v183", #4;
    %"v185" : L = Shl %"v184", #2;
    %"v186" = %"v70" +p %"v185";
    %"chk26" : A = (Renew 0 8 Write 8) %"chk25", %"v175";
    store.ptr [%"chk26" + 0] <- %"v186";
    %"chk27" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v29";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v192" : L = Ptoi %"v190";
    %"v194" : L = Sub %"v192", %"v83";
    %"v195" : L = Div %"v194", #4;
    %"v196" : L = Shl %"v195", #2;
    %"v197" = %"v70" +p %"v196";
    %"chk28" : A = (Renew 0 8 Write 8) %"chk27", %"v29";
    store.ptr [%"chk28" + 0] <- %"v197";
    %"v199" = %"v29" +p #8;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v199";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v205" : L = Ptoi %"v203";
    %"v207" : L = Sub %"v205", %"v83";
    %"v208" : L = Div %"v207", #4;
    %"v209" : L = Shl %"v208", #2;
    %"v210" = %"v70" +p %"v209";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk29", %"v199";
    store.ptr [%"chk30" + 0] <- %"v210";
    %"v212" = %"v29" +p #32;
    %"chk31" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v212";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v218" : L = Ptoi %"v216";
    %"v220" : L = Sub %"v218", %"v83";
    %"v221" : L = Div %"v220", #4;
    %"v222" : L = Shl %"v221", #2;
    %"v223" = %"v70" +p %"v222";
    %"chk32" : A = (Renew 0 8 Write 8) %"chk31", %"v212";
    store.ptr [%"chk32" + 0] <- %"v223";
    %"v225" = %"v29" +p #24;
    %"chk33" : A = (Renew 0 8 Write 8) %"chk6", %"v225";
    store.ptr [%"chk33" + 0] <- %"v70";
    %"v228" = %"v29" +p #40;
    %"v230" = %"v29" +p #56;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk5", %"v230";
    %"v231" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (Renew 0 8 Write 8) %"chk5", %"v228";
    store.ptr [%"chk35" + 0] <- %"v231"
    => goto "L114";
  @"L114":
    %"v237" : W = (Cmp Sge L) %"v2", %"v40"
    => br %"v237" ? "L234" : "L233";
  @"L233":
    %"v238" : P = Copy $"glibc_wstrops#str.257";
    %"v239" : P = Copy $"glibc_wstrops#str.258";
    %"v240" : P = Copy $"glibc_wstrops#str.259";
    call void $"__libc_assert_fail"(P %"v238", P %"v239", W #228, P %"v240")
    => goto "L234";
  @"L234":
    => br %"v4" ? "L241" : "L242";
  @"L241":
    %"v246" = %"v29" +p #16;
    %"chk36" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v249" : L = Shl %"v40", #2;
    %"v250" = %"v247" +p %"v249";
    %"v253" : L = Sub %"v2", %"v40";
    call %"v254" : P = $"__GI___wmemset"(P %"v250", W #0, L %"v253")
    => goto "L243";
  @"L242":
    %"v256" = %"v29" +p #24;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk6", %"v256";
    %"v257" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v259" : L = Shl %"v40", #2;
    %"v260" = %"v257" +p %"v259";
    %"v263" : L = Sub %"v2", %"v40";
    call %"v264" : P = $"__GI___wmemset"(P %"v260", W #0, L %"v263")
    => goto "L243";
  @"L243":
    => ret #0
} }.
