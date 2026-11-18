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

Definition hello_image_fn_glibc_genops'23save_for_backup : func :=
  ir_fn{ "local" "glibc_genops#save_for_backup"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"iw_1.v7" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" : L = Ptoi %"v2";
    %"iw_1.v10" : L = Ptoi %"iw_1.v8";
    %"iw_1.v11" : L = Sub %"iw_1.v9", %"iw_1.v10";
    %"iw_1.v14" = %"v0" +p #96;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v14";
    %"iw_1.v15" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "iw_1.L16";
  @"iw_1.L16" [%"iw_1.pr.3" : P = phi("iw_1.L26" => %"iw_1.v38", "start" => %"iw_1.v15"); %"iw_1.pr.1" : L = phi("iw_1.L26" => %"iw_1.pr.2", "start" => %"iw_1.v11")]:
    %"iw_1.v21" : L = Ptoi %"iw_1.pr.3";
    %"iw_1.v22" : L = Ptoi #0;
    %"iw_1.v23" : W = (Cmp Ne L) %"iw_1.v21", %"iw_1.v22"
    => br %"iw_1.v23" ? "iw_1.L17" : "iw_1.join";
  @"iw_1.L17":
    %"iw_1.v28" = %"iw_1.pr.3" +p #16;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v28";
    %"iw_1.v29" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v31" : L = (Ext Sw) %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Slt L) %"iw_1.v31", %"iw_1.pr.1"
    => br %"iw_1.v32" ? "iw_1.L24" : "iw_1.L26";
  @"iw_1.L24":
    %"iw_1.v34" = %"iw_1.pr.3" +p #16;
    %"iw_1.v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"iw_1.v36" : L = (Ext Sw) %"iw_1.v35"
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.pr.2" : L = phi("iw_1.L24" => %"iw_1.v36", "iw_1.L17" => %"iw_1.pr.1")]:
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"iw_1.pr.3";
    %"iw_1.v38" : P = (RawLoadPointer 0 load_effects) %"chk4"
    => goto poll "iw_1.L16";
  @"iw_1.join":
    %"v11" = %"v0" +p #24;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v14" : L = Ptoi %"v12";
    %"v15" : L = Sub %"iw_1.v9", %"v14";
    %"v17" : L = Sub %"v15", %"iw_1.pr.1";
    %"v20" = %"v0" +p #88;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v23" = %"v0" +p #72;
    %"v24" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v25" : L = Ptoi %"v21";
    %"v26" : L = Ptoi %"v24";
    %"v27" : L = Sub %"v25", %"v26";
    %"v36" : W = (Cmp Ugt L) %"v17", %"v27"
    => br %"v36" ? "L31" : "L32";
  @"L31":
    %"v40" : L = Add %"v17", #100;
    call %"v41" : P = $"malloc"(L %"v40");
    %"v46" : L = Ptoi %"v41";
    %"v48" : W = (Cmp Eq L) %"v46", %"iw_1.v22"
    => br %"v48" ? "L42" : "L44";
  @"L42":
    => ret #4294967295;
  @"L44":
    %"v55" : W = (Cmp Slt L) %"iw_1.pr.1", #0
    => br %"v55" ? "L51" : "L52";
  @"L51":
    %"v58" = %"v41" +p #100;
    %"v60" = %"v0" +p #88;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v63" = %"v61" +p %"iw_1.pr.1";
    %"v65" : L = Neg %"iw_1.pr.1";
    call %"v66" : P = $"__GI_mempcpy"(P %"v58", P %"v63", L %"v65");
    %"v68" = %"v0" +p #24;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v75" : L = Ptoi %"v73";
    %"v76" : L = Sub %"iw_1.v9", %"v75";
    call %"v77" : P = $"__GI_mempcpy"(P %"v66", P %"v69", L %"v76")
    => goto "L53";
  @"L52":
    %"v80" = %"v41" +p #100;
    %"v82" = %"v0" +p #24;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk0", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v85" = %"v83" +p %"iw_1.pr.1";
    call %"v87" : P = $"__GI_memcpy"(P %"v80", P %"v85", L %"v17")
    => goto "L53";
  @"L53":
    %"v90" = %"v0" +p #72;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_2.v9" = %"v0" +p #119;
    %"iw_2.v10" : L = Ptoi %"v91";
    %"iw_2.v11" : L = Ptoi %"iw_2.v9";
    %"iw_2.v12" : W = (Cmp Ne L) %"iw_2.v10", %"iw_2.v11"
    => br %"iw_2.v12" ? "iw_2.L4" : "iw_2.join";
  @"iw_2.L4":
    call void $"free"(P %"v91")
    => goto "iw_2.join";
  @"iw_2.join":
    %"v93" = %"v0" +p #72;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk12", %"v93";
    store.ptr [%"chk13" + 0] <- %"v41";
    %"v96" = %"v0" +p #88;
    %"v99" = %"v41" +p #100;
    %"v101" = %"v99" +p %"v17";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk6", %"v96";
    store.ptr [%"chk14" + 0] <- %"v101"
    => goto "L33";
  @"L32":
    %"v104" : L = Sub %"v27", %"v17";
    %"v109" : W = (Cmp Slt L) %"iw_1.pr.1", #0
    => br %"v109" ? "L105" : "L106";
  @"L105":
    %"v111" = %"v0" +p #72;
    %"v112" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v114" = %"v112" +p %"v104";
    %"v116" = %"v0" +p #88;
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v119" = %"v117" +p %"iw_1.pr.1";
    %"v121" : L = Neg %"iw_1.pr.1";
    call %"v122" : P = $"__GI_memmove"(P %"v114", P %"v119", L %"v121");
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v111";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v127" = %"v125" +p %"v104";
    (Flight (a "v129") Sub [(FAddress (t "v127")); (FValue (t "iw_1.pr.1"))] (LowerOf (t "v127")));
    %"v131" = %"v0" +p #24;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v131";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v136" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v138" : L = Ptoi %"v136";
    %"v139" : L = Sub %"iw_1.v9", %"v138";
    call %"v140" : P = $"__GI_memcpy"(P %"v129", P %"v132", L %"v139")
    => goto "L33";
  @"L106":
    %"v145" : W = (Cmp Ugt L) %"v17", #0
    => br %"v145" ? "L141" : "L33";
  @"L141":
    %"v147" = %"v0" +p #72;
    %"v148" : P = (RawLoadPointer (-16) load_effects) %"chk6";
    %"v150" = %"v148" +p %"v104";
    %"v152" = %"v0" +p #24;
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v155" = %"v153" +p %"iw_1.pr.1";
    call %"v157" : P = $"__GI_memcpy"(P %"v150", P %"v155", L %"v17")
    => goto "L33";
  @"L33" [%"pr.1" : L = phi("iw_2.join" => #100, "L105" => %"v104", "L141" => %"v104", "L106" => %"v104")]:
    %"v159" = %"v0" +p #80;
    %"v161" = %"v0" +p #72;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v164" = %"v162" +p %"pr.1";
    %"chk23" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v159";
    store.ptr [%"chk23" + 0] <- %"v164";
    %"v167" = %"v0" +p #24;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v170" : L = Ptoi %"v168";
    %"v171" : L = Sub %"iw_1.v9", %"v170";
    %"v173" = %"v0" +p #96;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk25"
    => goto "L175";
  @"L175" [%"pr.2" : P = phi("L176" => %"v190", "L33" => %"v174")]:
    %"v180" : L = Ptoi %"pr.2";
    %"v182" : W = (Cmp Ne L) %"v180", %"iw_1.v22"
    => br %"v182" ? "L176" : "L178";
  @"L176":
    %"v184" = %"pr.2" +p #16;
    %"chk26" : A = (Check 0 4 Read 1) %"v184";
    %"v185" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v187" : L = (Ext Sw) %"v185";
    %"v188" : L = Sub %"v187", %"v171";
    %"chk27" : A = (Renew 0 4 Write 1) %"chk26", %"v184";
    store Ww [%"chk27" + 0] <- %"v188";
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk26", %"pr.2";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk28"
    => goto poll "L175";
  @"L178":
    => ret #0
} }.

Definition hello_image_fn_glibc_wgenops'23save_for_wbackup : func :=
  ir_fn{ "local" "glibc_wgenops#save_for_wbackup"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v7" : L = $"__GI__IO_least_wmarker"(P %"v0", P %"v2");
    %"v11" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" : L = Ptoi %"v2";
    %"v16" : L = Ptoi %"v14";
    %"v17" : L = Sub %"v15", %"v16";
    %"v18" : L = Div %"v17", #4;
    %"v20" : L = Sub %"v18", %"v7";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v25" = %"v24" +p #80;
    %"chk3" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v30" = %"v29" +p #64;
    %"chk5" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v32" : L = Ptoi %"v26";
    %"v33" : L = Ptoi %"v31";
    %"v34" : L = Sub %"v32", %"v33";
    %"v35" : L = Div %"v34", #4;
    %"v44" : W = (Cmp Ugt L) %"v20", %"v35"
    => br %"v44" ? "L39" : "L40";
  @"L39":
    %"v48" : L = Add %"v20", #100;
    %"v49" : L = Shl %"v48", #2;
    call %"v50" : P = $"malloc"(L %"v49");
    %"v55" : L = Ptoi %"v50";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Eq L) %"v55", %"v56"
    => br %"v57" ? "L51" : "L53";
  @"L51":
    => ret #4294967295;
  @"L53":
    %"v64" : W = (Cmp Slt L) %"v7", #0
    => br %"v64" ? "L60" : "L61";
  @"L60":
    %"v68" = %"v50" +p #400;
    %"v70" = %"v0" +p #160;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v70";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v72" = %"v71" +p #80;
    %"chk7" : A = (Check 0 8 Read 8) %"v72";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v75" : L = Shl %"v7", #2;
    %"v76" = %"v73" +p %"v75";
    %"v78" : L = Neg %"v7";
    call %"v79" : P = $"__wmempcpy"(P %"v68", P %"v76", L %"v78");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v70";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" = %"v82" +p #16;
    %"chk9" : A = (Check 0 8 Read 8) %"v83";
    %"v84" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v89" = %"v88" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v92" : L = Ptoi %"v90";
    %"v93" : L = Sub %"v15", %"v92";
    %"v94" : L = Div %"v93", #4;
    call %"v95" : P = $"__wmempcpy"(P %"v79", P %"v84", L %"v94")
    => goto "L62";
  @"L61":
    %"v99" = %"v50" +p #400;
    %"v101" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v103" = %"v102" +p #16;
    %"chk13" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v106" : L = Shl %"v7", #2;
    %"v107" = %"v104" +p %"v106";
    call %"v109" : P = $"__wmemcpy"(P %"v99", P %"v107", L %"v20")
    => goto "L62";
  @"L62":
    %"v111" = %"v0" +p #160;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v113" = %"v112" +p #64;
    %"chk15" : A = (Check 0 8 Read 8) %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call void $"free"(P %"v114");
    %"chk16" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v118" = %"v117" +p #64;
    %"chk17" : A = (Check 0 8 Write 8) %"v118";
    store.ptr [%"chk17" + 0] <- %"v50";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v123" = %"v122" +p #80;
    %"v127" = %"v50" +p #400;
    %"v129" : L = Shl %"v20", #2;
    %"v130" = %"v127" +p %"v129";
    %"chk19" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk19" + 0] <- %"v130"
    => goto "L41";
  @"L40":
    %"v133" : L = Sub %"v35", %"v20";
    %"v138" : W = (Cmp Slt L) %"v7", #0
    => br %"v138" ? "L134" : "L135";
  @"L134":
    %"v140" = %"v0" +p #160;
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v142" = %"v141" +p #64;
    %"chk21" : A = (Check 0 8 Read 8) %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v145" : L = Shl %"v133", #2;
    %"v146" = %"v143" +p %"v145";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v150" = %"v149" +p #80;
    %"chk23" : A = (Check 0 8 Read 8) %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v153" : L = Shl %"v7", #2;
    %"v154" = %"v151" +p %"v153";
    %"v156" : L = Neg %"v7";
    call %"v157" : P = $"__wmemmove"(P %"v146", P %"v154", L %"v156");
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v140";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v161" = %"v160" +p #64;
    %"chk25" : A = (Check 0 8 Read 8) %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v165" = %"v162" +p %"v145";
    (Flight (a "v168") Sub [(FAddress (t "v165")); (FValue (t "v153"))] (LowerOf (t "v165")));
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v172" = %"v171" +p #16;
    %"chk27" : A = (Check 0 8 Read 8) %"v172";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v178" = %"v177" +p #16;
    %"chk29" : A = (Check 0 8 Read 8) %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v181" : L = Ptoi %"v179";
    %"v182" : L = Sub %"v15", %"v181";
    %"v183" : L = Div %"v182", #4;
    call %"v184" : P = $"__wmemcpy"(P %"v168", P %"v173", L %"v183")
    => goto "L41";
  @"L135":
    %"v189" : W = (Cmp Ugt L) %"v20", #0
    => br %"v189" ? "L185" : "L41";
  @"L185":
    %"v191" = %"v0" +p #160;
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v193" = %"v192" +p #64;
    %"chk31" : A = (Check 0 8 Read 8) %"v193";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v196" : L = Shl %"v133", #2;
    %"v197" = %"v194" +p %"v196";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v201" = %"v200" +p #16;
    %"chk33" : A = (Check 0 8 Read 8) %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v204" : L = Shl %"v7", #2;
    %"v205" = %"v202" +p %"v204";
    call %"v207" : P = $"__wmemcpy"(P %"v197", P %"v205", L %"v20")
    => goto "L41";
  @"L41" [%"pr.1" : L = phi("L62" => #100, "L134" => %"v133", "L185" => %"v133", "L135" => %"v133")]:
    %"v209" = %"v0" +p #160;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk0", %"v209";
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v211" = %"v210" +p #72;
    %"v214" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v215" = %"v214" +p #64;
    %"chk36" : A = (Check 0 8 Read 8) %"v215";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v218" : L = Shl %"pr.1", #2;
    %"v219" = %"v216" +p %"v218";
    %"chk37" : A = (Check 0 8 Write 8) %"v211";
    store.ptr [%"chk37" + 0] <- %"v219";
    %"chk38" : A = (Renew 0 8 Read 8) %"chk0", %"v209";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v224" = %"v223" +p #16;
    %"chk39" : A = (Check 0 8 Read 8) %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v227" : L = Ptoi %"v225";
    %"v228" : L = Sub %"v15", %"v227";
    %"v229" : L = Div %"v228", #4;
    %"v231" = %"v0" +p #96;
    %"chk40" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk40"
    => goto "L233";
  @"L233" [%"pr.2" : P = phi("L234" => %"v248", "L41" => %"v232")]:
    %"v238" : L = Ptoi %"pr.2";
    %"v239" : L = Ptoi #0;
    %"v240" : W = (Cmp Ne L) %"v238", %"v239"
    => br %"v240" ? "L234" : "L236";
  @"L234":
    %"v242" = %"pr.2" +p #16;
    %"chk41" : A = (Check 0 4 Read 1) %"v242";
    %"v243" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"v245" : L = (Ext Sw) %"v243";
    %"v246" : L = Sub %"v245", %"v229";
    %"chk42" : A = (Renew 0 4 Write 1) %"chk41", %"v242";
    store Ww [%"chk42" + 0] <- %"v246";
    %"chk43" : A = (HalfCheck Lower 0 8 Read 8) %"chk41", %"pr.2";
    %"v248" : P = (RawLoadPointer 0 load_effects) %"chk43"
    => goto poll "L233";
  @"L236":
    => ret #0
} }.
