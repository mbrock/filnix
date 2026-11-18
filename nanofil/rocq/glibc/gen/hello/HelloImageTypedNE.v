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

Definition hello_image_fn_glibc_setlocale'23new_composite_name : func :=
  ir_fn{ "local" "glibc_setlocale#new_composite_name"(W %"v0", P %"v2") -> (RClass P) {
  @"start":
    => goto "L10";
  @"L10" [%"pr.9" : W = phi("L18" => %"pr.10", "start" => #1); %"pr.5" : W = phi("L18" => %"v91", "start" => #0); %"pr.3" : L = phi("L18" => %"pr.4", "start" => #0); %"pr.1" : L = phi("L18" => %"pr.2", "start" => #0)]:
    %"v15" : W = (Cmp Slt W) %"pr.5", #13
    => br %"v15" ? "L11" : "L13";
  @"L11":
    %"v20" : W = (Cmp Ne W) %"pr.5", #6
    => br %"v20" ? "L16" : "L18";
  @"L16":
    %"v26" : W = (Cmp Eq W) %"v0", #6
    => br %"v26" ? "L22" : "L23";
  @"L22":
    %"v29" : L = (Ext Sw) %"pr.5";
    %"v30" : L = Shl %"v29", #3;
    %"v31" = %"v2" +p %"v30";
    %"chk0" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L24";
  @"L23":
    %"v38" : W = (Cmp Eq W) %"v0", %"pr.5"
    => br %"v38" ? "L33" : "L34";
  @"L33":
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L24";
  @"L34":
    %"v42" : P = Copy $"_nl_global_locale";
    %"v43" = %"v42" +p #128;
    %"v45" : L = (Ext Sw) %"pr.5";
    %"v46" : L = Shl %"v45", #3;
    %"v47" = %"v43" +p %"v46";
    %"chk2" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "L24";
  @"L24" [%"v50" : P = phi("L22" => %"v32", "L33" => %"v41", "L34" => %"v48")]:
    call %"v52" : L = $"__GI_strlen"(P %"v50");
    %"v54" : P = Copy $"_nl_category_name_sizes";
    %"v56" : L = (Ext Sw) %"pr.5";
    %"v57" = %"v54" +p %"v56";
    %"chk3" : A = (Check 0 1 Read 1) %"v57";
    %"v58" : W = (RawLoad (LdNarrow Ub) 0) %"chk3";
    %"v59" : W = Add %"v58", #1;
    %"v61" : L = (Ext Sw) %"v59";
    %"v62" : L = Add %"v61", %"v52";
    %"v63" : L = Add %"v62", #1;
    %"v64" : L = Add %"pr.3", %"v63"
    => br %"pr.9" ? "L69" : "L70";
  @"L69":
    %"chk4" : A = (Check 0 8 Read 8) %"v2";
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v75" : L = Ptoi %"v50";
    %"v76" : L = Ptoi %"v74";
    %"v77" : W = (Cmp Ne L) %"v75", %"v76"
    => goto "L70";
  @"L70" [%"v79" : W = phi("L24" => #0, "L69" => %"v77")]:
    => br %"v79" ? "L80" : "L81";
  @"L80":
    %"chk5" : A = (Check 0 8 Read 8) %"v2";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v86" : W = $"__GI_strcmp"(P %"v50", P %"v85");
    %"v87" : W = (Cmp Ne W) %"v86", #0
    => goto "L81";
  @"L81" [%"v89" : W = phi("L70" => #0, "L80" => %"v87")]:
    => br %"v89" ? "L18" : "L66";
  @"L66":
    => goto "L18";
  @"L18" [%"pr.10" : W = phi("L66" => %"pr.9", "L81" => #0, "L11" => %"pr.9"); %"pr.4" : L = phi("L66" => %"v64", "L81" => %"v64", "L11" => %"pr.3"); %"pr.2" : L = phi("L66" => %"v52", "L81" => %"v52", "L11" => %"pr.1")]:
    %"v91" : W = Add %"pr.5", #1
    => goto poll "L10";
  @"L13":
    => br %"pr.9" ? "L92" : "L94";
  @"L92":
    %"chk6" : A = (Check 0 8 Read 8) %"v2";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v102" : P = Copy $"_nl_C_name";
    call %"v103" : W = $"__GI_strcmp"(P %"v101", P %"v102");
    %"v104" : W = (Cmp Eq W) %"v103", #0
    => br %"v104" ? "L106" : "L105";
  @"L105":
    %"chk7" : A = (Renew 0 8 Read 8) %"chk6", %"v2";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v110" : P = Copy $"_nl_POSIX_name";
    call %"v111" : W = $"__GI_strcmp"(P %"v109", P %"v110");
    %"v112" : W = (Cmp Eq W) %"v111", #0
    => goto "L106";
  @"L106" [%"v114" : W = phi("L92" => #1, "L105" => %"v112")]:
    => br %"v114" ? "L96" : "L98";
  @"L96":
    %"v115" : P = Copy $"_nl_C_name"
    => ret %"v115";
  @"L98":
    %"v118" : L = Add %"pr.1", #1;
    call %"v119" : P = $"malloc"(L %"v118");
    %"v124" : L = Ptoi %"v119";
    %"v125" : L = Ptoi #0;
    %"v126" : W = (Cmp Eq L) %"v124", %"v125"
    => br %"v126" ? "L122" : "L121";
  @"L121":
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v2";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk8";
    call %"v133" : P = $"__GI_memcpy"(P %"v119", P %"v130", L %"v118")
    => goto "L122";
  @"L122" [%"v134" : P = phi("L121" => %"v133", "L98" => #0)]:
    => ret %"v134";
  @"L94":
    call %"v137" : P = $"malloc"(L %"pr.3");
    %"v142" : L = Ptoi %"v137";
    %"v143" : L = Ptoi #0;
    %"v144" : W = (Cmp Eq L) %"v142", %"v143"
    => br %"v144" ? "L138" : "L147";
  @"L138":
    => ret #0;
  @"L147" [%"pr.7" : P = phi("L155" => %"pr.8", "L94" => %"v137"); %"pr.6" : W = phi("L155" => %"v200", "L94" => #0)]:
    %"v152" : W = (Cmp Slt W) %"pr.6", #13
    => br %"v152" ? "L148" : "L150";
  @"L148":
    %"v157" : W = (Cmp Ne W) %"pr.6", #6
    => br %"v157" ? "L153" : "L155";
  @"L153":
    %"v163" : W = (Cmp Eq W) %"v0", #6
    => br %"v163" ? "L159" : "L160";
  @"L159":
    %"v166" : L = (Ext Sw) %"pr.6";
    %"v167" : L = Shl %"v166", #3;
    %"v168" = %"v2" +p %"v167";
    %"chk9" : A = (Check 0 8 Read 8) %"v168";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk9"
    => goto "L161";
  @"L160":
    %"v175" : W = (Cmp Eq W) %"v0", %"pr.6"
    => br %"v175" ? "L170" : "L171";
  @"L170":
    %"chk10" : A = (Check 0 8 Read 8) %"v2";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk10"
    => goto "L161";
  @"L171":
    %"v179" : P = Copy $"_nl_global_locale";
    %"v180" = %"v179" +p #128;
    %"v182" : L = (Ext Sw) %"pr.6";
    %"v183" : L = Shl %"v182", #3;
    %"v184" = %"v180" +p %"v183";
    %"chk11" : A = (Check 0 8 Read 8) %"v184";
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto "L161";
  @"L161" [%"v187" : P = phi("L159" => %"v169", "L170" => %"v178", "L171" => %"v185")]:
    %"iw_1.v2" : P = Copy $"_nl_category_names";
    %"iw_1.v3" : P = Copy $"_nl_category_name_idxs";
    %"iw_1.v5" : L = (Ext Sw) %"pr.6";
    %"iw_1.v6" = %"iw_1.v3" +p %"iw_1.v5";
    %"chk12" : A = (Check 0 1 Read 1) %"iw_1.v6";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"iw_1.v8" : L = (Ext Uw) %"iw_1.v7";
    %"iw_1.v9" = %"iw_1.v2" +p %"iw_1.v8";
    call %"v191" : P = $"__GI_stpcpy"(P %"pr.7", P %"iw_1.v9");
    %"v193" = %"v191" +p #1;
    %"chk13" : A = (Check 0 1 Write 1) %"v191";
    store Wb [%"chk13" + 0] <- #61;
    call %"v196" : P = $"__GI_stpcpy"(P %"v193", P %"v187");
    %"v198" = %"v196" +p #1;
    %"chk14" : A = (Check 0 1 Write 1) %"v196";
    store Wb [%"chk14" + 0] <- #59
    => goto "L155";
  @"L155" [%"pr.8" : P = phi("L161" => %"v198", "L148" => %"pr.7")]:
    %"v200" : W = Add %"pr.6", #1
    => goto poll "L147";
  @"L150":
    %"v204" = %"pr.7" +p #18446744073709551615;
    %"chk15" : A = (Check 0 1 Write 1) %"v204";
    store Wb [%"chk15" + 0] <- #0
    => ret %"v137"
} }.

Definition hello_image_fn_glibc_getsysstats'23next_line : func :=
  ir_fn{ "local" "glibc_getsysstats#next_line"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> (RClass P) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk2" : A = (Check 0 8 Read 8) %"v6";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v20" : L = Ptoi %"v17";
    %"v21" : L = Ptoi %"v19";
    %"v22" : L = Sub %"v20", %"v21";
    call %"v23" : P = $"__GI_memchr"(P %"v15", W #10, L %"v22");
    %"v28" : L = Ptoi %"v23";
    %"v29" : L = Ptoi #0;
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => br %"v30" ? "L24" : "L26";
  @"L24":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v37" : L = Ptoi %"v35";
    %"v38" : L = Ptoi %"v2";
    %"v39" : W = (Cmp Ne L) %"v37", %"v38"
    => br %"v39" ? "L31" : "L33";
  @"L31":
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v46" : L = Ptoi %"v44";
    %"v47" : L = Ptoi %"v8";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => br %"v48" ? "L40" : "L41";
  @"L40":
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v56" : L = Ptoi %"v53";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    call %"v59" : P = $"__GI_memmove"(P %"v2", P %"v51", L %"v58");
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" : L = Ptoi %"v63";
    %"v67" : L = Ptoi %"v65";
    %"v68" : L = Sub %"v66", %"v67";
    %"v69" = %"v2" +p %"v68";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk11" + 0] <- %"v69";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk12" + 0] <- %"v2";
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v80" : L = Ptoi %"v78";
    %"v81" : L = Sub %"v47", %"v80";
    call %"v82" : L = $"__GI___read_nocancel"(W %"v0", P %"v75", L %"v81");
    %"v87" : W = (Cmp Slt L) %"v82", #0
    => br %"v87" ? "L83" : "L85";
  @"L83":
    => ret #0;
  @"L85":
    %"chk15" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v92" = %"v90" +p %"v82";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk16" + 0] <- %"v92";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v99" : L = Ptoi %"v96";
    %"v100" : L = Ptoi %"v98";
    %"v101" : L = Sub %"v99", %"v100";
    call %"v102" : P = $"__GI_memchr"(P %"v94", W #10, L %"v101")
    => goto "L103";
  @"L103" [%"pr.3" : P = phi("L142" => %"v149", "L85" => %"v102")]:
    %"v107" : L = Ptoi %"pr.3";
    %"v109" : W = (Cmp Eq L) %"v107", %"v29"
    => br %"v109" ? "L110" : "L111";
  @"L110":
    %"chk20" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v115" : L = Ptoi %"v113";
    %"v117" : W = (Cmp Eq L) %"v115", %"v47"
    => goto "L111";
  @"L111" [%"v119" : W = phi("L103" => #0, "L110" => %"v117")]:
    => br %"v119" ? "L104" : "L42";
  @"L104":
    %"v126" : L = Sub %"v47", %"v38";
    %"v127" : L = Mul %"v126", #3;
    %"v128" : L = Div %"v127", #4;
    %"v129" = %"v2" +p %"v128";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk21" + 0] <- %"v129";
    %"chk22" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v137" : L = Ptoi %"v135";
    %"v138" : L = Sub %"v47", %"v137";
    call %"v139" : L = $"__GI___read_nocancel"(W %"v0", P %"v132", L %"v138");
    %"v144" : W = (Cmp Slt L) %"v139", #0
    => br %"v144" ? "L140" : "L142";
  @"L140":
    => ret #0;
  @"L142":
    %"chk24" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v149" : P = $"__GI_memchr"(P %"v147", W #10, L %"v139");
    %"chk25" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 1 Write 1) %"v151";
    store Wb [%"chk26" + 0] <- #10;
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v155" = %"v153" +p %"v139";
    %"chk28" : A = (Renew 0 8 Write 8) %"chk2", %"v6";
    store.ptr [%"chk28" + 0] <- %"v155"
    => goto poll "L103";
  @"L41":
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v162" : L = Ptoi %"v159";
    %"v163" : L = Ptoi %"v161";
    %"v164" : L = Sub %"v162", %"v163";
    call %"v165" : P = $"__GI_memchr"(P %"v157", W #10, L %"v164")
    => goto "L42";
  @"L42" [%"pr.7" : P = phi("L41" => %"v165", "L111" => %"pr.3")]:
    %"chk32" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk32"
    => goto "L33";
  @"L33" [%"pr.6" : P = phi("L42" => %"pr.7", "L24" => %"v23"); %"pr.2" : P = phi("L42" => %"v167", "L24" => %"v12")]:
    %"v172" : L = Ptoi %"pr.6";
    %"v174" : W = (Cmp Eq L) %"v172", %"v29"
    => br %"v174" ? "L168" : "L26";
  @"L168":
    %"chk33" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk33";
    (Flight (a "v177") Sub [(FAddress (t "v176")); (FValue (Const 1))] (LowerOf (t "v176")))
    => goto "L26";
  @"L26" [%"pr.5" : P = phi("L168" => %"v177", "L33" => %"pr.6", "start" => %"v23"); %"pr.1" : P = phi("L168" => %"pr.2", "L33" => %"pr.2", "start" => %"v12")]:
    %"v180" = %"pr.5" +p #1;
    %"chk34" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk34" + 0] <- %"v180";
    %"chk35" : A = (Renew 0 8 Read 8) %"chk0", %"v4";
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v188" : L = Ptoi %"v185";
    %"v189" : L = Ptoi %"v187";
    %"v190" : W = (Cmp Ule L) %"v188", %"v189"
    => br %"v190" ? "L183" : "L182";
  @"L182":
    %"v191" : P = Copy $"glibc_getsysstats#str.311";
    %"v192" : P = Copy $"glibc_getsysstats#str.312";
    %"v193" : P = Copy $"glibc_getsysstats#str.313";
    call void $"__libc_assert_fail"(P %"v191", P %"v192", W #103, P %"v193")
    => goto "L183";
  @"L183":
    %"chk37" : A = (Renew 0 8 Read 8) %"chk2", %"v6";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v200" : L = Ptoi %"pr.1";
    %"v201" : L = Ptoi %"v199";
    %"v202" : W = (Cmp Eq L) %"v200", %"v201"
    => br %"v202" ? "L196" : "L195";
  @"L195":
    => goto "L196";
  @"L196" [%"v204" : P = phi("L195" => %"pr.1", "L183" => #0)]:
    => ret %"v204"
} }.

Definition hello_image_fn___new_exitfn : func :=
  ir_fn{ "export" "__new_exitfn"(P %"v0") -> (RClass P) {
  @"start":
    %"v9" : P = Copy $"__exit_funcs_done";
    %"chk0" : A = (Check 0 1 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Ub) 0) %"chk0"
    => br %"v10" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"chk1" : A = (Check 0 8 Read 8) %"v0";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L14";
  @"L14" [%"pr.6" : L = phi("L47" => %"pr.8", "L8" => #0); %"pr.3" : P = phi("L47" => %"v55", "L8" => %"v13"); %"pr.1" : P = phi("L47" => %"pr.3", "L8" => #0)]:
    %"v19" : L = Ptoi %"pr.3";
    %"v20" : L = Ptoi #0;
    %"v21" : W = (Cmp Ne L) %"v19", %"v20"
    => br %"v21" ? "L15" : "L17";
  @"L15":
    %"v23" = %"pr.3" +p #8;
    %"chk2" : A = (Check 0 8 Read 1) %"v23";
    %"v24" : L = (RawLoad LdL 0) %"chk2"
    => goto "L25";
  @"L25" [%"pr.8" : L = phi("L15" => %"v24", "L26" => %"v37")]:
    %"v30" : W = (Cmp Ugt L) %"pr.8", #0
    => br %"v30" ? "L26" : "L28";
  @"L26":
    %"v35" = %"pr.3" +p #16;
    %"v37" : L = Sub %"pr.8", #1;
    %"v38" : L = Shl %"v37", #5;
    %"v39" = %"v35" +p %"v38";
    %"chk3" : A = (Check 0 8 Read 1) %"v39";
    %"v40" : L = (RawLoad LdL 0) %"chk3";
    %"v41" : W = (Cmp Ne L) %"v40", #0
    => br %"v41" ? "L28" : poll "L25";
  @"L28":
    => br %"v30" ? "L17" : "L47";
  @"L47":
    %"v52" = %"pr.3" +p #8;
    %"chk4" : A = (Renew 0 8 Write 1) %"chk2", %"v52";
    store Wl [%"chk4" + 0] <- #0;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk2", %"pr.3";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto poll "L14";
  @"L17" [%"pr.7" : L = phi("L14" => %"pr.6", "L28" => %"pr.8")]:
    %"v62" : W = (Cmp Eq L) %"v19", %"v20"
    => br %"v62" ? "L64" : "L63";
  @"L63":
    %"v67" : W = (Cmp Eq L) %"pr.7", #32
    => goto "L64";
  @"L64" [%"v69" : W = phi("L17" => #1, "L63" => %"v67")]:
    => br %"v69" ? "L56" : "L57";
  @"L56":
    %"v74" : L = Ptoi %"pr.1";
    %"v76" : W = (Cmp Eq L) %"v74", %"v20"
    => br %"v76" ? "L70" : "L72";
  @"L70":
    => br %"v21" ? "L79" : "L78";
  @"L78":
    %"v84" : P = Copy $"glibc_cxa_atexit#str.236";
    %"v85" : P = Copy $"glibc_cxa_atexit#str.234";
    %"v86" : P = Copy $"glibc_cxa_atexit#str.237";
    call void $"__libc_assert_fail"(P %"v84", P %"v85", W #110, P %"v86")
    => goto "L79";
  @"L79":
    call %"v87" : P = $"calloc"(L #1, L #1040);
    %"v92" : L = Ptoi %"v87";
    %"v94" : W = (Cmp Ne L) %"v92", %"v20"
    => br %"v94" ? "L88" : "L72";
  @"L88":
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v0";
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v87";
    store.ptr [%"chk7" + 0] <- %"v97";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk1", %"v0";
    store.ptr [%"chk8" + 0] <- %"v87"
    => goto "L72";
  @"L72" [%"pr.2" : P = phi("L88" => %"v87", "L79" => %"v87", "L56" => %"pr.1")]:
    %"v104" : L = Ptoi %"pr.2";
    %"v106" : W = (Cmp Ne L) %"v104", %"v20"
    => br %"v106" ? "L100" : "L58";
  @"L100":
    %"v108" = %"pr.2" +p #16;
    %"v111" = %"pr.2" +p #8;
    %"chk9" : A = (Check 0 8 Write 1) %"v111";
    store Wl [%"chk9" + 0] <- #1
    => goto "L58";
  @"L57":
    %"v113" = %"pr.3" +p #16;
    %"v115" : L = Shl %"pr.7", #5;
    %"v116" = %"v113" +p %"v115";
    %"v118" = %"pr.3" +p #8;
    %"v120" : L = Add %"pr.7", #1;
    %"chk10" : A = (Check 0 8 Write 1) %"v118";
    store Wl [%"chk10" + 0] <- %"v120"
    => goto "L58";
  @"L58" [%"pr.5" : P = phi("L57" => %"v116", "L100" => %"v108", "L72" => #0)]:
    %"v125" : L = Ptoi %"pr.5";
    %"v127" : W = (Cmp Ne L) %"v125", %"v20"
    => br %"v127" ? "L121" : "L123";
  @"L121":
    %"chk11" : A = (Check 0 8 Write 1) %"pr.5";
    store Wl [%"chk11" + 0] <- #1;
    %"v129" : P = Copy $"__new_exitfn_called";
    %"chk12" : A = (Check 0 8 Read 1) %"v129";
    %"v130" : L = (RawLoad LdL 0) %"chk12";
    %"v131" : L = Add %"v130", #1;
    %"chk13" : A = (Renew 0 8 Write 1) %"chk12", %"v129";
    store Wl [%"chk13" + 0] <- %"v131"
    => goto "L123";
  @"L123":
    => ret %"pr.5"
} }.
