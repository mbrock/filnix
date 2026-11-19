(** This file defines checked IR from glibc’s `intl/localealias.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn__nl_expand_alias : func :=
  ir_fn{ "export" "_nl_expand_alias"(P %"v0") -> (RClass P) {
  @"start":
    %"v43" : P = (Alloc 8) #16;
    %"v6" : P = Copy $"glibc_localealias#lock";
    %"chk0" : A = (Check 0 4 Write 4) %"v6";
    %"v13" : W = (RawCas (CasNarrow Sw) 0) %"chk0", #0, #1;
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L16" : "L15";
  @"L15":
    => goto "L16";
  @"L16":
    %"v17" : W = (Cmp Ne W) %"v13", #0
    => br %"v17" ? "L20" : "L9";
  @"L20":
    call void $"__GI___lll_lock_wait_private"(P %"v6")
    => goto "L9";
  @"L9":
    %"v33" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk1" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v35" : L = Ptoi %"v34";
    %"v36" : L = Ptoi #0;
    %"v37" : W = (Cmp Eq L) %"v35", %"v36"
    => br %"v37" ? "L30" : "L40";
  @"L30":
    %"v38" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"v39" : P = Copy $"glibc_localealias#str.267";
    %"chk2" : A = (Check 0 8 Write 8) %"v38";
    store.ptr [%"chk2" + 0] <- %"v39"
    => goto "L40";
  @"L40":
    %"chk3" : A = (Check 0 8 Write 8) %"v43";
    store.ptr [%"chk3" + 0] <- %"v0";
    %"v48" : P = Copy $"glibc_localealias#nmap";
    %"chk4" : A = (Check 0 8 Read 1) %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk4";
    %"v50" : W = (Cmp Ugt L) %"v49", #0
    => br %"v50" ? "L45" : "L47";
  @"L45":
    %"v51" : P = Copy $"glibc_localealias#map";
    %"chk5" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v53" : P = Copy $"glibc_localealias#nmap";
    %"chk6" : A = (Check 0 8 Read 1) %"v53";
    %"v54" : L = (RawLoad LdL 0) %"chk6";
    %"v55" : P = Copy $"glibc_localealias#alias_compare";
    call %"v56" : P = $"__GI_bsearch"(P %"v43", P %"v52", L %"v54", L #16, P %"v55")
    => goto "L47";
  @"L47" [%"pr.1" : P = phi("L45" => %"v56", "L40" => #0)]:
    %"v61" : L = Ptoi %"pr.1";
    %"v63" : W = (Cmp Ne L) %"v61", %"v36"
    => br %"v63" ? "L57" : "L68";
  @"L57":
    %"v65" = %"pr.1" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto "L42";
  @"L68" [%"pr.4" : L = phi("L47" => #0, "L116" => %"v132", "L98" => %"pr.4")]:
    %"v72" : W = (Cmp Eq L) %"pr.4", #0
    => br %"v72" ? "L73" : "L74";
  @"L73":
    %"v75" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk8" : A = (Check 0 8 Read 8) %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 1 Read 1) %"v76";
    %"v78" : W = (RawLoad (LdNarrow Sb) 0) %"chk9";
    %"v79" : W = (Cmp Ne W) %"v78", #0
    => goto "L74";
  @"L74" [%"v81" : W = phi("L68" => #0, "L73" => %"v79")]:
    => br %"v81" ? "L83" : "L41";
  @"L83":
    %"v86" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk10" : A = (Check 0 8 Read 8) %"v86";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 1 Read 1) %"v87";
    %"v89" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"v90" : W = (Cmp Eq W) %"v89", #58
    => br %"v90" ? "L84" : "L85";
  @"L84":
    %"v91" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk12" : A = (Check 0 8 Read 8) %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v93" = %"v92" +p #1;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk12", %"v91";
    store.ptr [%"chk13" + 0] <- %"v93"
    => goto poll "L83";
  @"L85":
    %"v94" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk14" : A = (Check 0 8 Read 8) %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk14"
    => goto "L96";
  @"L96":
    %"v99" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk15" : A = (Check 0 8 Read 8) %"v99";
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 1 Read 1) %"v100";
    %"v102" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v103" : W = (Cmp Ne W) %"v102", #0
    => br %"v103" ? "L104" : "L105";
  @"L104":
    %"v106" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk17" : A = (Check 0 8 Read 8) %"v106";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 1 Read 1) %"v107";
    %"v109" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"v110" : W = (Cmp Ne W) %"v109", #58
    => goto "L105";
  @"L105" [%"v112" : W = phi("L96" => #0, "L104" => %"v110")]:
    => br %"v112" ? "L97" : "L98";
  @"L97":
    %"v113" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk19" : A = (Check 0 8 Read 8) %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v115" = %"v114" +p #1;
    %"chk20" : A = (Renew 0 8 Write 8) %"chk19", %"v113";
    store.ptr [%"chk20" + 0] <- %"v115"
    => goto poll "L96";
  @"L98":
    %"v120" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk21" : A = (Check 0 8 Read 8) %"v120";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v122" : L = Ptoi %"v95";
    %"v123" : L = Ptoi %"v121";
    %"v124" : W = (Cmp Ult L) %"v122", %"v123"
    => br %"v124" ? "L116" : poll "L68";
  @"L116":
    %"v126" : P = Copy $"glibc_localealias#_nl_expand_alias.locale_alias_path.266";
    %"chk22" : A = (Check 0 8 Read 8) %"v126";
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v129" : L = Ptoi %"v127";
    %"v131" : L = Sub %"v129", %"v122";
    call %"v132" : L = $"glibc_localealias#read_alias_file"(P %"v95", W %"v131")
    => goto poll "L68";
  @"L41":
    %"v134" : W = (Cmp Ne L) %"pr.4", #0
    => br %"v134" ? poll "L40" : "L42";
  @"L42" [%"pr.2" : P = phi("L41" => #0, "L57" => %"v66")]:
    %"v136" : P = Copy $"glibc_localealias#lock";
    %"chk23" : A = (Check 0 4 Read 1) %"v136";
    %"v140" : W = (RawLoad (LdNarrow Sw) 0) %"chk23"
    => goto "L141";
  @"L141" [%"v143" : W = phi("L42" => %"v140", "L141" => %"v144")]:
    %"chk24" : A = (HalfCheck Lower 0 4 Write 4) %"chk23", %"v136";
    %"v144" : W = (RawCas (CasNarrow Sw) 0) %"chk24", %"v143", #0;
    %"v145" : W = (Cmp Eq W) %"v144", %"v143"
    => br %"v145" ? "L142" : poll "L141";
  @"L142":
    %"v150" : W = (Cmp Sgt W) %"v143", #1
    => br %"v150" ? "L153" : "L148";
  @"L153":
    call void $"__GI___lll_lock_wake_private"(P %"v136")
    => goto "L148";
  @"L148":
    => ret %"pr.2"
} }.

Definition item_glibc_localealias'23_nl_expand_alias'2elocale_alias_path'2e266 : item :=
  (IData (a "glibc_localealias#_nl_expand_alias.locale_alias_path.266") LLocal 8 [(Zero 8)]).

Definition fn_glibc_localealias'23alias_compare : func :=
  ir_fn{ "local" "glibc_localealias#alias_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v8" : P = Copy $"_nl_C_locobj";
    call %"v9" : W = $"__GI___strcasecmp_l"(P %"v5", P %"v7", P %"v8")
    => ret %"v9"
} }.

Definition item_glibc_localealias'23lock : item :=
  (IData (a "glibc_localealias#lock") LLocal 4 [(Zero 4)]).

Definition item_glibc_localealias'23map : item :=
  (IData (a "glibc_localealias#map") LLocal 8 [(Zero 8)]).

Definition item_glibc_localealias'23maxmap : item :=
  (IData (a "glibc_localealias#maxmap") LLocal 8 [(Zero 8)]).

Definition item_glibc_localealias'23nmap : item :=
  (IData (a "glibc_localealias#nmap") LLocal 8 [(Zero 8)]).

Definition fn_glibc_localealias'23read_alias_file : func :=
  ir_fn{ "local" "glibc_localealias#read_alias_file"(P %"v0", W %"v2") -> (RClass L) {
  @"start":
    %"v59" : P = (Alloc 4) #400;
    %"v8" : L = (Ext Sw) %"v2";
    %"v9" : L = Add %"v8", #14;
    %"v10" : P = (Alloc 16) %"v9";
    call %"v15" : P = $"__GI_mempcpy"(P %"v10", P %"v0", L %"v8");
    %"v16" : P = Copy $"glibc_localealias#read_alias_file.aliasfile.268";
    call %"v17" : P = $"__GI_mempcpy"(P %"v15", P %"v16", L #14);
    %"v19" : P = Copy $"glibc_localealias#str.269";
    call %"v20" : P = $"_IO_new_fopen"(P %"v10", P %"v19");
    %"v25" : L = Ptoi %"v20";
    %"v26" : L = Ptoi #0;
    %"v27" : W = (Cmp Eq L) %"v25", %"v26"
    => br %"v27" ? "L21" : "L23";
  @"L21":
    => ret #0;
  @"L23":
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v35" : W = And %"v34", #32768
    => br %"v35" ? "L37" : "L31";
  @"L31":
    => goto "L37";
  @"L37":
    %"v42" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v44" : W = And %"v42", #4294934527;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v20";
    store Ww [%"chk2" + 0] <- %"v44";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v51" : W = Or %"v50", #32768;
    store Ww [%"chk2" + 0] <- %"v51"
    => goto "L53";
  @"L53" [%"pr.2" : L = phi("L37" => #0, "L389" => %"pr.3", "L388" => %"pr.3", "L95" => %"pr.3")]:
    call %"v57" : W = $"__feof_unlocked"(P %"v20");
    %"v58" : W = (Cmp Eq W) %"v57", #0
    => br %"v58" ? "L54" : "L229";
  @"L54":
    call %"v68" : P = $"__GI___fgets_unlocked"(P %"v59", W #400, P %"v20");
    %"v69" : L = Ptoi %"v68";
    %"v71" : W = (Cmp Eq L) %"v69", %"v26"
    => br %"v71" ? "L229" : "L66";
  @"L66":
    call %"v73" : P = $"__GI_strchr"(P %"v59", W #10);
    %"v74" : L = Ptoi %"v73"
    => goto "L77";
  @"L77" [%"pr.8" : P = phi("L66" => %"v59", "L78" => %"v92")]:
    %"iw_1.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v0";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 1 Read 1) %"pr.8";
    %"v84" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v85" : W = (Ext Ub) %"v84";
    %"v86" : L = (Ext Sw) %"v85";
    %"v87" : L = Shl %"v86", #1;
    %"v88" = %"v81" +p %"v87";
    %"chk7" : A = (Check 0 2 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Uh) 0) %"chk7";
    %"v90" : W = And %"v89", #8192
    => br %"v90" ? "L78" : "L79";
  @"L78":
    %"v92" = %"pr.8" +p #1
    => goto poll "L77";
  @"L79":
    %"v98" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v99" : W = (Cmp Ne W) %"v98", #0
    => br %"v99" ? "L100" : "L101";
  @"L100":
    %"v104" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v105" : W = (Cmp Ne W) %"v104", #35
    => goto "L101";
  @"L101" [%"v107" : W = phi("L79" => #0, "L100" => %"v105")]:
    => br %"v107" ? "L93" : "L95";
  @"L93":
    %"v109" = %"pr.8" +p #1
    => goto "L110";
  @"L110" [%"pr.4" : P = phi("L111" => %"v134", "L93" => %"v109")]:
    %"chk10" : A = (Check 0 1 Read 1) %"pr.4";
    %"v115" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v116" : W = (Cmp Ne W) %"v115", #0
    => br %"v116" ? "iw_2.start" : "L118";
  @"iw_2.start":
    %"iw_2.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk11" : A = (Check 0 8 Read 8) %"iw_2.v0";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Renew 0 1 Read 1) %"chk10", %"pr.4";
    %"v123" : W = (RawLoad (LdNarrow Sb) 0) %"chk12";
    %"v124" : W = (Ext Ub) %"v123";
    %"v125" : L = (Ext Sw) %"v124";
    %"v126" : L = Shl %"v125", #1;
    %"v127" = %"v120" +p %"v126";
    %"chk13" : A = (Check 0 2 Read 1) %"v127";
    %"v128" : W = (RawLoad (LdNarrow Uh) 0) %"chk13";
    %"v129" : W = And %"v128", #8192;
    %"v130" : W = (Cmp Eq W) %"v129", #0
    => goto "L118";
  @"L118" [%"v132" : W = phi("L110" => #0, "iw_2.start" => %"v130")]:
    => br %"v132" ? "L111" : "L112";
  @"L111":
    %"v134" = %"pr.4" +p #1
    => goto poll "L110";
  @"L112":
    %"chk14" : A = (Renew 0 1 Read 1) %"chk10", %"pr.4";
    %"v140" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v141" : W = (Cmp Ne W) %"v140", #0
    => br %"v141" ? "L135" : "L144";
  @"L135":
    %"v143" = %"pr.4" +p #1;
    %"chk15" : A = (Renew 0 1 Write 1) %"chk10", %"pr.4";
    store Wb [%"chk15" + 0] <- #0
    => goto "L144";
  @"L144" [%"pr.6" : P = phi("L145" => %"v159", "L135" => %"v143", "L112" => %"pr.4")]:
    %"iw_3.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk16" : A = (Check 0 8 Read 8) %"iw_3.v0";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 1 Read 1) %"pr.6";
    %"v151" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v152" : W = (Ext Ub) %"v151";
    %"v153" : L = (Ext Sw) %"v152";
    %"v154" : L = Shl %"v153", #1;
    %"v155" = %"v148" +p %"v154";
    %"chk18" : A = (Check 0 2 Read 1) %"v155";
    %"v156" : W = (RawLoad (LdNarrow Uh) 0) %"chk18";
    %"v157" : W = And %"v156", #8192
    => br %"v157" ? "L145" : "L146";
  @"L145":
    %"v159" = %"pr.6" +p #1
    => goto poll "L144";
  @"L146":
    %"v165" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v166" : W = (Cmp Ne W) %"v165", #0
    => br %"v166" ? "L160" : "L95";
  @"L160":
    %"v168" = %"pr.6" +p #1
    => goto "L169";
  @"L169" [%"pr.7" : P = phi("L160" => %"v168", "L170" => %"v193")]:
    %"chk20" : A = (Check 0 1 Read 1) %"pr.7";
    %"v174" : W = (RawLoad (LdNarrow Sb) 0) %"chk20";
    %"v175" : W = (Cmp Ne W) %"v174", #0
    => br %"v175" ? "iw_4.start" : "L177";
  @"iw_4.start":
    %"iw_4.v0" : P = Copy $"__libc_tsd_CTYPE_B";
    %"chk21" : A = (Check 0 8 Read 8) %"iw_4.v0";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Renew 0 1 Read 1) %"chk20", %"pr.7";
    %"v182" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"v183" : W = (Ext Ub) %"v182";
    %"v184" : L = (Ext Sw) %"v183";
    %"v185" : L = Shl %"v184", #1;
    %"v186" = %"v179" +p %"v185";
    %"chk23" : A = (Check 0 2 Read 1) %"v186";
    %"v187" : W = (RawLoad (LdNarrow Uh) 0) %"chk23";
    %"v188" : W = And %"v187", #8192;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => goto "L177";
  @"L177" [%"v191" : W = phi("L169" => #0, "iw_4.start" => %"v189")]:
    => br %"v191" ? "L170" : "L171";
  @"L170":
    %"v193" = %"pr.7" +p #1
    => goto poll "L169";
  @"L171":
    %"chk24" : A = (Renew 0 1 Read 1) %"chk20", %"pr.7";
    %"v199" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v200" : W = (Cmp Eq W) %"v199", #10
    => br %"v200" ? "L194" : "L195";
  @"L194":
    %"v202" = %"pr.7" +p #1;
    %"chk25" : A = (Renew 0 1 Write 1) %"chk20", %"pr.7";
    store Wb [%"chk25" + 0] <- #0;
    %"chk26" : A = (HalfCheck Upper 0 1 Write 1) %"chk20", %"v202";
    store Wb [%"chk26" + 0] <- #10
    => goto "L196";
  @"L195":
    %"v209" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v210" : W = (Cmp Ne W) %"v209", #0
    => br %"v210" ? "L204" : "L196";
  @"L204":
    %"chk28" : A = (Renew 0 1 Write 1) %"chk20", %"pr.7";
    store Wb [%"chk28" + 0] <- #0
    => goto "L196";
  @"L196":
    %"v218" : P = Copy $"glibc_localealias#nmap";
    %"chk29" : A = (Check 0 8 Read 1) %"v218";
    %"v219" : L = (RawLoad LdL 0) %"chk29";
    %"v220" : P = Copy $"glibc_localealias#maxmap";
    %"chk30" : A = (Check 0 8 Read 1) %"v220";
    %"v221" : L = (RawLoad LdL 0) %"chk30";
    %"v222" : W = (Cmp Uge L) %"v219", %"v221"
    => br %"v222" ? "iw_5.start" : "L217";
  @"iw_5.start":
    %"iw_5.v5" : P = Copy $"glibc_localealias#maxmap";
    %"chk31" : A = (Check 0 8 Read 1) %"iw_5.v5";
    %"iw_5.v6" : L = (RawLoad LdL 0) %"chk31";
    %"iw_5.v7" : W = (Cmp Eq L) %"iw_5.v6", #0
    => br %"iw_5.v7" ? "iw_5.L4" : "iw_5.L3";
  @"iw_5.L3":
    %"iw_5.v8" : P = Copy $"glibc_localealias#maxmap";
    %"chk32" : A = (Check 0 8 Read 1) %"iw_5.v8";
    %"iw_5.v9" : L = (RawLoad LdL 0) %"chk32";
    %"iw_5.v10" : L = Shl %"iw_5.v9", #1
    => goto "iw_5.L4";
  @"iw_5.L4" [%"iw_5.v11" : L = phi("iw_5.L3" => %"iw_5.v10", "iw_5.start" => #100)]:
    %"iw_5.v12" : P = Copy $"glibc_localealias#map";
    %"chk33" : A = (Check 0 8 Read 8) %"iw_5.v12";
    %"iw_5.v13" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_5.v15" : L = Shl %"iw_5.v11", #4;
    call %"iw_5.v16" : P = $"realloc"(P %"iw_5.v13", L %"iw_5.v15");
    %"iw_5.v21" : L = Ptoi %"iw_5.v16";
    %"iw_5.v23" : W = (Cmp Eq L) %"iw_5.v21", %"v26"
    => br %"iw_5.v23" ? "iw_5.join" : "iw_5.L19";
  @"iw_5.L19":
    %"iw_5.v26" : P = Copy $"glibc_localealias#map";
    %"chk34" : A = (Check 0 8 Write 8) %"iw_5.v26";
    store.ptr [%"chk34" + 0] <- %"iw_5.v16";
    %"iw_5.v28" : P = Copy $"glibc_localealias#maxmap";
    %"chk35" : A = (Check 0 8 Write 1) %"iw_5.v28";
    store Wl [%"chk35" + 0] <- %"iw_5.v11"
    => goto "iw_5.join";
  @"iw_5.join" [%"v226" : W = phi("iw_5.L19" => #0, "iw_5.L4" => #4294967295)]:
    %"v227" : L = (Ext Sw) %"v226";
    %"v228" : W = (Cmp Ne L) %"v227", #0
    => br %"v228" ? "L229" : "L217";
  @"L217":
    call %"v232" : L = $"__GI_strlen"(P %"pr.8");
    %"v233" : L = Add %"v232", #1;
    call %"v235" : L = $"__GI_strlen"(P %"pr.6");
    %"v236" : L = Add %"v235", #1;
    %"v240" : P = Copy $"glibc_localealias#string_space_act";
    %"chk36" : A = (Check 0 8 Read 1) %"v240";
    %"v241" : L = (RawLoad LdL 0) %"chk36";
    %"v243" : L = Add %"v241", %"v233";
    %"v245" : L = Add %"v243", %"v236";
    %"v246" : P = Copy $"glibc_localealias#string_space_max";
    %"chk37" : A = (Check 0 8 Read 1) %"v246";
    %"v247" : L = (RawLoad LdL 0) %"chk37";
    %"v248" : W = (Cmp Ugt L) %"v245", %"v247"
    => br %"v248" ? "L237" : "L239";
  @"L237":
    %"v250" : P = Copy $"glibc_localealias#string_space_max";
    %"chk38" : A = (Check 0 8 Read 1) %"v250";
    %"v251" : L = (RawLoad LdL 0) %"chk38";
    %"v257" : L = Add %"v233", %"v236";
    %"v258" : W = (Cmp Ugt L) %"v257", #1024
    => br %"v258" ? "L254" : "L253";
  @"L253":
    => goto "L254";
  @"L254" [%"v262" : L = phi("L253" => #1024, "L237" => %"v257")]:
    %"v263" : L = Add %"v251", %"v262";
    %"v265" : P = Copy $"glibc_localealias#string_space";
    %"chk39" : A = (Check 0 8 Read 8) %"v265";
    %"v266" : P = (RawLoadPointer 0 load_effects) %"chk39";
    call %"v268" : P = $"realloc"(P %"v266", L %"v263");
    %"v273" : L = Ptoi %"v268";
    %"v275" : W = (Cmp Eq L) %"v273", %"v26"
    => br %"v275" ? "L229" : "L271";
  @"L271":
    %"v280" : P = Copy $"glibc_localealias#string_space";
    %"chk40" : A = (Check 0 8 Read 8) %"v280";
    %"v281" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v283" : L = Ptoi %"v281";
    %"v285" : W = (Cmp Ne L) %"v283", %"v273"
    => br %"v285" ? "L289" : "L279";
  @"L289" [%"pr.9" : L = phi("L290" => %"v336", "L271" => #0)]:
    %"v294" : P = Copy $"glibc_localealias#nmap";
    %"chk41" : A = (Check 0 8 Read 1) %"v294";
    %"v295" : L = (RawLoad LdL 0) %"chk41";
    %"v296" : W = (Cmp Ult L) %"pr.9", %"v295"
    => br %"v296" ? "L290" : "L279";
  @"L290":
    %"v297" : P = Copy $"glibc_localealias#map";
    %"chk42" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v300" : L = Shl %"pr.9", #4;
    %"v301" = %"v298" +p %"v300";
    %"v303" : P = Copy $"glibc_localealias#map";
    %"chk43" : A = (Check 0 8 Read 8) %"v303";
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v307" = %"v304" +p %"v300";
    %"chk44" : A = (Check 0 8 Read 8) %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v309" : P = Copy $"glibc_localealias#string_space";
    %"chk45" : A = (Check 0 8 Read 8) %"v309";
    %"v310" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v311" : L = Ptoi %"v308";
    %"v312" : L = Ptoi %"v310";
    %"v313" : L = Sub %"v311", %"v312";
    %"v314" = %"v268" +p %"v313";
    %"chk46" : A = (Check 0 8 Write 8) %"v301";
    store.ptr [%"chk46" + 0] <- %"v314";
    %"v315" : P = Copy $"glibc_localealias#map";
    %"chk47" : A = (Check 0 8 Read 8) %"v315";
    %"v316" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v319" = %"v316" +p %"v300";
    %"v320" = %"v319" +p #8;
    %"v322" : P = Copy $"glibc_localealias#map";
    %"chk48" : A = (Check 0 8 Read 8) %"v322";
    %"v323" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v326" = %"v323" +p %"v300";
    %"v327" = %"v326" +p #8;
    %"chk49" : A = (Check 0 8 Read 8) %"v327";
    %"v328" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v329" : P = Copy $"glibc_localealias#string_space";
    %"chk50" : A = (Check 0 8 Read 8) %"v329";
    %"v330" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v331" : L = Ptoi %"v328";
    %"v332" : L = Ptoi %"v330";
    %"v333" : L = Sub %"v331", %"v332";
    %"v334" = %"v268" +p %"v333";
    %"chk51" : A = (Check 0 8 Write 8) %"v320";
    store.ptr [%"chk51" + 0] <- %"v334";
    %"v336" : L = Add %"pr.9", #1
    => goto poll "L289";
  @"L279":
    %"v337" : P = Copy $"glibc_localealias#string_space";
    %"chk52" : A = (Check 0 8 Write 8) %"v337";
    store.ptr [%"chk52" + 0] <- %"v268";
    %"v339" : P = Copy $"glibc_localealias#string_space_max";
    %"chk53" : A = (Check 0 8 Write 1) %"v339";
    store Wl [%"chk53" + 0] <- %"v263"
    => goto "L239";
  @"L239":
    %"v341" : P = Copy $"glibc_localealias#map";
    %"chk54" : A = (Check 0 8 Read 8) %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v343" : P = Copy $"glibc_localealias#nmap";
    %"chk55" : A = (Check 0 8 Read 1) %"v343";
    %"v344" : L = (RawLoad LdL 0) %"chk55";
    %"v345" : L = Shl %"v344", #4;
    %"v346" = %"v342" +p %"v345";
    %"v347" : P = Copy $"glibc_localealias#string_space";
    %"chk56" : A = (Check 0 8 Read 8) %"v347";
    %"v348" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v349" : P = Copy $"glibc_localealias#string_space_act";
    %"chk57" : A = (Check 0 8 Read 1) %"v349";
    %"v350" : L = (RawLoad LdL 0) %"chk57";
    %"v351" = %"v348" +p %"v350";
    call %"v354" : P = $"__GI_memcpy"(P %"v351", P %"pr.8", L %"v233");
    %"chk58" : A = (Check 0 8 Write 8) %"v346";
    store.ptr [%"chk58" + 0] <- %"v354";
    %"v355" : P = Copy $"glibc_localealias#string_space_act";
    %"chk59" : A = (Check 0 8 Read 1) %"v355";
    %"v356" : L = (RawLoad LdL 0) %"chk59";
    %"v358" : L = Add %"v356", %"v233";
    %"chk60" : A = (Renew 0 8 Write 1) %"chk59", %"v355";
    store Wl [%"chk60" + 0] <- %"v358";
    %"v359" : P = Copy $"glibc_localealias#map";
    %"chk61" : A = (Check 0 8 Read 8) %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v361" : P = Copy $"glibc_localealias#nmap";
    %"chk62" : A = (Check 0 8 Read 1) %"v361";
    %"v362" : L = (RawLoad LdL 0) %"chk62";
    %"v363" : L = Shl %"v362", #4;
    %"v364" = %"v360" +p %"v363";
    %"v365" = %"v364" +p #8;
    %"v366" : P = Copy $"glibc_localealias#string_space";
    %"chk63" : A = (Check 0 8 Read 8) %"v366";
    %"v367" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"v368" : P = Copy $"glibc_localealias#string_space_act";
    %"chk64" : A = (Check 0 8 Read 1) %"v368";
    %"v369" : L = (RawLoad LdL 0) %"chk64";
    %"v370" = %"v367" +p %"v369";
    call %"v373" : P = $"__GI_memcpy"(P %"v370", P %"pr.6", L %"v236");
    %"chk65" : A = (Check 0 8 Write 8) %"v365";
    store.ptr [%"chk65" + 0] <- %"v373";
    %"v374" : P = Copy $"glibc_localealias#string_space_act";
    %"chk66" : A = (Check 0 8 Read 1) %"v374";
    %"v375" : L = (RawLoad LdL 0) %"chk66";
    %"v377" : L = Add %"v375", %"v236";
    %"chk67" : A = (Renew 0 8 Write 1) %"chk66", %"v374";
    store Wl [%"chk67" + 0] <- %"v377";
    %"v378" : P = Copy $"glibc_localealias#nmap";
    %"chk68" : A = (Check 0 8 Read 1) %"v378";
    %"v379" : L = (RawLoad LdL 0) %"chk68";
    %"v380" : L = Add %"v379", #1;
    %"chk69" : A = (Renew 0 8 Write 1) %"chk68", %"v378";
    store Wl [%"chk69" + 0] <- %"v380";
    %"v382" : L = Add %"pr.2", #1
    => goto "L95";
  @"L95" [%"pr.3" : L = phi("L239" => %"v382", "L146" => %"pr.2", "L101" => %"pr.2")]:
    %"v387" : W = (Cmp Eq L) %"v74", %"v26"
    => br %"v387" ? "L388" : poll "L53";
  @"L388":
    call %"v395" : P = $"__GI___fgets_unlocked"(P %"v59", W #400, P %"v20");
    %"v396" : L = Ptoi %"v395";
    %"v398" : W = (Cmp Eq L) %"v396", %"v26"
    => br %"v398" ? poll "L53" : "L389";
  @"L389":
    call %"v400" : P = $"__GI_strchr"(P %"v59", W #10);
    %"v401" : L = Ptoi %"v400";
    %"v403" : W = (Cmp Eq L) %"v401", %"v26"
    => br %"v403" ? poll "L388" : poll "L53";
  @"L229":
    call %"v405" : W = $"_IO_new_fclose"(P %"v20");
    %"v410" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v410" ? "L406" : "L408";
  @"L406":
    %"v411" : P = Copy $"glibc_localealias#map";
    %"chk70" : A = (Check 0 8 Read 8) %"v411";
    %"v412" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v413" : P = Copy $"glibc_localealias#nmap";
    %"chk71" : A = (Check 0 8 Read 1) %"v413";
    %"v414" : L = (RawLoad LdL 0) %"chk71";
    %"v415" : P = Copy $"glibc_localealias#alias_compare";
    call void $"__GI_qsort"(P %"v412", L %"v414", L #16, P %"v415")
    => goto "L408";
  @"L408":
    => ret %"pr.2"
} }.

Definition item_glibc_localealias'23read_alias_file'2ealiasfile'2e268 : item :=
  (IData (a "glibc_localealias#read_alias_file.aliasfile.268") (LRo (a "local")) 1 ["/locale.alias"%irbytes; (Zero 1)]).

Definition item_glibc_localealias'23str'2e267 : item :=
  (IData (a "glibc_localealias#str.267") (LRo (a "local")) 1 (app [(Item Wb 47); (Item Wb 110); (Item Wb 105); (Item Wb 120); (Item Wb 47); (Item Wb 115); (Item Wb 116); (Item Wb 111); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 55); (Item Wb 104); (Item Wb 104); (Item Wb 52); (Item Wb 53); (Item Wb 99); (Item Wb 118); (Item Wb 119); (Item Wb 122); (Item Wb 114); (Item Wb 113); (Item Wb 121); (Item Wb 113); (Item Wb 118); (Item Wb 112); (Item Wb 107); (Item Wb 110); (Item Wb 110); (Item Wb 108); (Item Wb 106); (Item Wb 56); (Item Wb 50); (Item Wb 118); (Item Wb 114); (Item Wb 113); (Item Wb 100); (Item Wb 109)] [(Item Wb 103); (Item Wb 54); (Item Wb 107); (Item Wb 120); (Item Wb 119); (Item Wb 45); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 99); (Item Wb 45); (Item Wb 103); (Item Wb 108); (Item Wb 105); (Item Wb 98); (Item Wb 99); (Item Wb 45); (Item Wb 112); (Item Wb 112); (Item Wb 45); (Item Wb 50); (Item Wb 46); (Item Wb 52); (Item Wb 52); (Item Wb 47); (Item Wb 115); (Item Wb 104); (Item Wb 97); (Item Wb 114); (Item Wb 101); (Item Wb 47); (Item Wb 108); (Item Wb 111); (Item Wb 99); (Item Wb 97); (Item Wb 108); (Item Wb 101); (Item Wb 0)])).

Definition item_glibc_localealias'23str'2e269 : item :=
  (IData (a "glibc_localealias#str.269") (LRo (a "local")) 1 [(Item Wb 114); (Item Wb 99); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_localealias'23string_space : item :=
  (IData (a "glibc_localealias#string_space") LLocal 8 [(Zero 8)]).

Definition item_glibc_localealias'23string_space_act : item :=
  (IData (a "glibc_localealias#string_space_act") LLocal 8 [(Zero 8)]).

Definition item_glibc_localealias'23string_space_max : item :=
  (IData (a "glibc_localealias#string_space_max") LLocal 8 [(Zero 8)]).
