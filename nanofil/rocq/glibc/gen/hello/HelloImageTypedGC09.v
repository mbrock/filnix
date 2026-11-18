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

Definition hello_image_fn___gconv_transform_ucs2_internal : func :=
  ir_fn{ "export" "__gconv_transform_ucs2_internal"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v103" : P = (Alloc 8) #8;
    %"v266" : P = (Alloc 8) #8;
    %"v18" = %"v0" +p #104;
    %"v21" = %"v2" +p #48;
    %"v28" = %"v2" +p #16;
    %"chk0" : A = (Check 0 4 Read 1) %"v28";
    %"v29" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v30" : W = And %"v29", #1
    => br %"v30" ? "L26" : "L24" };
  ir_blk{ @"L24":
    %"v33" = %"v18" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v18";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v40" : L = Ptoi %"v39";
    %"v41" : L = Ptoi #0;
    %"v42" : W = (Cmp Ne L) %"v40", %"v41"
    => br %"v42" ? "L26" : "L36" };
  ir_blk{ @"L36":
    => goto "L26" };
  ir_blk{ @"L26" [%"pr.1" : P = phi("L36" => %"v34", "L24" => %"v34", "start" => #0)]:
    %"v48" : L = (Ext Sw) %"v12";
    %"v49" : W = (Cmp Ne L) %"v48", #0
    => br %"v49" ? "L44" : "L45" };
  ir_blk{ @"L44":
    %"v54" : L = Ptoi %"v8";
    %"v55" : L = Ptoi #0;
    %"v56" : W = (Cmp Eq L) %"v54", %"v55"
    => br %"v56" ? "L52" : "L51" };
  ir_blk{ @"L51":
    %"v57" : P = Copy $"glibc_gconv_simple#str.270";
    %"v58" : P = Copy $"glibc_gconv_simple#str.271";
    %"v59" : P = Copy $"glibc_gconv_simple#str.284";
    call void $"__libc_assert_fail"(P %"v57", P %"v58", W #350, P %"v59")
    => goto "L52" };
  ir_blk{ @"L52":
    %"v61" = %"v2" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk3";
    call %"v63" : P = $"__GI_memset"(P %"v62", W #0, L #8);
    %"v68" = %"v2" +p #16;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk0", %"v68";
    %"v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v70" : W = And %"v69", #1
    => br %"v70" ? "L46" : "iw_1.join" };
  ir_blk{ @"iw_1.join":
    %"chk5" : F = CheckFunction %"pr.1";
    rawcall %"v79" : W = %"chk5"(P %"v18", P %"v21", P #0, P #0, P #0, P %"v10", W %"v12", W %"v14")
    => goto "L46" };
  ir_blk{ @"L45":
    %"chk6" : A = (Check 0 8 Read 8) %"v4";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v88" : L = Ptoi %"v8";
    %"v89" : L = Ptoi #0;
    %"v90" : W = (Cmp Eq L) %"v88", %"v89"
    => br %"v90" ? "L84" : "L85" };
  ir_blk{ @"L84":
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v94" : P = (RawLoadPointer 0 load_effects) %"chk7"
    => goto "L86" };
  ir_blk{ @"L85":
    %"chk8" : A = (Check 0 8 Read 8) %"v8";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk8"
    => goto "L86" };
  ir_blk{ @"L86" [%"v97" : P = phi("L84" => %"v94", "L85" => %"v96")]:
    %"v100" = %"v2" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 8 Write 1) %"v103";
    store Wl [%"chk10" + 0] <- #0;
    %"v109" : L = Ptoi %"v10";
    %"v110" : W = (Cmp Ne L) %"v109", #0
    => br %"v110" ? "L107" : "L106" };
  ir_blk{ @"L106":
    => goto "L107" };
  ir_blk{ @"L107" [%"v111" : P = phi("L106" => #0, "L86" => %"v103")]:
    %"v143" : W = (Cmp Ne W) %"v14", #0
    => br %"v143" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v148" = %"v2" +p #32;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Read 1) %"v149";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v151" : W = And %"v150", #7;
    %"v152" : W = (Cmp Ne W) %"v151", #0
    => goto "L146" };
  ir_blk{ @"L146" [%"v154" : W = phi("L107" => #0, "L145" => %"v152")]:
    => br %"v154" ? "L112" : "L188" };
  ir_blk{ @"L112":
    => br %"v90" ? "iw_2.start" : "L156" };
  ir_blk{ @"L156":
    %"v162" : P = Copy $"glibc_gconv_simple#str.270";
    %"v163" : P = Copy $"glibc_gconv_simple#str.271";
    %"v164" : P = Copy $"glibc_gconv_simple#str.284";
    call void $"__libc_assert_fail"(P %"v162", P %"v163", W #467, P %"v164")
    => goto "iw_2.start" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v23" : P = (Alloc 4) #2;
    %"iw_2.v16" = %"v2" +p #32;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v16";
    %"iw_2.v17" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_2.v20" = %"v2" +p #16;
    %"chk14" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.v20";
    %"iw_2.v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"chk15" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v26" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"iw_2.v36" : W = And %"iw_2.v35", #7;
    %"iw_2.v37" : L = (Ext Sw) %"iw_2.v36";
    %"iw_2.v38" : W = (Cmp Ule L) %"iw_2.v37", #4
    => br %"iw_2.v38" ? "iw_2.L42" : "iw_2.L32" };
  ir_blk{ @"iw_2.L32":
    %"iw_2.v39" : P = Copy $"glibc_gconv_simple#str.288";
    %"iw_2.v40" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v41" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v39", P %"iw_2.v40", W #315, P %"iw_2.v41")
    => goto "iw_2.L42" };
  ir_blk{ @"iw_2.L42" [%"iw_2.pr.15" : L = phi("iw_2.L43" => %"iw_2.v61", "iw_2.L32" => #0, "iw_2.start" => #0)]:
    %"chk17" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v48" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"iw_2.v49" : W = And %"iw_2.v48", #7;
    %"iw_2.v50" : L = (Ext Sw) %"iw_2.v49";
    %"iw_2.v51" : W = (Cmp Ult L) %"iw_2.pr.15", %"iw_2.v50"
    => br %"iw_2.v51" ? "iw_2.L43" : "iw_2.L66" };
  ir_blk{ @"iw_2.L43":
    %"iw_2.v53" = %"iw_2.v23" +p %"iw_2.pr.15";
    %"iw_2.v55" = %"iw_2.v17" +p #4;
    %"iw_2.v57" = %"iw_2.v55" +p %"iw_2.pr.15";
    %"chk18" : A = (Check 0 1 Read 1) %"iw_2.v57";
    %"iw_2.v58" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_2.v59" : W = (Ext Ub) %"iw_2.v58";
    %"chk19" : A = (Check 0 1 Write 1) %"iw_2.v53";
    store Wb [%"chk19" + 0] <- %"iw_2.v59";
    %"iw_2.v61" : L = Add %"iw_2.pr.15", #1
    => goto poll "iw_2.L42" };
  ir_blk{ @"iw_2.L66":
    %"iw_2.v70" : L = Sub #2, %"iw_2.pr.15";
    %"iw_2.v71" = %"iw_2.v26" +p %"iw_2.v70";
    %"iw_2.v73" : L = Ptoi %"iw_2.v71";
    %"iw_2.v74" : L = Ptoi %"v6";
    %"iw_2.v75" : W = (Cmp Ugt L) %"iw_2.v73", %"iw_2.v74"
    => br %"iw_2.v75" ? "iw_2.L62" : "iw_2.L120" };
  ir_blk{ @"iw_2.L62":
    %"chk20" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk20" + 0] <- %"v6";
    %"iw_2.v87" : L = Ptoi %"iw_2.v26";
    %"iw_2.v88" : L = Sub %"iw_2.v74", %"iw_2.v87";
    %"iw_2.v89" : L = Add %"iw_2.pr.15", %"iw_2.v88";
    %"iw_2.v94" : W = (Cmp Ule L) %"iw_2.v89", #4
    => br %"iw_2.v94" ? "iw_2.L98" : "iw_2.L91" };
  ir_blk{ @"iw_2.L91":
    %"iw_2.v95" : P = Copy $"glibc_gconv_simple#str.291";
    %"iw_2.v96" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v97" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v95", P %"iw_2.v96", W #344, P %"iw_2.v97")
    => goto "iw_2.L98" };
  ir_blk{ @"iw_2.L98" [%"iw_2.pr.16" : L = phi("iw_2.L99" => %"iw_2.v114", "iw_2.L91" => %"iw_2.pr.15", "iw_2.L62" => %"iw_2.pr.15"); %"iw_2.pr.9" : P = phi("iw_2.L99" => %"iw_2.v110", "iw_2.L91" => %"iw_2.v26", "iw_2.L62" => %"iw_2.v26")]:
    %"iw_2.v104" : W = (Cmp Ult L) %"iw_2.pr.16", %"iw_2.v89"
    => br %"iw_2.v104" ? "iw_2.L99" : "iw_2.join" };
  ir_blk{ @"iw_2.L99":
    %"iw_2.v106" = %"iw_2.v17" +p #4;
    %"iw_2.v108" = %"iw_2.v106" +p %"iw_2.pr.16";
    %"iw_2.v110" = %"iw_2.pr.9" +p #1;
    %"chk21" : A = (Check 0 1 Read 1) %"iw_2.pr.9";
    %"iw_2.v111" : W = (RawLoad (LdNarrow Ub) 0) %"chk21";
    %"iw_2.v112" : W = (Ext Sb) %"iw_2.v111";
    %"chk22" : A = (Check 0 1 Write 1) %"iw_2.v108";
    store Wb [%"chk22" + 0] <- %"iw_2.v112";
    %"iw_2.v114" : L = Add %"iw_2.pr.16", #1
    => goto poll "iw_2.L98" };
  ir_blk{ @"iw_2.L120":
    %"iw_2.v123" = %"v97" +p #4;
    %"iw_2.v125" : L = Ptoi %"iw_2.v123";
    %"iw_2.v126" : L = Ptoi %"v101";
    %"iw_2.v127" : W = (Cmp Ugt L) %"iw_2.v125", %"iw_2.v126"
    => br %"iw_2.v127" ? "iw_2.L131" : "iw_2.L134" };
  ir_blk{ @"iw_2.L134":
    => goto "iw_2.L131" };
  ir_blk{ @"iw_2.L131" [%"iw_2.v143" : W = phi("iw_2.L120" => #1, "iw_2.L134" => #0)]:
    => br %"iw_2.v143" ? "iw_2.join" : "iw_2.L118" };
  ir_blk{ @"iw_2.L118":
    %"iw_2.v149" : W = (Cmp Uge L) %"iw_2.pr.15", #2
    => br %"iw_2.v149" ? "iw_2.L151" : "iw_2.L150" };
  ir_blk{ @"iw_2.L150":
    %"iw_2.v154" : L = Ptoi %"iw_2.v26";
    %"iw_2.v156" : W = (Cmp Uge L) %"iw_2.v154", %"iw_2.v74"
    => goto "iw_2.L151" };
  ir_blk{ @"iw_2.L151" [%"iw_2.v158" : W = phi("iw_2.L118" => #1, "iw_2.L150" => %"iw_2.v156")]:
    => br %"iw_2.v158" ? "iw_2.L145" : "iw_2.L160" };
  ir_blk{ @"iw_2.L145":
    => unreachable };
  ir_blk{ @"iw_2.L160" [%"iw_2.pr.13" : L = phi("iw_2.L172" => %"iw_2.v164", "iw_2.L151" => %"iw_2.pr.15"); %"iw_2.pr.5" : P = phi("iw_2.L172" => %"iw_2.v167", "iw_2.L151" => %"iw_2.v26")]:
    %"iw_2.v164" : L = Add %"iw_2.pr.13", #1;
    %"iw_2.v165" = %"iw_2.v23" +p %"iw_2.pr.13";
    %"iw_2.v167" = %"iw_2.pr.5" +p #1;
    %"chk23" : A = (Check 0 1 Read 1) %"iw_2.pr.5";
    %"iw_2.v168" : W = (RawLoad (LdNarrow Ub) 0) %"chk23";
    %"chk24" : A = (Check 0 1 Write 1) %"iw_2.v165";
    store Wb [%"chk24" + 0] <- %"iw_2.v168";
    %"iw_2.v170" : W = (Cmp Ult L) %"iw_2.v164", #2
    => br %"iw_2.v170" ? "iw_2.L171" : "iw_2.L172" };
  ir_blk{ @"iw_2.L171":
    %"iw_2.v175" : L = Ptoi %"iw_2.v167";
    %"iw_2.v177" : W = (Cmp Ult L) %"iw_2.v175", %"iw_2.v74"
    => goto "iw_2.L172" };
  ir_blk{ @"iw_2.L172" [%"iw_2.v179" : W = phi("iw_2.L160" => #0, "iw_2.L171" => %"iw_2.v177")]:
    => br %"iw_2.v179" ? poll "iw_2.L160" : "iw_2.L162" };
  ir_blk{ @"iw_2.L162":
    %"iw_2.v181" = %"iw_2.v23" +p %"iw_2.v164";
    %"chk25" : A = (Check 0 2 Read 1) %"iw_2.v23";
    %"iw_2.v189" : W = (RawLoad (LdNarrow Uh) 0) %"chk25";
    %"iw_2.v194" : W = (Cmp Sge W) %"iw_2.v189", #55296
    => br %"iw_2.v194" ? "iw_2.L195" : "iw_2.L196" };
  ir_blk{ @"iw_2.L195":
    %"iw_2.v198" : W = (Cmp Slt W) %"iw_2.v189", #57344
    => goto "iw_2.L196" };
  ir_blk{ @"iw_2.L196" [%"iw_2.v200" : W = phi("iw_2.L162" => #0, "iw_2.L195" => %"iw_2.v198")]:
    => br %"iw_2.v200" ? "iw_2.iw_1.start" : "iw_2.L192" };
  ir_blk{ @"iw_2.iw_1.start":
    %"iw_2.iw_1.v3" = %"v2" +p #16;
    %"chk26" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.iw_1.v3";
    %"iw_2.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"iw_2.iw_1.v5" : W = Or %"iw_2.iw_1.v4", #1073741824;
    %"chk27" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk27" + 0] <- %"iw_2.iw_1.v5";
    %"iw_2.v209" : L = Ptoi %"v111";
    %"iw_2.v211" : W = (Cmp Ne L) %"iw_2.v209", %"v89"
    => br %"iw_2.v211" ? "iw_2.L212" : "iw_2.L213" };
  ir_blk{ @"iw_2.L212":
    %"iw_2.v215" : W = And %"iw_2.v21", #2;
    %"iw_2.v216" : W = (Cmp Ne W) %"iw_2.v215", #0
    => goto "iw_2.L213" };
  ir_blk{ @"iw_2.L213" [%"iw_2.v217" : W = phi("iw_2.iw_1.start" => #0, "iw_2.L212" => %"iw_2.v216")]:
    => br %"iw_2.v217" ? "iw_2.L207" : "iw_2.L184" };
  ir_blk{ @"iw_2.L207":
    %"iw_2.v221" = %"iw_2.v23" +p #2;
    %"chk28" : A = (Check 0 8 Read 1) %"v111";
    %"iw_2.v223" : L = (RawLoad LdL 0) %"chk28";
    %"iw_2.v224" : L = Add %"iw_2.v223", #1;
    %"chk29" : A = (Renew 0 8 Write 1) %"chk28", %"v111";
    store Wl [%"chk29" + 0] <- %"iw_2.v224"
    => goto "iw_2.L184" };
  ir_blk{ @"iw_2.L192":
    %"chk30" : A = (Check 0 4 Write 1) %"v97";
    store Ww [%"chk30" + 0] <- %"iw_2.v189";
    %"iw_2.v229" = %"v97" +p #4;
    %"iw_2.v231" = %"iw_2.v23" +p #2
    => goto "iw_2.L184" };
  ir_blk{ @"iw_2.L184" [%"iw_2.pr.12" : P = phi("iw_2.L213" => %"v97", "iw_2.L207" => %"v97", "iw_2.L192" => %"iw_2.v229"); %"iw_2.pr.8" : P = phi("iw_2.L213" => %"iw_2.v23", "iw_2.L207" => %"iw_2.v221", "iw_2.L192" => %"iw_2.v231"); %"iw_2.pr.3" : W = phi("iw_2.L213" => #6, "iw_2.L207" => #6, "iw_2.L192" => #0)]:
    %"iw_2.v236" : L = Ptoi %"iw_2.pr.8";
    %"iw_2.v237" : L = Ptoi %"iw_2.v23";
    %"iw_2.v238" : W = (Cmp Ne L) %"iw_2.v236", %"iw_2.v237"
    => br %"iw_2.v238" ? "iw_2.L232" : "iw_2.L233" };
  ir_blk{ @"iw_2.L232":
    %"iw_2.v247" : L = Sub %"iw_2.v236", %"iw_2.v237";
    %"chk31" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v249" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"iw_2.v250" : W = And %"iw_2.v249", #7;
    %"iw_2.v251" : L = (Ext Sw) %"iw_2.v250";
    %"iw_2.v252" : W = (Cmp Sgt L) %"iw_2.v247", %"iw_2.v251"
    => br %"iw_2.v252" ? "iw_2.L243" : "iw_2.L242" };
  ir_blk{ @"iw_2.L242":
    %"iw_2.v253" : P = Copy $"glibc_gconv_simple#str.292";
    %"iw_2.v254" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v255" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v253", P %"iw_2.v254", W #391, P %"iw_2.v255")
    => goto "iw_2.L243" };
  ir_blk{ @"iw_2.L243":
    %"chk32" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v257" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v263" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"iw_2.v264" : W = And %"iw_2.v263", #7;
    %"iw_2.v265" : L = (Ext Sw) %"iw_2.v264";
    %"iw_2.v266" : L = Sub %"iw_2.v247", %"iw_2.v265";
    %"iw_2.v267" = %"iw_2.v257" +p %"iw_2.v266";
    %"chk34" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk34" + 0] <- %"iw_2.v267";
    %"chk35" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v271" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"iw_2.v273" : W = And %"iw_2.v271", #4294967288;
    %"chk36" : A = (Renew 0 4 Write 1) %"chk16", %"iw_2.v17";
    store Ww [%"chk36" + 0] <- %"iw_2.v273"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L233":
    %"iw_2.v278" : W = (Cmp Eq W) %"iw_2.pr.3", #7
    => br %"iw_2.v278" ? "iw_2.L274" : "iw_2.join" };
  ir_blk{ @"iw_2.L274":
    %"iw_2.v283" = %"iw_2.v23" +p #2;
    %"iw_2.v284" : L = Ptoi %"iw_2.v181";
    %"iw_2.v285" : L = Ptoi %"iw_2.v283";
    %"iw_2.v286" : W = (Cmp Ne L) %"iw_2.v284", %"iw_2.v285"
    => br %"iw_2.v286" ? "iw_2.L281" : "iw_2.L280" };
  ir_blk{ @"iw_2.L280":
    %"iw_2.v287" : P = Copy $"glibc_gconv_simple#str.293";
    %"iw_2.v288" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v289" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v287", P %"iw_2.v288", W #409, P %"iw_2.v289")
    => goto "iw_2.L281" };
  ir_blk{ @"iw_2.L281":
    %"chk37" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v291" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_2.v295" : L = Sub %"iw_2.v284", %"iw_2.v237";
    %"chk38" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v297" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"iw_2.v298" : W = And %"iw_2.v297", #7;
    %"iw_2.v299" : L = (Ext Sw) %"iw_2.v298";
    %"iw_2.v300" : L = Sub %"iw_2.v295", %"iw_2.v299";
    %"iw_2.v301" = %"iw_2.v291" +p %"iw_2.v300";
    %"chk39" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk39" + 0] <- %"iw_2.v301";
    %"iw_2.v309" : L = Sub %"iw_2.v284", %"iw_2.v236";
    %"chk40" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v311" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"iw_2.v313" : W = And %"iw_2.v311", #4294967288;
    %"iw_2.v314" : L = (Ext Sw) %"iw_2.v313";
    %"iw_2.v315" : W = (Cmp Sgt L) %"iw_2.v309", %"iw_2.v314"
    => br %"iw_2.v315" ? "iw_2.L304" : "iw_2.L303" };
  ir_blk{ @"iw_2.L303":
    %"iw_2.v316" : P = Copy $"glibc_gconv_simple#str.294";
    %"iw_2.v317" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v318" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v316", P %"iw_2.v317", W #419, P %"iw_2.v318")
    => goto "iw_2.L304" };
  ir_blk{ @"iw_2.L304":
    %"iw_2.v327" : W = (Cmp Ule L) %"iw_2.v309", #4
    => br %"iw_2.v327" ? "iw_2.L321" : "iw_2.L320" };
  ir_blk{ @"iw_2.L320":
    %"iw_2.v328" : P = Copy $"glibc_gconv_simple#str.295";
    %"iw_2.v329" : P = Copy $"glibc_gconv_simple#str.289";
    %"iw_2.v330" : P = Copy $"glibc_gconv_simple#str.306";
    call void $"__libc_assert_fail"(P %"iw_2.v328", P %"iw_2.v329", W #420, P %"iw_2.v330")
    => goto "iw_2.L321" };
  ir_blk{ @"iw_2.L321":
    %"chk41" : A = (Renew 0 4 Read 1) %"chk16", %"iw_2.v17";
    %"iw_2.v333" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"iw_2.v335" : W = And %"iw_2.v333", #4294967288;
    %"iw_2.v341" : L = (Ext Sw) %"iw_2.v335";
    %"iw_2.v342" : L = Or %"iw_2.v341", %"iw_2.v309";
    %"chk42" : A = (Renew 0 4 Write 1) %"chk16", %"iw_2.v17";
    store Ww [%"chk42" + 0] <- %"iw_2.v342"
    => goto "iw_2.L343" };
  ir_blk{ @"iw_2.L343" [%"iw_2.pr.14" : L = phi("iw_2.L321" => #0, "iw_2.L344" => %"iw_2.v364")]:
    %"iw_2.v353" : W = (Cmp Ult L) %"iw_2.pr.14", %"iw_2.v309"
    => br %"iw_2.v353" ? "iw_2.L344" : "iw_2.join" };
  ir_blk{ @"iw_2.L344":
    %"iw_2.v355" = %"iw_2.v17" +p #4;
    %"iw_2.v357" = %"iw_2.v355" +p %"iw_2.pr.14";
    %"iw_2.v360" = %"iw_2.pr.8" +p %"iw_2.pr.14";
    %"chk43" : A = (Check 0 1 Read 1) %"iw_2.v360";
    %"iw_2.v361" : W = (RawLoad (LdNarrow Ub) 0) %"chk43";
    %"iw_2.v362" : W = (Ext Sb) %"iw_2.v361";
    %"chk44" : A = (Check 0 1 Write 1) %"iw_2.v357";
    store Wb [%"chk44" + 0] <- %"iw_2.v362";
    %"iw_2.v364" : L = Add %"iw_2.pr.14", #1
    => goto poll "iw_2.L343" };
  ir_blk{ @"iw_2.join" [%"v179" : W = phi("iw_2.L98" => #7, "iw_2.L131" => #5, "iw_2.L243" => #0, "iw_2.L233" => %"iw_2.pr.3", "iw_2.L343" => %"iw_2.pr.3"); %"pr.18" : P = phi("iw_2.L98" => %"v97", "iw_2.L131" => %"v97", "iw_2.L243" => %"iw_2.pr.12", "iw_2.L233" => %"v97", "iw_2.L343" => %"v97")]:
    %"v184" : L = (Ext Sw) %"v179";
    %"v185" : W = (Cmp Ne L) %"v184", #0
    => br %"v185" ? "L180" : "L188" }] [ir_blk{ @"L180":
    => ret %"v179" };
  ir_blk{ @"L188" [%"pr.14" : P = phi("L472" => %"v477", "iw_2.join" => %"pr.18", "L146" => %"v97")]:
    %"chk45" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"chk46" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v195" : L = (RawLoad LdL 0) %"chk46"
    => br %"v110" ? "L196" : "L198" };
  ir_blk{ @"L196":
    %"chk47" : A = (Check 0 8 Read 1) %"v10";
    %"v203" : L = (RawLoad LdL 0) %"chk47"
    => goto "L198" };
  ir_blk{ @"L198" [%"v204" : L = phi("L196" => %"v203", "L188" => #0)]:
    %"v205" : L = Add %"v195", %"v204";
    %"iw_3.v16" = %"v2" +p #16;
    %"chk48" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.v16";
    %"iw_3.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_3.v21" : P = (RawLoadPointer 0 load_effects) %"chk45"
    => goto "iw_3.L25" };
  ir_blk{ @"iw_3.L25" [%"iw_3.pr.4" : P = phi("iw_3.L105" => %"iw_3.pr.4", "iw_3.L90" => %"iw_3.v127", "L198" => %"pr.14"); %"iw_3.pr.3" : P = phi("iw_3.L105" => %"iw_3.v119", "iw_3.L90" => %"iw_3.v129", "L198" => %"iw_3.v21"); %"iw_3.pr.1" : W = phi("iw_3.L105" => #6, "iw_3.L90" => %"iw_3.pr.1", "L198" => #4)]:
    %"iw_3.v30" : L = Ptoi %"iw_3.pr.3";
    %"iw_3.v31" : L = Ptoi %"v6";
    %"iw_3.v32" : W = (Cmp Ne L) %"iw_3.v30", %"iw_3.v31"
    => br %"iw_3.v32" ? "iw_3.L37" : "iw_3.L27" };
  ir_blk{ @"iw_3.L37":
    %"iw_3.v40" = %"iw_3.pr.3" +p #2;
    %"iw_3.v42" : L = Ptoi %"iw_3.v40";
    %"iw_3.v44" : W = (Cmp Ugt L) %"iw_3.v42", %"iw_3.v31"
    => br %"iw_3.v44" ? "iw_3.L27" : "iw_3.L54" };
  ir_blk{ @"iw_3.L54":
    %"iw_3.v57" = %"iw_3.pr.4" +p #4;
    %"iw_3.v59" : L = Ptoi %"iw_3.v57";
    %"iw_3.v60" : L = Ptoi %"v101";
    %"iw_3.v61" : W = (Cmp Ugt L) %"iw_3.v59", %"iw_3.v60"
    => br %"iw_3.v61" ? "iw_3.L67" : "iw_3.L70" };
  ir_blk{ @"iw_3.L70":
    => goto "iw_3.L67" };
  ir_blk{ @"iw_3.L67" [%"iw_3.v81" : W = phi("iw_3.L54" => #1, "iw_3.L70" => #0)]:
    => br %"iw_3.v81" ? "iw_3.L27" : "iw_3.L52" };
  ir_blk{ @"iw_3.L52":
    %"chk50" : A = (Check 0 2 Read 1) %"iw_3.pr.3";
    %"iw_3.v87" : W = (RawLoad (LdNarrow Uh) 0) %"chk50";
    %"iw_3.v92" : W = (Cmp Sge W) %"iw_3.v87", #55296
    => br %"iw_3.v92" ? "iw_3.L93" : "iw_3.L94" };
  ir_blk{ @"iw_3.L93":
    %"iw_3.v96" : W = (Cmp Slt W) %"iw_3.v87", #57344
    => goto "iw_3.L94" };
  ir_blk{ @"iw_3.L94" [%"iw_3.v98" : W = phi("iw_3.L52" => #0, "iw_3.L93" => %"iw_3.v96")]:
    => br %"iw_3.v98" ? "iw_3.iw_1.start" : "iw_3.L90" };
  ir_blk{ @"iw_3.iw_1.start":
    %"iw_3.iw_1.v3" = %"v2" +p #16;
    %"chk51" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.iw_1.v3";
    %"iw_3.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"iw_3.iw_1.v5" : W = Or %"iw_3.iw_1.v4", #1073741824;
    %"chk52" : A = (Renew 0 4 Write 1) %"chk0", %"iw_3.iw_1.v3";
    store Ww [%"chk52" + 0] <- %"iw_3.iw_1.v5";
    %"iw_3.v107" : L = Ptoi %"v111";
    %"iw_3.v109" : W = (Cmp Ne L) %"iw_3.v107", %"v89"
    => br %"iw_3.v109" ? "iw_3.L110" : "iw_3.L111" };
  ir_blk{ @"iw_3.L110":
    %"iw_3.v113" : W = And %"iw_3.v17", #2;
    %"iw_3.v114" : W = (Cmp Ne W) %"iw_3.v113", #0
    => goto "iw_3.L111" };
  ir_blk{ @"iw_3.L111" [%"iw_3.v115" : W = phi("iw_3.iw_1.start" => #0, "iw_3.L110" => %"iw_3.v114")]:
    => br %"iw_3.v115" ? "iw_3.L105" : "iw_3.L27" };
  ir_blk{ @"iw_3.L105":
    %"iw_3.v119" = %"iw_3.pr.3" +p #2;
    %"chk53" : A = (Check 0 8 Read 1) %"v111";
    %"iw_3.v121" : L = (RawLoad LdL 0) %"chk53";
    %"iw_3.v122" : L = Add %"iw_3.v121", #1;
    %"chk54" : A = (Renew 0 8 Write 1) %"chk53", %"v111";
    store Wl [%"chk54" + 0] <- %"iw_3.v122"
    => goto poll "iw_3.L25" };
  ir_blk{ @"iw_3.L90":
    %"chk55" : A = (Check 0 4 Write 1) %"iw_3.pr.4";
    store Ww [%"chk55" + 0] <- %"iw_3.v87";
    %"iw_3.v127" = %"iw_3.pr.4" +p #4;
    %"iw_3.v129" = %"iw_3.pr.3" +p #2
    => goto poll "iw_3.L25" };
  ir_blk{ @"iw_3.L27" [%"iw_3.pr.2" : W = phi("iw_3.L25" => %"iw_3.pr.1", "iw_3.L37" => #7, "iw_3.L67" => #5, "iw_3.L111" => #6)]:
    %"chk56" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk56" + 0] <- %"iw_3.pr.3";
    %"v229" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v229" ? "L223" : "L225" };
  ir_blk{ @"L223":
    %"chk57" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk57" + 0] <- %"iw_3.pr.4"
    => ret %"iw_3.pr.2" };
  ir_blk{ @"L225":
    %"v237" = %"v2" +p #20;
    %"chk58" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v237";
    %"v238" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v239" : W = Add %"v238", #1;
    %"chk59" : A = (Renew 0 4 Write 1) %"chk58", %"v237";
    store Ww [%"chk59" + 0] <- %"v239";
    %"v244" = %"v2" +p #16;
    %"chk60" : A = (Renew 0 4 Read 1) %"chk0", %"v244";
    %"v245" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v246" : W = And %"v245", #1
    => br %"v246" ? "L240" : "L242" };
  ir_blk{ @"L240":
    %"chk61" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk61" + 0] <- %"iw_3.pr.4";
    %"chk62" : A = (Check 0 8 Read 1) %"v10";
    %"v252" : L = (RawLoad LdL 0) %"chk62";
    %"chk63" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v253" : L = (RawLoad LdL 0) %"chk63";
    %"v254" : L = Add %"v252", %"v253";
    %"chk64" : A = (Renew 0 8 Write 1) %"chk62", %"v10";
    store Wl [%"chk64" + 0] <- %"v254"
    => goto "L190" };
  ir_blk{ @"L242":
    %"v261" : L = Ptoi %"iw_3.pr.4";
    %"v262" : L = Ptoi %"pr.14";
    %"v263" : W = (Cmp Ugt L) %"v261", %"v262"
    => br %"v263" ? "L256" : "L258" };
  ir_blk{ @"L256":
    %"chk65" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v268" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Check 0 8 Write 8) %"v266";
    store.ptr [%"chk66" + 0] <- %"v268";
    %"chk67" : F = CheckFunction %"pr.1";
    rawcall %"v277" : W = %"chk67"(P %"v18", P %"v21", P %"v266", P %"iw_3.pr.4", P #0, P %"v10", W #0, W %"v14");
    %"v282" : W = (Cmp Ne W) %"v277", #4
    => br %"v282" ? "L278" : "L279" };
  ir_blk{ @"L278":
    %"chk68" : A = (Renew 0 8 Read 8) %"chk66", %"v266";
    %"v286" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v288" : L = Ptoi %"v286";
    %"v290" : W = (Cmp Ne L) %"v288", %"v261"
    => br %"v290" ? "L283" : "L258" };
  ir_blk{ @"L283":
    %"chk69" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v297" : L = (RawLoad LdL 0) %"chk69"
    => br %"v110" ? "L298" : "L300" };
  ir_blk{ @"L298":
    %"chk70" : A = (Check 0 8 Read 1) %"v10";
    %"v305" : L = (RawLoad LdL 0) %"chk70"
    => goto "L300" };
  ir_blk{ @"L300" [%"v306" : L = phi("L298" => %"v305", "L283" => #0)]:
    %"v307" : L = Add %"v297", %"v306";
    %"v308" : W = (Cmp Eq L) %"v205", %"v307"
    => br %"v308" ? "L328" : "L295" };
  ir_blk{ @"L328":
    %"chk71" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v336" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v338" : L = Ptoi %"v336";
    %"v339" : L = Sub %"v261", %"v338";
    %"v346" : L = Div %"v339", #2;
    (Flight (a "v347") Sub [(FAddress (t "v334")); (FValue (t "v346"))] (LowerOf (t "v334")));
    %"chk73" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk73" + 0] <- %"v347"
    => goto "L258" };
  ir_blk{ @"L295":
    %"chk74" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk74" + 0] <- %"v192";
    %"chk75" : A = (Renew 0 8 Read 8) %"chk66", %"v266";
    %"v417" : P = (RawLoadPointer 0 load_effects) %"chk75";
    %"iw_6.v16" = %"v2" +p #16;
    %"chk76" : A = (Renew 0 4 Read 1) %"chk0", %"iw_6.v16";
    %"iw_6.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"chk77" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_6.v21" : P = (RawLoadPointer 0 load_effects) %"chk77"
    => goto "iw_6.L25" };
  ir_blk{ @"iw_6.L25" [%"iw_6.pr.4" : P = phi("iw_6.L105" => %"iw_6.pr.4", "iw_6.L90" => %"iw_6.v127", "L295" => %"pr.14"); %"iw_6.pr.3" : P = phi("iw_6.L105" => %"iw_6.v119", "iw_6.L90" => %"iw_6.v129", "L295" => %"iw_6.v21"); %"iw_6.pr.1" : W = phi("iw_6.L105" => #6, "iw_6.L90" => %"iw_6.pr.1", "L295" => #4)]:
    %"iw_6.v30" : L = Ptoi %"iw_6.pr.3";
    %"iw_6.v32" : W = (Cmp Ne L) %"iw_6.v30", %"iw_3.v31"
    => br %"iw_6.v32" ? "iw_6.L37" : "iw_6.L27" };
  ir_blk{ @"iw_6.L37":
    %"iw_6.v40" = %"iw_6.pr.3" +p #2;
    %"iw_6.v42" : L = Ptoi %"iw_6.v40";
    %"iw_6.v44" : W = (Cmp Ugt L) %"iw_6.v42", %"iw_3.v31"
    => br %"iw_6.v44" ? "iw_6.L27" : "iw_6.L54" };
  ir_blk{ @"iw_6.L54":
    %"iw_6.v57" = %"iw_6.pr.4" +p #4;
    %"iw_6.v59" : L = Ptoi %"iw_6.v57";
    %"iw_6.v60" : L = Ptoi %"v417";
    %"iw_6.v61" : W = (Cmp Ugt L) %"iw_6.v59", %"iw_6.v60"
    => br %"iw_6.v61" ? "iw_6.L67" : "iw_6.L70" };
  ir_blk{ @"iw_6.L70":
    => goto "iw_6.L67" };
  ir_blk{ @"iw_6.L67" [%"iw_6.v81" : W = phi("iw_6.L54" => #1, "iw_6.L70" => #0)]:
    => br %"iw_6.v81" ? "iw_6.L27" : "iw_6.L52" };
  ir_blk{ @"iw_6.L52":
    %"chk78" : A = (Check 0 2 Read 1) %"iw_6.pr.3";
    %"iw_6.v87" : W = (RawLoad (LdNarrow Uh) 0) %"chk78";
    %"iw_6.v92" : W = (Cmp Sge W) %"iw_6.v87", #55296
    => br %"iw_6.v92" ? "iw_6.L93" : "iw_6.L94" };
  ir_blk{ @"iw_6.L93":
    %"iw_6.v96" : W = (Cmp Slt W) %"iw_6.v87", #57344
    => goto "iw_6.L94" };
  ir_blk{ @"iw_6.L94" [%"iw_6.v98" : W = phi("iw_6.L52" => #0, "iw_6.L93" => %"iw_6.v96")]:
    => br %"iw_6.v98" ? "iw_6.iw_1.start" : "iw_6.L90" };
  ir_blk{ @"iw_6.iw_1.start":
    %"iw_6.iw_1.v3" = %"v2" +p #16;
    %"chk79" : A = (Renew 0 4 Read 1) %"chk0", %"iw_6.iw_1.v3";
    %"iw_6.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk79";
    %"iw_6.iw_1.v5" : W = Or %"iw_6.iw_1.v4", #1073741824;
    %"chk80" : A = (Renew 0 4 Write 1) %"chk0", %"iw_6.iw_1.v3";
    store Ww [%"chk80" + 0] <- %"iw_6.iw_1.v5";
    %"iw_6.v107" : L = Ptoi %"v111";
    %"iw_6.v109" : W = (Cmp Ne L) %"iw_6.v107", %"v89"
    => br %"iw_6.v109" ? "iw_6.L110" : "iw_6.L111" };
  ir_blk{ @"iw_6.L110":
    %"iw_6.v113" : W = And %"iw_6.v17", #2;
    %"iw_6.v114" : W = (Cmp Ne W) %"iw_6.v113", #0
    => goto "iw_6.L111" };
  ir_blk{ @"iw_6.L111" [%"iw_6.v115" : W = phi("iw_6.iw_1.start" => #0, "iw_6.L110" => %"iw_6.v114")]:
    => br %"iw_6.v115" ? "iw_6.L105" : "iw_6.L27" };
  ir_blk{ @"iw_6.L105":
    %"iw_6.v119" = %"iw_6.pr.3" +p #2;
    %"chk81" : A = (Check 0 8 Read 1) %"v111";
    %"iw_6.v121" : L = (RawLoad LdL 0) %"chk81";
    %"iw_6.v122" : L = Add %"iw_6.v121", #1;
    %"chk82" : A = (Renew 0 8 Write 1) %"chk81", %"v111";
    store Wl [%"chk82" + 0] <- %"iw_6.v122"
    => goto poll "iw_6.L25" };
  ir_blk{ @"iw_6.L90":
    %"chk83" : A = (Check 0 4 Write 1) %"iw_6.pr.4";
    store Ww [%"chk83" + 0] <- %"iw_6.v87";
    %"iw_6.v127" = %"iw_6.pr.4" +p #4;
    %"iw_6.v129" = %"iw_6.pr.3" +p #2
    => goto poll "iw_6.L25" };
  ir_blk{ @"iw_6.L27" [%"iw_6.pr.2" : W = phi("iw_6.L25" => %"iw_6.pr.1", "iw_6.L37" => #7, "iw_6.L67" => #5, "iw_6.L111" => #6)]:
    %"chk84" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk84" + 0] <- %"iw_6.pr.3";
    %"v420" : L = (Ext Sw) %"iw_6.pr.2";
    %"chk85" : A = (Renew 0 8 Read 8) %"chk66", %"v266";
    %"v433" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v434" : L = Ptoi %"iw_6.pr.4";
    %"v435" : L = Ptoi %"v433";
    %"v436" : W = (Cmp Eq L) %"v434", %"v435"
    => br %"v436" ? "L431" : "L430" };
  ir_blk{ @"L430":
    %"v437" : P = Copy $"glibc_gconv_simple#str.273";
    %"v438" : P = Copy $"glibc_gconv_simple#str.271";
    %"v439" : P = Copy $"glibc_gconv_simple#str.284";
    call void $"__libc_assert_fail"(P %"v437", P %"v438", W #594, P %"v439")
    => goto "L431" };
  ir_blk{ @"L431":
    %"v444" : W = (Cmp Eq L) %"v420", #5
    => br %"v444" ? "L442" : "L441" };
  ir_blk{ @"L441":
    %"v445" : P = Copy $"glibc_gconv_simple#str.274";
    %"v446" : P = Copy $"glibc_gconv_simple#str.271";
    %"v447" : P = Copy $"glibc_gconv_simple#str.284";
    call void $"__libc_assert_fail"(P %"v445", P %"v446", W #595, P %"v447")
    => goto "L442" };
  ir_blk{ @"L442":
    %"v455" : W = (Cmp Eq L) %"v434", %"v262"
    => br %"v455" ? "L448" : "L258" };
  ir_blk{ @"L448":
    %"v459" = %"v2" +p #20;
    %"chk86" : A = (Renew 0 4 Read 1) %"chk58", %"v459";
    %"v460" : W = (RawLoad (LdNarrow Sw) 0) %"chk86";
    %"v461" : W = Sub %"v460", #1;
    %"chk87" : A = (Renew 0 4 Write 1) %"chk58", %"v459";
    store Ww [%"chk87" + 0] <- %"v461"
    => goto "L258" };
  ir_blk{ @"L279":
    %"v467" : W = (Cmp Eq W) %"iw_3.pr.2", #5
    => br %"v467" ? "L463" : "L258" };
  ir_blk{ @"L463":
    %"chk88" : A = (Renew 0 8 Read 8) %"chk65", %"v2";
    %"v469" : P = (RawLoadPointer 0 load_effects) %"chk88"
    => goto "L258" };
  ir_blk{ @"L258" [%"pr.7" : W = phi("L328" => %"v277", "L448" => %"v277", "L442" => %"v277", "L278" => %"v277", "L463" => #0, "L279" => %"iw_3.pr.2", "L242" => %"iw_3.pr.2")]:
    %"v474" : W = (Cmp Ne W) %"pr.7", #0
    => br %"v474" ? "L190" : "L472" };
  ir_blk{ @"L472":
    %"chk89" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v477" : P = (RawLoadPointer 0 load_effects) %"chk89"
    => goto poll "L188" };
  ir_blk{ @"L190" [%"pr.5" : W = phi("L240" => %"iw_3.pr.2", "L258" => %"pr.7")]:
    %"v509" : L = (Ext Sw) %"v14";
    %"v510" : W = (Cmp Ne L) %"v509", #0
    => br %"v510" ? "L513" : "L514" };
  ir_blk{ @"L513":
    %"v516" : W = (Cmp Eq W) %"pr.5", #7
    => goto "L514" };
  ir_blk{ @"L514" [%"v518" : W = phi("L190" => #0, "L513" => %"v516")]:
    => br %"v518" ? "L478" : "L46" };
  ir_blk{ @"L478":
    %"chk90" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v522" : P = (RawLoadPointer 0 load_effects) %"chk90";
    %"v524" : L = Ptoi %"v522";
    %"v525" : L = Sub %"iw_3.v31", %"v524";
    %"v530" : W = (Cmp Ule L) %"v525", #4
    => br %"v530" ? "L535" : "L527" };
  ir_blk{ @"L527":
    %"v531" : P = Copy $"glibc_gconv_simple#str.275";
    %"v532" : P = Copy $"glibc_gconv_simple#str.271";
    %"v533" : P = Copy $"glibc_gconv_simple#str.284";
    call void $"__libc_assert_fail"(P %"v531", P %"v532", W #647, P %"v533")
    => goto "L535" };
  ir_blk{ @"L535" [%"pr.20" : L = phi("L536" => %"v555", "L527" => #0, "L478" => #0)]:
    %"v541" : W = (Cmp Ult L) %"pr.20", %"v525"
    => br %"v541" ? "L536" : "L538" };
  ir_blk{ @"L536":
    %"v543" = %"v2" +p #32;
    %"chk91" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v543";
    %"v544" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"v545" = %"v544" +p #4;
    %"v547" = %"v545" +p %"pr.20";
    %"chk92" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v549" : P = (RawLoadPointer 0 load_effects) %"chk92";
    %"v551" = %"v549" +p %"pr.20";
    %"chk93" : A = (Check 0 1 Read 1) %"v551";
    %"v552" : W = (RawLoad (LdNarrow Ub) 0) %"chk93";
    %"v553" : W = (Ext Sb) %"v552";
    %"chk94" : A = (Check 0 1 Write 1) %"v547";
    store Wb [%"chk94" + 0] <- %"v553";
    %"v555" : L = Add %"pr.20", #1
    => goto poll "L535" };
  ir_blk{ @"L538":
    %"chk95" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk95" + 0] <- %"v6";
    %"v559" = %"v2" +p #32;
    %"chk96" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v559";
    %"v560" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"chk97" : A = (Check 0 4 Read 1) %"v560";
    %"v561" : W = (RawLoad (LdNarrow Sw) 0) %"chk97";
    %"v563" : W = And %"v561", #4294967288;
    %"chk98" : A = (Renew 0 4 Write 1) %"chk97", %"v560";
    store Ww [%"chk98" + 0] <- %"v563";
    %"v566" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"chk100" : A = (Check 0 4 Read 1) %"v566";
    %"v567" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v569" : L = (Ext Sw) %"v567";
    %"v570" : L = Or %"v569", %"pr.20";
    %"chk101" : A = (Renew 0 4 Write 1) %"chk100", %"v566";
    store Ww [%"chk101" + 0] <- %"v570"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.9" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L538" => %"pr.5", "L514" => %"pr.5")]:
    => ret %"pr.9" }])) }.
