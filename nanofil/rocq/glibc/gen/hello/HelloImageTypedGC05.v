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

Definition hello_image_fn___gconv_transform_ucs4le_internal : func :=
  ir_fn{ "export" "__gconv_transform_ucs4le_internal"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v103" : P = (Alloc 8) #8;
    %"v273" : P = (Alloc 8) #8;
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
    %"v59" : P = Copy $"glibc_gconv_simple#str.278";
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
    => br %"v154" ? "L112" : "L195" };
  ir_blk{ @"L112":
    => br %"v90" ? "iw_2.start" : "L156" };
  ir_blk{ @"L156":
    %"v162" : P = Copy $"glibc_gconv_simple#str.270";
    %"v163" : P = Copy $"glibc_gconv_simple#str.271";
    %"v164" : P = Copy $"glibc_gconv_simple#str.278";
    call void $"__libc_assert_fail"(P %"v162", P %"v163", W #467, P %"v164")
    => goto "iw_2.start" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v16" = %"v2" +p #32;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v16";
    %"iw_2.v17" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_2.v20" = %"v2" +p #16;
    %"chk14" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.v20";
    %"iw_2.v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"chk15" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"iw_2.v25" : W = And %"iw_2.v24", #7;
    %"iw_2.v26" : L = (Ext Sw) %"iw_2.v25"
    => goto "iw_2.L27" };
  ir_blk{ @"iw_2.L27" [%"iw_2.pr.1" : L = phi("iw_2.L28" => %"iw_2.v45", "iw_2.start" => %"iw_2.v26")]:
    %"chk16" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v31" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v33" : L = Ptoi %"iw_2.v31";
    %"iw_2.v34" : L = Ptoi %"v6";
    %"iw_2.v35" : W = (Cmp Ult L) %"iw_2.v33", %"iw_2.v34"
    => br %"iw_2.v35" ? "iw_2.L36" : "iw_2.L37" };
  ir_blk{ @"iw_2.L36":
    %"iw_2.v39" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => goto "iw_2.L37" };
  ir_blk{ @"iw_2.L37" [%"iw_2.v41" : W = phi("iw_2.L27" => #0, "iw_2.L36" => %"iw_2.v39")]:
    => br %"iw_2.v41" ? "iw_2.L28" : "iw_2.L29" };
  ir_blk{ @"iw_2.L28":
    %"iw_2.v43" = %"iw_2.v17" +p #4;
    %"iw_2.v45" : L = Add %"iw_2.pr.1", #1;
    %"iw_2.v46" = %"iw_2.v43" +p %"iw_2.pr.1";
    %"iw_2.v48" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v49" = %"iw_2.v48" +p #1;
    %"chk18" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk18" + 0] <- %"iw_2.v49";
    %"chk19" : A = (Check 0 1 Read 1) %"iw_2.v48";
    %"iw_2.v50" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"iw_2.v51" : W = (Ext Sb) %"iw_2.v50";
    %"chk20" : A = (Check 0 1 Write 1) %"iw_2.v46";
    store Wb [%"chk20" + 0] <- %"iw_2.v51"
    => goto poll "iw_2.L27" };
  ir_blk{ @"iw_2.L29":
    %"iw_2.v56" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => br %"iw_2.v56" ? "iw_2.L52" : "iw_2.L54" };
  ir_blk{ @"iw_2.L52":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk15", %"iw_2.v17";
    %"iw_2.v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"iw_2.v62" : W = And %"iw_2.v60", #4294967288;
    %"chk22" : A = (Renew 0 4 Write 1) %"chk15", %"iw_2.v17";
    store Ww [%"chk22" + 0] <- %"iw_2.v62";
    %"iw_2.v64" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"iw_2.v66" : L = (Ext Sw) %"iw_2.v64";
    %"iw_2.v67" : L = Or %"iw_2.v66", %"iw_2.pr.1";
    store Ww [%"chk22" + 0] <- %"iw_2.v67"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L54":
    %"iw_2.v73" = %"iw_2.v17" +p #4;
    %"iw_2.v74" = %"iw_2.v73" +p #3;
    %"chk25" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"iw_2.v74";
    %"iw_2.v75" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"iw_2.v76" : W = (Cmp Sgt W) %"iw_2.v75", #128
    => br %"iw_2.v76" ? "iw_2.L69" : "iw_2.L70" };
  ir_blk{ @"iw_2.L69":
    %"iw_2.v83" : W = And %"iw_2.v21", #2;
    %"iw_2.v84" : W = (Cmp Eq W) %"iw_2.v83", #0
    => br %"iw_2.v84" ? "iw_2.iw_1.start" : "iw_2.L71" };
  ir_blk{ @"iw_2.iw_1.start":
    %"iw_2.iw_1.v3" = %"v2" +p #16;
    %"chk26" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.iw_1.v3";
    %"iw_2.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"iw_2.iw_1.v5" : W = Or %"iw_2.iw_1.v4", #1073741824;
    %"chk27" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk27" + 0] <- %"iw_2.iw_1.v5"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L70":
    %"iw_2.v92" = %"iw_2.v17" +p #4;
    %"chk28" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"iw_2.v92";
    %"iw_2.v94" : W = (RawLoad (LdNarrow Sb) 0) %"chk28";
    %"iw_2.v95" : W = (Ext Ub) %"iw_2.v94";
    %"chk29" : A = (Check 0 1 Write 1) %"v97";
    store Wb [%"chk29" + 0] <- %"iw_2.v95";
    %"iw_2.v98" = %"v97" +p #1;
    %"iw_2.v101" = %"iw_2.v92" +p #1;
    %"iw_2.v102" : W = (RawLoad (LdNarrow Sb) 1) %"chk28";
    %"iw_2.v103" : W = (Ext Ub) %"iw_2.v102";
    %"chk31" : A = (HalfCheck Upper 0 1 Write 1) %"chk29", %"iw_2.v98";
    store Wb [%"chk31" + 0] <- %"iw_2.v103";
    %"iw_2.v106" = %"v97" +p #2;
    %"iw_2.v109" = %"iw_2.v92" +p #2;
    %"iw_2.v110" : W = (RawLoad (LdNarrow Sb) (-1)) %"chk25";
    %"iw_2.v111" : W = (Ext Ub) %"iw_2.v110";
    %"chk33" : A = (HalfCheck Upper 0 1 Write 1) %"chk29", %"iw_2.v106";
    store Wb [%"chk33" + 0] <- %"iw_2.v111";
    %"iw_2.v114" = %"v97" +p #3;
    %"iw_2.v117" = %"iw_2.v92" +p #3;
    %"iw_2.v118" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"iw_2.v119" : W = (Ext Ub) %"iw_2.v118";
    %"chk35" : A = (HalfCheck Upper 0 1 Write 1) %"chk29", %"iw_2.v114";
    store Wb [%"chk35" + 0] <- %"iw_2.v119";
    %"iw_2.v122" = %"v97" +p #4
    => goto "iw_2.L71" };
  ir_blk{ @"iw_2.L71" [%"pr.17" : P = phi("iw_2.L69" => %"v97", "iw_2.L70" => %"iw_2.v122")]:
    %"chk36" : A = (Renew 0 4 Read 1) %"chk15", %"iw_2.v17";
    %"iw_2.v124" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"iw_2.v126" : W = And %"iw_2.v124", #4294967288;
    %"chk37" : A = (Renew 0 4 Write 1) %"chk15", %"iw_2.v17";
    store Ww [%"chk37" + 0] <- %"iw_2.v126"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join" [%"v179" : W = phi("iw_2.L52" => #7, "iw_2.iw_1.start" => #6, "iw_2.L71" => #0); %"pr.18" : P = phi("iw_2.L52" => %"v97", "iw_2.L71" => %"pr.17", "iw_2.iw_1.start" => %"v97")]:
    %"v191" : L = (Ext Sw) %"v179";
    %"v192" : W = (Cmp Ne L) %"v191", #0
    => br %"v192" ? "L187" : "L195" };
  ir_blk{ @"L187":
    => ret %"v179" };
  ir_blk{ @"L195" [%"pr.14" : P = phi("L479" => %"v484", "iw_2.join" => %"pr.18", "L146" => %"v97")]:
    %"chk38" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v202" : L = (RawLoad LdL 0) %"chk39"
    => br %"v110" ? "L203" : "L205" };
  ir_blk{ @"L203":
    %"chk40" : A = (Check 0 8 Read 1) %"v10";
    %"v210" : L = (RawLoad LdL 0) %"chk40"
    => goto "L205" };
  ir_blk{ @"L205" [%"v211" : L = phi("L203" => %"v210", "L195" => #0)]:
    %"v212" : L = Add %"v202", %"v211";
    %"iw_4.v16" = %"v2" +p #16;
    %"chk41" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.v16";
    %"iw_4.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"iw_4.v20" : P = (RawLoadPointer 0 load_effects) %"chk38"
    => goto "iw_4.L25" };
  ir_blk{ @"iw_4.L25" [%"iw_4.pr.2" : P = phi("iw_4.L27" => %"iw_4.pr.3", "L205" => %"pr.14"); %"iw_4.pr.1" : P = phi("iw_4.L27" => %"iw_4.v93", "L205" => %"iw_4.v20")]:
    %"iw_4.v30" = %"iw_4.pr.1" +p #4;
    %"iw_4.v32" : L = Ptoi %"iw_4.v30";
    %"iw_4.v33" : L = Ptoi %"v6";
    %"iw_4.v34" : W = (Cmp Ule L) %"iw_4.v32", %"iw_4.v33"
    => br %"iw_4.v34" ? "iw_4.L35" : "iw_4.L36" };
  ir_blk{ @"iw_4.L35":
    %"iw_4.v38" = %"iw_4.pr.2" +p #4;
    %"iw_4.v40" : L = Ptoi %"iw_4.v38";
    %"iw_4.v41" : L = Ptoi %"v101";
    %"iw_4.v42" : W = (Cmp Ule L) %"iw_4.v40", %"iw_4.v41"
    => goto "iw_4.L36" };
  ir_blk{ @"iw_4.L36" [%"iw_4.v44" : W = phi("iw_4.L25" => #0, "iw_4.L35" => %"iw_4.v42")]:
    => br %"iw_4.v44" ? "iw_4.L26" : "iw_4.L28" };
  ir_blk{ @"iw_4.L26":
    %"chk43" : A = (Check 0 4 Read 1) %"iw_4.pr.1";
    %"iw_4.v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk43";
    %"iw_4.v54" : W = (Cmp Ugt W) %"iw_4.v49", #2147483647
    => br %"iw_4.v54" ? "iw_4.L50" : "iw_4.L83" };
  ir_blk{ @"iw_4.L50":
    %"iw_4.v61" : L = Ptoi %"v111";
    %"iw_4.v63" : W = (Cmp Eq L) %"iw_4.v61", %"v89"
    => br %"iw_4.v63" ? "iw_4.iw_1.start" : "iw_4.L59" };
  ir_blk{ @"iw_4.iw_1.start":
    %"iw_4.iw_1.v3" = %"v2" +p #16;
    %"chk44" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.iw_1.v3";
    %"iw_4.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"iw_4.iw_1.v5" : W = Or %"iw_4.iw_1.v4", #1073741824;
    %"chk45" : A = (Renew 0 4 Write 1) %"chk0", %"iw_4.iw_1.v3";
    store Ww [%"chk45" + 0] <- %"iw_4.iw_1.v5"
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.L59":
    %"iw_4.v71" : W = And %"iw_4.v17", #2
    => br %"iw_4.v71" ? "iw_4.L67" : "iw_4.L69" };
  ir_blk{ @"iw_4.L67":
    %"chk46" : A = (Check 0 8 Read 1) %"v111";
    %"iw_4.v73" : L = (RawLoad LdL 0) %"chk46";
    %"iw_4.v74" : L = Add %"iw_4.v73", #1;
    %"chk47" : A = (Renew 0 8 Write 1) %"chk46", %"v111";
    store Wl [%"chk47" + 0] <- %"iw_4.v74"
    => goto "iw_4.L27" };
  ir_blk{ @"iw_4.L69":
    %"chk48" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk48" + 0] <- %"iw_4.pr.1";
    %"iw_4.iw_2.v3" = %"v2" +p #16;
    %"chk49" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.iw_2.v3";
    %"iw_4.iw_2.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"iw_4.iw_2.v5" : W = Or %"iw_4.iw_2.v4", #1073741824;
    %"chk50" : A = (Renew 0 4 Write 1) %"chk0", %"iw_4.iw_2.v3";
    store Ww [%"chk50" + 0] <- %"iw_4.iw_2.v5"
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.L83":
    %"chk51" : A = (Check 0 4 Write 1) %"iw_4.pr.2";
    store Ww [%"chk51" + 0] <- %"iw_4.v49";
    %"iw_4.v91" = %"iw_4.pr.2" +p #4
    => goto "iw_4.L27" };
  ir_blk{ @"iw_4.L27" [%"iw_4.pr.3" : P = phi("iw_4.L67" => %"iw_4.pr.2", "iw_4.L83" => %"iw_4.v91")]:
    %"iw_4.v93" = %"iw_4.pr.1" +p #4
    => goto poll "iw_4.L25" };
  ir_blk{ @"iw_4.L28":
    %"chk52" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk52" + 0] <- %"iw_4.pr.1";
    %"chk53" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_4.v102" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"iw_4.v104" : L = Ptoi %"iw_4.v102";
    %"iw_4.v106" : W = (Cmp Eq L) %"iw_4.v104", %"iw_4.v33"
    => br %"iw_4.v106" ? "iw_4.join" : "iw_4.L99" };
  ir_blk{ @"iw_4.L99":
    %"iw_4.v111" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"iw_4.v112" = %"iw_4.v111" +p #4;
    %"iw_4.v114" : L = Ptoi %"iw_4.v112";
    %"iw_4.v116" : W = (Cmp Ugt L) %"iw_4.v114", %"iw_4.v33"
    => br %"iw_4.v116" ? "iw_4.join" : "iw_4.L108" }] [ir_blk{ @"iw_4.L108":
    %"iw_4.v122" = %"iw_4.pr.2" +p #4;
    %"iw_4.v124" : L = Ptoi %"iw_4.v122";
    %"iw_4.v125" : L = Ptoi %"v101";
    %"iw_4.v126" : W = (Cmp Ugt L) %"iw_4.v124", %"iw_4.v125"
    => br %"iw_4.v126" ? "iw_4.join" : "iw_4.L118" };
  ir_blk{ @"iw_4.L118":
    %"iw_4.v127" : P = Copy $"glibc_gconv_simple#str.315";
    %"iw_4.v128" : P = Copy $"glibc_gconv_simple#str.316";
    %"iw_4.v129" : P = Copy $"glibc_gconv_simple#str.317";
    call void $"__libc_assert_fail"(P %"iw_4.v127", P %"iw_4.v128", W #484, P %"iw_4.v129")
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join" [%"v222" : W = phi("iw_4.iw_1.start" => #6, "iw_4.L69" => #6, "iw_4.L28" => #4, "iw_4.L99" => #7, "iw_4.L108" => #5, "iw_4.L118" => #5); %"pr.21" : P = phi("iw_4.L69" => %"iw_4.pr.2", "iw_4.iw_1.start" => %"pr.14", "iw_4.L28" => %"iw_4.pr.2", "iw_4.L99" => %"iw_4.pr.2", "iw_4.L108" => %"iw_4.pr.2", "iw_4.L118" => %"iw_4.pr.2")]:
    %"v236" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v236" ? "L230" : "L232" };
  ir_blk{ @"L230":
    %"chk55" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk55" + 0] <- %"pr.21"
    => ret %"v222" };
  ir_blk{ @"L232":
    %"v244" = %"v2" +p #20;
    %"chk56" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v244";
    %"v245" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v246" : W = Add %"v245", #1;
    %"chk57" : A = (Renew 0 4 Write 1) %"chk56", %"v244";
    store Ww [%"chk57" + 0] <- %"v246";
    %"v251" = %"v2" +p #16;
    %"chk58" : A = (Renew 0 4 Read 1) %"chk0", %"v251";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v253" : W = And %"v252", #1
    => br %"v253" ? "L247" : "L249" };
  ir_blk{ @"L247":
    %"chk59" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk59" + 0] <- %"pr.21";
    %"chk60" : A = (Check 0 8 Read 1) %"v10";
    %"v259" : L = (RawLoad LdL 0) %"chk60";
    %"chk61" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v260" : L = (RawLoad LdL 0) %"chk61";
    %"v261" : L = Add %"v259", %"v260";
    %"chk62" : A = (Renew 0 8 Write 1) %"chk60", %"v10";
    store Wl [%"chk62" + 0] <- %"v261"
    => goto "L197" };
  ir_blk{ @"L249":
    %"v268" : L = Ptoi %"pr.21";
    %"v269" : L = Ptoi %"pr.14";
    %"v270" : W = (Cmp Ugt L) %"v268", %"v269"
    => br %"v270" ? "L263" : "L265" };
  ir_blk{ @"L263":
    %"chk63" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk64" + 0] <- %"v275";
    %"chk65" : F = CheckFunction %"pr.1";
    rawcall %"v284" : W = %"chk65"(P %"v18", P %"v21", P %"v273", P %"pr.21", P #0, P %"v10", W #0, W %"v14");
    %"v289" : W = (Cmp Ne W) %"v284", #4
    => br %"v289" ? "L285" : "L286" };
  ir_blk{ @"L285":
    %"chk66" : A = (Renew 0 8 Read 8) %"chk64", %"v273";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v295" : L = Ptoi %"v293";
    %"v297" : W = (Cmp Ne L) %"v295", %"v268"
    => br %"v297" ? "L290" : "L265" };
  ir_blk{ @"L290":
    %"chk67" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v304" : L = (RawLoad LdL 0) %"chk67"
    => br %"v110" ? "L305" : "L307" };
  ir_blk{ @"L305":
    %"chk68" : A = (Check 0 8 Read 1) %"v10";
    %"v312" : L = (RawLoad LdL 0) %"chk68"
    => goto "L307" };
  ir_blk{ @"L307" [%"v313" : L = phi("L305" => %"v312", "L290" => #0)]:
    %"v314" : L = Add %"v304", %"v313";
    %"v315" : W = (Cmp Eq L) %"v212", %"v314"
    => br %"v315" ? "L319" : "L302" };
  ir_blk{ @"L319":
    %"chk69" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v329" : L = Ptoi %"v327";
    %"v330" : L = Sub %"v268", %"v329";
    (Flight (a "v334") Sub [(FAddress (t "v325")); (FValue (t "v330"))] (LowerOf (t "v325")));
    %"chk71" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk71" + 0] <- %"v334"
    => goto "L265" };
  ir_blk{ @"L302":
    %"chk72" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk72" + 0] <- %"v199";
    %"chk73" : A = (Renew 0 8 Read 8) %"chk64", %"v273";
    %"v424" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"iw_7.v16" = %"v2" +p #16;
    %"chk74" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.v16";
    %"iw_7.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"chk75" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v20" : P = (RawLoadPointer 0 load_effects) %"chk75"
    => goto "iw_7.L25" };
  ir_blk{ @"iw_7.L25" [%"iw_7.pr.2" : P = phi("iw_7.L27" => %"iw_7.pr.3", "L302" => %"pr.14"); %"iw_7.pr.1" : P = phi("iw_7.L27" => %"iw_7.v93", "L302" => %"iw_7.v20")]:
    %"iw_7.v30" = %"iw_7.pr.1" +p #4;
    %"iw_7.v32" : L = Ptoi %"iw_7.v30";
    %"iw_7.v34" : W = (Cmp Ule L) %"iw_7.v32", %"iw_4.v33"
    => br %"iw_7.v34" ? "iw_7.L35" : "iw_7.L36" };
  ir_blk{ @"iw_7.L35":
    %"iw_7.v38" = %"iw_7.pr.2" +p #4;
    %"iw_7.v40" : L = Ptoi %"iw_7.v38";
    %"iw_7.v41" : L = Ptoi %"v424";
    %"iw_7.v42" : W = (Cmp Ule L) %"iw_7.v40", %"iw_7.v41"
    => goto "iw_7.L36" };
  ir_blk{ @"iw_7.L36" [%"iw_7.v44" : W = phi("iw_7.L25" => #0, "iw_7.L35" => %"iw_7.v42")]:
    => br %"iw_7.v44" ? "iw_7.L26" : "iw_7.L28" };
  ir_blk{ @"iw_7.L26":
    %"chk76" : A = (Check 0 4 Read 1) %"iw_7.pr.1";
    %"iw_7.v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk76";
    %"iw_7.v54" : W = (Cmp Ugt W) %"iw_7.v49", #2147483647
    => br %"iw_7.v54" ? "iw_7.L50" : "iw_7.L83" };
  ir_blk{ @"iw_7.L50":
    %"iw_7.v61" : L = Ptoi %"v111";
    %"iw_7.v63" : W = (Cmp Eq L) %"iw_7.v61", %"v89"
    => br %"iw_7.v63" ? "iw_7.iw_1.start" : "iw_7.L59" };
  ir_blk{ @"iw_7.iw_1.start":
    %"iw_7.iw_1.v3" = %"v2" +p #16;
    %"chk77" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.iw_1.v3";
    %"iw_7.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"iw_7.iw_1.v5" : W = Or %"iw_7.iw_1.v4", #1073741824;
    %"chk78" : A = (Renew 0 4 Write 1) %"chk0", %"iw_7.iw_1.v3";
    store Ww [%"chk78" + 0] <- %"iw_7.iw_1.v5"
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.L59":
    %"iw_7.v71" : W = And %"iw_7.v17", #2
    => br %"iw_7.v71" ? "iw_7.L67" : "iw_7.L69" };
  ir_blk{ @"iw_7.L67":
    %"chk79" : A = (Check 0 8 Read 1) %"v111";
    %"iw_7.v73" : L = (RawLoad LdL 0) %"chk79";
    %"iw_7.v74" : L = Add %"iw_7.v73", #1;
    %"chk80" : A = (Renew 0 8 Write 1) %"chk79", %"v111";
    store Wl [%"chk80" + 0] <- %"iw_7.v74"
    => goto "iw_7.L27" };
  ir_blk{ @"iw_7.L69":
    %"chk81" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk81" + 0] <- %"iw_7.pr.1";
    %"iw_7.iw_2.v3" = %"v2" +p #16;
    %"chk82" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.iw_2.v3";
    %"iw_7.iw_2.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk82";
    %"iw_7.iw_2.v5" : W = Or %"iw_7.iw_2.v4", #1073741824;
    %"chk83" : A = (Renew 0 4 Write 1) %"chk0", %"iw_7.iw_2.v3";
    store Ww [%"chk83" + 0] <- %"iw_7.iw_2.v5"
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.L83":
    %"chk84" : A = (Check 0 4 Write 1) %"iw_7.pr.2";
    store Ww [%"chk84" + 0] <- %"iw_7.v49";
    %"iw_7.v91" = %"iw_7.pr.2" +p #4
    => goto "iw_7.L27" };
  ir_blk{ @"iw_7.L27" [%"iw_7.pr.3" : P = phi("iw_7.L67" => %"iw_7.pr.2", "iw_7.L83" => %"iw_7.v91")]:
    %"iw_7.v93" = %"iw_7.pr.1" +p #4
    => goto poll "iw_7.L25" };
  ir_blk{ @"iw_7.L28":
    %"chk85" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk85" + 0] <- %"iw_7.pr.1";
    %"chk86" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v102" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"iw_7.v104" : L = Ptoi %"iw_7.v102";
    %"iw_7.v106" : W = (Cmp Eq L) %"iw_7.v104", %"iw_4.v33"
    => br %"iw_7.v106" ? "iw_7.join" : "iw_7.L99" };
  ir_blk{ @"iw_7.L99":
    %"iw_7.v111" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"iw_7.v112" = %"iw_7.v111" +p #4;
    %"iw_7.v114" : L = Ptoi %"iw_7.v112";
    %"iw_7.v116" : W = (Cmp Ugt L) %"iw_7.v114", %"iw_4.v33"
    => br %"iw_7.v116" ? "iw_7.join" : "iw_7.L108" };
  ir_blk{ @"iw_7.L108":
    %"iw_7.v122" = %"iw_7.pr.2" +p #4;
    %"iw_7.v124" : L = Ptoi %"iw_7.v122";
    %"iw_7.v125" : L = Ptoi %"v424";
    %"iw_7.v126" : W = (Cmp Ugt L) %"iw_7.v124", %"iw_7.v125"
    => br %"iw_7.v126" ? "iw_7.join" : "iw_7.L118" };
  ir_blk{ @"iw_7.L118":
    %"iw_7.v127" : P = Copy $"glibc_gconv_simple#str.315";
    %"iw_7.v128" : P = Copy $"glibc_gconv_simple#str.316";
    %"iw_7.v129" : P = Copy $"glibc_gconv_simple#str.317";
    call void $"__libc_assert_fail"(P %"iw_7.v127", P %"iw_7.v128", W #484, P %"iw_7.v129")
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join" [%"v426" : W = phi("iw_7.iw_1.start" => #6, "iw_7.L69" => #6, "iw_7.L28" => #4, "iw_7.L99" => #7, "iw_7.L108" => #5, "iw_7.L118" => #5); %"pr.23" : P = phi("iw_7.L69" => %"iw_7.pr.2", "iw_7.iw_1.start" => %"pr.14", "iw_7.L28" => %"iw_7.pr.2", "iw_7.L99" => %"iw_7.pr.2", "iw_7.L108" => %"iw_7.pr.2", "iw_7.L118" => %"iw_7.pr.2")]:
    %"v427" : L = (Ext Sw) %"v426";
    %"chk88" : A = (Renew 0 8 Read 8) %"chk64", %"v273";
    %"v440" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"v441" : L = Ptoi %"pr.23";
    %"v442" : L = Ptoi %"v440";
    %"v443" : W = (Cmp Eq L) %"v441", %"v442"
    => br %"v443" ? "L438" : "L437" };
  ir_blk{ @"L437":
    %"v444" : P = Copy $"glibc_gconv_simple#str.273";
    %"v445" : P = Copy $"glibc_gconv_simple#str.271";
    %"v446" : P = Copy $"glibc_gconv_simple#str.278";
    call void $"__libc_assert_fail"(P %"v444", P %"v445", W #594, P %"v446")
    => goto "L438" };
  ir_blk{ @"L438":
    %"v451" : W = (Cmp Eq L) %"v427", #5
    => br %"v451" ? "L449" : "L448" };
  ir_blk{ @"L448":
    %"v452" : P = Copy $"glibc_gconv_simple#str.274";
    %"v453" : P = Copy $"glibc_gconv_simple#str.271";
    %"v454" : P = Copy $"glibc_gconv_simple#str.278";
    call void $"__libc_assert_fail"(P %"v452", P %"v453", W #595, P %"v454")
    => goto "L449" };
  ir_blk{ @"L449":
    %"v462" : W = (Cmp Eq L) %"v441", %"v269"
    => br %"v462" ? "L455" : "L265" };
  ir_blk{ @"L455":
    %"v466" = %"v2" +p #20;
    %"chk89" : A = (Renew 0 4 Read 1) %"chk56", %"v466";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk89";
    %"v468" : W = Sub %"v467", #1;
    %"chk90" : A = (Renew 0 4 Write 1) %"chk56", %"v466";
    store Ww [%"chk90" + 0] <- %"v468"
    => goto "L265" };
  ir_blk{ @"L286":
    %"v474" : W = (Cmp Eq W) %"v222", #5
    => br %"v474" ? "L470" : "L265" };
  ir_blk{ @"L470":
    %"chk91" : A = (Renew 0 8 Read 8) %"chk63", %"v2";
    %"v476" : P = (RawLoadPointer 0 load_effects) %"chk91"
    => goto "L265" };
  ir_blk{ @"L265" [%"pr.7" : W = phi("L319" => %"v284", "L455" => %"v284", "L449" => %"v284", "L285" => %"v284", "L470" => #0, "L286" => %"v222", "L249" => %"v222")]:
    %"v481" : W = (Cmp Ne W) %"pr.7", #0
    => br %"v481" ? "L197" : "L479" };
  ir_blk{ @"L479":
    %"chk92" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk92"
    => goto poll "L195" };
  ir_blk{ @"L197" [%"pr.5" : W = phi("L247" => %"v222", "L265" => %"pr.7")]:
    %"v516" : L = (Ext Sw) %"v14";
    %"v517" : W = (Cmp Ne L) %"v516", #0
    => br %"v517" ? "L520" : "L521" };
  ir_blk{ @"L520":
    %"v523" : W = (Cmp Eq W) %"pr.5", #7
    => goto "L521" };
  ir_blk{ @"L521" [%"v525" : W = phi("L197" => #0, "L520" => %"v523")]:
    => br %"v525" ? "L485" : "L46" };
  ir_blk{ @"L485":
    %"chk93" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v529" : P = (RawLoadPointer 0 load_effects) %"chk93";
    %"v531" : L = Ptoi %"v529";
    %"v532" : L = Sub %"iw_4.v33", %"v531";
    %"v537" : W = (Cmp Ule L) %"v532", #4
    => br %"v537" ? "L542" : "L534" };
  ir_blk{ @"L534":
    %"v538" : P = Copy $"glibc_gconv_simple#str.275";
    %"v539" : P = Copy $"glibc_gconv_simple#str.271";
    %"v540" : P = Copy $"glibc_gconv_simple#str.278";
    call void $"__libc_assert_fail"(P %"v538", P %"v539", W #647, P %"v540")
    => goto "L542" };
  ir_blk{ @"L542" [%"pr.26" : L = phi("L543" => %"v562", "L534" => #0, "L485" => #0)]:
    %"v548" : W = (Cmp Ult L) %"pr.26", %"v532"
    => br %"v548" ? "L543" : "L545" };
  ir_blk{ @"L543":
    %"v550" = %"v2" +p #32;
    %"chk94" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v550";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk94";
    %"v552" = %"v551" +p #4;
    %"v554" = %"v552" +p %"pr.26";
    %"chk95" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v556" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v558" = %"v556" +p %"pr.26";
    %"chk96" : A = (Check 0 1 Read 1) %"v558";
    %"v559" : W = (RawLoad (LdNarrow Ub) 0) %"chk96";
    %"v560" : W = (Ext Sb) %"v559";
    %"chk97" : A = (Check 0 1 Write 1) %"v554";
    store Wb [%"chk97" + 0] <- %"v560";
    %"v562" : L = Add %"pr.26", #1
    => goto poll "L542" };
  ir_blk{ @"L545":
    %"chk98" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk98" + 0] <- %"v6";
    %"v566" = %"v2" +p #32;
    %"chk99" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v566";
    %"v567" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"chk100" : A = (Check 0 4 Read 1) %"v567";
    %"v568" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v570" : W = And %"v568", #4294967288;
    %"chk101" : A = (Renew 0 4 Write 1) %"chk100", %"v567";
    store Ww [%"chk101" + 0] <- %"v570";
    %"v573" : P = (RawLoadPointer 0 load_effects) %"chk99";
    %"chk103" : A = (Check 0 4 Read 1) %"v573";
    %"v574" : W = (RawLoad (LdNarrow Sw) 0) %"chk103";
    %"v576" : L = (Ext Sw) %"v574";
    %"v577" : L = Or %"v576", %"pr.26";
    %"chk104" : A = (Renew 0 4 Write 1) %"chk103", %"v573";
    store Ww [%"chk104" + 0] <- %"v577"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.9" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L545" => %"pr.5", "L521" => %"pr.5")]:
    => ret %"pr.9" }])) }.

Definition hello_image_fn___gconv_transform_ascii_internal : func :=
  ir_fn{ "export" "__gconv_transform_ascii_internal"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
    %"v103" : P = (Alloc 8) #8;
    %"v251" : P = (Alloc 8) #8;
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
    %"v59" : P = Copy $"glibc_gconv_simple#str.279";
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
    => br #0 ? "L140" : "L141" };
  ir_blk{ @"L140":
    %"v143" : W = (Cmp Ne W) %"v14", #0
    => goto "L141" };
  ir_blk{ @"L141" [%"v144" : W = phi("L107" => #0, "L140" => %"v143")]:
    => br %"v144" ? "L145" : "L146" };
  ir_blk{ @"L145":
    %"v148" = %"v2" +p #32;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 4 Read 1) %"v149";
    %"v150" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v151" : W = And %"v150", #7;
    %"v152" : W = (Cmp Ne W) %"v151", #0
    => goto "L146" };
  ir_blk{ @"L146" [%"v154" : W = phi("L141" => #0, "L145" => %"v152")]:
    => br %"v154" ? "L112" : "L173" };
  ir_blk{ @"L112":
    => br %"v90" ? "L173" : "L156" };
  ir_blk{ @"L156":
    %"v162" : P = Copy $"glibc_gconv_simple#str.270";
    %"v163" : P = Copy $"glibc_gconv_simple#str.271";
    %"v164" : P = Copy $"glibc_gconv_simple#str.279";
    call void $"__libc_assert_fail"(P %"v162", P %"v163", W #467, P %"v164")
    => goto "L173" };
  ir_blk{ @"L173" [%"pr.10" : P = phi("L457" => %"v462", "L156" => %"v97", "L112" => %"v97", "L146" => %"v97")]:
    %"chk13" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v180" : L = (RawLoad LdL 0) %"chk14"
    => br %"v110" ? "L181" : "L183" };
  ir_blk{ @"L181":
    %"chk15" : A = (Check 0 8 Read 1) %"v10";
    %"v188" : L = (RawLoad LdL 0) %"chk15"
    => goto "L183" };
  ir_blk{ @"L183" [%"v189" : L = phi("L181" => %"v188", "L173" => #0)]:
    %"v190" : L = Add %"v180", %"v189";
    %"iw_2.v16" = %"v2" +p #16;
    %"chk16" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.v16";
    %"iw_2.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"iw_2.v21" : P = (RawLoadPointer 0 load_effects) %"chk13"
    => goto "iw_2.L25" };
  ir_blk{ @"iw_2.L25" [%"iw_2.pr.4" : P = phi("iw_2.L95" => %"iw_2.pr.4", "L183" => %"pr.10", "iw_2.L84" => %"iw_2.v119"); %"iw_2.pr.3" : P = phi("iw_2.L95" => %"iw_2.v109", "L183" => %"iw_2.v21", "iw_2.L84" => %"iw_2.v116"); %"iw_2.pr.1" : W = phi("iw_2.L95" => #6, "L183" => #4, "iw_2.L84" => %"iw_2.pr.1")]:
    %"iw_2.v30" : L = Ptoi %"iw_2.pr.3";
    %"iw_2.v31" : L = Ptoi %"v6";
    %"iw_2.v32" : W = (Cmp Ne L) %"iw_2.v30", %"iw_2.v31"
    => br %"iw_2.v32" ? "iw_2.L54" : "iw_2.L27" };
  ir_blk{ @"iw_2.L54":
    %"iw_2.v57" = %"iw_2.pr.4" +p #4;
    %"iw_2.v59" : L = Ptoi %"iw_2.v57";
    %"iw_2.v60" : L = Ptoi %"v101";
    %"iw_2.v61" : W = (Cmp Ugt L) %"iw_2.v59", %"iw_2.v60"
    => br %"iw_2.v61" ? "iw_2.L67" : "iw_2.L70" };
  ir_blk{ @"iw_2.L70":
    => goto "iw_2.L67" };
  ir_blk{ @"iw_2.L67" [%"iw_2.v81" : W = phi("iw_2.L54" => #1, "iw_2.L70" => #0)]:
    => br %"iw_2.v81" ? "iw_2.L27" : "iw_2.L52" };
  ir_blk{ @"iw_2.L52":
    %"chk18" : A = (Check 0 1 Read 1) %"iw_2.pr.3";
    %"iw_2.v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"iw_2.v88" : W = (Cmp Sgt W) %"iw_2.v87", #127
    => br %"iw_2.v88" ? "iw_2.iw_1.start" : "iw_2.L84" };
  ir_blk{ @"iw_2.iw_1.start":
    %"iw_2.iw_1.v3" = %"v2" +p #16;
    %"chk19" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.iw_1.v3";
    %"iw_2.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"iw_2.iw_1.v5" : W = Or %"iw_2.iw_1.v4", #1073741824;
    %"chk20" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk20" + 0] <- %"iw_2.iw_1.v5";
    %"iw_2.v97" : L = Ptoi %"v111";
    %"iw_2.v99" : W = (Cmp Ne L) %"iw_2.v97", %"v89"
    => br %"iw_2.v99" ? "iw_2.L100" : "iw_2.L101" };
  ir_blk{ @"iw_2.L100":
    %"iw_2.v103" : W = And %"iw_2.v17", #2;
    %"iw_2.v104" : W = (Cmp Ne W) %"iw_2.v103", #0
    => goto "iw_2.L101" };
  ir_blk{ @"iw_2.L101" [%"iw_2.v105" : W = phi("iw_2.iw_1.start" => #0, "iw_2.L100" => %"iw_2.v104")]:
    => br %"iw_2.v105" ? "iw_2.L95" : "iw_2.L27" };
  ir_blk{ @"iw_2.L95":
    %"iw_2.v109" = %"iw_2.pr.3" +p #1;
    %"chk21" : A = (Check 0 8 Read 1) %"v111";
    %"iw_2.v111" : L = (RawLoad LdL 0) %"chk21";
    %"iw_2.v112" : L = Add %"iw_2.v111", #1;
    %"chk22" : A = (Renew 0 8 Write 1) %"chk21", %"v111";
    store Wl [%"chk22" + 0] <- %"iw_2.v112"
    => goto poll "iw_2.L25" };
  ir_blk{ @"iw_2.L84":
    %"iw_2.v116" = %"iw_2.pr.3" +p #1;
    %"iw_2.v117" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"chk24" : A = (Check 0 4 Write 1) %"iw_2.pr.4";
    store Ww [%"chk24" + 0] <- %"iw_2.v117";
    %"iw_2.v119" = %"iw_2.pr.4" +p #4
    => goto poll "iw_2.L25" };
  ir_blk{ @"iw_2.L27" [%"iw_2.pr.2" : W = phi("iw_2.L25" => %"iw_2.pr.1", "iw_2.L67" => #5, "iw_2.L101" => #6)]:
    %"chk25" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk25" + 0] <- %"iw_2.pr.3";
    %"v214" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v214" ? "L208" : "L210" };
  ir_blk{ @"L208":
    %"chk26" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk26" + 0] <- %"iw_2.pr.4"
    => ret %"iw_2.pr.2" };
  ir_blk{ @"L210":
    %"v222" = %"v2" +p #20;
    %"chk27" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v222";
    %"v223" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"v224" : W = Add %"v223", #1;
    %"chk28" : A = (Renew 0 4 Write 1) %"chk27", %"v222";
    store Ww [%"chk28" + 0] <- %"v224";
    %"v229" = %"v2" +p #16;
    %"chk29" : A = (Renew 0 4 Read 1) %"chk0", %"v229";
    %"v230" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v231" : W = And %"v230", #1
    => br %"v231" ? "L225" : "L227" };
  ir_blk{ @"L225":
    %"chk30" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk30" + 0] <- %"iw_2.pr.4";
    %"chk31" : A = (Check 0 8 Read 1) %"v10";
    %"v237" : L = (RawLoad LdL 0) %"chk31";
    %"chk32" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v238" : L = (RawLoad LdL 0) %"chk32";
    %"v239" : L = Add %"v237", %"v238";
    %"chk33" : A = (Renew 0 8 Write 1) %"chk31", %"v10";
    store Wl [%"chk33" + 0] <- %"v239"
    => goto "L175" };
  ir_blk{ @"L227":
    %"v246" : L = Ptoi %"iw_2.pr.4";
    %"v247" : L = Ptoi %"pr.10";
    %"v248" : W = (Cmp Ugt L) %"v246", %"v247"
    => br %"v248" ? "L241" : "L243" }] [ir_blk{ @"L241":
    %"chk34" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v253" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (Check 0 8 Write 8) %"v251";
    store.ptr [%"chk35" + 0] <- %"v253";
    %"chk36" : F = CheckFunction %"pr.1";
    rawcall %"v262" : W = %"chk36"(P %"v18", P %"v21", P %"v251", P %"iw_2.pr.4", P #0, P %"v10", W #0, W %"v14");
    %"v267" : W = (Cmp Ne W) %"v262", #4
    => br %"v267" ? "L263" : "L264" };
  ir_blk{ @"L263":
    %"chk37" : A = (Renew 0 8 Read 8) %"chk35", %"v251";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v273" : L = Ptoi %"v271";
    %"v275" : W = (Cmp Ne L) %"v273", %"v246"
    => br %"v275" ? "L268" : "L243" };
  ir_blk{ @"L268":
    %"chk38" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v282" : L = (RawLoad LdL 0) %"chk38"
    => br %"v110" ? "L283" : "L285" };
  ir_blk{ @"L283":
    %"chk39" : A = (Check 0 8 Read 1) %"v10";
    %"v290" : L = (RawLoad LdL 0) %"chk39"
    => goto "L285" };
  ir_blk{ @"L285" [%"v291" : L = phi("L283" => %"v290", "L268" => #0)]:
    %"v292" : L = Add %"v282", %"v291";
    %"v293" : W = (Cmp Eq L) %"v190", %"v292"
    => br %"v293" ? "L313" : "L280" };
  ir_blk{ @"L313":
    %"chk40" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v319" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v321" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v323" : L = Ptoi %"v321";
    %"v324" : L = Sub %"v246", %"v323";
    %"v331" : L = Div %"v324", #4;
    (Flight (a "v332") Sub [(FAddress (t "v319")); (FValue (t "v331"))] (LowerOf (t "v319")));
    %"chk42" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk42" + 0] <- %"v332"
    => goto "L243" };
  ir_blk{ @"L280":
    %"chk43" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk43" + 0] <- %"v177";
    %"chk44" : A = (Renew 0 8 Read 8) %"chk35", %"v251";
    %"v402" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"iw_5.v16" = %"v2" +p #16;
    %"chk45" : A = (Renew 0 4 Read 1) %"chk0", %"iw_5.v16";
    %"iw_5.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk45";
    %"chk46" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_5.v21" : P = (RawLoadPointer 0 load_effects) %"chk46"
    => goto "iw_5.L25" };
  ir_blk{ @"iw_5.L25" [%"iw_5.pr.4" : P = phi("iw_5.L95" => %"iw_5.pr.4", "L280" => %"pr.10", "iw_5.L84" => %"iw_5.v119"); %"iw_5.pr.3" : P = phi("iw_5.L95" => %"iw_5.v109", "L280" => %"iw_5.v21", "iw_5.L84" => %"iw_5.v116"); %"iw_5.pr.1" : W = phi("iw_5.L95" => #6, "L280" => #4, "iw_5.L84" => %"iw_5.pr.1")]:
    %"iw_5.v30" : L = Ptoi %"iw_5.pr.3";
    %"iw_5.v32" : W = (Cmp Ne L) %"iw_5.v30", %"iw_2.v31"
    => br %"iw_5.v32" ? "iw_5.L54" : "iw_5.L27" };
  ir_blk{ @"iw_5.L54":
    %"iw_5.v57" = %"iw_5.pr.4" +p #4;
    %"iw_5.v59" : L = Ptoi %"iw_5.v57";
    %"iw_5.v60" : L = Ptoi %"v402";
    %"iw_5.v61" : W = (Cmp Ugt L) %"iw_5.v59", %"iw_5.v60"
    => br %"iw_5.v61" ? "iw_5.L67" : "iw_5.L70" };
  ir_blk{ @"iw_5.L70":
    => goto "iw_5.L67" };
  ir_blk{ @"iw_5.L67" [%"iw_5.v81" : W = phi("iw_5.L54" => #1, "iw_5.L70" => #0)]:
    => br %"iw_5.v81" ? "iw_5.L27" : "iw_5.L52" };
  ir_blk{ @"iw_5.L52":
    %"chk47" : A = (Check 0 1 Read 1) %"iw_5.pr.3";
    %"iw_5.v87" : W = (RawLoad (LdNarrow Ub) 0) %"chk47";
    %"iw_5.v88" : W = (Cmp Sgt W) %"iw_5.v87", #127
    => br %"iw_5.v88" ? "iw_5.iw_1.start" : "iw_5.L84" };
  ir_blk{ @"iw_5.iw_1.start":
    %"iw_5.iw_1.v3" = %"v2" +p #16;
    %"chk48" : A = (Renew 0 4 Read 1) %"chk0", %"iw_5.iw_1.v3";
    %"iw_5.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"iw_5.iw_1.v5" : W = Or %"iw_5.iw_1.v4", #1073741824;
    %"chk49" : A = (Renew 0 4 Write 1) %"chk0", %"iw_5.iw_1.v3";
    store Ww [%"chk49" + 0] <- %"iw_5.iw_1.v5";
    %"iw_5.v97" : L = Ptoi %"v111";
    %"iw_5.v99" : W = (Cmp Ne L) %"iw_5.v97", %"v89"
    => br %"iw_5.v99" ? "iw_5.L100" : "iw_5.L101" };
  ir_blk{ @"iw_5.L100":
    %"iw_5.v103" : W = And %"iw_5.v17", #2;
    %"iw_5.v104" : W = (Cmp Ne W) %"iw_5.v103", #0
    => goto "iw_5.L101" };
  ir_blk{ @"iw_5.L101" [%"iw_5.v105" : W = phi("iw_5.iw_1.start" => #0, "iw_5.L100" => %"iw_5.v104")]:
    => br %"iw_5.v105" ? "iw_5.L95" : "iw_5.L27" };
  ir_blk{ @"iw_5.L95":
    %"iw_5.v109" = %"iw_5.pr.3" +p #1;
    %"chk50" : A = (Check 0 8 Read 1) %"v111";
    %"iw_5.v111" : L = (RawLoad LdL 0) %"chk50";
    %"iw_5.v112" : L = Add %"iw_5.v111", #1;
    %"chk51" : A = (Renew 0 8 Write 1) %"chk50", %"v111";
    store Wl [%"chk51" + 0] <- %"iw_5.v112"
    => goto poll "iw_5.L25" };
  ir_blk{ @"iw_5.L84":
    %"iw_5.v116" = %"iw_5.pr.3" +p #1;
    %"iw_5.v117" : W = (RawLoad (LdNarrow Ub) 0) %"chk47";
    %"chk53" : A = (Check 0 4 Write 1) %"iw_5.pr.4";
    store Ww [%"chk53" + 0] <- %"iw_5.v117";
    %"iw_5.v119" = %"iw_5.pr.4" +p #4
    => goto poll "iw_5.L25" };
  ir_blk{ @"iw_5.L27" [%"iw_5.pr.2" : W = phi("iw_5.L25" => %"iw_5.pr.1", "iw_5.L67" => #5, "iw_5.L101" => #6)]:
    %"chk54" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk54" + 0] <- %"iw_5.pr.3";
    %"v405" : L = (Ext Sw) %"iw_5.pr.2";
    %"chk55" : A = (Renew 0 8 Read 8) %"chk35", %"v251";
    %"v418" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v419" : L = Ptoi %"iw_5.pr.4";
    %"v420" : L = Ptoi %"v418";
    %"v421" : W = (Cmp Eq L) %"v419", %"v420"
    => br %"v421" ? "L416" : "L415" };
  ir_blk{ @"L415":
    %"v422" : P = Copy $"glibc_gconv_simple#str.273";
    %"v423" : P = Copy $"glibc_gconv_simple#str.271";
    %"v424" : P = Copy $"glibc_gconv_simple#str.279";
    call void $"__libc_assert_fail"(P %"v422", P %"v423", W #594, P %"v424")
    => goto "L416" };
  ir_blk{ @"L416":
    %"v429" : W = (Cmp Eq L) %"v405", #5
    => br %"v429" ? "L427" : "L426" };
  ir_blk{ @"L426":
    %"v430" : P = Copy $"glibc_gconv_simple#str.274";
    %"v431" : P = Copy $"glibc_gconv_simple#str.271";
    %"v432" : P = Copy $"glibc_gconv_simple#str.279";
    call void $"__libc_assert_fail"(P %"v430", P %"v431", W #595, P %"v432")
    => goto "L427" };
  ir_blk{ @"L427":
    %"v440" : W = (Cmp Eq L) %"v419", %"v247"
    => br %"v440" ? "L433" : "L243" };
  ir_blk{ @"L433":
    %"v444" = %"v2" +p #20;
    %"chk56" : A = (Renew 0 4 Read 1) %"chk27", %"v444";
    %"v445" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v446" : W = Sub %"v445", #1;
    %"chk57" : A = (Renew 0 4 Write 1) %"chk27", %"v444";
    store Ww [%"chk57" + 0] <- %"v446"
    => goto "L243" };
  ir_blk{ @"L264":
    %"v452" : W = (Cmp Eq W) %"iw_2.pr.2", #5
    => br %"v452" ? "L448" : "L243" };
  ir_blk{ @"L448":
    %"chk58" : A = (Renew 0 8 Read 8) %"chk34", %"v2";
    %"v454" : P = (RawLoadPointer 0 load_effects) %"chk58"
    => goto "L243" };
  ir_blk{ @"L243" [%"pr.5" : W = phi("L313" => %"v262", "L433" => %"v262", "L427" => %"v262", "L263" => %"v262", "L448" => #0, "L264" => %"iw_2.pr.2", "L227" => %"iw_2.pr.2")]:
    %"v459" : W = (Cmp Ne W) %"pr.5", #0
    => br %"v459" ? "L175" : "L457" };
  ir_blk{ @"L457":
    %"chk59" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v462" : P = (RawLoadPointer 0 load_effects) %"chk59"
    => goto poll "L173" };
  ir_blk{ @"L175" [%"pr.3" : W = phi("L225" => %"iw_2.pr.2", "L243" => %"pr.5")]:
    => br #0 ? "L491" : "L492" };
  ir_blk{ @"L491":
    %"v494" : L = (Ext Sw) %"v14";
    %"v495" : W = (Cmp Ne L) %"v494", #0
    => goto "L492" };
  ir_blk{ @"L492" [%"v497" : W = phi("L175" => #0, "L491" => %"v495")]:
    => br %"v497" ? "L498" : "L499" };
  ir_blk{ @"L498":
    %"v501" : W = (Cmp Eq W) %"pr.3", #7
    => goto "L499" };
  ir_blk{ @"L499" [%"v503" : W = phi("L492" => #0, "L498" => %"v501")]:
    => br %"v503" ? "L463" : "L46" };
  ir_blk{ @"L463":
    %"chk60" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v507" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"v509" : L = Ptoi %"v507";
    %"v510" : L = Sub %"iw_2.v31", %"v509";
    %"v515" : W = (Cmp Ule L) %"v510", #4
    => br %"v515" ? "L520" : "L512" };
  ir_blk{ @"L512":
    %"v516" : P = Copy $"glibc_gconv_simple#str.275";
    %"v517" : P = Copy $"glibc_gconv_simple#str.271";
    %"v518" : P = Copy $"glibc_gconv_simple#str.279";
    call void $"__libc_assert_fail"(P %"v516", P %"v517", W #647, P %"v518")
    => goto "L520" };
  ir_blk{ @"L520" [%"pr.14" : L = phi("L521" => %"v540", "L512" => #0, "L463" => #0)]:
    %"v526" : W = (Cmp Ult L) %"pr.14", %"v510"
    => br %"v526" ? "L521" : "L523" };
  ir_blk{ @"L521":
    %"v528" = %"v2" +p #32;
    %"chk61" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v528";
    %"v529" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v530" = %"v529" +p #4;
    %"v532" = %"v530" +p %"pr.14";
    %"chk62" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v534" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v536" = %"v534" +p %"pr.14";
    %"chk63" : A = (Check 0 1 Read 1) %"v536";
    %"v537" : W = (RawLoad (LdNarrow Ub) 0) %"chk63";
    %"v538" : W = (Ext Sb) %"v537";
    %"chk64" : A = (Check 0 1 Write 1) %"v532";
    store Wb [%"chk64" + 0] <- %"v538";
    %"v540" : L = Add %"pr.14", #1
    => goto poll "L520" };
  ir_blk{ @"L523":
    %"chk65" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk65" + 0] <- %"v6";
    %"v544" = %"v2" +p #32;
    %"chk66" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v544";
    %"v545" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"chk67" : A = (Check 0 4 Read 1) %"v545";
    %"v546" : W = (RawLoad (LdNarrow Sw) 0) %"chk67";
    %"v548" : W = And %"v546", #4294967288;
    %"chk68" : A = (Renew 0 4 Write 1) %"chk67", %"v545";
    store Ww [%"chk68" + 0] <- %"v548";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"chk70" : A = (Check 0 4 Read 1) %"v551";
    %"v552" : W = (RawLoad (LdNarrow Sw) 0) %"chk70";
    %"v554" : L = (Ext Sw) %"v552";
    %"v555" : L = Or %"v554", %"pr.14";
    %"chk71" : A = (Renew 0 4 Write 1) %"chk70", %"v551";
    store Ww [%"chk71" + 0] <- %"v555"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.8" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L523" => %"pr.3", "L499" => %"pr.3")]:
    => ret %"pr.8" }])) }.
