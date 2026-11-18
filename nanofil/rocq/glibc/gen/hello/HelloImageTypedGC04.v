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

Definition hello_image_fn___gconv_transform_ucs4_internal : func :=
  ir_fn{ "export" "__gconv_transform_ucs4_internal"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
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
    %"v59" : P = Copy $"glibc_gconv_simple#str.276";
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
    %"v164" : P = Copy $"glibc_gconv_simple#str.276";
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
    %"chk25" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"iw_2.v73";
    %"iw_2.v75" : W = (RawLoad (LdNarrow Ub) 0) %"chk25";
    %"iw_2.v76" : W = (Cmp Sgt W) %"iw_2.v75", #128
    => br %"iw_2.v76" ? "iw_2.L69" : "iw_2.L70" };
  ir_blk{ @"iw_2.L69":
    %"iw_2.v83" : W = And %"iw_2.v21", #2;
    %"iw_2.v84" : W = (Cmp Eq W) %"iw_2.v83", #0
    => br %"iw_2.v84" ? "iw_2.L79" : "iw_2.L71" };
  ir_blk{ @"iw_2.L79":
    %"iw_2.v86" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk27" : A = (Renew 0 4 Read 1) %"chk15", %"iw_2.v17";
    %"iw_2.v89" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"iw_2.v90" : W = And %"iw_2.v89", #7;
    %"iw_2.v91" : L = (Ext Sw) %"iw_2.v90";
    %"iw_2.v92" : L = Sub %"iw_2.pr.1", %"iw_2.v91";
    (Flight (a "iw_2.v93") Sub [(FAddress (t "iw_2.v86")); (FValue (t "iw_2.v92"))] (LowerOf (t "iw_2.v86")));
    %"chk28" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk28" + 0] <- %"iw_2.v93";
    %"iw_2.iw_1.v3" = %"v2" +p #16;
    %"chk29" : A = (Renew 0 4 Read 1) %"chk0", %"iw_2.iw_1.v3";
    %"iw_2.iw_1.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"iw_2.iw_1.v5" : W = Or %"iw_2.iw_1.v4", #1073741824;
    %"chk30" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk30" + 0] <- %"iw_2.iw_1.v5"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L70":
    %"iw_2.v101" = %"iw_2.v17" +p #4;
    %"iw_2.v102" = %"iw_2.v101" +p #3;
    %"chk31" : A = (HalfCheck Upper 0 1 Read 1) %"chk15", %"iw_2.v102";
    %"iw_2.v103" : W = (RawLoad (LdNarrow Sb) 0) %"chk31";
    %"iw_2.v104" : W = (Ext Ub) %"iw_2.v103";
    %"chk32" : A = (Check 0 1 Write 1) %"v97";
    store Wb [%"chk32" + 0] <- %"iw_2.v104";
    %"iw_2.v107" = %"v97" +p #1;
    %"iw_2.v110" = %"iw_2.v101" +p #2;
    %"iw_2.v111" : W = (RawLoad (LdNarrow Sb) (-1)) %"chk31";
    %"iw_2.v112" : W = (Ext Ub) %"iw_2.v111";
    %"chk34" : A = (HalfCheck Upper 0 1 Write 1) %"chk32", %"iw_2.v107";
    store Wb [%"chk34" + 0] <- %"iw_2.v112";
    %"iw_2.v115" = %"v97" +p #2;
    %"iw_2.v118" = %"iw_2.v101" +p #1;
    %"iw_2.v119" : W = (RawLoad (LdNarrow Sb) 1) %"chk25";
    %"iw_2.v120" : W = (Ext Ub) %"iw_2.v119";
    %"chk36" : A = (HalfCheck Upper 0 1 Write 1) %"chk32", %"iw_2.v115";
    store Wb [%"chk36" + 0] <- %"iw_2.v120";
    %"iw_2.v123" = %"v97" +p #3;
    %"iw_2.v127" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"iw_2.v128" : W = (Ext Ub) %"iw_2.v127";
    %"chk38" : A = (HalfCheck Upper 0 1 Write 1) %"chk32", %"iw_2.v123";
    store Wb [%"chk38" + 0] <- %"iw_2.v128";
    %"iw_2.v131" = %"v97" +p #4
    => goto "iw_2.L71" };
  ir_blk{ @"iw_2.L71" [%"pr.17" : P = phi("iw_2.L69" => %"v97", "iw_2.L70" => %"iw_2.v131")]:
    %"chk39" : A = (Renew 0 4 Read 1) %"chk15", %"iw_2.v17";
    %"iw_2.v133" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"iw_2.v135" : W = And %"iw_2.v133", #4294967288;
    %"chk40" : A = (Renew 0 4 Write 1) %"chk15", %"iw_2.v17";
    store Ww [%"chk40" + 0] <- %"iw_2.v135"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join" [%"v179" : W = phi("iw_2.L52" => #7, "iw_2.L79" => #6, "iw_2.L71" => #0); %"pr.18" : P = phi("iw_2.L52" => %"v97", "iw_2.L71" => %"pr.17", "iw_2.L79" => %"v97")]:
    %"v191" : L = (Ext Sw) %"v179";
    %"v192" : W = (Cmp Ne L) %"v191", #0
    => br %"v192" ? "L187" : "L195" };
  ir_blk{ @"L187":
    => ret %"v179" };
  ir_blk{ @"L195" [%"pr.14" : P = phi("L479" => %"v484", "iw_2.join" => %"pr.18", "L146" => %"v97")]:
    %"chk41" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v202" : L = (RawLoad LdL 0) %"chk42"
    => br %"v110" ? "L203" : "L205" };
  ir_blk{ @"L203":
    %"chk43" : A = (Check 0 8 Read 1) %"v10";
    %"v210" : L = (RawLoad LdL 0) %"chk43"
    => goto "L205" };
  ir_blk{ @"L205" [%"v211" : L = phi("L203" => %"v210", "L195" => #0)]:
    %"v212" : L = Add %"v202", %"v211";
    %"iw_4.v16" = %"v2" +p #16;
    %"chk44" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.v16";
    %"iw_4.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"iw_4.v20" : P = (RawLoadPointer 0 load_effects) %"chk41"
    => goto "iw_4.L25" };
  ir_blk{ @"iw_4.L25" [%"iw_4.pr.2" : P = phi("iw_4.L27" => %"iw_4.pr.3", "L205" => %"pr.14"); %"iw_4.pr.1" : P = phi("iw_4.L27" => %"iw_4.v95", "L205" => %"iw_4.v20")]:
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
    %"chk46" : A = (Check 0 4 Read 1) %"iw_4.pr.1";
    %"iw_4.v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk46";
    %"iw_4.iw_1.v3" : W = And %"iw_4.v49", #4278190080;
    %"iw_4.iw_1.v4" : W = Shr %"iw_4.iw_1.v3", #24;
    %"iw_4.iw_1.v6" : W = And %"iw_4.v49", #16711680;
    %"iw_4.iw_1.v7" : W = Shr %"iw_4.iw_1.v6", #8;
    %"iw_4.iw_1.v8" : W = Or %"iw_4.iw_1.v4", %"iw_4.iw_1.v7";
    %"iw_4.iw_1.v10" : W = And %"iw_4.v49", #65280;
    %"iw_4.iw_1.v11" : W = Shl %"iw_4.iw_1.v10", #8;
    %"iw_4.iw_1.v12" : W = Or %"iw_4.iw_1.v8", %"iw_4.iw_1.v11";
    %"iw_4.iw_1.v14" : W = And %"iw_4.v49", #255;
    %"iw_4.iw_1.v15" : W = Shl %"iw_4.iw_1.v14", #24;
    %"iw_4.iw_1.v16" : W = Or %"iw_4.iw_1.v12", %"iw_4.iw_1.v15";
    %"iw_4.v56" : W = (Cmp Ugt W) %"iw_4.iw_1.v16", #2147483647
    => br %"iw_4.v56" ? "iw_4.L52" : "iw_4.L85" };
  ir_blk{ @"iw_4.L52":
    %"iw_4.v63" : L = Ptoi %"v111";
    %"iw_4.v65" : W = (Cmp Eq L) %"iw_4.v63", %"v89"
    => br %"iw_4.v65" ? "iw_4.iw_2.start" : "iw_4.L61" };
  ir_blk{ @"iw_4.iw_2.start":
    %"iw_4.iw_2.v3" = %"v2" +p #16;
    %"chk47" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.iw_2.v3";
    %"iw_4.iw_2.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk47";
    %"iw_4.iw_2.v5" : W = Or %"iw_4.iw_2.v4", #1073741824;
    %"chk48" : A = (Renew 0 4 Write 1) %"chk0", %"iw_4.iw_2.v3";
    store Ww [%"chk48" + 0] <- %"iw_4.iw_2.v5"
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.L61":
    %"iw_4.v73" : W = And %"iw_4.v17", #2
    => br %"iw_4.v73" ? "iw_4.L69" : "iw_4.L71" };
  ir_blk{ @"iw_4.L69":
    %"chk49" : A = (Check 0 8 Read 1) %"v111";
    %"iw_4.v75" : L = (RawLoad LdL 0) %"chk49";
    %"iw_4.v76" : L = Add %"iw_4.v75", #1;
    %"chk50" : A = (Renew 0 8 Write 1) %"chk49", %"v111";
    store Wl [%"chk50" + 0] <- %"iw_4.v76"
    => goto "iw_4.L27" };
  ir_blk{ @"iw_4.L71":
    %"chk51" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk51" + 0] <- %"iw_4.pr.1";
    %"iw_4.iw_3.v3" = %"v2" +p #16;
    %"chk52" : A = (Renew 0 4 Read 1) %"chk0", %"iw_4.iw_3.v3";
    %"iw_4.iw_3.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"iw_4.iw_3.v5" : W = Or %"iw_4.iw_3.v4", #1073741824;
    %"chk53" : A = (Renew 0 4 Write 1) %"chk0", %"iw_4.iw_3.v3";
    store Ww [%"chk53" + 0] <- %"iw_4.iw_3.v5"
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.L85":
    %"chk54" : A = (Check 0 4 Write 1) %"iw_4.pr.2";
    store Ww [%"chk54" + 0] <- %"iw_4.iw_1.v16";
    %"iw_4.v93" = %"iw_4.pr.2" +p #4
    => goto "iw_4.L27" };
  ir_blk{ @"iw_4.L27" [%"iw_4.pr.3" : P = phi("iw_4.L69" => %"iw_4.pr.2", "iw_4.L85" => %"iw_4.v93")]:
    %"iw_4.v95" = %"iw_4.pr.1" +p #4
    => goto poll "iw_4.L25" };
  ir_blk{ @"iw_4.L28":
    %"chk55" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk55" + 0] <- %"iw_4.pr.1";
    %"chk56" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_4.v104" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"iw_4.v106" : L = Ptoi %"iw_4.v104";
    %"iw_4.v108" : W = (Cmp Eq L) %"iw_4.v106", %"iw_4.v33"
    => br %"iw_4.v108" ? "iw_4.join" : "iw_4.L101" }] [ir_blk{ @"iw_4.L101":
    %"iw_4.v114" = %"iw_4.pr.2" +p #4;
    %"iw_4.v116" : L = Ptoi %"iw_4.v114";
    %"iw_4.v117" : L = Ptoi %"v101";
    %"iw_4.v118" : W = (Cmp Ugt L) %"iw_4.v116", %"iw_4.v117"
    => br %"iw_4.v118" ? "iw_4.join" : "iw_4.L110" };
  ir_blk{ @"iw_4.L110":
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join" [%"v222" : W = phi("iw_4.iw_2.start" => #6, "iw_4.L71" => #6, "iw_4.L28" => #4, "iw_4.L101" => #5, "iw_4.L110" => #7); %"pr.21" : P = phi("iw_4.L71" => %"iw_4.pr.2", "iw_4.iw_2.start" => %"pr.14", "iw_4.L28" => %"iw_4.pr.2", "iw_4.L101" => %"iw_4.pr.2", "iw_4.L110" => %"iw_4.pr.2")]:
    %"v236" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v236" ? "L230" : "L232" };
  ir_blk{ @"L230":
    %"chk57" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk57" + 0] <- %"pr.21"
    => ret %"v222" };
  ir_blk{ @"L232":
    %"v244" = %"v2" +p #20;
    %"chk58" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v244";
    %"v245" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"v246" : W = Add %"v245", #1;
    %"chk59" : A = (Renew 0 4 Write 1) %"chk58", %"v244";
    store Ww [%"chk59" + 0] <- %"v246";
    %"v251" = %"v2" +p #16;
    %"chk60" : A = (Renew 0 4 Read 1) %"chk0", %"v251";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk60";
    %"v253" : W = And %"v252", #1
    => br %"v253" ? "L247" : "L249" };
  ir_blk{ @"L247":
    %"chk61" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk61" + 0] <- %"pr.21";
    %"chk62" : A = (Check 0 8 Read 1) %"v10";
    %"v259" : L = (RawLoad LdL 0) %"chk62";
    %"chk63" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v260" : L = (RawLoad LdL 0) %"chk63";
    %"v261" : L = Add %"v259", %"v260";
    %"chk64" : A = (Renew 0 8 Write 1) %"chk62", %"v10";
    store Wl [%"chk64" + 0] <- %"v261"
    => goto "L197" };
  ir_blk{ @"L249":
    %"v268" : L = Ptoi %"pr.21";
    %"v269" : L = Ptoi %"pr.14";
    %"v270" : W = (Cmp Ugt L) %"v268", %"v269"
    => br %"v270" ? "L263" : "L265" };
  ir_blk{ @"L263":
    %"chk65" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk66" + 0] <- %"v275";
    %"chk67" : F = CheckFunction %"pr.1";
    rawcall %"v284" : W = %"chk67"(P %"v18", P %"v21", P %"v273", P %"pr.21", P #0, P %"v10", W #0, W %"v14");
    %"v289" : W = (Cmp Ne W) %"v284", #4
    => br %"v289" ? "L285" : "L286" };
  ir_blk{ @"L285":
    %"chk68" : A = (Renew 0 8 Read 8) %"chk66", %"v273";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v295" : L = Ptoi %"v293";
    %"v297" : W = (Cmp Ne L) %"v295", %"v268"
    => br %"v297" ? "L290" : "L265" };
  ir_blk{ @"L290":
    %"chk69" : A = (Renew 0 8 Read 1) %"chk10", %"v103";
    %"v304" : L = (RawLoad LdL 0) %"chk69"
    => br %"v110" ? "L305" : "L307" };
  ir_blk{ @"L305":
    %"chk70" : A = (Check 0 8 Read 1) %"v10";
    %"v312" : L = (RawLoad LdL 0) %"chk70"
    => goto "L307" };
  ir_blk{ @"L307" [%"v313" : L = phi("L305" => %"v312", "L290" => #0)]:
    %"v314" : L = Add %"v304", %"v313";
    %"v315" : W = (Cmp Eq L) %"v212", %"v314"
    => br %"v315" ? "L319" : "L302" };
  ir_blk{ @"L319":
    %"chk71" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v329" : L = Ptoi %"v327";
    %"v330" : L = Sub %"v268", %"v329";
    (Flight (a "v334") Sub [(FAddress (t "v325")); (FValue (t "v330"))] (LowerOf (t "v325")));
    %"chk73" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk73" + 0] <- %"v334"
    => goto "L265" };
  ir_blk{ @"L302":
    %"chk74" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk74" + 0] <- %"v199";
    %"chk75" : A = (Renew 0 8 Read 8) %"chk66", %"v273";
    %"v424" : P = (RawLoadPointer 0 load_effects) %"chk75";
    %"iw_7.v16" = %"v2" +p #16;
    %"chk76" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.v16";
    %"iw_7.v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"chk77" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v20" : P = (RawLoadPointer 0 load_effects) %"chk77"
    => goto "iw_7.L25" };
  ir_blk{ @"iw_7.L25" [%"iw_7.pr.2" : P = phi("iw_7.L27" => %"iw_7.pr.3", "L302" => %"pr.14"); %"iw_7.pr.1" : P = phi("iw_7.L27" => %"iw_7.v95", "L302" => %"iw_7.v20")]:
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
    %"chk78" : A = (Check 0 4 Read 1) %"iw_7.pr.1";
    %"iw_7.v49" : W = (RawLoad (LdNarrow Uw) 0) %"chk78";
    %"iw_7.iw_1.v3" : W = And %"iw_7.v49", #4278190080;
    %"iw_7.iw_1.v4" : W = Shr %"iw_7.iw_1.v3", #24;
    %"iw_7.iw_1.v6" : W = And %"iw_7.v49", #16711680;
    %"iw_7.iw_1.v7" : W = Shr %"iw_7.iw_1.v6", #8;
    %"iw_7.iw_1.v8" : W = Or %"iw_7.iw_1.v4", %"iw_7.iw_1.v7";
    %"iw_7.iw_1.v10" : W = And %"iw_7.v49", #65280;
    %"iw_7.iw_1.v11" : W = Shl %"iw_7.iw_1.v10", #8;
    %"iw_7.iw_1.v12" : W = Or %"iw_7.iw_1.v8", %"iw_7.iw_1.v11";
    %"iw_7.iw_1.v14" : W = And %"iw_7.v49", #255;
    %"iw_7.iw_1.v15" : W = Shl %"iw_7.iw_1.v14", #24;
    %"iw_7.iw_1.v16" : W = Or %"iw_7.iw_1.v12", %"iw_7.iw_1.v15";
    %"iw_7.v56" : W = (Cmp Ugt W) %"iw_7.iw_1.v16", #2147483647
    => br %"iw_7.v56" ? "iw_7.L52" : "iw_7.L85" };
  ir_blk{ @"iw_7.L52":
    %"iw_7.v63" : L = Ptoi %"v111";
    %"iw_7.v65" : W = (Cmp Eq L) %"iw_7.v63", %"v89"
    => br %"iw_7.v65" ? "iw_7.iw_2.start" : "iw_7.L61" };
  ir_blk{ @"iw_7.iw_2.start":
    %"iw_7.iw_2.v3" = %"v2" +p #16;
    %"chk79" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.iw_2.v3";
    %"iw_7.iw_2.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk79";
    %"iw_7.iw_2.v5" : W = Or %"iw_7.iw_2.v4", #1073741824;
    %"chk80" : A = (Renew 0 4 Write 1) %"chk0", %"iw_7.iw_2.v3";
    store Ww [%"chk80" + 0] <- %"iw_7.iw_2.v5"
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.L61":
    %"iw_7.v73" : W = And %"iw_7.v17", #2
    => br %"iw_7.v73" ? "iw_7.L69" : "iw_7.L71" };
  ir_blk{ @"iw_7.L69":
    %"chk81" : A = (Check 0 8 Read 1) %"v111";
    %"iw_7.v75" : L = (RawLoad LdL 0) %"chk81";
    %"iw_7.v76" : L = Add %"iw_7.v75", #1;
    %"chk82" : A = (Renew 0 8 Write 1) %"chk81", %"v111";
    store Wl [%"chk82" + 0] <- %"iw_7.v76"
    => goto "iw_7.L27" };
  ir_blk{ @"iw_7.L71":
    %"chk83" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk83" + 0] <- %"iw_7.pr.1";
    %"iw_7.iw_3.v3" = %"v2" +p #16;
    %"chk84" : A = (Renew 0 4 Read 1) %"chk0", %"iw_7.iw_3.v3";
    %"iw_7.iw_3.v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk84";
    %"iw_7.iw_3.v5" : W = Or %"iw_7.iw_3.v4", #1073741824;
    %"chk85" : A = (Renew 0 4 Write 1) %"chk0", %"iw_7.iw_3.v3";
    store Ww [%"chk85" + 0] <- %"iw_7.iw_3.v5"
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.L85":
    %"chk86" : A = (Check 0 4 Write 1) %"iw_7.pr.2";
    store Ww [%"chk86" + 0] <- %"iw_7.iw_1.v16";
    %"iw_7.v93" = %"iw_7.pr.2" +p #4
    => goto "iw_7.L27" };
  ir_blk{ @"iw_7.L27" [%"iw_7.pr.3" : P = phi("iw_7.L69" => %"iw_7.pr.2", "iw_7.L85" => %"iw_7.v93")]:
    %"iw_7.v95" = %"iw_7.pr.1" +p #4
    => goto poll "iw_7.L25" };
  ir_blk{ @"iw_7.L28":
    %"chk87" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk87" + 0] <- %"iw_7.pr.1";
    %"chk88" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v104" : P = (RawLoadPointer 0 load_effects) %"chk88";
    %"iw_7.v106" : L = Ptoi %"iw_7.v104";
    %"iw_7.v108" : W = (Cmp Eq L) %"iw_7.v106", %"iw_4.v33"
    => br %"iw_7.v108" ? "iw_7.join" : "iw_7.L101" };
  ir_blk{ @"iw_7.L101":
    %"iw_7.v114" = %"iw_7.pr.2" +p #4;
    %"iw_7.v116" : L = Ptoi %"iw_7.v114";
    %"iw_7.v117" : L = Ptoi %"v424";
    %"iw_7.v118" : W = (Cmp Ugt L) %"iw_7.v116", %"iw_7.v117"
    => br %"iw_7.v118" ? "iw_7.join" : "iw_7.L110" };
  ir_blk{ @"iw_7.L110":
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join" [%"v426" : W = phi("iw_7.iw_2.start" => #6, "iw_7.L71" => #6, "iw_7.L28" => #4, "iw_7.L101" => #5, "iw_7.L110" => #7); %"pr.23" : P = phi("iw_7.L71" => %"iw_7.pr.2", "iw_7.iw_2.start" => %"pr.14", "iw_7.L28" => %"iw_7.pr.2", "iw_7.L101" => %"iw_7.pr.2", "iw_7.L110" => %"iw_7.pr.2")]:
    %"v427" : L = (Ext Sw) %"v426";
    %"chk89" : A = (Renew 0 8 Read 8) %"chk66", %"v273";
    %"v440" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"v441" : L = Ptoi %"pr.23";
    %"v442" : L = Ptoi %"v440";
    %"v443" : W = (Cmp Eq L) %"v441", %"v442"
    => br %"v443" ? "L438" : "L437" };
  ir_blk{ @"L437":
    %"v444" : P = Copy $"glibc_gconv_simple#str.273";
    %"v445" : P = Copy $"glibc_gconv_simple#str.271";
    %"v446" : P = Copy $"glibc_gconv_simple#str.276";
    call void $"__libc_assert_fail"(P %"v444", P %"v445", W #594, P %"v446")
    => goto "L438" };
  ir_blk{ @"L438":
    %"v451" : W = (Cmp Eq L) %"v427", #5
    => br %"v451" ? "L449" : "L448" };
  ir_blk{ @"L448":
    %"v452" : P = Copy $"glibc_gconv_simple#str.274";
    %"v453" : P = Copy $"glibc_gconv_simple#str.271";
    %"v454" : P = Copy $"glibc_gconv_simple#str.276";
    call void $"__libc_assert_fail"(P %"v452", P %"v453", W #595, P %"v454")
    => goto "L449" };
  ir_blk{ @"L449":
    %"v462" : W = (Cmp Eq L) %"v441", %"v269"
    => br %"v462" ? "L455" : "L265" };
  ir_blk{ @"L455":
    %"v466" = %"v2" +p #20;
    %"chk90" : A = (Renew 0 4 Read 1) %"chk58", %"v466";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk90";
    %"v468" : W = Sub %"v467", #1;
    %"chk91" : A = (Renew 0 4 Write 1) %"chk58", %"v466";
    store Ww [%"chk91" + 0] <- %"v468"
    => goto "L265" };
  ir_blk{ @"L286":
    %"v474" : W = (Cmp Eq W) %"v222", #5
    => br %"v474" ? "L470" : "L265" };
  ir_blk{ @"L470":
    %"chk92" : A = (Renew 0 8 Read 8) %"chk65", %"v2";
    %"v476" : P = (RawLoadPointer 0 load_effects) %"chk92"
    => goto "L265" };
  ir_blk{ @"L265" [%"pr.7" : W = phi("L319" => %"v284", "L455" => %"v284", "L449" => %"v284", "L285" => %"v284", "L470" => #0, "L286" => %"v222", "L249" => %"v222")]:
    %"v481" : W = (Cmp Ne W) %"pr.7", #0
    => br %"v481" ? "L197" : "L479" };
  ir_blk{ @"L479":
    %"chk93" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk93"
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
    %"chk94" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v529" : P = (RawLoadPointer 0 load_effects) %"chk94";
    %"v531" : L = Ptoi %"v529";
    %"v532" : L = Sub %"iw_4.v33", %"v531";
    %"v537" : W = (Cmp Ule L) %"v532", #4
    => br %"v537" ? "L542" : "L534" };
  ir_blk{ @"L534":
    %"v538" : P = Copy $"glibc_gconv_simple#str.275";
    %"v539" : P = Copy $"glibc_gconv_simple#str.271";
    %"v540" : P = Copy $"glibc_gconv_simple#str.276";
    call void $"__libc_assert_fail"(P %"v538", P %"v539", W #647, P %"v540")
    => goto "L542" };
  ir_blk{ @"L542" [%"pr.26" : L = phi("L543" => %"v562", "L534" => #0, "L485" => #0)]:
    %"v548" : W = (Cmp Ult L) %"pr.26", %"v532"
    => br %"v548" ? "L543" : "L545" };
  ir_blk{ @"L543":
    %"v550" = %"v2" +p #32;
    %"chk95" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v550";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v552" = %"v551" +p #4;
    %"v554" = %"v552" +p %"pr.26";
    %"chk96" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v556" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v558" = %"v556" +p %"pr.26";
    %"chk97" : A = (Check 0 1 Read 1) %"v558";
    %"v559" : W = (RawLoad (LdNarrow Ub) 0) %"chk97";
    %"v560" : W = (Ext Sb) %"v559";
    %"chk98" : A = (Check 0 1 Write 1) %"v554";
    store Wb [%"chk98" + 0] <- %"v560";
    %"v562" : L = Add %"pr.26", #1
    => goto poll "L542" };
  ir_blk{ @"L545":
    %"chk99" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk99" + 0] <- %"v6";
    %"v566" = %"v2" +p #32;
    %"chk100" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v566";
    %"v567" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"chk101" : A = (Check 0 4 Read 1) %"v567";
    %"v568" : W = (RawLoad (LdNarrow Sw) 0) %"chk101";
    %"v570" : W = And %"v568", #4294967288;
    %"chk102" : A = (Renew 0 4 Write 1) %"chk101", %"v567";
    store Ww [%"chk102" + 0] <- %"v570";
    %"v573" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"chk104" : A = (Check 0 4 Read 1) %"v573";
    %"v574" : W = (RawLoad (LdNarrow Sw) 0) %"chk104";
    %"v576" : L = (Ext Sw) %"v574";
    %"v577" : L = Or %"v576", %"pr.26";
    %"chk105" : A = (Renew 0 4 Write 1) %"chk104", %"v573";
    store Ww [%"chk105" + 0] <- %"v577"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.9" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L545" => %"pr.5", "L521" => %"pr.5")]:
    => ret %"pr.9" }])) }.

Definition hello_image_fn___gconv_transform_internal_ucs4le : func :=
  ir_fn{ "export" "__gconv_transform_internal_ucs4le"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10", W %"v12", W %"v14") -> (RClass W) blocks ((app [ir_blk{ @"start":
    alloca "v103" 8;
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
    %"v59" : P = Copy $"glibc_gconv_simple#str.277";
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
    %"chk10" : A = (CheckLocal (a "v103") 0 8 Write 1);
    store Wl [%"chk10" + 0] <- #0;
    %"v109" : L = Ptoi %"v10";
    %"v110" : W = (Cmp Ne L) %"v109", #0
    => br %"v110" ? "L140" : "L106" };
  ir_blk{ @"L106":
    => goto "L140" };
  ir_blk{ @"L140":
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
  ir_blk{ @"L146" [%"v154" : W = phi("L140" => #0, "L145" => %"v152")]:
    => br %"v154" ? "L112" : "L195" };
  ir_blk{ @"L112":
    => br %"v90" ? "iw_2.start" : "L156" };
  ir_blk{ @"L156":
    %"v162" : P = Copy $"glibc_gconv_simple#str.270";
    %"v163" : P = Copy $"glibc_gconv_simple#str.271";
    %"v164" : P = Copy $"glibc_gconv_simple#str.277";
    call void $"__libc_assert_fail"(P %"v162", P %"v163", W #467, P %"v164")
    => goto "iw_2.start" };
  ir_blk{ @"iw_2.start":
    %"iw_2.v16" = %"v2" +p #32;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v16";
    %"iw_2.v17" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"iw_2.v21" : W = And %"iw_2.v20", #7;
    %"iw_2.v22" : L = (Ext Sw) %"iw_2.v21"
    => goto "iw_2.L23" };
  ir_blk{ @"iw_2.L23" [%"iw_2.pr.1" : L = phi("iw_2.L24" => %"iw_2.v41", "iw_2.start" => %"iw_2.v22")]:
    %"chk15" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_2.v27" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_2.v29" : L = Ptoi %"iw_2.v27";
    %"iw_2.v30" : L = Ptoi %"v6";
    %"iw_2.v31" : W = (Cmp Ult L) %"iw_2.v29", %"iw_2.v30"
    => br %"iw_2.v31" ? "iw_2.L32" : "iw_2.L33" };
  ir_blk{ @"iw_2.L32":
    %"iw_2.v35" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => goto "iw_2.L33" };
  ir_blk{ @"iw_2.L33" [%"iw_2.v37" : W = phi("iw_2.L23" => #0, "iw_2.L32" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L24" : "iw_2.L25" };
  ir_blk{ @"iw_2.L24":
    %"iw_2.v39" = %"iw_2.v17" +p #4;
    %"iw_2.v41" : L = Add %"iw_2.pr.1", #1;
    %"iw_2.v42" = %"iw_2.v39" +p %"iw_2.pr.1";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_2.v45" = %"iw_2.v44" +p #1;
    %"chk17" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk17" + 0] <- %"iw_2.v45";
    %"chk18" : A = (Check 0 1 Read 1) %"iw_2.v44";
    %"iw_2.v46" : W = (RawLoad (LdNarrow Ub) 0) %"chk18";
    %"iw_2.v47" : W = (Ext Sb) %"iw_2.v46";
    %"chk19" : A = (Check 0 1 Write 1) %"iw_2.v42";
    store Wb [%"chk19" + 0] <- %"iw_2.v47"
    => goto poll "iw_2.L23" };
  ir_blk{ @"iw_2.L25":
    %"iw_2.v52" : W = (Cmp Ult L) %"iw_2.pr.1", #4
    => br %"iw_2.v52" ? "iw_2.L48" : "iw_2.L50" };
  ir_blk{ @"iw_2.L48":
    %"chk20" : A = (Renew 0 4 Read 1) %"chk14", %"iw_2.v17";
    %"iw_2.v56" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"iw_2.v58" : W = And %"iw_2.v56", #4294967288;
    %"chk21" : A = (Renew 0 4 Write 1) %"chk14", %"iw_2.v17";
    store Ww [%"chk21" + 0] <- %"iw_2.v58";
    %"iw_2.v60" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"iw_2.v62" : L = (Ext Sw) %"iw_2.v60";
    %"iw_2.v63" : L = Or %"iw_2.v62", %"iw_2.pr.1";
    store Ww [%"chk21" + 0] <- %"iw_2.v63"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.L50":
    %"iw_2.v69" = %"iw_2.v17" +p #4;
    %"chk24" : A = (HalfCheck Upper 0 1 Read 1) %"chk14", %"iw_2.v69";
    %"iw_2.v71" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_2.v72" : W = (Ext Ub) %"iw_2.v71";
    %"chk25" : A = (Check 0 1 Write 1) %"v97";
    store Wb [%"chk25" + 0] <- %"iw_2.v72";
    %"iw_2.v75" = %"v97" +p #1;
    %"iw_2.v78" = %"iw_2.v69" +p #1;
    %"chk26" : A = (HalfCheck Upper 0 1 Read 1) %"chk24", %"iw_2.v78";
    %"iw_2.v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"iw_2.v80" : W = (Ext Ub) %"iw_2.v79";
    %"chk27" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v75";
    store Wb [%"chk27" + 0] <- %"iw_2.v80";
    %"iw_2.v83" = %"v97" +p #2;
    %"iw_2.v86" = %"iw_2.v69" +p #2;
    %"chk28" : A = (HalfCheck Upper 0 1 Read 1) %"chk24", %"iw_2.v86";
    %"iw_2.v87" : W = (RawLoad (LdNarrow Sb) 0) %"chk28";
    %"iw_2.v88" : W = (Ext Ub) %"iw_2.v87";
    %"chk29" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v83";
    store Wb [%"chk29" + 0] <- %"iw_2.v88";
    %"iw_2.v91" = %"v97" +p #3;
    %"iw_2.v94" = %"iw_2.v69" +p #3;
    %"chk30" : A = (HalfCheck Upper 0 1 Read 1) %"chk24", %"iw_2.v94";
    %"iw_2.v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk30";
    %"iw_2.v96" : W = (Ext Ub) %"iw_2.v95";
    %"chk31" : A = (HalfCheck Upper 0 1 Write 1) %"chk25", %"iw_2.v91";
    store Wb [%"chk31" + 0] <- %"iw_2.v96";
    %"iw_2.v99" = %"v97" +p #4;
    %"chk32" : A = (Renew 0 4 Read 1) %"chk14", %"iw_2.v17";
    %"iw_2.v101" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"iw_2.v103" : W = And %"iw_2.v101", #4294967288;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk14", %"iw_2.v17";
    store Ww [%"chk33" + 0] <- %"iw_2.v103"
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join" [%"v179" : W = phi("iw_2.L48" => #7, "iw_2.L50" => #0); %"pr.17" : P = phi("iw_2.L48" => %"v97", "iw_2.L50" => %"iw_2.v99")]:
    %"v191" : L = (Ext Sw) %"v179";
    %"v192" : W = (Cmp Ne L) %"v191", #0
    => br %"v192" ? "L187" : "L195" };
  ir_blk{ @"L187":
    => ret %"v179" };
  ir_blk{ @"L195" [%"pr.14" : P = phi("L479" => %"v484", "iw_2.join" => %"pr.17", "L146" => %"v97")]:
    %"chk34" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v202" : L = (RawLoad LdL 0) %"chk35"
    => br %"v110" ? "L203" : "L205" };
  ir_blk{ @"L203":
    %"chk36" : A = (Check 0 8 Read 1) %"v10";
    %"v210" : L = (RawLoad LdL 0) %"chk36"
    => goto "L205" };
  ir_blk{ @"L205" [%"v211" : L = phi("L203" => %"v210", "L195" => #0)]:
    %"v212" : L = Add %"v202", %"v211";
    %"iw_4.v16" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_4.v26" : L = Ptoi %"v6";
    %"iw_4.v27" : L = Ptoi %"iw_4.v16";
    %"iw_4.v28" : L = Sub %"iw_4.v26", %"iw_4.v27";
    %"iw_4.v31" : L = Ptoi %"v101";
    %"iw_4.v32" : L = Ptoi %"pr.14";
    %"iw_4.v33" : L = Sub %"iw_4.v31", %"iw_4.v32";
    %"iw_4.v34" : W = (Cmp Slt L) %"iw_4.v28", %"iw_4.v33"
    => br %"iw_4.v34" ? "iw_4.L23" : "iw_4.L22" };
  ir_blk{ @"iw_4.L22":
    => goto "iw_4.L23" };
  ir_blk{ @"iw_4.L23" [%"iw_4.v45" : L = phi("iw_4.L22" => %"iw_4.v33", "L205" => %"iw_4.v28")]:
    %"iw_4.v46" : L = Div %"iw_4.v45", #4;
    %"iw_4.v51" : L = Shl %"iw_4.v46", #2;
    %"iw_4.v52" = %"iw_4.v16" +p %"iw_4.v51";
    %"chk38" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk38" + 0] <- %"iw_4.v52";
    call %"iw_4.v58" : P = $"__GI_mempcpy"(P %"pr.14", P %"iw_4.v16", L %"iw_4.v51");
    %"chk39" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_4.v63" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"iw_4.v65" : L = Ptoi %"iw_4.v63";
    %"iw_4.v67" : W = (Cmp Eq L) %"iw_4.v65", %"iw_4.v26"
    => br %"iw_4.v67" ? "iw_4.L61" : "iw_4.L60" };
  ir_blk{ @"iw_4.L60":
    %"iw_4.v73" = %"iw_4.v58" +p #4;
    %"iw_4.v75" : L = Ptoi %"iw_4.v73";
    %"iw_4.v77" : W = (Cmp Ugt L) %"iw_4.v75", %"iw_4.v31"
    => br %"iw_4.v77" ? "iw_4.L61" : "iw_4.L69" };
  ir_blk{ @"iw_4.L69":
    => goto "iw_4.L61" }] [ir_blk{ @"iw_4.L61" [%"iw_4.pr.1" : W = phi("iw_4.L23" => #4, "iw_4.L69" => #7, "iw_4.L60" => #5)]:
    %"v236" : W = (Cmp Ne L) %"v88", %"v89"
    => br %"v236" ? "L230" : "L232" };
  ir_blk{ @"L230":
    %"chk40" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk40" + 0] <- %"iw_4.v58"
    => ret %"iw_4.pr.1" };
  ir_blk{ @"L232":
    %"v244" = %"v2" +p #20;
    %"chk41" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v244";
    %"v245" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"v246" : W = Add %"v245", #1;
    %"chk42" : A = (Renew 0 4 Write 1) %"chk41", %"v244";
    store Ww [%"chk42" + 0] <- %"v246";
    %"v251" = %"v2" +p #16;
    %"chk43" : A = (Renew 0 4 Read 1) %"chk0", %"v251";
    %"v252" : W = (RawLoad (LdNarrow Sw) 0) %"chk43";
    %"v253" : W = And %"v252", #1
    => br %"v253" ? "L247" : "L249" };
  ir_blk{ @"L247":
    %"chk44" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v2";
    store.ptr [%"chk44" + 0] <- %"iw_4.v58";
    %"chk45" : A = (Check 0 8 Read 1) %"v10";
    %"v259" : L = (RawLoad LdL 0) %"chk45";
    %"chk46" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v260" : L = (RawLoad LdL 0) %"chk46";
    %"v261" : L = Add %"v259", %"v260";
    %"chk47" : A = (Renew 0 8 Write 1) %"chk45", %"v10";
    store Wl [%"chk47" + 0] <- %"v261"
    => goto "L197" };
  ir_blk{ @"L249":
    %"v268" : L = Ptoi %"iw_4.v58";
    %"v270" : W = (Cmp Ugt L) %"v268", %"iw_4.v32"
    => br %"v270" ? "L263" : "L265" };
  ir_blk{ @"L263":
    %"chk48" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"chk49" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk49" + 0] <- %"v275";
    %"chk50" : F = CheckFunction %"pr.1";
    rawcall %"v284" : W = %"chk50"(P %"v18", P %"v21", P %"v273", P %"iw_4.v58", P #0, P %"v10", W #0, W %"v14");
    %"v289" : W = (Cmp Ne W) %"v284", #4
    => br %"v289" ? "L285" : "L286" };
  ir_blk{ @"L285":
    %"chk51" : A = (Renew 0 8 Read 8) %"chk49", %"v273";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v295" : L = Ptoi %"v293";
    %"v297" : W = (Cmp Ne L) %"v295", %"v268"
    => br %"v297" ? "L290" : "L265" };
  ir_blk{ @"L290":
    %"chk52" : A = (CheckLocal (a "v103") 0 8 Read 1);
    %"v304" : L = (RawLoad LdL 0) %"chk52"
    => br %"v110" ? "L305" : "L307" };
  ir_blk{ @"L305":
    %"chk53" : A = (Check 0 8 Read 1) %"v10";
    %"v312" : L = (RawLoad LdL 0) %"chk53"
    => goto "L307" };
  ir_blk{ @"L307" [%"v313" : L = phi("L305" => %"v312", "L290" => #0)]:
    %"v314" : L = Add %"v304", %"v313";
    %"v315" : W = (Cmp Eq L) %"v212", %"v314"
    => br %"v315" ? "L319" : "L302" };
  ir_blk{ @"L319":
    %"chk54" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v329" : L = Ptoi %"v327";
    %"v330" : L = Sub %"v268", %"v329";
    (Flight (a "v334") Sub [(FAddress (t "v325")); (FValue (t "v330"))] (LowerOf (t "v325")));
    %"chk56" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk56" + 0] <- %"v334"
    => goto "L265" };
  ir_blk{ @"L302":
    %"chk57" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk57" + 0] <- %"v199";
    %"chk58" : A = (Renew 0 8 Read 8) %"chk49", %"v273";
    %"v424" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"chk59" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v16" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"iw_7.v27" : L = Ptoi %"iw_7.v16";
    %"iw_7.v28" : L = Sub %"iw_4.v26", %"iw_7.v27";
    %"iw_7.v31" : L = Ptoi %"v424";
    %"iw_7.v33" : L = Sub %"iw_7.v31", %"iw_4.v32";
    %"iw_7.v34" : W = (Cmp Slt L) %"iw_7.v28", %"iw_7.v33"
    => br %"iw_7.v34" ? "iw_7.L23" : "iw_7.L22" };
  ir_blk{ @"iw_7.L22":
    => goto "iw_7.L23" };
  ir_blk{ @"iw_7.L23" [%"iw_7.v45" : L = phi("iw_7.L22" => %"iw_7.v33", "L302" => %"iw_7.v28")]:
    %"iw_7.v46" : L = Div %"iw_7.v45", #4;
    %"iw_7.v51" : L = Shl %"iw_7.v46", #2;
    %"iw_7.v52" = %"iw_7.v16" +p %"iw_7.v51";
    %"chk60" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk60" + 0] <- %"iw_7.v52";
    call %"iw_7.v58" : P = $"__GI_mempcpy"(P %"pr.14", P %"iw_7.v16", L %"iw_7.v51");
    %"chk61" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"iw_7.v63" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"iw_7.v65" : L = Ptoi %"iw_7.v63";
    %"iw_7.v67" : W = (Cmp Eq L) %"iw_7.v65", %"iw_4.v26"
    => br %"iw_7.v67" ? "iw_7.L61" : "iw_7.L60" };
  ir_blk{ @"iw_7.L60":
    %"iw_7.v73" = %"iw_7.v58" +p #4;
    %"iw_7.v75" : L = Ptoi %"iw_7.v73";
    %"iw_7.v77" : W = (Cmp Ugt L) %"iw_7.v75", %"iw_7.v31"
    => br %"iw_7.v77" ? "iw_7.L61" : "iw_7.L69" };
  ir_blk{ @"iw_7.L69":
    => goto "iw_7.L61" };
  ir_blk{ @"iw_7.L61" [%"iw_7.pr.1" : W = phi("iw_7.L23" => #4, "iw_7.L69" => #7, "iw_7.L60" => #5)]:
    %"v427" : L = (Ext Sw) %"iw_7.pr.1";
    %"chk62" : A = (Renew 0 8 Read 8) %"chk49", %"v273";
    %"v440" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v441" : L = Ptoi %"iw_7.v58";
    %"v442" : L = Ptoi %"v440";
    %"v443" : W = (Cmp Eq L) %"v441", %"v442"
    => br %"v443" ? "L438" : "L437" };
  ir_blk{ @"L437":
    %"v444" : P = Copy $"glibc_gconv_simple#str.273";
    %"v445" : P = Copy $"glibc_gconv_simple#str.271";
    %"v446" : P = Copy $"glibc_gconv_simple#str.277";
    call void $"__libc_assert_fail"(P %"v444", P %"v445", W #594, P %"v446")
    => goto "L438" };
  ir_blk{ @"L438":
    %"v451" : W = (Cmp Eq L) %"v427", #5
    => br %"v451" ? "L449" : "L448" };
  ir_blk{ @"L448":
    %"v452" : P = Copy $"glibc_gconv_simple#str.274";
    %"v453" : P = Copy $"glibc_gconv_simple#str.271";
    %"v454" : P = Copy $"glibc_gconv_simple#str.277";
    call void $"__libc_assert_fail"(P %"v452", P %"v453", W #595, P %"v454")
    => goto "L449" };
  ir_blk{ @"L449":
    %"v462" : W = (Cmp Eq L) %"v441", %"iw_4.v32"
    => br %"v462" ? "L455" : "L265" };
  ir_blk{ @"L455":
    %"v466" = %"v2" +p #20;
    %"chk63" : A = (Renew 0 4 Read 1) %"chk41", %"v466";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk63";
    %"v468" : W = Sub %"v467", #1;
    %"chk64" : A = (Renew 0 4 Write 1) %"chk41", %"v466";
    store Ww [%"chk64" + 0] <- %"v468"
    => goto "L265" };
  ir_blk{ @"L286":
    %"v474" : W = (Cmp Eq W) %"iw_4.pr.1", #5
    => br %"v474" ? "L470" : "L265" };
  ir_blk{ @"L470":
    %"chk65" : A = (Renew 0 8 Read 8) %"chk48", %"v2";
    %"v476" : P = (RawLoadPointer 0 load_effects) %"chk65"
    => goto "L265" };
  ir_blk{ @"L265" [%"pr.7" : W = phi("L319" => %"v284", "L455" => %"v284", "L449" => %"v284", "L285" => %"v284", "L470" => #0, "L286" => %"iw_4.pr.1", "L249" => %"iw_4.pr.1")]:
    %"v481" : W = (Cmp Ne W) %"pr.7", #0
    => br %"v481" ? "L197" : "L479" };
  ir_blk{ @"L479":
    %"chk66" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v2";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk66"
    => goto poll "L195" };
  ir_blk{ @"L197" [%"pr.5" : W = phi("L247" => %"iw_4.pr.1", "L265" => %"pr.7")]:
    %"v516" : L = (Ext Sw) %"v14";
    %"v517" : W = (Cmp Ne L) %"v516", #0
    => br %"v517" ? "L520" : "L521" };
  ir_blk{ @"L520":
    %"v523" : W = (Cmp Eq W) %"pr.5", #7
    => goto "L521" };
  ir_blk{ @"L521" [%"v525" : W = phi("L197" => #0, "L520" => %"v523")]:
    => br %"v525" ? "L485" : "L46" };
  ir_blk{ @"L485":
    %"chk67" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v529" : P = (RawLoadPointer 0 load_effects) %"chk67";
    %"v531" : L = Ptoi %"v529";
    %"v532" : L = Sub %"iw_4.v26", %"v531";
    %"v537" : W = (Cmp Ule L) %"v532", #4
    => br %"v537" ? "L542" : "L534" };
  ir_blk{ @"L534":
    %"v538" : P = Copy $"glibc_gconv_simple#str.275";
    %"v539" : P = Copy $"glibc_gconv_simple#str.271";
    %"v540" : P = Copy $"glibc_gconv_simple#str.277";
    call void $"__libc_assert_fail"(P %"v538", P %"v539", W #647, P %"v540")
    => goto "L542" };
  ir_blk{ @"L542" [%"pr.20" : L = phi("L543" => %"v562", "L534" => #0, "L485" => #0)]:
    %"v548" : W = (Cmp Ult L) %"pr.20", %"v532"
    => br %"v548" ? "L543" : "L545" };
  ir_blk{ @"L543":
    %"v550" = %"v2" +p #32;
    %"chk68" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v550";
    %"v551" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v552" = %"v551" +p #4;
    %"v554" = %"v552" +p %"pr.20";
    %"chk69" : A = (Renew 0 8 Read 8) %"chk6", %"v4";
    %"v556" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"v558" = %"v556" +p %"pr.20";
    %"chk70" : A = (Check 0 1 Read 1) %"v558";
    %"v559" : W = (RawLoad (LdNarrow Ub) 0) %"chk70";
    %"v560" : W = (Ext Sb) %"v559";
    %"chk71" : A = (Check 0 1 Write 1) %"v554";
    store Wb [%"chk71" + 0] <- %"v560";
    %"v562" : L = Add %"pr.20", #1
    => goto poll "L542" };
  ir_blk{ @"L545":
    %"chk72" : A = (Renew 0 8 Write 8) %"chk6", %"v4";
    store.ptr [%"chk72" + 0] <- %"v6";
    %"v566" = %"v2" +p #32;
    %"chk73" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v566";
    %"v567" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk74" : A = (Check 0 4 Read 1) %"v567";
    %"v568" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v570" : W = And %"v568", #4294967288;
    %"chk75" : A = (Renew 0 4 Write 1) %"chk74", %"v567";
    store Ww [%"chk75" + 0] <- %"v570";
    %"v573" : P = (RawLoadPointer 0 load_effects) %"chk73";
    %"chk77" : A = (Check 0 4 Read 1) %"v573";
    %"v574" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"v576" : L = (Ext Sw) %"v574";
    %"v577" : L = Or %"v576", %"pr.20";
    %"chk78" : A = (Renew 0 4 Write 1) %"chk77", %"v573";
    store Ww [%"chk78" + 0] <- %"v577"
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.9" : W = phi("iw_1.join" => %"v79", "L52" => #0, "L545" => %"pr.5", "L521" => %"pr.5")]:
    => ret %"pr.9" }])) }.
