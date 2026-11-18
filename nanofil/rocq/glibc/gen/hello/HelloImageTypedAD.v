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

Definition hello_image_fn_glibc_gconv_conf'23add_alias2 : func :=
  ir_fn{ "local" "glibc_gconv_conf#add_alias2"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" : P = Copy $"__gconv_modules_db";
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v3";
    %"iw_1.v4" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "iw_1.L5";
  @"iw_1.L5" [%"iw_1.pr.2" : P = phi("start" => %"iw_1.v4", "iw_1.L23" => %"iw_1.v30", "iw_1.L24" => %"iw_1.v33")]:
    %"iw_1.v9" : L = Ptoi %"iw_1.pr.2";
    %"iw_1.v10" : L = Ptoi #0;
    %"iw_1.v11" : W = (Cmp Ne L) %"iw_1.v9", %"iw_1.v10"
    => br %"iw_1.v11" ? "iw_1.L6" : "iw_1.join";
  @"iw_1.L6":
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.pr.2";
    %"iw_1.v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"iw_1.v16" : W = $"__GI_strcmp"(P %"v0", P %"iw_1.v15");
    %"iw_1.v21" : W = (Cmp Eq W) %"iw_1.v16", #0
    => br %"iw_1.v21" ? "iw_1.join" : "iw_1.L18";
  @"iw_1.L18":
    %"iw_1.v27" : W = (Cmp Slt W) %"iw_1.v16", #0
    => br %"iw_1.v27" ? "iw_1.L23" : "iw_1.L24";
  @"iw_1.L23":
    %"iw_1.v29" = %"iw_1.pr.2" +p #32;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_1.v29";
    %"iw_1.v30" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto poll "iw_1.L5";
  @"iw_1.L24":
    %"iw_1.v32" = %"iw_1.pr.2" +p #48;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_1.v32";
    %"iw_1.v33" : P = (RawLoadPointer 0 load_effects) %"chk3"
    => goto poll "iw_1.L5";
  @"iw_1.join" [%"v10" : W = phi("iw_1.L6" => #1, "iw_1.L5" => %"iw_1.v11")]:
    => br %"v10" ? "L6" : "L8";
  @"L6":
    => ret void;
  @"L8":
    %"v15" : L = Ptoi %"v4";
    %"v16" : L = Ptoi %"v0";
    %"v17" : L = Sub %"v15", %"v16";
    %"v18" : L = Add %"v17", #16;
    call %"v19" : P = $"malloc"(L %"v18");
    %"v24" : L = Ptoi %"v19";
    %"v26" : W = (Cmp Ne L) %"v24", %"iw_1.v10"
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v30" = %"v19" +p #16;
    call %"v37" : P = $"__GI_memcpy"(P %"v30", P %"v0", L %"v17");
    %"chk4" : A = (Check 0 8 Write 8) %"v19";
    store.ptr [%"chk4" + 0] <- %"v37";
    %"v39" = %"v19" +p #8;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk4", %"v19";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v44" : L = Ptoi %"v2";
    %"v46" : L = Sub %"v44", %"v16";
    %"v47" = %"v41" +p %"v46";
    %"chk6" : A = (HalfCheck Upper 0 8 Write 8) %"chk4", %"v39";
    store.ptr [%"chk6" + 0] <- %"v47";
    %"v49" : P = Copy $"__gconv_alias_db";
    %"v50" : P = Copy $"__gconv_alias_compare";
    call %"v51" : P = $"__GI___tsearch"(P %"v19", P %"v49", P %"v50");
    %"v56" : L = Ptoi %"v51";
    %"v58" : W = (Cmp Eq L) %"v56", %"iw_1.v10"
    => br %"v58" ? "L60" : "L59";
  @"L59":
    %"chk7" : A = (Check 0 8 Read 8) %"v51";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v64" : L = Ptoi %"v62";
    %"v66" : W = (Cmp Ne L) %"v64", %"v24"
    => goto "L60";
  @"L60" [%"v68" : W = phi("L20" => #1, "L59" => %"v66")]:
    => br %"v68" ? "L52" : "L22";
  @"L52":
    call void $"free"(P %"v19")
    => goto "L22";
  @"L22":
    => ret void
} }.

Definition hello_image_fn_glibc_gconv_conf'23add_module : func :=
  ir_fn{ "local" "glibc_gconv_conf#add_module"(P %"v0", P %"v2", L %"v4", W %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #16;
    %"v262" : P = (Alloc 8) #8
    => goto "L16";
  @"L16" [%"pr.5" : P = phi("L17" => %"v30", "start" => %"v0")]:
    %"v19" : P = Copy $"_nl_C_locobj";
    %"v20" = %"v19" +p #104;
    %"chk0" : A = (Check 0 8 Read 8) %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 1 Read 1) %"pr.5";
    %"v23" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v24" : L = (Ext Sw) %"v23";
    %"v25" : L = Shl %"v24", #1;
    %"v26" = %"v21" +p %"v25";
    %"chk2" : A = (Check 0 2 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Uh) 0) %"chk2";
    %"v28" : W = And %"v27", #8192
    => br %"v28" ? "L17" : "L32";
  @"L17":
    %"v30" = %"pr.5" +p #1
    => goto poll "L16";
  @"L32" [%"pr.8" : P = phi("L56" => %"v103", "L16" => %"pr.5")]:
    %"chk3" : A = (Check 0 1 Read 1) %"pr.8";
    %"v36" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v37" : W = (Cmp Ne W) %"v36", #0
    => br %"v37" ? "L38" : "L39";
  @"L38":
    %"v40" : P = Copy $"_nl_C_locobj";
    %"v41" = %"v40" +p #104;
    %"chk4" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Renew 0 1 Read 1) %"chk3", %"pr.8";
    %"v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk5";
    %"v45" : L = (Ext Sw) %"v44";
    %"v46" : L = Shl %"v45", #1;
    %"v47" = %"v42" +p %"v46";
    %"chk6" : A = (Check 0 2 Read 1) %"v47";
    %"v48" : W = (RawLoad (LdNarrow Uh) 0) %"chk6";
    %"v49" : W = And %"v48", #8192;
    %"v50" : W = (Cmp Eq W) %"v49", #0
    => goto "L39";
  @"L39" [%"v52" : W = phi("L32" => #0, "L38" => %"v50")]:
    => br %"v52" ? "L56" : "L34";
  @"L56":
    %"v91" : P = Copy $"_nl_C_locobj";
    %"v92" = %"v91" +p #120;
    %"chk7" : A = (Check 0 8 Read 8) %"v92";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Renew 0 1 Read 1) %"chk3", %"pr.8";
    %"v95" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v96" : L = (Ext Sw) %"v95";
    %"v97" : L = Shl %"v96", #2;
    %"v98" = %"v93" +p %"v97";
    %"chk9" : A = (Check 0 4 Read 1) %"v98";
    %"v99" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v101" : W = (Ext Sb) %"v99";
    %"chk10" : A = (Renew 0 1 Write 1) %"chk3", %"pr.8";
    store Wb [%"chk10" + 0] <- %"v101";
    %"v103" = %"pr.8" +p #1
    => goto poll "L32";
  @"L34":
    %"chk11" : A = (Renew 0 1 Read 1) %"chk3", %"pr.8";
    %"v108" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"v109" : W = (Cmp Eq W) %"v108", #0
    => br %"v109" ? "L104" : "L106";
  @"L104":
    => ret void;
  @"L106":
    %"v112" = %"pr.8" +p #1;
    %"chk12" : A = (Renew 0 1 Write 1) %"chk3", %"pr.8";
    store Wb [%"chk12" + 0] <- #0
    => goto "L114";
  @"L114" [%"pr.1" : P = phi("L106" => %"v112", "L115" => %"v128")]:
    %"v117" : P = Copy $"_nl_C_locobj";
    %"v118" = %"v117" +p #104;
    %"chk13" : A = (Check 0 8 Read 8) %"v118";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 1 Read 1) %"pr.1";
    %"v121" : W = (RawLoad (LdNarrow Sb) 0) %"chk14";
    %"v122" : L = (Ext Sw) %"v121";
    %"v123" : L = Shl %"v122", #1;
    %"v124" = %"v119" +p %"v123";
    %"chk15" : A = (Check 0 2 Read 1) %"v124";
    %"v125" : W = (RawLoad (LdNarrow Uh) 0) %"chk15";
    %"v126" : W = And %"v125", #8192
    => br %"v126" ? "L115" : "L129";
  @"L115":
    %"v128" = %"pr.1" +p #1
    => goto poll "L114";
  @"L129" [%"pr.10" : P = phi("L130" => %"v151", "L114" => %"v112"); %"pr.2" : P = phi("L130" => %"v195", "L114" => %"pr.1")]:
    %"chk16" : A = (Check 0 1 Read 1) %"pr.2";
    %"v133" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v134" : W = (Cmp Ne W) %"v133", #0
    => br %"v134" ? "L135" : "L136";
  @"L135":
    %"v137" : P = Copy $"_nl_C_locobj";
    %"v138" = %"v137" +p #104;
    %"chk17" : A = (Check 0 8 Read 8) %"v138";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 1 Read 1) %"chk16", %"pr.2";
    %"v141" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"v142" : L = (Ext Sw) %"v141";
    %"v143" : L = Shl %"v142", #1;
    %"v144" = %"v139" +p %"v143";
    %"chk19" : A = (Check 0 2 Read 1) %"v144";
    %"v145" : W = (RawLoad (LdNarrow Uh) 0) %"chk19";
    %"v146" : W = And %"v145", #8192;
    %"v147" : W = (Cmp Eq W) %"v146", #0
    => goto "L136";
  @"L136" [%"v149" : W = phi("L129" => #0, "L135" => %"v147")]:
    => br %"v149" ? "L130" : "L131";
  @"L130":
    %"v151" = %"pr.10" +p #1;
    %"v191" : P = Copy $"_nl_C_locobj";
    %"v192" = %"v191" +p #120;
    %"chk20" : A = (Check 0 8 Read 8) %"v192";
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v195" = %"pr.2" +p #1;
    %"chk21" : A = (Renew 0 1 Read 1) %"chk16", %"pr.2";
    %"v196" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v197" : L = (Ext Sw) %"v196";
    %"v198" : L = Shl %"v197", #2;
    %"v199" = %"v193" +p %"v198";
    %"chk22" : A = (Check 0 4 Read 1) %"v199";
    %"v200" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v202" : W = (Ext Sb) %"v200";
    %"chk23" : A = (Check 0 1 Write 1) %"pr.10";
    store Wb [%"chk23" + 0] <- %"v202"
    => goto poll "L129";
  @"L131":
    %"chk24" : A = (Renew 0 1 Read 1) %"chk16", %"pr.2";
    %"v207" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"v208" : W = (Cmp Eq W) %"v207", #0
    => br %"v208" ? "L203" : "L205";
  @"L203":
    => ret void;
  @"L205":
    %"v211" = %"pr.10" +p #1;
    %"chk25" : A = (Check 0 1 Write 1) %"pr.10";
    store Wb [%"chk25" + 0] <- #0
    => goto "L212";
  @"L212" [%"pr.6" : P = phi("L205" => %"pr.2", "L212" => %"v216")]:
    %"v216" = %"pr.6" +p #1;
    %"v217" : P = Copy $"_nl_C_locobj";
    %"v218" = %"v217" +p #104;
    %"chk26" : A = (Check 0 8 Read 8) %"v218";
    %"v219" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 1 Read 1) %"v216";
    %"v221" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v222" : L = (Ext Sw) %"v221";
    %"v223" : L = Shl %"v222", #1;
    %"v224" = %"v219" +p %"v223";
    %"chk28" : A = (Check 0 2 Read 1) %"v224";
    %"v225" : W = (RawLoad (LdNarrow Uh) 0) %"chk28";
    %"v226" : W = And %"v225", #8192
    => br %"v226" ? poll "L212" : "L228";
  @"L228" [%"pr.11" : P = phi("L229" => %"v250", "L212" => %"v211"); %"pr.7" : P = phi("L229" => %"v252", "L212" => %"v216")]:
    %"chk29" : A = (Check 0 1 Read 1) %"pr.7";
    %"v232" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"v233" : W = (Cmp Ne W) %"v232", #0
    => br %"v233" ? "L234" : "L235";
  @"L234":
    %"v236" : P = Copy $"_nl_C_locobj";
    %"v237" = %"v236" +p #104;
    %"chk30" : A = (Check 0 8 Read 8) %"v237";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"chk31" : A = (Renew 0 1 Read 1) %"chk29", %"pr.7";
    %"v240" : W = (RawLoad (LdNarrow Sb) 0) %"chk31";
    %"v241" : L = (Ext Sw) %"v240";
    %"v242" : L = Shl %"v241", #1;
    %"v243" = %"v238" +p %"v242";
    %"chk32" : A = (Check 0 2 Read 1) %"v243";
    %"v244" : W = (RawLoad (LdNarrow Uh) 0) %"chk32";
    %"v245" : W = And %"v244", #8192;
    %"v246" : W = (Cmp Eq W) %"v245", #0
    => goto "L235";
  @"L235" [%"v248" : W = phi("L228" => #0, "L234" => %"v246")]:
    => br %"v248" ? "L229" : "L230";
  @"L229":
    %"v250" = %"pr.11" +p #1;
    %"v252" = %"pr.7" +p #1;
    %"chk33" : A = (Renew 0 1 Read 1) %"chk29", %"pr.7";
    %"v253" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"chk34" : A = (Check 0 1 Write 1) %"pr.11";
    store Wb [%"chk34" + 0] <- %"v253"
    => goto poll "L228";
  @"L230":
    %"chk35" : A = (Renew 0 1 Read 1) %"chk29", %"pr.7";
    %"v258" : W = (RawLoad (LdNarrow Sb) 0) %"chk35";
    %"v259" : W = (Cmp Eq W) %"v258", #0
    => br %"v259" ? "L254" : "L255";
  @"L254":
    %"v261" = %"pr.11" +p #1;
    %"chk36" : A = (Check 0 1 Write 1) %"pr.11";
    store Wb [%"chk36" + 0] <- #0
    => goto "L256";
  @"L255":
    %"v264" = %"pr.11" +p #1;
    %"chk37" : A = (Check 0 1 Write 1) %"pr.11";
    store Wb [%"chk37" + 0] <- #0;
    call %"v266" : L = $"__GI___isoc23_strtol"(P %"pr.7", P %"v262", W #10);
    %"chk38" : A = (Check 0 8 Read 8) %"v262";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v272" : L = Ptoi %"pr.7";
    %"v273" : L = Ptoi %"v271";
    %"v274" : W = (Cmp Eq L) %"v272", %"v273"
    => br %"v274" ? "L276" : "L275";
  @"L275":
    %"v277" : W = Copy %"v266";
    %"v278" : W = (Cmp Slt W) %"v277", #1
    => goto "L276";
  @"L276" [%"v280" : W = phi("L255" => #1, "L275" => %"v278")]:
    => br %"v280" ? "L256" : "L268";
  @"L268":
    => goto "L256";
  @"L256" [%"pr.14" : W = phi("L254" => #1, "L268" => %"v266", "L276" => #1); %"pr.12" : P = phi("L254" => %"v261", "L268" => %"v264", "L276" => %"v264")]:
    %"chk39" : A = (HalfCheck Upper 0 1 Read 1) %"chk25", %"v211";
    %"v286" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    %"v287" : W = (Cmp Eq W) %"v286", #0
    => br %"v287" ? "L281" : "L283";
  @"L281":
    => ret void;
  @"L283":
    %"v294" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    %"v295" : W = (Cmp Eq W) %"v294", #47
    => br %"v295" ? "L291" : "L290";
  @"L290":
    => goto "L291";
  @"L291" [%"pr.9" : L = phi("L290" => %"v4", "L283" => #0)]:
    %"v301" : L = Ptoi %"pr.12";
    %"v302" : L = Ptoi %"v211";
    %"v303" : L = Sub %"v301", %"v302";
    %"v304" : W = (Cmp Slt L) %"v303", #4
    => br %"v304" ? "L306" : "L305";
  @"L305":
    (Flight (a "v308") Sub [(FAddress (t "pr.12")); (FValue (Const 4))] (LowerOf (t "pr.12")));
    %"v309" : P = Copy $"glibc_gconv_conf#gconv_module_ext";
    call %"v310" : W = $"__GI_memcmp"(P %"v308", P %"v309", L #4);
    %"v311" : W = (Cmp Ne W) %"v310", #0
    => goto "L306";
  @"L306" [%"v313" : W = phi("L291" => #1, "L305" => %"v311")]:
    => br %"v313" ? "L298" : "L297";
  @"L297":
    => goto "L298";
  @"L298" [%"pr.13" : W = phi("L297" => #0, "L306" => #3)]:
    %"v321" : L = Ptoi %"v112";
    %"v322" : L = Ptoi %"pr.5";
    %"v323" : L = Sub %"v321", %"v322";
    call %"v324" : L = $"__GI___strnlen"(P %"pr.5", L %"v323");
    %"v327" : L = Add %"v324", #1;
    %"v328" : P = (Alloc 16) %"v327";
    %"v331" = %"v328" +p %"v324";
    %"chk41" : A = (Check 0 1 Write 1) %"v331";
    store Wb [%"chk41" + 0] <- #0;
    call %"v335" : P = $"__GI_memcpy"(P %"v328", P %"pr.5", L %"v324");
    %"chk42" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk42" + 0] <- %"v335";
    %"v339" : P = Copy $"__gconv_alias_db";
    %"v340" : P = Copy $"__gconv_alias_compare";
    call %"v341" : P = $"__GI___tfind"(P %"v8", P %"v339", P %"v340");
    %"v342" : L = Ptoi %"v341";
    %"v343" : L = Ptoi #0;
    %"v344" : W = (Cmp Ne L) %"v342", %"v343"
    => br %"v344" ? "L336" : "L338";
  @"L336":
    => ret void;
  @"L338":
    %"v350" : L = Sub %"v301", %"v322";
    %"v351" : L = Add %"v350", #56;
    %"v353" : L = Add %"v351", %"pr.9";
    %"v355" : L = (Ext Sw) %"pr.13";
    %"v356" : L = Add %"v353", %"v355";
    call %"v357" : P = $"calloc"(L #1, L %"v356");
    %"v362" : L = Ptoi %"v357";
    %"v364" : W = (Cmp Ne L) %"v362", %"v343"
    => br %"v364" ? "L358" : "L360";
  @"L358":
    %"v368" = %"v357" +p #56;
    %"chk43" : A = (Check 0 8 Write 8) %"v357";
    store.ptr [%"chk43" + 0] <- %"v368";
    call %"v376" : P = $"__GI_mempcpy"(P %"v368", P %"pr.5", L %"v323");
    %"v378" = %"v357" +p #8;
    %"chk44" : A = (HalfCheck Upper 0 8 Write 8) %"chk43", %"v378";
    store.ptr [%"chk44" + 0] <- %"v376";
    %"v386" : L = Sub %"v302", %"v321";
    call %"v387" : P = $"__GI_mempcpy"(P %"v376", P %"v112", L %"v386");
    %"v389" = %"v357" +p #16;
    %"chk45" : A = (HalfCheck Upper 0 4 Write 1) %"chk43", %"v389";
    store Ww [%"chk45" + 0] <- %"pr.14";
    %"v392" = %"v357" +p #20;
    %"chk46" : A = (HalfCheck Upper 0 4 Write 1) %"chk43", %"v392";
    store Ww [%"chk46" + 0] <- %"v6";
    %"v395" = %"v357" +p #24;
    %"chk47" : A = (HalfCheck Upper 0 8 Write 8) %"chk43", %"v395";
    store.ptr [%"chk47" + 0] <- %"v387";
    %"v401" : W = (Cmp Ne L) %"pr.9", #0
    => br %"v401" ? "L397" : "L399";
  @"L397":
    call %"v405" : P = $"__GI_mempcpy"(P %"v387", P %"v2", L %"pr.9")
    => goto "L399";
  @"L399" [%"pr.20" : P = phi("L397" => %"v405", "L358" => %"v387")]:
    call %"v413" : P = $"__GI_mempcpy"(P %"pr.20", P %"v211", L %"v303")
    => br %"pr.13" ? "L414" : "iw_1.start";
  @"L414":
    (Flight (a "v419") Sub [(FAddress (t "v413")); (FValue (Const 1))] (LowerOf (t "v413")));
    %"v420" : P = Copy $"glibc_gconv_conf#gconv_module_ext";
    call %"v421" : P = $"__GI_memcpy"(P %"v419", P %"v420", L #4)
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v5" : P = Copy $"__gconv_modules_db"
    => goto "iw_1.L6";
  @"iw_1.L6" [%"iw_1.pr.4" : P = phi("iw_1.start" => %"iw_1.v5", "iw_1.L125" => %"iw_1.v131", "iw_1.L126" => %"iw_1.v133")]:
    %"chk48" : A = (Check 0 8 Read 8) %"iw_1.pr.4";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"iw_1.v11" : L = Ptoi %"iw_1.v10";
    %"iw_1.v13" : W = (Cmp Ne L) %"iw_1.v11", %"v343"
    => br %"iw_1.v13" ? "iw_1.L7" : "iw_1.L8";
  @"iw_1.L7":
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"chk50" : A = (Renew 0 8 Read 8) %"chk43", %"v357";
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : A = (Check 0 8 Read 8) %"iw_1.v16";
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk51";
    call %"iw_1.v22" : W = $"__GI_strcmp"(P %"iw_1.v19", P %"iw_1.v21");
    %"iw_1.v27" : W = (Cmp Eq W) %"iw_1.v22", #0
    => br %"iw_1.v27" ? "iw_1.L28" : "iw_1.L24";
  @"iw_1.L28" [%"iw_1.pr.6" : P = phi("iw_1.L7" => %"iw_1.v16", "iw_1.L29" => %"iw_1.v52"); %"iw_1.pr.2" : P = phi("iw_1.L7" => %"iw_1.pr.4", "iw_1.L29" => %"iw_1.v50")]:
    %"chk52" : A = (Renew 0 8 Read 8) %"chk43", %"v357";
    %"iw_1.v32" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"chk53" : A = (Check 0 8 Read 8) %"iw_1.pr.6";
    %"iw_1.v34" : P = (RawLoadPointer 0 load_effects) %"chk53";
    call %"iw_1.v35" : W = $"__GI_strcmp"(P %"iw_1.v32", P %"iw_1.v34");
    %"iw_1.v36" : W = (Cmp Ne W) %"iw_1.v35", #0
    => br %"iw_1.v36" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v40" = %"v357" +p #8;
    %"chk54" : A = (Renew 0 8 Read 8) %"chk44", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"iw_1.v43" = %"iw_1.pr.6" +p #8;
    %"chk55" : A = (HalfCheck Upper 0 8 Read 8) %"chk53", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk55";
    call %"iw_1.v45" : W = $"__GI_strcmp"(P %"iw_1.v41", P %"iw_1.v44");
    %"iw_1.v46" : W = (Cmp Ne W) %"iw_1.v45", #0
    => goto "iw_1.L38";
  @"iw_1.L38" [%"iw_1.v48" : W = phi("iw_1.L28" => #1, "iw_1.L37" => %"iw_1.v46")]:
    => br %"iw_1.v48" ? "iw_1.L29" : "iw_1.L30";
  @"iw_1.L29":
    %"iw_1.v50" = %"iw_1.pr.6" +p #40;
    %"chk56" : A = (HalfCheck Upper 0 8 Read 8) %"chk53", %"iw_1.v50";
    %"iw_1.v52" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"iw_1.v57" : L = Ptoi %"iw_1.v52";
    %"iw_1.v59" : W = (Cmp Eq L) %"iw_1.v57", %"v343"
    => br %"iw_1.v59" ? "iw_1.L30" : poll "iw_1.L28";
  @"iw_1.L30" [%"iw_1.pr.7" : P = phi("iw_1.L38" => %"iw_1.pr.6", "iw_1.L29" => %"iw_1.v52"); %"iw_1.pr.3" : P = phi("iw_1.L38" => %"iw_1.pr.2", "iw_1.L29" => %"iw_1.v50")]:
    %"iw_1.v65" : L = Ptoi %"iw_1.pr.7";
    %"iw_1.v67" : W = (Cmp Ne L) %"iw_1.v65", %"v343"
    => br %"iw_1.v67" ? "iw_1.L61" : "iw_1.L8";
  @"iw_1.L61":
    %"iw_1.v72" = %"v357" +p #16;
    %"chk57" : A = (Renew 0 4 Read 1) %"chk45", %"iw_1.v72";
    %"iw_1.v73" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"iw_1.v75" = %"iw_1.pr.7" +p #16;
    %"chk58" : A = (Check 0 4 Read 1) %"iw_1.v75";
    %"iw_1.v76" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"iw_1.v77" : W = (Cmp Slt W) %"iw_1.v73", %"iw_1.v76"
    => br %"iw_1.v77" ? "iw_1.L79" : "iw_1.L78";
  @"iw_1.L78":
    %"iw_1.v81" = %"v357" +p #16;
    %"iw_1.v82" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"iw_1.v84" = %"iw_1.pr.7" +p #16;
    %"iw_1.v85" : W = (RawLoad (LdNarrow Sw) 0) %"chk58";
    %"iw_1.v86" : W = (Cmp Eq W) %"iw_1.v82", %"iw_1.v85"
    => br %"iw_1.v86" ? "iw_1.L87" : "iw_1.L79";
  @"iw_1.L87":
    %"iw_1.v90" = %"v357" +p #20;
    %"chk61" : A = (Renew 0 4 Read 1) %"chk46", %"iw_1.v90";
    %"iw_1.v91" : W = (RawLoad (LdNarrow Sw) 0) %"chk61";
    %"iw_1.v93" = %"iw_1.pr.7" +p #20;
    %"chk62" : A = (HalfCheck Upper 0 4 Read 1) %"chk58", %"iw_1.v93";
    %"iw_1.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"iw_1.v95" : W = (Cmp Slt W) %"iw_1.v91", %"iw_1.v94"
    => goto "iw_1.L79";
  @"iw_1.L79" [%"iw_1.v99" : W = phi("iw_1.L61" => #1, "iw_1.L78" => #0, "iw_1.L87" => %"iw_1.v95")]:
    => br %"iw_1.v99" ? "iw_1.L68" : "iw_1.L118";
  @"iw_1.L68":
    %"iw_1.v101" = %"v357" +p #32;
    %"iw_1.v103" = %"iw_1.pr.7" +p #32;
    %"chk63" : A = (HalfCheck Upper 0 8 Read 8) %"chk58", %"iw_1.v103";
    %"iw_1.v104" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (HalfCheck Upper 0 8 Write 8) %"chk43", %"iw_1.v101";
    store.ptr [%"chk64" + 0] <- %"iw_1.v104";
    %"iw_1.v106" = %"v357" +p #48;
    %"iw_1.v108" = %"iw_1.pr.7" +p #48;
    %"chk65" : A = (HalfCheck Upper 0 8 Read 8) %"chk58", %"iw_1.v108";
    %"iw_1.v109" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (HalfCheck Upper 0 8 Write 8) %"chk43", %"iw_1.v106";
    store.ptr [%"chk66" + 0] <- %"iw_1.v109";
    %"iw_1.v111" = %"v357" +p #40;
    %"iw_1.v113" = %"iw_1.pr.7" +p #40;
    %"chk67" : A = (HalfCheck Upper 0 8 Read 8) %"chk58", %"iw_1.v113";
    %"iw_1.v114" : P = (RawLoadPointer 0 load_effects) %"chk67";
    %"chk68" : A = (HalfCheck Upper 0 8 Write 8) %"chk43", %"iw_1.v111";
    store.ptr [%"chk68" + 0] <- %"iw_1.v114";
    %"chk69" : A = (Check 0 8 Write 8) %"iw_1.pr.3";
    store.ptr [%"chk69" + 0] <- %"v357";
    call void $"free"(P %"iw_1.pr.7")
    => goto "L360";
  @"iw_1.L118":
    call void $"free"(P %"v357")
    => goto "L360";
  @"iw_1.L24":
    %"iw_1.v129" : W = (Cmp Slt W) %"iw_1.v22", #0
    => br %"iw_1.v129" ? "iw_1.L125" : "iw_1.L126";
  @"iw_1.L125":
    %"iw_1.v131" = %"iw_1.v16" +p #32
    => goto poll "iw_1.L6";
  @"iw_1.L126":
    %"iw_1.v133" = %"iw_1.v16" +p #48
    => goto poll "iw_1.L6";
  @"iw_1.L8" [%"iw_1.pr.5" : P = phi("iw_1.L6" => %"iw_1.pr.4", "iw_1.L30" => %"iw_1.pr.3")]:
    %"chk70" : A = (Check 0 8 Write 8) %"iw_1.pr.5";
    store.ptr [%"chk70" + 0] <- %"v357"
    => goto "L360";
  @"L360":
    => ret void
} }.
