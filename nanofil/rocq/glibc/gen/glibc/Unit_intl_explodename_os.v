(** This file defines checked IR from glibc’s `intl/explodename.os` object.
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

Definition fn__nl_explode_name : func :=
  ir_fn{ "export" "_nl_explode_name"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", P %"v10") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk1" + 0] <- #0;
    %"chk2" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk2" + 0] <- #0;
    %"chk3" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk4" + 0] <- %"v0";
    %"chk5" : A = (Renew 0 8 Read 8) %"chk4", %"v2";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto "iw_1.L2";
  @"iw_1.L2" [%"iw_1.pr.1" : P = phi("iw_1.L3" => %"iw_1.v34", "start" => %"v21")]:
    %"chk6" : A = (Check 0 1 Read 1) %"iw_1.pr.1";
    %"iw_1.v7" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v8" : W = (Cmp Ne W) %"iw_1.v7", #0
    => br %"iw_1.v8" ? "iw_1.L9" : "iw_1.L10";
  @"iw_1.L9":
    %"iw_1.v13" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v14" : W = (Cmp Ne W) %"iw_1.v13", #95
    => goto "iw_1.L10";
  @"iw_1.L10" [%"iw_1.v16" : W = phi("iw_1.L2" => #0, "iw_1.L9" => %"iw_1.v14")]:
    => br %"iw_1.v16" ? "iw_1.L17" : "iw_1.L18";
  @"iw_1.L17":
    %"iw_1.v21" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v22" : W = (Cmp Ne W) %"iw_1.v21", #64
    => goto "iw_1.L18";
  @"iw_1.L18" [%"iw_1.v24" : W = phi("iw_1.L10" => #0, "iw_1.L17" => %"iw_1.v22")]:
    => br %"iw_1.v24" ? "iw_1.L25" : "iw_1.L26";
  @"iw_1.L25":
    %"iw_1.v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"iw_1.v30" : W = (Cmp Ne W) %"iw_1.v29", #46
    => goto "iw_1.L26";
  @"iw_1.L26" [%"iw_1.v32" : W = phi("iw_1.L18" => #0, "iw_1.L25" => %"iw_1.v30")]:
    => br %"iw_1.v32" ? "iw_1.L3" : "iw_1.join";
  @"iw_1.L3":
    %"iw_1.v34" = %"iw_1.pr.1" +p #1
    => goto poll "iw_1.L2";
  @"iw_1.join":
    %"chk10" : A = (Renew 0 8 Read 8) %"chk4", %"v2";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Ptoi %"iw_1.pr.1";
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => br %"v31" ? "L23" : "L24";
  @"L23":
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk10";
    call %"v34" : P = $"__GI_strchr"(P %"v33", W #0)
    => goto "L25";
  @"L24":
    %"v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v41" : W = (Cmp Eq W) %"v40", #95
    => br %"v41" ? "L35" : "L37";
  @"L35":
    %"chk13" : A = (Renew 0 1 Write 1) %"chk6", %"iw_1.pr.1";
    store Wb [%"chk13" + 0] <- #0;
    %"v46" = %"iw_1.pr.1" +p #1;
    %"chk14" : A = (Renew 0 8 Write 8) %"chk1", %"v6";
    store.ptr [%"chk14" + 0] <- %"v46"
    => goto "L47";
  @"L47" [%"pr.3" : P = phi("L35" => %"v46", "L48" => %"v71")]:
    %"chk15" : A = (Check 0 1 Read 1) %"pr.3";
    %"v52" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v53" : W = (Cmp Ne W) %"v52", #0
    => br %"v53" ? "L54" : "L55";
  @"L54":
    %"v58" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v59" : W = (Cmp Ne W) %"v58", #46
    => goto "L55";
  @"L55" [%"v61" : W = phi("L47" => #0, "L54" => %"v59")]:
    => br %"v61" ? "L62" : "L63";
  @"L62":
    %"v66" : W = (RawLoad (LdNarrow Sb) 0) %"chk15";
    %"v67" : W = (Cmp Ne W) %"v66", #64
    => goto "L63";
  @"L63" [%"v69" : W = phi("L55" => #0, "L62" => %"v67")]:
    => br %"v69" ? "L48" : "L37";
  @"L48":
    %"v71" = %"pr.3" +p #1
    => goto poll "L47";
  @"L37" [%"pr.13" : W = phi("L63" => #4, "L24" => #0); %"pr.2" : P = phi("L63" => %"pr.3", "L24" => %"iw_1.pr.1")]:
    %"chk18" : A = (Check 0 1 Read 1) %"pr.2";
    %"v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"v80" : W = (Cmp Eq W) %"v79", #46
    => br %"v80" ? "L74" : "L25";
  @"L74":
    %"chk19" : A = (Renew 0 1 Write 1) %"chk18", %"pr.2";
    store Wb [%"chk19" + 0] <- #0;
    %"v85" = %"pr.2" +p #1;
    %"chk20" : A = (Renew 0 8 Write 8) %"chk2", %"v8";
    store.ptr [%"chk20" + 0] <- %"v85"
    => goto "L86";
  @"L86" [%"pr.5" : P = phi("L74" => %"v85", "L87" => %"v102")]:
    %"chk21" : A = (Check 0 1 Read 1) %"pr.5";
    %"v91" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v92" : W = (Cmp Ne W) %"v91", #0
    => br %"v92" ? "L93" : "L94";
  @"L93":
    %"v97" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v98" : W = (Cmp Ne W) %"v97", #64
    => goto "L94";
  @"L94" [%"v100" : W = phi("L86" => #0, "L93" => %"v98")]:
    => br %"v100" ? "L87" : "L88";
  @"L87":
    %"v102" = %"pr.5" +p #1
    => goto poll "L86";
  @"L88":
    %"v104" : W = Or %"pr.13", #2;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v111" : L = Ptoi %"v109";
    %"v112" : L = Ptoi %"pr.5";
    %"v113" : W = (Cmp Ne L) %"v111", %"v112"
    => br %"v113" ? "L114" : "L115";
  @"L114":
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk25" : A = (Check 0 1 Read 1) %"v117";
    %"v119" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"v120" : W = (Cmp Ne W) %"v119", #0
    => goto "L115";
  @"L115" [%"v122" : W = phi("L88" => #0, "L114" => %"v120")]:
    => br %"v122" ? "L105" : "L25";
  @"L105":
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v130" : L = Ptoi %"v128";
    %"v131" : L = Sub %"v112", %"v130";
    call %"v132" : P = $"_nl_normalize_codeset"(P %"v125", L %"v131");
    %"chk28" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk28" + 0] <- %"v132";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v138" : L = Ptoi %"v137";
    %"v139" : L = Ptoi #0;
    %"v140" : W = (Cmp Eq L) %"v138", %"v139"
    => br %"v140" ? "L133" : "L134";
  @"L133":
    => ret #4294967295;
  @"L134":
    %"chk30" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v147" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk29";
    call %"v150" : W = $"__GI_strcmp"(P %"v147", P %"v149");
    %"v151" : W = (Cmp Eq W) %"v150", #0
    => br %"v151" ? "L143" : "L144";
  @"L143":
    %"chk32" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk32";
    call void $"free"(P %"v153")
    => goto "L145";
  @"L144":
    %"v155" : W = Or %"v104", #1
    => goto "L145";
  @"L145" [%"pr.7" : W = phi("L143" => %"v104", "L144" => %"v155")]:
    => goto "L25";
  @"L25" [%"pr.12" : W = phi("L23" => #0, "L145" => %"pr.7", "L115" => %"v104", "L37" => %"pr.13"); %"pr.1" : P = phi("L23" => %"v34", "L145" => %"pr.5", "L115" => %"pr.5", "L37" => %"pr.2")]:
    %"chk33" : A = (Check 0 1 Read 1) %"pr.1";
    %"v161" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v162" : W = (Cmp Eq W) %"v161", #64
    => br %"v162" ? "L156" : "L158";
  @"L156":
    %"chk34" : A = (Renew 0 1 Write 1) %"chk33", %"pr.1";
    store Wb [%"chk34" + 0] <- #0;
    %"v167" = %"pr.1" +p #1;
    %"chk35" : A = (Renew 0 8 Write 8) %"chk0", %"v4";
    store.ptr [%"chk35" + 0] <- %"v167";
    %"chk36" : A = (HalfCheck Upper 0 1 Read 1) %"chk33", %"v167";
    %"v173" : W = (RawLoad (LdNarrow Sb) 0) %"chk36";
    %"v174" : W = (Cmp Ne W) %"v173", #0
    => br %"v174" ? "L168" : "L158";
  @"L168":
    %"v176" : W = Or %"pr.12", #8
    => goto "L158";
  @"L158" [%"pr.8" : W = phi("L168" => %"v176", "L156" => %"pr.12", "L25" => %"pr.12")]:
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"v6";
    %"v181" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v182" : L = Ptoi %"v181";
    %"v183" : L = Ptoi #0;
    %"v184" : W = (Cmp Ne L) %"v182", %"v183"
    => br %"v184" ? "L185" : "L186";
  @"L185":
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"chk39" : A = (Check 0 1 Read 1) %"v188";
    %"v190" : W = (RawLoad (LdNarrow Sb) 0) %"chk39";
    %"v191" : W = (Cmp Eq W) %"v190", #0
    => goto "L186";
  @"L186" [%"v193" : W = phi("L158" => #0, "L185" => %"v191")]:
    => br %"v193" ? "L177" : "L179";
  @"L177":
    %"v196" : W = And %"pr.8", #4294967291
    => goto "L179";
  @"L179" [%"pr.10" : W = phi("L177" => %"v196", "L186" => %"pr.8")]:
    %"chk40" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v202" : L = Ptoi %"v201";
    %"v204" : W = (Cmp Ne L) %"v202", %"v183"
    => br %"v204" ? "L205" : "L206";
  @"L205":
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk42" : A = (Check 0 1 Read 1) %"v208";
    %"v210" : W = (RawLoad (LdNarrow Sb) 0) %"chk42";
    %"v211" : W = (Cmp Eq W) %"v210", #0
    => goto "L206";
  @"L206" [%"v213" : W = phi("L179" => #0, "L205" => %"v211")]:
    => br %"v213" ? "L197" : "L199";
  @"L197":
    %"v216" : W = And %"pr.10", #4294967293
    => goto "L199";
  @"L199" [%"pr.11" : W = phi("L197" => %"v216", "L206" => %"pr.10")]:
    => ret %"pr.11"
} }.
