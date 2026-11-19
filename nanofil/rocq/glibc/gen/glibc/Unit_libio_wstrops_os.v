(** This file defines checked IR from glibc’s `libio/wstrops.os` object.
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

Definition fn__IO_wstr_count : func :=
  ir_fn{ "export" "_IO_wstr_count"(P %"v0") -> (RClass L) {
  @"start":
    %"v4" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v5" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" = %"v5" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v15" : L = Ptoi %"v11";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Ugt L) %"v15", %"v16"
    => br %"v17" ? "L6" : "L7";
  @"L6":
    %"v19" = %"v5" +p #32;
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => goto "L8";
  @"L7":
    %"v22" = %"v5" +p #8;
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "L8";
  @"L8" [%"v24" : P = phi("L6" => %"v20", "L7" => %"v23")]:
    %"v26" = %"v5" +p #16;
    %"v27" : P = (RawLoadPointer 8 load_effects) %"chk2";
    %"v28" : L = Ptoi %"v24";
    %"v29" : L = Ptoi %"v27";
    %"v30" : L = Sub %"v28", %"v29";
    %"v31" : L = Div %"v30", #4
    => ret %"v31"
} }.

Definition fn__IO_wstr_finish : func :=
  ir_fn{ "export" "_IO_wstr_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v10" = %"v9" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" : L = Ptoi %"v11";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L14" : "L15";
  @"L14":
    %"v17" = %"v0" +p #116;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v17";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v19" : W = Shl %"v18", #8;
    %"v20" : W = Sar %"v19", #8;
    %"v21" : W = And %"v20", #8;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => goto "L15";
  @"L15" [%"v24" : W = phi("start" => #0, "L14" => %"v22")]:
    => br %"v24" ? "L4" : "L6";
  @"L4":
    %"v26" = %"v0" +p #160;
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v28" = %"v27" +p #48;
    %"chk4" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk4";
    call void $"free"(P %"v29")
    => goto "L6";
  @"L6":
    %"v31" = %"v0" +p #160;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v33" = %"v32" +p #48;
    %"chk6" : A = (Check 0 8 Write 8) %"v33";
    store.ptr [%"chk6" + 0] <- #0;
    call void $"__GI__IO_wdefault_finish"(P %"v0", W #0)
    => ret void
} }.

Definition fn__IO_wstr_overflow : func :=
  ir_fn{ "export" "_IO_wstr_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v6" : W = (Cmp Eq W) %"v2", #4294967295;
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v12" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v13" : W = And %"v12", #8
    => br %"v13" ? "L8" : "L10";
  @"L8":
    => br %"v6" ? "L16" : "L15";
  @"L15":
    => goto "L16";
  @"L16" [%"v18" : W = phi("L15" => #4294967295, "L8" => #0)]:
    => ret %"v18";
  @"L10":
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v25" : W = And %"v24", #1024
    => br %"v25" ? "L26" : "L27";
  @"L26":
    %"v29" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v30" : W = And %"v29", #2048;
    %"v31" : W = (Cmp Eq W) %"v30", #0
    => goto "L27";
  @"L27" [%"v33" : W = phi("L10" => #0, "L26" => %"v31")]:
    => br %"v33" ? "L20" : "L22";
  @"L20":
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v36" : W = Or %"v35", #2048;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk4" + 0] <- %"v36";
    %"v38" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v40" = %"v39" +p #32;
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk7" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Write 8) %"v40";
    store.ptr [%"chk8" + 0] <- %"v44";
    %"chk9" : A = (Renew 0 8 Read 8) %"chk5", %"v38";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v51" = %"v50" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Write 8) %"v47";
    store.ptr [%"chk12" + 0] <- %"v52"
    => goto "L22";
  @"L22":
    %"v54" = %"v0" +p #160;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v56" = %"v55" +p #32;
    %"chk14" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v61" = %"v60" +p #24;
    %"chk16" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v63" : L = Ptoi %"v57";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Sub %"v63", %"v64";
    %"v66" : L = Div %"v65", #4;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v74" = %"v73" +p #56;
    %"chk18" : A = (Check 0 8 Read 8) %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v79" = %"v78" +p #48;
    %"chk20" : A = (Check 0 8 Read 8) %"v79";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v81" : L = Ptoi %"v75";
    %"v82" : L = Ptoi %"v80";
    %"v83" : L = Sub %"v81", %"v82";
    %"v84" : L = Div %"v83", #4;
    %"v86" : L = (Ext Sw) %"v6";
    %"v87" : L = Add %"v84", %"v86";
    %"v88" : W = (Cmp Uge L) %"v66", %"v87"
    => br %"v88" ? "L67" : "L69";
  @"L67":
    %"v93" = %"v0" +p #116;
    %"chk21" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v93";
    %"v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"v95" : W = Shl %"v94", #8;
    %"v96" : W = Sar %"v95", #8;
    %"v97" : W = And %"v96", #8
    => br %"v97" ? "L89" : "L90";
  @"L89":
    => ret #4294967295;
  @"L90":
    %"v102" = %"v0" +p #160;
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v104" = %"v103" +p #48;
    %"chk23" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v110" = %"v109" +p #56;
    %"chk25" : A = (Check 0 8 Read 8) %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v115" = %"v114" +p #48;
    %"chk27" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v117" : L = Ptoi %"v111";
    %"v118" : L = Ptoi %"v116";
    %"v119" : L = Sub %"v117", %"v118";
    %"v120" : L = Div %"v119", #4;
    %"v123" : L = Shl %"v120", #1;
    %"v124" : L = Add %"v123", #100;
    %"v130" : W = (Cmp Ult L) %"v124", %"v120"
    => br %"v130" ? "L134" : "L133";
  @"L133":
    %"v137" : W = (Cmp Ugt L) %"v124", #4611686018427387903
    => goto "L134";
  @"L134" [%"v141" : W = phi("L90" => #1, "L133" => %"v137")]:
    => br %"v141" ? "L125" : "L127";
  @"L125":
    => ret #4294967295;
  @"L127":
    %"v145" : L = Shl %"v124", #2;
    call %"v146" : P = $"malloc"(L %"v145");
    %"v151" : L = Ptoi %"v146";
    %"v152" : L = Ptoi #0;
    %"v153" : W = (Cmp Eq L) %"v151", %"v152"
    => br %"v153" ? "L147" : "L149";
  @"L147":
    => ret #4294967295;
  @"L149":
    %"v159" : L = Ptoi %"v105";
    %"v160" : W = (Cmp Ne L) %"v159", #0
    => br %"v160" ? "L155" : "L157";
  @"L155":
    call %"v164" : P = $"__wmemcpy"(P %"v146", P %"v105", L %"v120");
    call void $"free"(P %"v105");
    %"v167" = %"v0" +p #160;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk13", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v169" = %"v168" +p #48;
    %"chk29" : A = (Check 0 8 Write 8) %"v169";
    store.ptr [%"chk29" + 0] <- #0
    => goto "L157";
  @"L157":
    code ((app ir[ %"v172" : L = Shl %"v120", #2;
      %"v173" = %"v146" +p %"v172";
      %"v176" : L = Sub %"v124", %"v120";
      call %"v177" : P = $"__GI___wmemset"(P %"v173", W #0, L %"v176");
      %"v183" = %"v146" +p %"v145";
      call void $"__GI__IO_wsetb"(P %"v0", P %"v146", P %"v183", W #1);
      %"v185" = %"v0" +p #160;
      %"chk30" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v186" : P = (RawLoadPointer 0 load_effects) %"chk30";
      %"v187" = %"v186" +p #16;
      %"v191" : P = (RawLoadPointer 0 load_effects) %"chk30";
      %"v192" = %"v191" +p #16;
      %"chk32" : A = (Check 0 8 Read 8) %"v192";
      %"v193" : P = (RawLoadPointer 0 load_effects) %"chk32";
      %"v195" : L = Ptoi %"v193";
      %"v197" : L = Sub %"v195", %"v159";
      %"v198" : L = Div %"v197", #4;
      %"v199" : L = Shl %"v198", #2;
      %"v200" = %"v146" +p %"v199";
      %"chk33" : A = (Check 0 8 Write 8) %"v187";
      store.ptr [%"chk33" + 0] <- %"v200";
      %"chk34" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v203" : P = (RawLoadPointer 0 load_effects) %"chk34";
      %"v207" : P = (RawLoadPointer 0 load_effects) %"chk34";
      %"chk36" : A = (Check 0 8 Read 8) %"v207";
      %"v208" : P = (RawLoadPointer 0 load_effects) %"chk36";
      %"v210" : L = Ptoi %"v208";
      %"v212" : L = Sub %"v210", %"v159";
      %"v213" : L = Div %"v212", #4;
      %"v214" : L = Shl %"v213", #2;
      %"v215" = %"v146" +p %"v214";
      %"chk37" : A = (Check 0 8 Write 8) %"v203";
      store.ptr [%"chk37" + 0] <- %"v215";
      %"chk38" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v218" : P = (RawLoadPointer 0 load_effects) %"chk38";
      %"v219" = %"v218" +p #8;
      %"v223" : P = (RawLoadPointer 0 load_effects) %"chk38"] ir[ %"v224" = %"v223" +p #8;
      %"chk40" : A = (Check 0 8 Read 8) %"v224";
      %"v225" : P = (RawLoadPointer 0 load_effects) %"chk40";
      %"v227" : L = Ptoi %"v225";
      %"v229" : L = Sub %"v227", %"v159";
      %"v230" : L = Div %"v229", #4;
      %"v231" : L = Shl %"v230", #2;
      %"v232" = %"v146" +p %"v231";
      %"chk41" : A = (Check 0 8 Write 8) %"v219";
      store.ptr [%"chk41" + 0] <- %"v232";
      %"chk42" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v235" : P = (RawLoadPointer 0 load_effects) %"chk42";
      %"v236" = %"v235" +p #32;
      %"v240" : P = (RawLoadPointer 0 load_effects) %"chk42";
      %"v241" = %"v240" +p #32;
      %"chk44" : A = (Check 0 8 Read 8) %"v241";
      %"v242" : P = (RawLoadPointer 0 load_effects) %"chk44";
      %"v244" : L = Ptoi %"v242";
      %"v246" : L = Sub %"v244", %"v159";
      %"v247" : L = Div %"v246", #4;
      %"v248" : L = Shl %"v247", #2;
      %"v249" = %"v146" +p %"v248";
      %"chk45" : A = (Check 0 8 Write 8) %"v236";
      store.ptr [%"chk45" + 0] <- %"v249";
      %"chk46" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v252" : P = (RawLoadPointer 0 load_effects) %"chk46";
      %"v253" = %"v252" +p #24;
      %"chk47" : A = (Check 0 8 Write 8) %"v253";
      store.ptr [%"chk47" + 0] <- %"v146";
      %"chk48" : A = (Renew 0 8 Read 8) %"chk13", %"v185";
      %"v257" : P = (RawLoadPointer 0 load_effects) %"chk48";
      %"v258" = %"v257" +p #40;
      %"v261" : P = (RawLoadPointer 0 load_effects) %"chk48";
      %"v262" = %"v261" +p #56;
      %"chk50" : A = (Check 0 8 Read 8) %"v262";
      %"v263" : P = (RawLoadPointer 0 load_effects) %"chk50";
      %"chk51" : A = (Check 0 8 Write 8) %"v258";
      store.ptr [%"chk51" + 0] <- %"v263"]))
    => goto "L69";
  @"L69":
    %"v268" : W = (Cmp Ne W) %"v2", #4294967295
    => br %"v268" ? "L264" : "L266";
  @"L264":
    %"v270" = %"v0" +p #160;
    %"chk52" : A = (Renew 0 8 Read 8) %"chk13", %"v270";
    %"v271" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v272" = %"v271" +p #32;
    %"chk53" : A = (Check 0 8 Read 8) %"v272";
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v274" = %"v273" +p #4;
    %"chk54" : A = (Renew 0 8 Write 8) %"chk53", %"v272";
    store.ptr [%"chk54" + 0] <- %"v274";
    %"chk55" : A = (Check 0 4 Write 1) %"v273";
    store Ww [%"chk55" + 0] <- %"v2"
    => goto "L266";
  @"L266":
    %"v280" = %"v0" +p #160;
    %"chk56" : A = (Renew 0 8 Read 8) %"chk13", %"v280";
    %"v281" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v282" = %"v281" +p #32;
    %"chk57" : A = (Check 0 8 Read 8) %"v282";
    %"v283" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"v286" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v287" = %"v286" +p #8;
    %"chk59" : A = (Check 0 8 Read 8) %"v287";
    %"v288" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"v289" : L = Ptoi %"v283";
    %"v290" : L = Ptoi %"v288";
    %"v291" : W = (Cmp Ugt L) %"v289", %"v290"
    => br %"v291" ? "L276" : "L278";
  @"L276":
    %"v293" = %"v0" +p #160;
    %"v294" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v295" = %"v294" +p #8;
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v299" = %"v298" +p #32;
    %"chk62" : A = (Check 0 8 Read 8) %"v299";
    %"v300" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (Check 0 8 Write 8) %"v295";
    store.ptr [%"chk63" + 0] <- %"v300"
    => goto "L278";
  @"L278":
    => br %"v6" ? "L301" : "L302";
  @"L301":
    => ret #0;
  @"L302":
    => ret %"v2"
} }.

Definition fn__IO_wstr_pbackfail : func :=
  ir_fn{ "export" "_IO_wstr_pbackfail"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L10" : "L11";
  @"L10":
    %"v13" : W = (Cmp Ne W) %"v2", #4294967295
    => goto "L11";
  @"L11" [%"v15" : W = phi("start" => #0, "L10" => %"v13")]:
    => br %"v15" ? "L4" : "L6";
  @"L4":
    => ret #4294967295;
  @"L6":
    call %"v19" : W = $"__GI__IO_wdefault_pbackfail"(P %"v0", W %"v2")
    => ret %"v19"
} }.

Definition fn__IO_wstr_seekoff : func :=
  ir_fn{ "export" "_IO_wstr_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v13" : W = (Cmp Eq W) %"v6", #0
    => br %"v13" ? "L14" : "L15";
  @"L14":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v18" : W = And %"v17", #1024;
    %"v19" : W = (Cmp Ne W) %"v18", #0
    => goto "L15";
  @"L15" [%"v20" : W = phi("start" => #0, "L14" => %"v19")]:
    => br %"v20" ? "L9" : "L11";
  @"L9":
    %"chk1" : A = (Check 0 4 Read 1) %"v0";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v26" : W = And %"v25", #2048
    => br %"v26" ? "L11" : "L22";
  @"L22":
    => goto "L11";
  @"L11" [%"pr.1" : W = phi("L22" => #1, "L9" => #2, "L15" => %"v6")]:
    %"v30" = %"v0" +p #160;
    %"chk2" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v32" = %"v31" +p #32;
    %"chk3" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v37" = %"v36" +p #24;
    %"chk5" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v39" : L = Ptoi %"v33";
    %"v40" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Ugt L) %"v39", %"v40"
    => br %"v41" ? "L43" : "L42";
  @"L42":
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v0";
    %"v45" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"v46" : W = And %"v45", #2048;
    %"v47" : W = (Cmp Ne W) %"v46", #0
    => goto "L43";
  @"L43" [%"v48" : W = phi("L11" => #1, "L42" => %"v47")]:
    => br %"v48" ? "iw_1.start" : "L52";
  @"iw_1.start":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk2", %"v0";
    %"iw_1.v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"iw_1.v7" : W = And %"iw_1.v6", #256
    => br %"iw_1.v7" ? "iw_1.L2" : "iw_1.L3";
  @"iw_1.L2":
    %"iw_1.v9" = %"v0" +p #160;
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v11" = %"iw_1.v10" +p #16;
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v15" = %"iw_1.v14" +p #72;
    %"chk10" : A = (Check 0 8 Read 8) %"iw_1.v15";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"iw_1.v11";
    store.ptr [%"chk11" + 0] <- %"iw_1.v16"
    => goto "iw_1.L4";
  @"iw_1.L3":
    %"iw_1.v18" = %"v0" +p #160;
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v20" = %"iw_1.v19" +p #16;
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v24" = %"iw_1.v23" +p #48;
    %"chk14" : A = (Check 0 8 Read 8) %"iw_1.v24";
    %"iw_1.v25" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"iw_1.v20";
    store.ptr [%"chk15" + 0] <- %"iw_1.v25";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v18";
    %"iw_1.v31" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v32" = %"iw_1.v31" +p #32;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v32";
    %"iw_1.v33" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v36" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v37" = %"iw_1.v36" +p #8;
    %"chk19" : A = (Check 0 8 Read 8) %"iw_1.v37";
    %"iw_1.v38" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_1.v39" : L = Ptoi %"iw_1.v33";
    %"iw_1.v40" : L = Ptoi %"iw_1.v38";
    %"iw_1.v41" : W = (Cmp Ugt L) %"iw_1.v39", %"iw_1.v40"
    => br %"iw_1.v41" ? "iw_1.L26" : "iw_1.L4";
  @"iw_1.L26":
    %"iw_1.v43" = %"v0" +p #160;
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v45" = %"iw_1.v44" +p #8;
    %"iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.v49" = %"iw_1.v48" +p #32;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v49";
    %"iw_1.v50" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Check 0 8 Write 8) %"iw_1.v45";
    store.ptr [%"chk23" + 0] <- %"iw_1.v50"
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v52" = %"v0" +p #160;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v52";
    %"iw_1.v53" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v56" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v57" = %"iw_1.v56" +p #32;
    %"chk26" : A = (Check 0 8 Read 8) %"iw_1.v57";
    %"iw_1.v58" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 8 Write 8) %"iw_1.v53";
    store.ptr [%"chk27" + 0] <- %"iw_1.v58";
    %"chk28" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v52";
    %"iw_1.v61" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_1.v62" = %"iw_1.v61" +p #8;
    %"iw_1.v65" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_1.v66" = %"iw_1.v65" +p #32;
    %"chk30" : A = (Check 0 8 Read 8) %"iw_1.v66";
    %"iw_1.v67" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"chk31" : A = (Check 0 8 Write 8) %"iw_1.v62";
    store.ptr [%"chk31" + 0] <- %"iw_1.v67";
    %"chk32" : A = (Renew 0 4 Read 1) %"chk7", %"v0";
    %"iw_1.v69" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"iw_1.v71" : W = And %"iw_1.v69", #4294965247;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk7", %"v0";
    store Ww [%"chk33" + 0] <- %"iw_1.v71"
    => goto "L52";
  @"L52":
    %"v59" : W = (Cmp Eq W) %"pr.1", #0
    => br %"v59" ? "L55" : "L56";
  @"L55":
    %"v61" = %"v0" +p #160;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk2", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v63" = %"v62" +p #32;
    %"chk35" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v68" = %"v67" +p #24;
    %"chk37" : A = (Check 0 8 Read 8) %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v70" : L = Ptoi %"v64";
    %"v71" : L = Ptoi %"v69";
    %"v72" : L = Sub %"v70", %"v71";
    %"v73" : L = Div %"v72", #4
    => goto "L57";
  @"L56":
    call %"v76" : L = $"_IO_wstr_count"(P %"v0");
    %"v83" : W = And %"pr.1", #1
    => br %"v83" ? "L86" : "L81";
  @"L89":
    %"v91" = %"v0" +p #160;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk2", %"v91";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 8 Read 8) %"v92";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v97" = %"v96" +p #16;
    %"chk41" : A = (Check 0 8 Read 8) %"v97";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v99" : L = Ptoi %"v93";
    %"v100" : L = Ptoi %"v98";
    %"v101" : L = Sub %"v99", %"v100";
    %"v102" : L = Div %"v101", #4
    => goto "L87";
  @"L86":
    %"v106" : W = (Cmp Eq W) %"v4", #0
    => br %"v106" ? "L87" : "L107";
  @"L107":
    %"v108" : W = (Cmp Eq W) %"v4", #1
    => br %"v108" ? poll "L89" : "L87";
  @"L87" [%"pr.5" : L = phi("L89" => %"v102", "L86" => #0, "L107" => %"v76")]:
    %"v113" : L = Sub #2305843009213693951, %"pr.5";
    %"v119" : L = Neg %"pr.5";
    %"v120" : W = (Cmp Slt L) %"v2", %"v119"
    => br %"v120" ? "L122" : "L121";
  @"L121":
    %"v125" : W = (Cmp Sgt L) %"v2", %"v113"
    => goto "L122";
  @"L122" [%"v127" : W = phi("L87" => #1, "L121" => %"v125")]:
    => br %"v127" ? "L114" : "L116";
  @"L114":
    %"v128" : P = Copy $"__libc_errno";
    %"chk42" : A = (Check 0 4 Write 1) %"v128";
    store Ww [%"chk42" + 0] <- #22
    => ret #18446744073709551615;
  @"L116":
    %"v134" : L = Add %"pr.5", %"v2";
    %"v140" : W = (Cmp Sgt L) %"v134", %"v76"
    => br %"v140" ? "L141" : "L142";
  @"L141":
    call %"v145" : W = $"glibc_wstrops#enlarge_userbuf"(P %"v0", L %"v134", W #1);
    %"v146" : W = (Cmp Ne W) %"v145", #0
    => goto "L142";
  @"L142" [%"v148" : W = phi("L116" => #0, "L141" => %"v146")]:
    => br %"v148" ? "L135" : "L137";
  @"L135":
    => ret #18446744073709551615;
  @"L137":
    %"v153" = %"v0" +p #160;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk2", %"v153";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v158" = %"v157" +p #16;
    %"chk45" : A = (Check 0 8 Read 8) %"v158";
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v161" : L = Shl %"v134", #2;
    %"v162" = %"v159" +p %"v161";
    %"chk46" : A = (Check 0 8 Write 8) %"v154";
    store.ptr [%"chk46" + 0] <- %"v162";
    %"chk47" : A = (Renew 0 8 Read 8) %"chk2", %"v153";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v166" = %"v165" +p #8;
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v170" = %"v169" +p #16;
    %"chk49" : A = (Check 0 8 Read 8) %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v173" : L = Shl %"v76", #2;
    %"v174" = %"v171" +p %"v173";
    %"chk50" : A = (Check 0 8 Write 8) %"v166";
    store.ptr [%"chk50" + 0] <- %"v174"
    => goto "L81";
  @"L81" [%"pr.4" : L = phi("L137" => %"v2", "L56" => #18446744073709551615)]:
    %"v180" : W = And %"pr.1", #2
    => br %"v180" ? "L183" : "L57";
  @"L186":
    %"v188" = %"v0" +p #160;
    %"chk51" : A = (Renew 0 8 Read 8) %"chk2", %"v188";
    %"v189" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v190" = %"v189" +p #32;
    %"chk52" : A = (Check 0 8 Read 8) %"v190";
    %"v191" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v195" = %"v194" +p #24;
    %"chk54" : A = (Check 0 8 Read 8) %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v197" : L = Ptoi %"v191";
    %"v198" : L = Ptoi %"v196";
    %"v199" : L = Sub %"v197", %"v198";
    %"v200" : L = Div %"v199", #4
    => goto "L184";
  @"L183":
    %"v204" : W = (Cmp Eq W) %"v4", #0
    => br %"v204" ? "L184" : "L205";
  @"L205":
    %"v206" : W = (Cmp Eq W) %"v4", #1
    => br %"v206" ? poll "L186" : "L184";
  @"L184" [%"pr.6" : L = phi("L186" => %"v200", "L183" => #0, "L205" => %"v76")]:
    %"v211" : L = Sub #2305843009213693951, %"pr.6";
    %"v217" : L = Neg %"pr.6";
    %"v218" : W = (Cmp Slt L) %"v2", %"v217"
    => br %"v218" ? "L220" : "L219";
  @"L219":
    %"v223" : W = (Cmp Sgt L) %"v2", %"v211"
    => goto "L220";
  @"L220" [%"v225" : W = phi("L184" => #1, "L219" => %"v223")]:
    => br %"v225" ? "L212" : "L214";
  @"L212":
    %"v226" : P = Copy $"__libc_errno";
    %"chk55" : A = (Check 0 4 Write 1) %"v226";
    store Ww [%"chk55" + 0] <- #22
    => ret #18446744073709551615;
  @"L214":
    %"v232" : L = Add %"pr.6", %"v2";
    %"v238" : W = (Cmp Sgt L) %"v232", %"v76"
    => br %"v238" ? "L239" : "L240";
  @"L239":
    call %"v243" : W = $"glibc_wstrops#enlarge_userbuf"(P %"v0", L %"v232", W #0);
    %"v244" : W = (Cmp Ne W) %"v243", #0
    => goto "L240";
  @"L240" [%"v246" : W = phi("L214" => #0, "L239" => %"v244")]:
    => br %"v246" ? "L233" : "L235";
  @"L233":
    => ret #18446744073709551615;
  @"L235":
    %"v251" = %"v0" +p #160;
    %"chk56" : A = (Renew 0 8 Read 8) %"chk2", %"v251";
    %"v252" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v253" = %"v252" +p #32;
    %"v256" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v257" = %"v256" +p #24;
    %"chk58" : A = (Check 0 8 Read 8) %"v257";
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v260" : L = Shl %"v232", #2;
    %"v261" = %"v258" +p %"v260";
    %"chk59" : A = (Check 0 8 Write 8) %"v253";
    store.ptr [%"chk59" + 0] <- %"v261"
    => goto "L57";
  @"L57" [%"pr.3" : L = phi("L55" => %"v73", "L235" => %"v232", "L81" => %"pr.4")]:
    => ret %"pr.3"
} }.

Definition fn__IO_wstr_underflow : func :=
  ir_fn{ "export" "_IO_wstr_underflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v7" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v15" : L = Ptoi %"v9";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Ugt L) %"v15", %"v16"
    => br %"v17" ? "L2" : "L4";
  @"L2":
    %"v19" = %"v0" +p #160;
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v21" = %"v20" +p #8;
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v25" = %"v24" +p #32;
    %"chk6" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v21";
    store.ptr [%"chk7" + 0] <- %"v26"
    => goto "L4";
  @"L4":
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v31" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v32" : W = And %"v31", #1024
    => br %"v32" ? "L33" : "L34";
  @"L33":
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v37" : W = And %"v36", #2048;
    %"v38" : W = (Cmp Ne W) %"v37", #0
    => goto "L34";
  @"L34" [%"v39" : W = phi("L4" => #0, "L33" => %"v38")]:
    => br %"v39" ? "L27" : "L29";
  @"L27":
    %"v41" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v43" : W = And %"v41", #4294965247;
    %"chk11" : A = (Renew 0 4 Write 1) %"chk8", %"v0";
    store Ww [%"chk11" + 0] <- %"v43";
    %"v45" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v50" = %"v49" +p #32;
    %"chk14" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v46";
    store.ptr [%"chk15" + 0] <- %"v51";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk0", %"v45";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v55" = %"v54" +p #32;
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v59" = %"v58" +p #40;
    %"chk18" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Check 0 8 Write 8) %"v55";
    store.ptr [%"chk19" + 0] <- %"v60"
    => goto "L29";
  @"L29":
    %"v65" = %"v0" +p #160;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk0", %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v71" = %"v70" +p #8;
    %"chk23" : A = (Check 0 8 Read 8) %"v71";
    %"v72" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v73" : L = Ptoi %"v67";
    %"v74" : L = Ptoi %"v72";
    %"v75" : W = (Cmp Ult L) %"v73", %"v74"
    => br %"v75" ? "L61" : "L62";
  @"L61":
    %"v77" = %"v0" +p #160;
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk25" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Check 0 4 Read 1) %"v79";
    %"v80" : W = (RawLoad (LdNarrow Sw) 0) %"chk26"
    => ret %"v80";
  @"L62":
    => ret #4294967295
} }.

Definition fn_glibc_wstrops'23enlarge_userbuf : func :=
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

Definition item_glibc_wstrops'23str'2e257 : item :=
  (IData (a "glibc_wstrops#str.257") (LRo (a "local")) 1 [(Item Wb 111); (Item Wb 102); (Item Wb 102); (Item Wb 115); (Item Wb 101); (Item Wb 116); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 111); (Item Wb 108); (Item Wb 100); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_wstrops'23str'2e258 : item :=
  (IData (a "glibc_wstrops#str.258") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 111); (Item Wb 112); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wstrops'23str'2e259 : item :=
  (IData (a "glibc_wstrops#str.259") (LRo (a "local")) 1 [(Item Wb 101); (Item Wb 110); (Item Wb 108); (Item Wb 97); (Item Wb 114); (Item Wb 103); (Item Wb 101); (Item Wb 95); (Item Wb 117); (Item Wb 115); (Item Wb 101); (Item Wb 114); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 0)]).
