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

Definition hi_fn__IO_new_file_overflow : func :=
  ir_fn{ "export" "_IO_new_file_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Or %"v11", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v12";
    %"v13" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v21" : W = And %"v20", #2048;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L24" : "L23";
  @"L23":
    %"v26" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" : L = Ptoi %"v27";
    %"v29" : L = Ptoi #0;
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => goto "L24";
  @"L24" [%"v32" : W = phi("L6" => #1, "L23" => %"v30")]:
    => br %"v32" ? "L16" : "L18";
  @"L16":
    %"v37" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v39" : L = Ptoi %"v38";
    %"v40" : L = Ptoi #0;
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => br %"v41" ? "L33" : "L35";
  @"L33":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v44" = %"v0" +p #24;
    %"v46" = %"v0" +p #56;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v44";
    store.ptr [%"chk8" + 0] <- %"v47";
    %"v49" = %"v0" +p #8;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk7", %"v46";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk10" + 0] <- %"v52";
    %"v54" = %"v0" +p #16;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk7", %"v46";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v54";
    store.ptr [%"chk12" + 0] <- %"v57"
    => goto "L35";
  @"L35":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v63" : W = And %"v62", #256;
    %"v64" : L = (Ext Sw) %"v63";
    %"v65" : W = (Cmp Ne L) %"v64", #0
    => br %"v65" ? "L58" : "L60";
  @"L58":
    %"v68" = %"v0" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v71" = %"v0" +p #8;
    %"v72" : P = (RawLoadPointer (-8) load_effects) %"chk14";
    %"v73" : L = Ptoi %"v69";
    %"v74" : L = Ptoi %"v72";
    %"v75" : L = Sub %"v73", %"v74";
    call void $"__GI__IO_free_backup_area"(P %"v0");
    %"v78" = %"v0" +p #24;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v88" = %"v0" +p #56;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v90" : L = Ptoi %"v86";
    %"v91" : L = Ptoi %"v89";
    %"v92" : L = Sub %"v90", %"v91";
    %"v93" : W = (Cmp Ult L) %"v75", %"v92"
    => br %"v93" ? "L82" : "L81";
  @"L81":
    %"v96" = %"v0" +p #24;
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v99" = %"v0" +p #56;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v101" : L = Ptoi %"v97";
    %"v102" : L = Ptoi %"v100";
    %"v103" : L = Sub %"v101", %"v102"
    => goto "L82";
  @"L82" [%"v104" : L = phi("L81" => %"v103", "L58" => %"v75")]:
    (Flight (a "v105") Sub [(FAddress (t "v79")); (FValue (t "v104"))] (LowerOf (t "v79")));
    %"chk21" : A = (Renew 0 8 Write 8) %"chk16", %"v78";
    store.ptr [%"chk21" + 0] <- %"v105";
    %"v107" = %"v0" +p #8;
    %"v109" = %"v0" +p #24;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk16", %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v107";
    store.ptr [%"chk23" + 0] <- %"v110"
    => goto "L60";
  @"L60":
    %"v115" = %"v0" +p #8;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v118" = %"v0" +p #64;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v118";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v120" : L = Ptoi %"v116";
    %"v121" : L = Ptoi %"v119";
    %"v122" : W = (Cmp Eq L) %"v120", %"v121"
    => br %"v122" ? "L111" : "L113";
  @"L111":
    %"v124" = %"v0" +p #16;
    %"v126" = %"v0" +p #8;
    %"v128" = %"v0" +p #56;
    %"v129" : P = (RawLoadPointer (-8) load_effects) %"chk25";
    %"chk27" : A = (Renew 0 8 Write 8) %"chk24", %"v126";
    store.ptr [%"chk27" + 0] <- %"v129";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v124";
    store.ptr [%"chk28" + 0] <- %"v129"
    => goto "L113";
  @"L113":
    %"v131" = %"v0" +p #40;
    %"v133" = %"v0" +p #8;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk24", %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v131";
    store.ptr [%"chk30" + 0] <- %"v134";
    %"v136" = %"v0" +p #32;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk30", %"v131";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Renew 0 8 Write 8) %"chk6", %"v136";
    store.ptr [%"chk32" + 0] <- %"v139";
    %"v141" = %"v0" +p #48;
    %"v143" = %"v0" +p #64;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk25", %"v143";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v141";
    store.ptr [%"chk34" + 0] <- %"v144";
    %"v146" = %"v0" +p #24;
    %"v150" = %"v0" +p #16;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Write 8) %"chk24", %"v133";
    store.ptr [%"chk36" + 0] <- %"v151";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v146";
    store.ptr [%"chk37" + 0] <- %"v151";
    %"chk38" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v153" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v154" : W = Or %"v153", #2048;
    %"chk39" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk39" + 0] <- %"v154";
    %"v159" = %"v0" +p #192;
    %"chk40" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v159";
    %"v160" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v161" : W = (Cmp Sle W) %"v160", #0
    => br %"v161" ? "L162" : "L163";
  @"L162":
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v167" : W = And %"v165", #514;
    %"v168" : W = (Cmp Ne W) %"v167", #0
    => goto "L163";
  @"L163" [%"v169" : W = phi("L113" => #0, "L162" => %"v168")]:
    => br %"v169" ? "L155" : "L18";
  @"L155":
    %"v171" = %"v0" +p #48;
    %"v173" = %"v0" +p #40;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk30", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk34", %"v171";
    store.ptr [%"chk43" + 0] <- %"v174"
    => goto "L18";
  @"L18":
    %"v180" : W = (Cmp Eq W) %"v2", #4294967295
    => br %"v180" ? "L175" : "L177";
  @"L175":
    %"v183" = %"v0" +p #32;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v186" = %"v0" +p #40;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v191" : L = Ptoi %"v187";
    %"v192" : L = Ptoi %"v190";
    %"v193" : L = Sub %"v191", %"v192";
    call %"v194" : W = $"_IO_new_do_write"(P %"v0", P %"v184", L %"v193")
    => ret %"v194";
  @"L177":
    %"v200" = %"v0" +p #40;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v200";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v203" = %"v0" +p #64;
    %"chk48" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v205" : L = Ptoi %"v201";
    %"v206" : L = Ptoi %"v204";
    %"v207" : W = (Cmp Eq L) %"v205", %"v206"
    => br %"v207" ? "L196" : "L198";
  @"L196":
    %"v215" = %"v0" +p #192;
    %"chk49" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v215";
    %"v216" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"v217" : W = (Cmp Sle W) %"v216", #0
    => br %"v217" ? "L211" : "L212";
  @"L211":
    %"v220" = %"v0" +p #32;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v223" = %"v0" +p #40;
    %"v224" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v228" : L = Ptoi %"v224";
    %"v229" : L = Ptoi %"v227";
    %"v230" : L = Sub %"v228", %"v229";
    call %"v231" : W = $"_IO_new_do_write"(P %"v0", P %"v221", L %"v230")
    => goto "L213";
  @"L212":
    %"v234" = %"v0" +p #160;
    %"v235" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v236" = %"v235" +p #24;
    %"chk54" : A = (Check 0 8 Read 8) %"v236";
    %"v237" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v240" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v241" = %"v240" +p #32;
    %"chk56" : A = (Check 0 8 Read 8) %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v245" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v246" = %"v245" +p #24;
    %"chk58" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v248" : L = Ptoi %"v242";
    %"v249" : L = Ptoi %"v247";
    %"v250" : L = Sub %"v248", %"v249";
    %"v251" : L = Div %"v250", #4;
    call %"v252" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v237", L %"v251")
    => goto "L213";
  @"L213" [%"v253" : W = phi("L211" => %"v231", "L212" => %"v252")]:
    %"v255" : W = (Cmp Eq W) %"v253", #4294967295
    => br %"v255" ? "L208" : "L198";
  @"L208":
    => ret #4294967295;
  @"L198":
    %"v259" = %"v0" +p #40;
    %"chk59" : A = (Renew 0 8 Read 8) %"chk47", %"v259";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"v261" = %"v260" +p #1;
    %"chk60" : A = (Renew 0 8 Write 8) %"chk47", %"v259";
    store.ptr [%"chk60" + 0] <- %"v261";
    %"v263" : W = (Ext Sb) %"v2";
    %"chk61" : A = (Check 0 1 Write 1) %"v260";
    store Wb [%"chk61" + 0] <- %"v263";
    %"chk62" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v268" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v269" : W = And %"v268", #2
    => br %"v269" ? "L271" : "L270";
  @"L270":
    %"v273" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v274" : W = And %"v273", #512
    => br %"v274" ? "L275" : "L271";
  @"L275":
    %"v278" : W = (Cmp Eq W) %"v2", #10
    => goto "L271";
  @"L271" [%"v282" : W = phi("L198" => #1, "L270" => #0, "L275" => %"v278")]:
    => br %"v282" ? "L264" : "L266";
  @"L264":
    %"v288" = %"v0" +p #32;
    %"chk64" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v291" = %"v0" +p #40;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk47", %"v291";
    %"v292" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v295" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v296" : L = Ptoi %"v292";
    %"v297" : L = Ptoi %"v295";
    %"v298" : L = Sub %"v296", %"v297";
    call %"v299" : W = $"_IO_new_do_write"(P %"v0", P %"v289", L %"v298");
    %"v301" : W = (Cmp Eq W) %"v299", #4294967295
    => br %"v301" ? "L283" : "L266";
  @"L283":
    => ret #4294967295;
  @"L266":
    %"v305" : W = (Ext Ub) %"v2"
    => ret %"v305"
} }.

Definition hi_fn__IO_new_file_sync : func :=
  ir_fn{ "export" "_IO_new_file_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ugt L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L6";
  @"L4":
    %"v23" = %"v0" +p #192;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v25" : W = (Cmp Sle W) %"v24", #0
    => br %"v25" ? "L19" : "L20";
  @"L19":
    %"v28" = %"v0" +p #32;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v31" = %"v0" +p #40;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v36" : L = Ptoi %"v32";
    %"v37" : L = Ptoi %"v35";
    %"v38" : L = Sub %"v36", %"v37";
    call %"v39" : W = $"_IO_new_do_write"(P %"v0", P %"v29", L %"v38")
    => goto "L21";
  @"L20":
    %"v42" = %"v0" +p #160;
    %"v43" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v44" = %"v43" +p #24;
    %"chk7" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v48" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v49" = %"v48" +p #32;
    %"chk9" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v54" = %"v53" +p #24;
    %"chk11" : A = (Check 0 8 Read 8) %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v56" : L = Ptoi %"v50";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    %"v59" : L = Div %"v58", #4;
    call %"v60" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v45", L %"v59")
    => goto "L21";
  @"L21" [%"v61" : W = phi("L19" => %"v39", "L20" => %"v60")]:
    => br %"v61" ? "L16" : "L6";
  @"L16":
    => ret #4294967295;
  @"L6":
    %"v65" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v68" = %"v0" +p #16;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v70" : L = Ptoi %"v66";
    %"v71" : L = Ptoi %"v69";
    %"v72" : L = Sub %"v70", %"v71";
    %"chk14" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v77" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"v78" : W = And %"v77", #256
    => br %"v78" ? "L73" : "L75";
  @"L73":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v82" = %"v0" +p #8;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk12", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v85" = %"v0" +p #16;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk13", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v87" : L = Ptoi %"v83";
    %"v88" : L = Ptoi %"v86";
    %"v89" : L = Sub %"v87", %"v88";
    %"v90" : L = Add %"v72", %"v89"
    => goto "L75";
  @"L75" [%"pr.1" : L = phi("L73" => %"v90", "L6" => %"v72")]:
    %"v95" : W = (Cmp Ne L) %"pr.1", #0
    => br %"v95" ? "L91" : "L93";
  @"L91":
    %"v98" = %"v0" +p #216;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v4" : L = Ptoi %"v99";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v101" = %"v99" +p #128;
    %"chk18" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : F = CheckFunction %"v102";
    rawcall %"v105" : L = %"chk19"(P %"v0", L %"pr.1", W #1);
    %"v112" : W = (Cmp Ne L) %"v105", #18446744073709551615
    => br %"v112" ? "L106" : "L107";
  @"L106":
    %"v114" = %"v0" +p #16;
    %"v116" = %"v0" +p #8;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk12", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk13", %"v114";
    store.ptr [%"chk21" + 0] <- %"v117"
    => goto "L93";
  @"L107":
    %"v121" : P = Copy $"__libc_errno";
    %"chk22" : A = (Check 0 4 Read 1) %"v121";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v123" : W = (Cmp Eq W) %"v122", #29
    => br %"v123" ? "L93" : "L119";
  @"L119":
    => goto "L93";
  @"L93" [%"pr.4" : W = phi("L106" => #0, "L119" => #4294967295, "L107" => #0, "L75" => #0)]:
    %"v130" : W = (Cmp Ne W) %"pr.4", #4294967295
    => br %"v130" ? "L125" : "L127";
  @"L125":
    %"v132" = %"v0" +p #144;
    %"chk23" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v132";
    store Wl [%"chk23" + 0] <- #18446744073709551615
    => goto "L127";
  @"L127":
    => ret %"pr.4"
} }.

Definition hi_fn__IO_file_sync_mmap : func :=
  ir_fn{ "export" "_IO_file_sync_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Read 1) %"v4";
    %"v5" : L = (RawLoad LdL 0) %"chk0";
    %"v7" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v10" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" : L = Ptoi %"v8";
    %"v13" : L = Ptoi %"v11";
    %"v14" : L = Sub %"v12", %"v13";
    %"v15" : L = Sub %"v5", %"v14";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v21";
    %"v26" : L = Ptoi %"v24";
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => br %"v27" ? "L16" : "L18";
  @"L16":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v33" : W = And %"v32", #256
    => br %"v33" ? "L28" : "L30";
  @"L28":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v37" = %"v0" +p #16;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v40" = %"v0" +p #24;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v42" : L = Ptoi %"v38";
    %"v43" : L = Ptoi %"v41";
    %"v44" : L = Sub %"v42", %"v43";
    %"v45" : L = Sub %"v15", %"v44"
    => goto "L30";
  @"L30" [%"pr.2" : L = phi("L28" => %"v45", "L16" => %"v15")]:
    %"v50" = %"v0" +p #112;
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v50";
    %"v51" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    call %"v53" : L = $"__lseek64"(W %"v51", L %"pr.2", W #0);
    %"v55" : W = (Cmp Ne L) %"v53", %"pr.2"
    => br %"v55" ? "L46" : "L18";
  @"L46":
    %"chk9" : A = (Renew 0 4 Read 1) %"chk5", %"v0";
    %"v57" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v58" : W = Or %"v57", #32;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk10" + 0] <- %"v58"
    => ret #4294967295;
  @"L18" [%"pr.1" : L = phi("L30" => %"pr.2", "start" => %"v15")]:
    %"v62" = %"v0" +p #144;
    %"chk11" : A = (Renew 0 8 Write 1) %"chk0", %"v62";
    store Wl [%"chk11" + 0] <- %"pr.1";
    %"v65" = %"v0" +p #16;
    %"v67" = %"v0" +p #8;
    %"v69" = %"v0" +p #24;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Renew 0 8 Write 8) %"chk2", %"v67";
    store.ptr [%"chk13" + 0] <- %"v70";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk1", %"v65";
    store.ptr [%"chk14" + 0] <- %"v70"
    => ret #0
} }.

Definition hi_fn__IO_new_file_seekoff : func :=
  ir_fn{ "export" "_IO_new_file_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v170" : P = (Alloc 8) #144;
    %"v16" : W = (Cmp Eq W) %"v6", #0
    => br %"v16" ? "iw_1.start" : "L14" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v8" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" : L = Ptoi %"iw_1.v9";
    %"iw_1.v11" : L = Ptoi #0;
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.L6" };
  ir_blk{ @"iw_1.L4":
    %"iw_1.v15" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v15";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v18" = %"v0" +p #32;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v18";
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v20" : L = Ptoi %"iw_1.v16";
    %"iw_1.v21" : L = Ptoi %"iw_1.v19";
    %"iw_1.v22" : W = (Cmp Ugt L) %"iw_1.v20", %"iw_1.v21";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"iw_1.v27" : W = And %"iw_1.v26", #4096;
    %"iw_1.v28" : W = (Cmp Eq W) %"iw_1.v27", #4096
    => br %"iw_1.v22" ? "iw_1.L34" : "iw_1.L35" };
  ir_blk{ @"iw_1.L34":
    => goto "iw_1.L35" };
  ir_blk{ @"iw_1.L35" [%"iw_1.v38" : W = phi("iw_1.L4" => #0, "iw_1.L34" => %"iw_1.v28")]:
    => br %"iw_1.v38" ? "iw_1.L30" : "iw_1.L32" };
  ir_blk{ @"iw_1.L30":
    %"iw_1.v40" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v41";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v43" = %"iw_1.v41" +p #128;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"iw_1.v44";
    rawcall %"iw_1.v46" : L = %"chk6"(P %"v0", L #0, W #2);
    %"iw_1.v53" : W = (Cmp Eq L) %"iw_1.v46", #18446744073709551615
    => br %"iw_1.v53" ? "iw_1.join" : "iw_1.L48" };
  ir_blk{ @"iw_1.L48":
    %"iw_1.v58" = %"v0" +p #144;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v58";
    store Wl [%"chk7" + 0] <- %"iw_1.v46"
    => goto "iw_1.L32" };
  ir_blk{ @"iw_1.L32":
    %"iw_1.v64" : W = (Cmp Ule L) %"iw_1.v20", %"iw_1.v21"
    => br %"iw_1.v64" ? "iw_1.L60" : "iw_1.L61" };
  ir_blk{ @"iw_1.L60":
    %"iw_1.v67" = %"v0" +p #16;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v67";
    %"iw_1.v68" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v70" = %"v0" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v72" : L = Ptoi %"iw_1.v68";
    %"iw_1.v73" : L = Ptoi %"iw_1.v71";
    %"iw_1.v74" : L = Sub %"iw_1.v72", %"iw_1.v73";
    %"iw_1.v75" : L = Sub #0, %"iw_1.v74"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L61":
    => br %"iw_1.v28" ? "iw_1.L76" : "iw_1.L77" };
  ir_blk{ @"iw_1.L76":
    %"iw_1.v82" = %"v0" +p #40;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v82";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v85" = %"v0" +p #32;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v85";
    %"iw_1.v86" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v87" : L = Ptoi %"iw_1.v83";
    %"iw_1.v88" : L = Ptoi %"iw_1.v86";
    %"iw_1.v89" : L = Sub %"iw_1.v87", %"iw_1.v88"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L77":
    %"iw_1.v93" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v93";
    %"iw_1.v94" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v96" = %"v0" +p #16;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v96";
    %"iw_1.v97" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v98" : L = Ptoi %"iw_1.v94";
    %"iw_1.v99" : L = Ptoi %"iw_1.v97";
    %"iw_1.v100" : L = Sub %"iw_1.v98", %"iw_1.v99"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L6" [%"iw_1.pr.2" : L = phi("iw_1.L60" => %"iw_1.v75", "iw_1.L76" => %"iw_1.v89", "iw_1.L77" => %"iw_1.v100", "iw_1.start" => #0)]:
    %"iw_1.v106" = %"v0" +p #144;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v106";
    %"iw_1.v107" : L = (RawLoad LdL 0) %"chk14";
    %"iw_1.v110" : W = (Cmp Ne L) %"iw_1.v107", #18446744073709551615
    => br %"iw_1.v110" ? "iw_1.L102" : "iw_1.L103" };
  ir_blk{ @"iw_1.L102":
    %"iw_1.v112" = %"v0" +p #144;
    %"iw_1.v113" : L = (RawLoad LdL 0) %"chk14"
    => goto "iw_1.L104" };
  ir_blk{ @"iw_1.L103":
    %"iw_1.v115" = %"v0" +p #216;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v115";
    %"iw_1.v116" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.iw_2.v4" : L = Ptoi %"iw_1.v116";
    %"iw_1.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_2.v8" : L = Ptoi %"iw_1.iw_2.v7";
    %"iw_1.iw_2.v9" : L = Sub %"iw_1.iw_2.v4", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v15" : W = (Cmp Uge L) %"iw_1.iw_2.v9", #2352
    => br %"iw_1.iw_2.v15" ? "iw_1.iw_2.L10" : "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.join":
    %"iw_1.v118" = %"iw_1.v116" +p #128;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v118";
    %"iw_1.v119" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : F = CheckFunction %"iw_1.v119";
    rawcall %"iw_1.v121" : L = %"chk18"(P %"v0", L #0, W #1)
    => goto "iw_1.L104" };
  ir_blk{ @"iw_1.L104" [%"iw_1.pr.1" : L = phi("iw_1.L102" => %"iw_1.v113", "iw_1.iw_2.join" => %"iw_1.v121")]:
    %"iw_1.v128" : W = (Cmp Eq L) %"iw_1.pr.1", #18446744073709551615
    => br %"iw_1.v128" ? "iw_1.join" : "iw_1.L124" };
  ir_blk{ @"iw_1.L124":
    %"iw_1.v135" : W = (Cmp Eq L) %"iw_1.pr.1", #0
    => br %"iw_1.v135" ? "iw_1.L136" : "iw_1.L137" };
  ir_blk{ @"iw_1.L136":
    %"iw_1.v139" : W = (Cmp Slt L) %"iw_1.pr.2", #0
    => goto "iw_1.L137" };
  ir_blk{ @"iw_1.L137" [%"iw_1.v141" : W = phi("iw_1.L124" => #0, "iw_1.L136" => %"iw_1.v139")]:
    => br %"iw_1.v141" ? "iw_1.L131" : "iw_1.L133" };
  ir_blk{ @"iw_1.L131":
    %"iw_1.v142" : P = Copy $"__libc_errno";
    %"chk19" : A = (Check 0 4 Write 1) %"iw_1.v142";
    store Ww [%"chk19" + 0] <- #29
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L133":
    %"iw_1.v148" : L = Add %"iw_1.pr.1", %"iw_1.pr.2";
    %"iw_1.v153" : W = (Cmp Slt L) %"iw_1.v148", #0
    => br %"iw_1.v153" ? "iw_1.L149" : "iw_1.join" };
  ir_blk{ @"iw_1.L149":
    %"iw_1.v154" : P = Copy $"__libc_errno";
    %"chk20" : A = (Check 0 4 Write 1) %"iw_1.v154";
    store Ww [%"chk20" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v18" : L = phi("iw_1.L131" => #18446744073709551615, "iw_1.L149" => #18446744073709551615, "iw_1.iw_1.join" => #18446744073709551615, "iw_1.L104" => %"iw_1.pr.1", "iw_1.L133" => %"iw_1.v148")]:
    => ret %"v18" };
  ir_blk{ @"L14":
    %"v22" = %"v0" +p #24;
    %"chk21" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v25" = %"v0" +p #16;
    %"chk22" : A = (HalfCheck Lower 0 8 Read 8) %"chk21", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v27" : L = Ptoi %"v23";
    %"v28" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L30" : "L31" };
  ir_blk{ @"L30":
    %"v33" = %"v0" +p #32;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v36" = %"v0" +p #40;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v38" : L = Ptoi %"v34";
    %"v39" : L = Ptoi %"v37";
    %"v40" : W = (Cmp Eq L) %"v38", %"v39"
    => goto "L31" };
  ir_blk{ @"L31" [%"v42" : W = phi("L14" => #0, "L30" => %"v40")]:
    %"v45" = %"v0" +p #40;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v48" = %"v0" +p #32;
    %"v49" : P = (RawLoadPointer (-8) load_effects) %"chk25";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ugt L) %"v50", %"v51"
    => br %"v52" ? "L54" : "L53" };
  ir_blk{ @"L53":
    %"chk27" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v56" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"v57" : W = And %"v56", #2048;
    %"v58" : W = (Cmp Ne W) %"v57", #0
    => goto "L54" };
  ir_blk{ @"L54" [%"v59" : W = phi("L31" => #1, "L53" => %"v58")]:
    => br %"v59" ? "L65" : "L66" };
  ir_blk{ @"L65":
    call %"v68" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v69" : W = (Cmp Ne W) %"v68", #0
    => goto "L66" };
  ir_blk{ @"L66" [%"v70" : W = phi("L54" => #0, "L65" => %"v69")]:
    => br %"v70" ? "L61" : "L63" };
  ir_blk{ @"L61":
    => ret #18446744073709551615 };
  ir_blk{ @"L63":
    %"v78" = %"v0" +p #56;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v80" : L = Ptoi %"v79";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L74" : "L129" };
  ir_blk{ @"L74":
    %"v87" = %"v0" +p #24;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk21", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v89" : L = Ptoi %"v88";
    %"v91" : W = (Cmp Ne L) %"v89", %"v81"
    => br %"v91" ? "L83" : "L85" };
  ir_blk{ @"L83":
    %"v94" = %"v0" +p #24;
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v9" = %"v0" +p #119;
    %"iw_2.v10" : L = Ptoi %"v95";
    %"iw_2.v11" : L = Ptoi %"iw_2.v9";
    %"iw_2.v12" : W = (Cmp Ne L) %"iw_2.v10", %"iw_2.v11"
    => br %"iw_2.v12" ? "iw_2.L4" : "iw_2.join" };
  ir_blk{ @"iw_2.L4":
    call void $"free"(P %"v95")
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"chk31" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v99" : W = And %"v97", #4294967039;
    %"chk32" : A = (Renew 0 4 Write 1) %"chk31", %"v0";
    store Ww [%"chk32" + 0] <- %"v99"
    => goto "L85" };
  ir_blk{ @"L85":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v102" = %"v0" +p #32;
    %"v104" = %"v0" +p #40;
    %"v106" = %"v0" +p #56;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Renew 0 8 Write 8) %"chk25", %"v104";
    store.ptr [%"chk34" + 0] <- %"v107";
    %"chk35" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v102";
    store.ptr [%"chk35" + 0] <- %"v107";
    %"v109" = %"v0" +p #48;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v109";
    store.ptr [%"chk37" + 0] <- %"v112";
    %"v114" = %"v0" +p #24;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Renew 0 8 Write 8) %"chk21", %"v114";
    store.ptr [%"chk39" + 0] <- %"v117";
    %"v119" = %"v0" +p #8;
    %"chk40" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v119";
    store.ptr [%"chk41" + 0] <- %"v122";
    %"v124" = %"v0" +p #16;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk22", %"v124";
    store.ptr [%"chk43" + 0] <- %"v127"
    => goto "L129" };
  ir_blk{ @"L131":
    %"v134" = %"v0" +p #16;
    %"chk44" : A = (Renew 0 8 Read 8) %"chk22", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v137" = %"v0" +p #8;
    %"chk45" : A = (HalfCheck Lower 0 8 Read 8) %"chk21", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v139" : L = Ptoi %"v135";
    %"v140" : L = Ptoi %"v138";
    %"v141" : L = Sub %"v139", %"v140";
    %"v142" : L = Sub %"v2", %"v141";
    %"v147" = %"v0" +p #144;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 1) %"chk21", %"v147";
    %"v148" : L = (RawLoad LdL 0) %"chk46";
    %"v151" : W = (Cmp Eq L) %"v148", #18446744073709551615
    => br %"v151" ? "L152" : "L145" };
  ir_blk{ @"L145":
    %"v156" = %"v0" +p #144;
    %"v157" : L = (RawLoad LdL 0) %"chk46";
    %"v158" : L = Add %"v142", %"v157";
    %"v163" : W = (Cmp Slt L) %"v158", #0
    => br %"v163" ? "L159" : "L130" }] [ir_blk{ @"L159":
    %"v164" : P = Copy $"__libc_errno";
    %"chk48" : A = (Check 0 4 Write 1) %"v164";
    store Ww [%"chk48" + 0] <- #22
    => ret #18446744073709551615 };
  ir_blk{ @"L169":
    %"v175" = %"v0" +p #216;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v175";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_3.v4" : L = Ptoi %"v176";
    %"iw_3.v7" : P = Copy $"__io_vtables";
    %"iw_3.v8" : L = Ptoi %"iw_3.v7";
    %"iw_3.v9" : L = Sub %"iw_3.v4", %"iw_3.v8";
    %"iw_3.v15" : W = (Cmp Uge L) %"iw_3.v9", #2352
    => br %"iw_3.v15" ? "iw_3.L10" : "iw_3.join" };
  ir_blk{ @"iw_3.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join":
    %"v178" = %"v176" +p #144;
    %"chk50" : A = (Check 0 8 Read 8) %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : F = CheckFunction %"v179";
    rawcall %"v181" : W = %"chk51"(P %"v0", P %"v170");
    %"v182" : W = (Cmp Eq W) %"v181", #0
    => br %"v182" ? "L183" : "L184" };
  ir_blk{ @"L183":
    %"v185" = %"v170" +p #24;
    %"chk52" : A = (Check 0 4 Read 1) %"v185";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk52";
    %"v187" : W = And %"v186", #61440;
    %"v188" : W = (Cmp Eq W) %"v187", #32768
    => goto "L184" };
  ir_blk{ @"L184" [%"v190" : W = phi("iw_3.join" => #0, "L183" => %"v188")]:
    => br %"v190" ? "L171" : "L152" };
  ir_blk{ @"L171":
    %"v192" = %"v170" +p #48;
    %"chk53" : A = (Check 0 8 Read 1) %"v192";
    %"v193" : L = (RawLoad LdL 0) %"chk53";
    %"v194" : L = Add %"v2", %"v193"
    => goto "L130" };
  ir_blk{ @"L129":
    %"v195" : W = (Cmp Eq W) %"v4", #1
    => br %"v195" ? poll "L131" : "L196" };
  ir_blk{ @"L196":
    %"v197" : W = (Cmp Eq W) %"v4", #0
    => br %"v197" ? "L130" : "L198" };
  ir_blk{ @"L198":
    %"v199" : W = (Cmp Eq W) %"v4", #2
    => br %"v199" ? poll "L169" : "L130" };
  ir_blk{ @"L130" [%"pr.3" : W = phi("L145" => #0, "L196" => %"v4", "L171" => #0, "L198" => %"v4"); %"pr.1" : L = phi("L145" => %"v158", "L196" => %"v2", "L171" => %"v194", "L198" => %"v2")]:
    call void $"__GI__IO_free_backup_area"(P %"v0");
    %"v206" = %"v0" +p #144;
    %"chk54" : A = (HalfCheck Upper 0 8 Read 1) %"chk21", %"v206";
    %"v207" : L = (RawLoad LdL 0) %"chk54";
    %"v210" : W = (Cmp Ne L) %"v207", #18446744073709551615
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v214" = %"v0" +p #24;
    %"chk55" : A = (Renew 0 8 Read 8) %"chk21", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v216" : L = Ptoi %"v215";
    %"v218" : W = (Cmp Ne L) %"v216", %"v81"
    => goto "L212" };
  ir_blk{ @"L212" [%"v220" : W = phi("L130" => #0, "L211" => %"v218")]:
    => br %"v220" ? "L221" : "L222" };
  ir_blk{ @"L221":
    %"chk56" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v224" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v225" : W = And %"v224", #256;
    %"v226" : W = (Cmp Eq W) %"v225", #0
    => goto "L222" };
  ir_blk{ @"L222" [%"v228" : W = phi("L212" => #0, "L221" => %"v226")]:
    => br %"v228" ? "L202" : "L204" };
  ir_blk{ @"L202":
    %"v231" = %"v0" +p #144;
    %"v232" : L = (RawLoad LdL 0) %"chk54";
    %"v234" = %"v0" +p #16;
    %"chk58" : A = (Renew 0 8 Read 8) %"chk22", %"v234";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v237" = %"v0" +p #56;
    %"v238" : P = (RawLoadPointer 40 load_effects) %"chk58";
    %"v239" : L = Ptoi %"v235";
    %"v240" : L = Ptoi %"v238";
    %"v241" : L = Sub %"v239", %"v240";
    %"v242" : L = Sub %"v232", %"v241";
    %"v248" : W = (Cmp Sge L) %"pr.1", %"v242"
    => br %"v248" ? "L249" : "L250" };
  ir_blk{ @"L249":
    %"v253" = %"v0" +p #144;
    %"v254" : L = (RawLoad LdL 0) %"chk54";
    %"v255" : W = (Cmp Slt L) %"pr.1", %"v254"
    => goto "L250" };
  ir_blk{ @"L250" [%"v257" : W = phi("L202" => #0, "L249" => %"v255")]:
    => br %"v257" ? "L243" : "L204" };
  ir_blk{ @"L243":
    %"v259" = %"v0" +p #24;
    %"v261" = %"v0" +p #56;
    %"v262" : P = (RawLoadPointer 40 load_effects) %"chk58";
    %"chk62" : A = (Renew 0 8 Write 8) %"chk21", %"v259";
    store.ptr [%"chk62" + 0] <- %"v262";
    %"v264" = %"v0" +p #8;
    %"chk63" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"v270" : L = Sub %"pr.1", %"v242";
    %"v271" = %"v267" +p %"v270";
    %"chk64" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v264";
    store.ptr [%"chk64" + 0] <- %"v271";
    %"v273" = %"v0" +p #16;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk22", %"v273";
    %"v276" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Renew 0 8 Write 8) %"chk22", %"v273";
    store.ptr [%"chk66" + 0] <- %"v276";
    %"v278" = %"v0" +p #32;
    %"v280" = %"v0" +p #40;
    %"chk67" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v283" : P = (RawLoadPointer 0 load_effects) %"chk67";
    %"chk68" : A = (Renew 0 8 Write 8) %"chk25", %"v280";
    store.ptr [%"chk68" + 0] <- %"v283";
    %"chk69" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v278";
    store.ptr [%"chk69" + 0] <- %"v283";
    %"v285" = %"v0" +p #48;
    %"chk70" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v288" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"chk71" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v285";
    store.ptr [%"chk71" + 0] <- %"v288";
    %"chk72" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk72";
    %"v293" : W = And %"v291", #4294967279;
    %"chk73" : A = (Renew 0 4 Write 1) %"chk72", %"v0";
    store Ww [%"chk73" + 0] <- %"v293";
    %"v507" = %"v0" +p #144;
    %"chk74" : A = (Renew 0 8 Read 1) %"chk54", %"v507";
    %"v508" : L = (RawLoad LdL 0) %"chk74";
    %"v509" : W = (Cmp Sge L) %"v508", #0
    => br %"v509" ? "L503" : "L505" };
  ir_blk{ @"L204":
    %"chk75" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v302" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v303" : W = And %"v302", #4
    => br %"v303" ? "L152" : "L300" };
  ir_blk{ @"L300":
    %"v307" = %"v0" +p #64;
    %"chk76" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v310" = %"v0" +p #56;
    %"v311" : P = (RawLoadPointer (-8) load_effects) %"chk76";
    %"v312" : L = Ptoi %"v308";
    %"v313" : L = Ptoi %"v311";
    %"v314" : L = Sub %"v312", %"v313";
    %"v315" : L = Sub %"v314", #1;
    %"v316" : L = Xor %"v315", #(-1);
    %"v317" : L = And %"pr.1", %"v316";
    %"v320" : L = Sub %"pr.1", %"v317";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v330" : P = (RawLoadPointer (-8) load_effects) %"chk76";
    %"v331" : L = Ptoi %"v327";
    %"v332" : L = Ptoi %"v330";
    %"v333" : L = Sub %"v331", %"v332";
    %"v334" : W = (Cmp Sgt L) %"v320", %"v333"
    => br %"v334" ? "L323" : "L322" };
  ir_blk{ @"L322":
    => goto "L323" };
  ir_blk{ @"L323" [%"pr.6" : L = phi("L322" => %"v317", "L300" => %"pr.1"); %"pr.5" : L = phi("L322" => %"v320", "L300" => #0)]:
    %"v337" = %"v0" +p #216;
    %"chk80" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v337";
    %"v338" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"iw_4.v4" : L = Ptoi %"v338";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v340" = %"v338" +p #128;
    %"chk81" : A = (Check 0 8 Read 8) %"v340";
    %"v341" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"chk82" : F = CheckFunction %"v341";
    rawcall %"v344" : L = %"chk82"(P %"v0", L %"pr.6", W #0);
    %"v349" : W = (Cmp Slt L) %"v344", #0
    => br %"v349" ? "L345" : "L347" };
  ir_blk{ @"L345":
    => ret #18446744073709551615 };
  ir_blk{ @"L347":
    %"v357" : W = (Cmp Eq L) %"pr.5", #0
    => br %"v357" ? "L355" : "L354" };
  ir_blk{ @"L354":
    %"v359" = %"v0" +p #216;
    %"chk83" : A = (Renew 0 8 Read 8) %"chk80", %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk83";
    %"iw_5.v4" : L = Ptoi %"v360";
    %"iw_5.v7" : P = Copy $"__io_vtables";
    %"iw_5.v8" : L = Ptoi %"iw_5.v7";
    %"iw_5.v9" : L = Sub %"iw_5.v4", %"iw_5.v8";
    %"iw_5.v15" : W = (Cmp Uge L) %"iw_5.v9", #2352
    => br %"iw_5.v15" ? "iw_5.L10" : "iw_5.join" };
  ir_blk{ @"iw_5.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_5.join" };
  ir_blk{ @"iw_5.join":
    %"v362" = %"v360" +p #112;
    %"chk84" : A = (Check 0 8 Read 8) %"v362";
    %"v363" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"v366" = %"v0" +p #56;
    %"chk85" : A = (Renew 0 8 Read 8) %"chk28", %"v366";
    %"v367" : P = (RawLoadPointer 0 load_effects) %"chk85"
    => br %"v42" ? "L370" : "L369" };
  ir_blk{ @"L369":
    %"v374" = %"v0" +p #64;
    %"chk86" : A = (Renew 0 8 Read 8) %"chk76", %"v374";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"v377" = %"v0" +p #56;
    %"v378" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v379" : L = Ptoi %"v375";
    %"v380" : L = Ptoi %"v378";
    %"v381" : L = Sub %"v379", %"v380"
    => goto "L370" };
  ir_blk{ @"L370" [%"v382" : L = phi("L369" => %"v381", "iw_5.join" => %"pr.5")]:
    %"chk88" : F = CheckFunction %"v363";
    rawcall %"v383" : L = %"chk88"(P %"v0", P %"v367", L %"v382");
    %"v389" : W = (Cmp Slt L) %"v383", %"pr.5"
    => br %"v389" ? "L384" : "L355" };
  ir_blk{ @"L384":
    %"v396" : W = (Cmp Eq L) %"v383", #18446744073709551615
    => br %"v396" ? "L152" : "L391" };
  ir_blk{ @"L391":
    %"v400" : L = Sub %"pr.5", %"v383"
    => goto "L152" };
  ir_blk{ @"L355" [%"pr.7" : L = phi("L347" => #0, "L370" => %"v383")]:
    %"v404" = %"v0" +p #24;
    %"v406" = %"v0" +p #56;
    %"chk89" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v407" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"chk90" : A = (Renew 0 8 Write 8) %"chk21", %"v404";
    store.ptr [%"chk90" + 0] <- %"v407";
    %"v409" = %"v0" +p #8;
    %"chk91" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v412" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"v414" = %"v412" +p %"pr.5";
    %"chk92" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v409";
    store.ptr [%"chk92" + 0] <- %"v414";
    %"v416" = %"v0" +p #16;
    %"chk93" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v419" : P = (RawLoadPointer 0 load_effects) %"chk93";
    %"v421" = %"v419" +p %"pr.7";
    %"chk94" : A = (Renew 0 8 Write 8) %"chk22", %"v416";
    store.ptr [%"chk94" + 0] <- %"v421";
    %"v423" = %"v0" +p #32;
    %"v425" = %"v0" +p #40;
    %"chk95" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v428" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"chk96" : A = (Renew 0 8 Write 8) %"chk25", %"v425";
    store.ptr [%"chk96" + 0] <- %"v428";
    %"chk97" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v423";
    store.ptr [%"chk97" + 0] <- %"v428";
    %"v430" = %"v0" +p #48;
    %"chk98" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v433" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"chk99" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v430";
    store.ptr [%"chk99" + 0] <- %"v433";
    %"v435" = %"v0" +p #144;
    %"v438" : L = Add %"v344", %"pr.7";
    %"chk100" : A = (Renew 0 8 Write 1) %"chk54", %"v435";
    store Wl [%"chk100" + 0] <- %"v438";
    %"chk101" : A = (Renew 0 4 Read 1) %"chk75", %"v0";
    %"v441" : W = (RawLoad (LdNarrow Sw) 0) %"chk101";
    %"v443" : W = And %"v441", #4294967279;
    store Ww [%"chk101" + 0] <- %"v443"
    => ret %"pr.1" };
  ir_blk{ @"L152" [%"pr.4" : W = phi("L131" => %"v4", "L184" => %"v4", "L204" => %"pr.3", "L391" => #1, "L384" => #1); %"pr.2" : L = phi("L131" => %"v142", "L184" => %"v2", "L204" => %"pr.1", "L391" => %"v400", "L384" => %"pr.5")]:
    call void $"__GI__IO_unsave_markers"(P %"v0");
    %"v449" = %"v0" +p #216;
    %"chk103" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk103";
    %"iw_6.v4" : L = Ptoi %"v450";
    %"iw_6.v7" : P = Copy $"__io_vtables";
    %"iw_6.v8" : L = Ptoi %"iw_6.v7";
    %"iw_6.v9" : L = Sub %"iw_6.v4", %"iw_6.v8";
    %"iw_6.v15" : W = (Cmp Uge L) %"iw_6.v9", #2352
    => br %"iw_6.v15" ? "iw_6.L10" : "iw_6.join" };
  ir_blk{ @"iw_6.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.join":
    %"v452" = %"v450" +p #128;
    %"chk104" : A = (Check 0 8 Read 8) %"v452";
    %"v453" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : F = CheckFunction %"v453";
    rawcall %"v457" : L = %"chk105"(P %"v0", L %"pr.2", W %"pr.4");
    %"v464" : W = (Cmp Ne L) %"v457", #18446744073709551615
    => br %"v464" ? "L458" : "L460" };
  ir_blk{ @"L458":
    %"chk106" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk106";
    %"v469" : W = And %"v467", #4294967279;
    %"chk107" : A = (Renew 0 4 Write 1) %"chk106", %"v0";
    store Ww [%"chk107" + 0] <- %"v469";
    %"v473" = %"v0" +p #144;
    %"chk108" : A = (HalfCheck Upper 0 8 Write 1) %"chk21", %"v473";
    store Wl [%"chk108" + 0] <- %"v457";
    %"v476" = %"v0" +p #24;
    %"v478" = %"v0" +p #56;
    %"chk109" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v479" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk110" : A = (Renew 0 8 Write 8) %"chk21", %"v476";
    store.ptr [%"chk110" + 0] <- %"v479";
    %"v481" = %"v0" +p #8;
    %"chk111" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk111";
    %"chk112" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v481";
    store.ptr [%"chk112" + 0] <- %"v484";
    %"v486" = %"v0" +p #16;
    %"chk113" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v489" : P = (RawLoadPointer 0 load_effects) %"chk113";
    %"chk114" : A = (Renew 0 8 Write 8) %"chk22", %"v486";
    store.ptr [%"chk114" + 0] <- %"v489";
    %"v491" = %"v0" +p #32;
    %"v493" = %"v0" +p #40;
    %"chk115" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v496" : P = (RawLoadPointer 0 load_effects) %"chk115";
    %"chk116" : A = (Renew 0 8 Write 8) %"chk25", %"v493";
    store.ptr [%"chk116" + 0] <- %"v496";
    %"chk117" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v491";
    store.ptr [%"chk117" + 0] <- %"v496";
    %"v498" = %"v0" +p #48;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v501" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"chk119" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v498";
    store.ptr [%"chk119" + 0] <- %"v501"
    => goto "L460" };
  ir_blk{ @"L460":
    => ret %"v457" };
  ir_blk{ @"L503":
    %"v511" = %"v0" +p #216;
    %"chk120" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v511";
    %"v512" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_7.v4" : L = Ptoi %"v512";
    %"iw_7.v7" : P = Copy $"__io_vtables";
    %"iw_7.v8" : L = Ptoi %"iw_7.v7";
    %"iw_7.v9" : L = Sub %"iw_7.v4", %"iw_7.v8";
    %"iw_7.v15" : W = (Cmp Uge L) %"iw_7.v9", #2352
    => br %"iw_7.v15" ? "iw_7.L10" : "iw_7.join" };
  ir_blk{ @"iw_7.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join":
    %"v514" = %"v512" +p #128;
    %"chk121" : A = (Check 0 8 Read 8) %"v514";
    %"v515" : P = (RawLoadPointer 0 load_effects) %"chk121";
    %"v518" = %"v0" +p #144;
    %"chk122" : A = (Renew 0 8 Read 1) %"chk54", %"v518";
    %"v519" : L = (RawLoad LdL 0) %"chk122";
    %"chk123" : F = CheckFunction %"v515";
    rawcall %"v520" : L = %"chk123"(P %"v0", L %"v519", W #0)
    => goto "L505" };
  ir_blk{ @"L505":
    => ret %"pr.1" }])) }.

Definition hi_fn__IO_file_seekoff_mmap : func :=
  ir_fn{ "export" "_IO_file_seekoff_mmap"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v13" : W = (Cmp Eq W) %"v6", #0
    => br %"v13" ? "L9" : "L11";
  @"L9":
    %"v15" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Read 1) %"v15";
    %"v16" : L = (RawLoad LdL 0) %"chk0";
    %"v18" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v21" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : L = Sub %"v23", %"v24";
    %"v26" : L = Sub %"v16", %"v25"
    => ret %"v26";
  @"L11":
    %"chk3" : A = (Check 0 4 Read 1) %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v33" : W = And %"v32", #256
    => br %"v33" ? "L28" : "L30";
  @"L28":
    %"v38" : W = (Cmp Eq W) %"v4", #1
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v44" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v46" : L = Ptoi %"v42";
    %"v47" : L = Ptoi %"v45";
    %"v48" : L = Sub %"v46", %"v47";
    %"v49" : L = Add %"v2", %"v48"
    => goto "L36";
  @"L36" [%"pr.2" : L = phi("L34" => %"v49", "L28" => %"v2")]:
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto "L30";
  @"L30" [%"pr.1" : L = phi("L36" => %"pr.2", "L11" => %"v2")]:
    %"v84" : W = (Cmp Eq W) %"v4", #1
    => br %"v84" ? "L54" : "L85";
  @"L54":
    %"v57" = %"v0" +p #144;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v57";
    %"v58" : L = (RawLoad LdL 0) %"chk6";
    %"v60" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v63" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v65" : L = Ptoi %"v61";
    %"v66" : L = Ptoi %"v64";
    %"v67" : L = Sub %"v65", %"v66";
    %"v68" : L = Sub %"v58", %"v67";
    %"v69" : L = Add %"pr.1", %"v68"
    => goto "L53";
  @"L71":
    %"v74" = %"v0" +p #64;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v77" = %"v0" +p #56;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v79" : L = Ptoi %"v75";
    %"v80" : L = Ptoi %"v78";
    %"v81" : L = Sub %"v79", %"v80";
    %"v82" : L = Add %"pr.1", %"v81"
    => goto "L53";
  @"L85":
    %"v86" : W = (Cmp Eq W) %"v4", #0
    => br %"v86" ? "L53" : "L87";
  @"L87":
    %"v88" : W = (Cmp Eq W) %"v4", #2
    => br %"v88" ? poll "L71" : "L53";
  @"L53" [%"pr.3" : L = phi("L54" => %"v69", "L71" => %"v82", "L85" => %"pr.1", "L87" => %"pr.1")]:
    %"v94" : W = (Cmp Slt L) %"pr.3", #0
    => br %"v94" ? "L90" : "L92";
  @"L90":
    %"v95" : P = Copy $"__libc_errno";
    %"chk11" : A = (Check 0 4 Write 1) %"v95";
    store Ww [%"chk11" + 0] <- #22
    => ret #18446744073709551615;
  @"L92":
    %"v100" = %"v0" +p #216;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v4" : L = Ptoi %"v101";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v103" = %"v101" +p #128;
    %"chk13" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : F = CheckFunction %"v104";
    rawcall %"v107" : L = %"chk14"(P %"v0", L %"pr.3", W #0);
    %"v112" : W = (Cmp Slt L) %"v107", #0
    => br %"v112" ? "L108" : "L110";
  @"L108":
    => ret #18446744073709551615;
  @"L110":
    %"v121" = %"v0" +p #64;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v124" = %"v0" +p #56;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v126" : L = Ptoi %"v122";
    %"v127" : L = Ptoi %"v125";
    %"v128" : L = Sub %"v126", %"v127";
    %"v129" : W = (Cmp Sgt L) %"pr.3", %"v128"
    => br %"v129" ? "L116" : "L117";
  @"L116":
    %"v131" = %"v0" +p #24;
    %"v133" = %"v0" +p #56;
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v131";
    store.ptr [%"chk18" + 0] <- %"v134";
    %"v136" = %"v0" +p #8;
    %"v138" = %"v0" +p #64;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk15", %"v138";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v136";
    store.ptr [%"chk20" + 0] <- %"v139";
    %"v141" = %"v0" +p #16;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk15", %"v138";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v141";
    store.ptr [%"chk22" + 0] <- %"v144"
    => goto "L118";
  @"L117":
    %"v146" = %"v0" +p #24;
    %"v148" = %"v0" +p #56;
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk24" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v146";
    store.ptr [%"chk24" + 0] <- %"v149";
    %"v151" = %"v0" +p #8;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk16", %"v148";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v156" = %"v154" +p %"pr.3";
    %"chk26" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v151";
    store.ptr [%"chk26" + 0] <- %"v156";
    %"v158" = %"v0" +p #16;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk16", %"v148";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v163" = %"v161" +p %"pr.3";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v158";
    store.ptr [%"chk28" + 0] <- %"v163"
    => goto "L118";
  @"L118":
    %"v165" = %"v0" +p #144;
    %"chk29" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v165";
    store Wl [%"chk29" + 0] <- %"v107";
    %"chk30" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v169" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v171" : W = And %"v169", #4294967279;
    store Ww [%"chk30" + 0] <- %"v171"
    => ret %"pr.3"
} }.

Definition hi_fn__IO_file_seekoff_maybe_mmap : func :=
  ir_fn{ "export" "_IO_file_seekoff_maybe_mmap"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v11";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v13" = %"v11" +p #128;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v14";
    rawcall %"v18" : L = %"chk2"(P %"v0", L %"v2", W %"v4");
    %"v23" : W = (Cmp Slt L) %"v18", #0
    => br %"v23" ? "L19" : "L21";
  @"L19":
    => ret #18446744073709551615;
  @"L21":
    %"v28" = %"v0" +p #144;
    %"chk3" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v28";
    store Wl [%"chk3" + 0] <- %"v18"
    => ret %"v18"
} }.

Definition hi_fn___GI__IO_file_read : func :=
  ir_fn{ "export" "__GI__IO_file_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Shl %"v11", #8;
    %"v13" : W = Sar %"v12", #8;
    %"v14" : W = And %"v13", #2;
    %"v15" : L = (Ext Sw) %"v14";
    %"v16" : W = (Cmp Ne L) %"v15", #0
    => br %"v16" ? "L6" : "L7";
  @"L6":
    %"v18" = %"v0" +p #112;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"v22" : L = $"__GI___read_nocancel"(W %"v19", P %"v2", L %"v4")
    => goto "L8";
  @"L7":
    %"v24" = %"v0" +p #112;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    call %"v28" : L = $"__GI___read"(W %"v25", P %"v2", L %"v4")
    => goto "L8";
  @"L8" [%"v29" : L = phi("L6" => %"v22", "L7" => %"v28")]:
    => ret %"v29"
} }.

Definition hi_fn___GI__IO_file_seek : func :=
  ir_fn{ "export" "__GI__IO_file_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v7" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v7";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v11" : L = $"__lseek64"(W %"v8", L %"v2", W %"v4")
    => ret %"v11"
} }.

Definition hi_fn___GI__IO_file_stat : func :=
  ir_fn{ "export" "__GI__IO_file_stat"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v5" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v8" : W = $"__GI___fstat64"(W %"v6", P %"v2")
    => ret %"v8"
} }.

Definition hi_fn__IO_file_close_mmap : func :=
  ir_fn{ "export" "_IO_file_close_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v6" = %"v0" +p #64;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : L = Sub %"v11", %"v12";
    call %"v14" : W = $"__GI___munmap"(P %"v4", L %"v13");
    %"chk3" : A = (Renew 0 8 Write 8) %"chk1", %"v6";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk0", %"v3";
    store.ptr [%"chk4" + 0] <- #0;
    %"v20" = %"v0" +p #112;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    call %"v22" : W = $"__GI___close_nocancel"(W %"v21")
    => ret %"v22"
} }.

Definition hi_fn___GI__IO_file_close : func :=
  ir_fn{ "export" "__GI__IO_file_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v5" : W = $"__GI___close_nocancel"(W %"v4")
    => ret %"v5"
} }.

Definition hi_fn__IO_new_file_write : func :=
  ir_fn{ "export" "_IO_new_file_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => goto "L8";
  @"L8" [%"pr.2" : L = phi("L40" => %"v54", "start" => %"v4"); %"pr.1" : P = phi("L40" => %"v57", "start" => %"v2")]:
    %"v12" : W = (Cmp Sgt L) %"pr.2", #0
    => br %"v12" ? "L9" : "L10";
  @"L9":
    %"v18" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v20" : W = Shl %"v19", #8;
    %"v21" : W = Sar %"v20", #8;
    %"v22" : W = And %"v21", #2;
    %"v23" : L = (Ext Sw) %"v22";
    %"v24" : W = (Cmp Ne L) %"v23", #0
    => br %"v24" ? "L14" : "L15";
  @"L14":
    %"v26" = %"v0" +p #112;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"v30" : L = $"__GI___write_nocancel"(W %"v27", P %"pr.1", L %"pr.2")
    => goto "L16";
  @"L15":
    %"v32" = %"v0" +p #112;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    call %"v36" : L = $"__GI___write"(W %"v33", P %"pr.1", L %"pr.2")
    => goto "L16";
  @"L16" [%"v37" : L = phi("L14" => %"v30", "L15" => %"v36")]:
    %"v42" : W = (Cmp Slt L) %"v37", #0
    => br %"v42" ? "L38" : "L40";
  @"L38":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v45" : W = Or %"v44", #32;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v45"
    => goto "L10";
  @"L40":
    %"v48" = %"v0" +p #200;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk5";
    %"v51" : L = Add %"v49", %"v37";
    %"chk6" : A = (Renew 0 8 Write 1) %"chk5", %"v48";
    store Wl [%"chk6" + 0] <- %"v51";
    %"v54" : L = Sub %"pr.2", %"v37";
    %"v57" = %"pr.1" +p %"v37"
    => goto poll "L8";
  @"L10":
    %"v60" : L = Sub %"v4", %"pr.2";
    %"v65" = %"v0" +p #144;
    %"chk7" : A = (Check 0 8 Read 1) %"v65";
    %"v66" : L = (RawLoad LdL 0) %"chk7";
    %"v67" : W = (Cmp Sge L) %"v66", #0
    => br %"v67" ? "L61" : "L63";
  @"L61":
    %"v69" = %"v0" +p #144;
    %"v70" : L = (RawLoad LdL 0) %"chk7";
    %"v72" : L = Add %"v70", %"v60";
    %"chk9" : A = (Renew 0 8 Write 1) %"chk7", %"v69";
    store Wl [%"chk9" + 0] <- %"v72"
    => goto "L63";
  @"L63":
    => ret %"v60"
} }.
