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

Definition hi_fn_glibc_libc_start'23get_isa_level : func :=
  ir_fn{ "local" "glibc_libc_start#get_isa_level"(P %"v0") -> (RClass W) {
  @"start":
    %"v7" = %"v0" +p #20;
    %"v9" = %"v7" +p #16;
    %"v10" = %"v9" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v13" : W = And %"v11", #32768;
    %"v14" : W = (Cmp Ne W) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v18" = %"v0" +p #20;
    %"v20" = %"v18" +p #16;
    %"v21" = %"v20" +p #12;
    %"v22" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v24" : W = And %"v22", #256;
    %"v25" : W = (Cmp Ne W) %"v24", #0
    => goto "L16";
  @"L16" [%"v27" : W = phi("start" => #0, "L15" => %"v25")]:
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v31" = %"v0" +p #20;
    %"v33" = %"v31" +p #12;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v33";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v36" : W = And %"v34", #1
    => goto "L29";
  @"L29" [%"v39" : W = phi("L16" => #0, "L28" => %"v36")]:
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" = %"v0" +p #20;
    %"v45" = %"v43" +p #16;
    %"v46" = %"v45" +p #12;
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v49" : W = And %"v47", #16777216;
    %"v50" : W = (Cmp Ne W) %"v49", #0
    => goto "L41";
  @"L41" [%"v52" : W = phi("L29" => #0, "L40" => %"v50")]:
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v56" = %"v0" +p #20;
    %"v58" = %"v56" +p #16;
    %"v59" = %"v58" +p #12;
    %"v60" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v62" : W = And %"v60", #8388608;
    %"v63" : W = (Cmp Ne W) %"v62", #0
    => goto "L54";
  @"L54" [%"v65" : W = phi("L41" => #0, "L53" => %"v63")]:
    => br %"v65" ? "L66" : "L67";
  @"L66":
    %"v69" = %"v0" +p #20;
    %"v71" = %"v69" +p #16;
    %"v72" = %"v71" +p #12;
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v75" : W = And %"v73", #33554432;
    %"v76" : W = (Cmp Ne W) %"v75", #0
    => goto "L67";
  @"L67" [%"v78" : W = phi("L54" => #0, "L66" => %"v76")]:
    => br %"v78" ? "L79" : "L80";
  @"L79":
    %"v82" = %"v0" +p #20;
    %"v84" = %"v82" +p #16;
    %"v85" = %"v84" +p #12;
    %"v86" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v88" : W = And %"v86", #67108864;
    %"v89" : W = (Cmp Ne W) %"v88", #0
    => goto "L80";
  @"L80" [%"v91" : W = phi("L67" => #0, "L79" => %"v89")]:
    => br %"v91" ? "L3" : "L5";
  @"L3":
    %"v97" = %"v0" +p #20;
    %"v99" = %"v97" +p #16;
    %"v100" = %"v99" +p #8;
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v100";
    %"v101" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v103" : W = And %"v101", #8192;
    %"v104" : W = (Cmp Ne W) %"v103", #0
    => br %"v104" ? "L105" : "L106";
  @"L105":
    %"v108" = %"v0" +p #20;
    %"v109" = %"v108" +p #64;
    %"v110" = %"v109" +p #16;
    %"v111" = %"v110" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v111";
    %"v112" : W = (RawLoad (LdNarrow Uw) 0) %"chk8";
    %"v114" : W = And %"v112", #1
    => goto "L106";
  @"L106" [%"v117" : W = phi("L3" => #0, "L105" => %"v114")]:
    => br %"v117" ? "L118" : "L119";
  @"L118":
    %"v121" = %"v0" +p #20;
    %"v123" = %"v121" +p #16;
    %"v124" = %"v123" +p #8;
    %"v125" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v127" : W = And %"v125", #8388608;
    %"v128" : W = (Cmp Ne W) %"v127", #0
    => goto "L119";
  @"L119" [%"v130" : W = phi("L106" => #0, "L118" => %"v128")]:
    => br %"v130" ? "L131" : "L132";
  @"L131":
    %"v134" = %"v0" +p #20;
    %"v136" = %"v134" +p #16;
    %"v137" = %"v136" +p #8;
    %"v138" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v140" : W = And %"v138", #1
    => goto "L132";
  @"L132" [%"v143" : W = phi("L119" => #0, "L131" => %"v140")]:
    => br %"v143" ? "L144" : "L145";
  @"L144":
    %"v147" = %"v0" +p #20;
    %"v149" = %"v147" +p #16;
    %"v150" = %"v149" +p #8;
    %"v151" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v153" : W = And %"v151", #512;
    %"v154" : W = (Cmp Ne W) %"v153", #0
    => goto "L145";
  @"L145" [%"v156" : W = phi("L132" => #0, "L144" => %"v154")]:
    => br %"v156" ? "L157" : "L158";
  @"L157":
    %"v160" = %"v0" +p #20;
    %"v162" = %"v160" +p #16;
    %"v163" = %"v162" +p #8;
    %"v164" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v166" : W = And %"v164", #524288;
    %"v167" : W = (Cmp Ne W) %"v166", #0
    => goto "L158";
  @"L158" [%"v169" : W = phi("L145" => #0, "L157" => %"v167")]:
    => br %"v169" ? "L170" : "L171";
  @"L170":
    %"v173" = %"v0" +p #20;
    %"v175" = %"v173" +p #16;
    %"v176" = %"v175" +p #8;
    %"v177" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v179" : W = And %"v177", #1048576;
    %"v180" : W = (Cmp Ne W) %"v179", #0
    => goto "L171";
  @"L171" [%"v182" : W = phi("L158" => #0, "L170" => %"v180")]:
    => br %"v182" ? "L93" : "L5";
  @"L93":
    %"v190" = %"v0" +p #20;
    %"v192" = %"v190" +p #16;
    %"v193" = %"v192" +p #8;
    %"v194" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v196" : W = And %"v194", #268435456;
    %"v197" : W = (Cmp Ne W) %"v196", #0
    => br %"v197" ? "L198" : "L199";
  @"L198":
    %"v201" = %"v0" +p #20;
    %"v202" = %"v201" +p #32;
    %"v203" = %"v202" +p #16;
    %"v204" = %"v203" +p #4;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v204";
    %"v205" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"v207" : W = And %"v205", #32;
    %"v208" : W = (Cmp Ne W) %"v207", #0
    => goto "L199";
  @"L199" [%"v210" : W = phi("L93" => #0, "L198" => %"v208")]:
    => br %"v210" ? "L211" : "L212";
  @"L211":
    %"v214" = %"v0" +p #20;
    %"v215" = %"v214" +p #32;
    %"v216" = %"v215" +p #16;
    %"v217" = %"v216" +p #4;
    %"chk16" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v217";
    %"v218" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v220" : W = And %"v218", #8;
    %"v221" : W = (Cmp Ne W) %"v220", #0
    => goto "L212";
  @"L212" [%"v223" : W = phi("L199" => #0, "L211" => %"v221")]:
    => br %"v223" ? "L224" : "L225";
  @"L224":
    %"v227" = %"v0" +p #20;
    %"v228" = %"v227" +p #32;
    %"v229" = %"v228" +p #16;
    %"v230" = %"v229" +p #4;
    %"chk17" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v230";
    %"v231" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v233" : W = And %"v231", #256;
    %"v234" : W = (Cmp Ne W) %"v233", #0
    => goto "L225";
  @"L225" [%"v236" : W = phi("L212" => #0, "L224" => %"v234")]:
    => br %"v236" ? "L237" : "L238";
  @"L237":
    %"v240" = %"v0" +p #20;
    %"v242" = %"v240" +p #16;
    %"v243" = %"v242" +p #8;
    %"v244" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v246" : W = And %"v244", #536870912;
    %"v247" : W = (Cmp Ne W) %"v246", #0
    => goto "L238";
  @"L238" [%"v249" : W = phi("L225" => #0, "L237" => %"v247")]:
    => br %"v249" ? "L250" : "L251";
  @"L250":
    %"v253" = %"v0" +p #20;
    %"v255" = %"v253" +p #16;
    %"v256" = %"v255" +p #8;
    %"v257" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v259" : W = And %"v257", #4096;
    %"v260" : W = (Cmp Ne W) %"v259", #0
    => goto "L251";
  @"L251" [%"v262" : W = phi("L238" => #0, "L250" => %"v260")]:
    => br %"v262" ? "L263" : "L264";
  @"L263":
    %"v266" = %"v0" +p #20;
    %"v267" = %"v266" +p #64;
    %"v268" = %"v267" +p #16;
    %"v269" = %"v268" +p #8;
    %"chk20" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v269";
    %"v270" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v272" : W = And %"v270", #32;
    %"v273" : W = (Cmp Ne W) %"v272", #0
    => goto "L264";
  @"L264" [%"v275" : W = phi("L251" => #0, "L263" => %"v273")]:
    => br %"v275" ? "L276" : "L277";
  @"L276":
    %"v279" = %"v0" +p #20;
    %"v281" = %"v279" +p #16;
    %"v282" = %"v281" +p #8;
    %"v283" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v285" : W = And %"v283", #4194304;
    %"v286" : W = (Cmp Ne W) %"v285", #0
    => goto "L277";
  @"L277" [%"v288" : W = phi("L264" => #0, "L276" => %"v286")]:
    => br %"v288" ? "L186" : "L5";
  @"L186":
    %"v296" = %"v0" +p #20;
    %"v297" = %"v296" +p #32;
    %"v298" = %"v297" +p #16;
    %"v299" = %"v298" +p #4;
    %"chk22" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v299";
    %"v300" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v302" : W = And %"v300", #65536;
    %"v303" : W = (Cmp Ne W) %"v302", #0
    => br %"v303" ? "L304" : "L305";
  @"L304":
    %"v307" = %"v0" +p #20;
    %"v308" = %"v307" +p #32;
    %"v309" = %"v308" +p #16;
    %"v310" = %"v309" +p #4;
    %"v311" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v313" : W = And %"v311", #1073741824;
    %"v314" : W = (Cmp Ne W) %"v313", #0
    => goto "L305";
  @"L305" [%"v316" : W = phi("L186" => #0, "L304" => %"v314")]:
    => br %"v316" ? "L317" : "L318";
  @"L317":
    %"v320" = %"v0" +p #20;
    %"v321" = %"v320" +p #32;
    %"v322" = %"v321" +p #16;
    %"v323" = %"v322" +p #4;
    %"v324" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v326" : W = And %"v324", #268435456;
    %"v327" : W = (Cmp Ne W) %"v326", #0
    => goto "L318";
  @"L318" [%"v329" : W = phi("L305" => #0, "L317" => %"v327")]:
    => br %"v329" ? "L330" : "L331";
  @"L330":
    %"v333" = %"v0" +p #20;
    %"v334" = %"v333" +p #32;
    %"v335" = %"v334" +p #16;
    %"v336" = %"v335" +p #4;
    %"v337" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v339" : W = And %"v337", #131072;
    %"v340" : W = (Cmp Ne W) %"v339", #0
    => goto "L331";
  @"L331" [%"v342" : W = phi("L318" => #0, "L330" => %"v340")]:
    => br %"v342" ? "L343" : "L344";
  @"L343":
    %"v346" = %"v0" +p #20;
    %"v347" = %"v346" +p #32;
    %"v348" = %"v347" +p #16;
    %"v349" = %"v348" +p #4;
    %"v350" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v352" : W = And %"v350", #2147483648;
    %"v353" : W = (Cmp Ne W) %"v352", #0
    => goto "L344";
  @"L344" [%"v355" : W = phi("L331" => #0, "L343" => %"v353")]:
    => br %"v355" ? "L5" : "L293";
  @"L293":
    => goto "L5";
  @"L5" [%"pr.3" : W = phi("L293" => #7, "L344" => #15, "L277" => #3, "L171" => #1, "L80" => #0)]:
    => ret %"pr.3"
} }.

Definition hi_fn_glibc_libc_start'23get_common_cache_info : func :=
  ir_fn{ "local" "glibc_libc_start#get_common_cache_info"(P %"v0", P %"v2", P %"v4", L %"v6", P %"v8") -> RVoid blocks ((app [ir_blk{ @"start":
    %"v10" : P = (Alloc 4) #4;
    %"v11" : P = (Alloc 4) #4;
    %"v12" : P = (Alloc 4) #4;
    %"v13" : P = (Alloc 4) #4;
    %"v17" : P = Copy $"_dl_x86_cpu_features";
    %"v20" = %"v17" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v24" = %"v17" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v28" = %"v17" +p #12;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v28";
    %"v29" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"chk3" : A = (Check 0 8 Read 1) %"v0";
    %"v32" : L = (RawLoad LdL 0) %"chk3";
    %"chk4" : A = (Check 0 8 Read 1) %"v2";
    %"v35" : L = (RawLoad LdL 0) %"chk4";
    %"chk5" : A = (Check 0 4 Read 1) %"v4";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v17";
    %"v48" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"v49" : W = (Cmp Eq W) %"v48", #3
    => br %"v49" ? "L50" : "L51" };
  ir_blk{ @"L50":
    %"v53" : W = (Cmp Eq W) %"v25", #6
    => goto "L51" };
  ir_blk{ @"L51" [%"v55" : W = phi("start" => #0, "L50" => %"v53")]:
    => br %"v55" ? "L46" : "L45" };
  ir_blk{ @"L45":
    => goto "L46" };
  ir_blk{ @"L46" [%"pr.46" : W = phi("L45" => #1, "L51" => #0)]:
    %"v61" : W = (Cmp Sle L) %"v32", #0
    => br %"v61" ? "L59" : "L58" };
  ir_blk{ @"L58":
    => goto "L59" };
  ir_blk{ @"L59" [%"pr.47" : W = phi("L58" => #3, "L46" => #2); %"pr.31" : L = phi("L58" => %"v35", "L46" => %"v6"); %"pr.28" : L = phi("L58" => %"v32", "L46" => %"v6"); %"pr.25" : W = phi("L58" => #0, "L46" => #4294967295)]:
    %"v68" : P = Copy $"_dl_x86_cpu_features";
    %"v69" = %"v68" +p #20;
    %"v71" = %"v69" +p #12;
    %"chk7" : A = (Check 0 4 Read 1) %"v71";
    %"v72" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v74" : W = And %"v72", #268435456;
    %"v75" : W = (Cmp Ne W) %"v74", #0
    => br %"v75" ? "L65" : "L67" };
  ir_blk{ @"L65":
    %"v80" : W = (Cmp Sge W) %"v21", #4
    => br %"v80" ? "L76" : "L154" };
  ir_blk{ @"L76":
    %"v84" : W = (Cmp Eq W) %"pr.25", #0;
    %"v85" : W = Shl %"v84", #1;
    %"v86" : W = Or %"v85", #1
    => goto "L87" };
  ir_blk{ @"L87" [%"pr.53" : W = phi("L76" => %"v86", "L160" => %"pr.50"); %"pr.49" : W = phi("L76" => #0, "L160" => %"v140"); %"pr.45" : W = phi("L76" => #1, "L160" => %"pr.41"); %"pr.26" : W = phi("L76" => %"pr.25", "L160" => %"pr.16"); %"pr.15" : W = phi("L76" => #0, "L160" => %"pr.2")]:
    %"v94" : L = Ptoi %"v8";
    %"v95" : L = Ptoi #0;
    %"v96" : W = (Cmp Ne L) %"v94", %"v95"
    => br %"v96" ? "L97" : "L98" };
  ir_blk{ @"L97":
    %"v101" = %"v8" +p #1;
    %"chk8" : A = (Check 0 1 Read 1) %"v101";
    %"v102" : W = (RawLoad (LdNarrow Ub) 0) %"chk8";
    %"v103" : W = (Cmp Slt W) %"pr.49", %"v102"
    => goto "L98" };
  ir_blk{ @"L98" [%"v105" : W = phi("L87" => #0, "L97" => %"v103")]:
    => br %"v105" ? "L90" : "L91" };
  ir_blk{ @"L90":
    %"v107" = %"v8" +p #20;
    %"v109" : L = (Ext Sw) %"pr.49";
    %"v110" : L = Shl %"v109", #4;
    %"v111" = %"v107" +p %"v110";
    %"chk9" : A = (Check 0 4 Read 1) %"v111";
    %"v113" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"chk10" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk10" + 0] <- %"v113";
    %"v120" = %"v111" +p #4;
    %"chk11" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v120";
    %"v121" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"v11";
    store Ww [%"chk12" + 0] <- %"v121";
    %"v128" = %"v111" +p #8;
    %"chk13" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v128";
    %"v129" : W = (RawLoad (LdNarrow Uw) 0) %"chk13";
    %"chk14" : A = (Check 0 4 Write 1) %"v12";
    store Ww [%"chk14" + 0] <- %"v129";
    %"v136" = %"v111" +p #12;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk9", %"v136";
    %"v137" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"chk16" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk16" + 0] <- %"v137"
    => goto "L92" };
  ir_blk{ @"L91":
    call void $"zcpuid_count"(W #4, W %"pr.49", P %"v10", P %"v11", P %"v12", P %"v13")
    => goto "L92" };
  ir_blk{ @"L92":
    %"v140" : W = Add %"pr.49", #1;
    %"chk17" : A = (Renew 0 4 Read 1) %"chk6", %"v17";
    %"v145" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"v146" : W = (Cmp Eq W) %"v145", #1
    => br %"v146" ? "L147" : "L148" };
  ir_blk{ @"L147":
    %"chk18" : A = (Check 0 4 Read 1) %"v10";
    %"v149" : W = (RawLoad (LdNarrow Uw) 0) %"chk18";
    %"v150" : W = And %"v149", #31;
    %"v151" : W = (Cmp Eq W) %"v150", #0
    => goto "L148" };
  ir_blk{ @"L148" [%"v153" : W = phi("L92" => #0, "L147" => %"v151")]:
    => br %"v153" ? "L154" : "L143" };
  ir_blk{ @"L143":
    %"chk19" : A = (Check 0 4 Read 1) %"v10";
    %"v156" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v157" : W = Shr %"v156", #5;
    %"v158" : W = And %"v157", #7;
    %"v193" : W = (Cmp Eq W) %"v158", #2
    => br %"v193" ? "L162" : "L194" };
  ir_blk{ @"L162":
    %"v167" : W = And %"pr.53", #1
    => br %"v167" ? "L163" : "L160" };
  ir_blk{ @"L163":
    %"v168" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"v169" : W = Shr %"v168", #14;
    %"v170" : W = And %"v169", #1023;
    %"v173" : W = And %"pr.53", #4294967294
    => goto "L160" };
  ir_blk{ @"L174":
    %"v180" : W = And %"pr.53", #2
    => br %"v180" ? "L175" : "L160" };
  ir_blk{ @"L175":
    %"chk21" : A = (Renew 0 4 Read 1) %"chk19", %"v10";
    %"v181" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v182" : W = Shr %"v181", #14;
    %"v183" : W = And %"v182", #1023;
    %"chk22" : A = (Check 0 4 Read 1) %"v13";
    %"v184" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v185" : W = And %"v184", #2;
    %"v186" : W = (Cmp Ne W) %"v185", #0;
    %"v191" : W = And %"pr.53", #4294967293
    => goto "L160" };
  ir_blk{ @"L194":
    %"v195" : W = (Cmp Eq W) %"v158", #3
    => br %"v195" ? poll "L174" : "L160" };
  ir_blk{ @"L160" [%"pr.50" : W = phi("L163" => %"v173", "L162" => %"pr.53", "L175" => %"v191", "L174" => %"pr.53", "L194" => %"pr.53"); %"pr.41" : W = phi("L163" => %"pr.45", "L162" => %"pr.45", "L175" => %"v186", "L174" => %"pr.45", "L194" => %"pr.45"); %"pr.16" : W = phi("L163" => %"pr.26", "L162" => %"pr.26", "L175" => %"v183", "L174" => %"pr.26", "L194" => %"pr.26"); %"pr.2" : W = phi("L163" => %"v170", "L162" => %"pr.15", "L175" => %"pr.15", "L174" => %"pr.15", "L194" => %"pr.15")]:
    => br %"pr.50" ? poll "L87" : "L89" };
  ir_blk{ @"L89":
    %"v202" : W = (Cmp Sge W) %"v21", #11
    => br %"v202" ? "L203" : "L204" };
  ir_blk{ @"L203":
    => goto "L204" };
  ir_blk{ @"L204" [%"v207" : W = phi("L89" => #0, "L203" => %"pr.46")]:
    => br %"v207" ? "L198" : "L200" };
  ir_blk{ @"L198":
    %"v210" : W = (Cmp Sgt W) %"pr.2", #0
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v214" : W = (Cmp Eq W) %"pr.47", #3
    => goto "L212" };
  ir_blk{ @"L212" [%"v216" : W = phi("L198" => #0, "L211" => %"v214")]:
    %"v218" : W = (Cmp Sgt W) %"pr.16", #0
    => br %"v218" ? "L220" : "L219" };
  ir_blk{ @"L219":
    => br %"v210" ? "L223" : "L220" };
  ir_blk{ @"L223":
    %"v226" : W = (Cmp Eq W) %"pr.47", #2
    => goto "L220" };
  ir_blk{ @"L220" [%"v230" : W = phi("L212" => #1, "L219" => #0, "L223" => %"v226")]:
    %"v231" : W = Shl %"v230", #1;
    %"v232" : W = Or %"v216", %"v231"
    => goto "L233" };
  ir_blk{ @"L233" [%"pr.54" : W = phi("L220" => %"v232", "L259" => %"pr.55"); %"pr.48" : W = phi("L220" => #0, "L259" => %"v238"); %"pr.19" : W = phi("L220" => %"pr.16", "L259" => %"pr.20"); %"pr.5" : W = phi("L220" => %"pr.2", "L259" => %"pr.6")]:
    => br %"pr.54" ? "L234" : "L200" };
  ir_blk{ @"L234":
    %"v238" : W = Add %"pr.48", #1;
    call void $"zcpuid_count"(W #11, W %"pr.48", P %"v10", P %"v11", P %"v12", P %"v13");
    %"chk23" : A = (Check 0 4 Read 1) %"v11";
    %"v240" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v241" : W = And %"v240", #255;
    %"chk24" : A = (Check 0 4 Read 1) %"v12";
    %"v243" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"v244" : W = And %"v243", #65280;
    %"v249" : W = (Cmp Eq W) %"v241", #0
    => br %"v249" ? "L251" : "L250" };
  ir_blk{ @"L250":
    %"v253" : W = (Cmp Eq W) %"v244", #0
    => goto "L251" };
  ir_blk{ @"L251" [%"v255" : W = phi("L234" => #1, "L250" => %"v253")]:
    => br %"v255" ? "L200" : "L246" };
  ir_blk{ @"L246":
    %"v261" : W = (Cmp Eq W) %"v244", #256
    => br %"v261" ? "L257" : "L258" };
  ir_blk{ @"L257":
    %"v266" : W = And %"pr.54", #1
    => br %"v266" ? "L262" : "L259" }] [ir_blk{ @"L262":
    %"v269" : L = (Ext Uw) %"pr.5";
    %"v270" : L = Shr %"v269", #1;
    %"v271" : L = Or %"v269", %"v270";
    %"v272" : L = Shr %"v271", #2;
    %"v273" : L = Or %"v271", %"v272";
    %"v274" : L = Shr %"v273", #4;
    %"v275" : L = Or %"v273", %"v274";
    %"v276" : L = Shr %"v275", #8;
    %"v277" : L = Or %"v275", %"v276";
    %"v278" : L = Shr %"v277", #16;
    %"v279" : L = Or %"v277", %"v278";
    %"v280" : L = Shr %"v279", #32;
    %"v281" : L = Or %"v279", %"v280";
    %"v282" : L = Shr %"v281", #1;
    %"v283" : L = And %"v282", #6148914691236517205;
    %"v284" : L = Sub %"v281", %"v283";
    %"v285" : L = And %"v284", #3689348814741910323;
    %"v286" : L = Shr %"v284", #2;
    %"v287" : L = And %"v286", #3689348814741910323;
    %"v288" : L = Add %"v285", %"v287";
    %"v289" : L = Shr %"v288", #4;
    %"v290" : L = Add %"v288", %"v289";
    %"v291" : L = And %"v290", #1085102592571150095;
    %"v292" : L = Mul %"v291", #72340172838076673;
    %"v293" : L = Shr %"v292", #56;
    %"v294" : L = Sub %"v293", #32;
    %"v295" : L = Neg %"v294";
    %"v296" : W = Xor %"v295", #31;
    %"v299" : W = Add %"v296", #1;
    %"v300" : W = Shl #4294967295, %"v299";
    %"v301" : W = Xor %"v300", #(-1);
    %"v303" : W = Sub %"v241", #1;
    %"v305" : W = And %"v303", %"v301";
    %"v308" : W = And %"pr.54", #4294967294
    => goto "L259" };
  ir_blk{ @"L258":
    %"v313" : W = (Cmp Eq W) %"v244", #512
    => br %"v313" ? "L309" : "L259" };
  ir_blk{ @"L309":
    %"v319" : W = And %"pr.54", #2
    => br %"v319" ? "L314" : "L259" };
  ir_blk{ @"L314":
    %"v326" : W = (Cmp Eq W) %"pr.47", #2
    => br %"v326" ? "L324" : "L323" };
  ir_blk{ @"L323":
    => goto "L324" };
  ir_blk{ @"L324" [%"v329" : W = phi("L323" => %"pr.19", "L314" => %"pr.5")]:
    %"v331" : L = (Ext Uw) %"v329";
    %"v332" : L = Shr %"v331", #1;
    %"v333" : L = Or %"v331", %"v332";
    %"v334" : L = Shr %"v333", #2;
    %"v335" : L = Or %"v333", %"v334";
    %"v336" : L = Shr %"v335", #4;
    %"v337" : L = Or %"v335", %"v336";
    %"v338" : L = Shr %"v337", #8;
    %"v339" : L = Or %"v337", %"v338";
    %"v340" : L = Shr %"v339", #16;
    %"v341" : L = Or %"v339", %"v340";
    %"v342" : L = Shr %"v341", #32;
    %"v343" : L = Or %"v341", %"v342";
    %"v344" : L = Shr %"v343", #1;
    %"v345" : L = And %"v344", #6148914691236517205;
    %"v346" : L = Sub %"v343", %"v345";
    %"v347" : L = And %"v346", #3689348814741910323;
    %"v348" : L = Shr %"v346", #2;
    %"v349" : L = And %"v348", #3689348814741910323;
    %"v350" : L = Add %"v347", %"v349";
    %"v351" : L = Shr %"v350", #4;
    %"v352" : L = Add %"v350", %"v351";
    %"v353" : L = And %"v352", #1085102592571150095;
    %"v354" : L = Mul %"v353", #72340172838076673;
    %"v355" : L = Shr %"v354", #56;
    %"v356" : L = Sub %"v355", #32;
    %"v357" : L = Neg %"v356";
    %"v358" : W = Xor %"v357", #31;
    %"v361" : W = Add %"v358", #1;
    %"v362" : W = Shl #4294967295, %"v361";
    %"v363" : W = Xor %"v362", #(-1);
    %"v365" : W = Sub %"v241", #1;
    %"v367" : W = And %"v365", %"v363"
    => br %"v326" ? "L370" : "L369" };
  ir_blk{ @"L369":
    => goto "L370" };
  ir_blk{ @"L370" [%"pr.23" : W = phi("L369" => %"v367", "L324" => %"pr.19"); %"pr.10" : W = phi("L369" => %"pr.5", "L324" => %"v367")]:
    %"v378" : W = And %"pr.54", #4294967293
    => goto "L259" };
  ir_blk{ @"L259" [%"pr.55" : W = phi("L262" => %"v308", "L257" => %"pr.54", "L370" => %"v378", "L309" => %"pr.54", "L258" => %"pr.54"); %"pr.20" : W = phi("L262" => %"pr.19", "L257" => %"pr.19", "L370" => %"pr.23", "L309" => %"pr.19", "L258" => %"pr.19"); %"pr.6" : W = phi("L262" => %"v305", "L257" => %"pr.5", "L370" => %"pr.10", "L309" => %"pr.5", "L258" => %"pr.5")]:
    => goto poll "L233" };
  ir_blk{ @"L200" [%"pr.18" : W = phi("L233" => %"pr.19", "L251" => %"pr.19", "L204" => %"pr.16"); %"pr.4" : W = phi("L233" => %"pr.5", "L251" => %"pr.5", "L204" => %"pr.2")]:
    %"v383" : W = (Cmp Sgt W) %"pr.4", #0
    => br %"v383" ? "L379" : "L381" };
  ir_blk{ @"L379":
    %"v385" : W = Add %"pr.4", #1
    => goto "L381" };
  ir_blk{ @"L381" [%"pr.11" : W = phi("L379" => %"v385", "L200" => %"pr.4")]:
    %"v390" : W = (Cmp Sgt W) %"pr.18", #0
    => br %"v390" ? "L386" : "L388" };
  ir_blk{ @"L386":
    %"v392" : W = Add %"pr.18", #1
    => goto "L388" };
  ir_blk{ @"L388" [%"pr.24" : W = phi("L386" => %"v392", "L381" => %"pr.18")]:
    %"v397" : W = (Cmp Eq W) %"pr.47", #2
    => br %"v397" ? "L393" : "L394" };
  ir_blk{ @"L393":
    => br %"pr.11" ? "L398" : "L78" };
  ir_blk{ @"L398":
    %"chk25" : A = (Renew 0 4 Read 1) %"chk6", %"v17";
    %"v407" : W = (RawLoad (LdNarrow Uw) 0) %"chk25";
    %"v408" : W = (Cmp Eq W) %"v407", #1
    => br %"v408" ? "L409" : "L410" };
  ir_blk{ @"L409":
    %"v412" : W = (Cmp Ugt W) %"pr.11", #2
    => goto "L410" };
  ir_blk{ @"L410" [%"v414" : W = phi("L398" => #0, "L409" => %"v412")]:
    => br %"v414" ? "L415" : "L416" };
  ir_blk{ @"L415":
    %"v418" : W = (Cmp Eq W) %"v25", #6
    => goto "L416" };
  ir_blk{ @"L416" [%"v420" : W = phi("L410" => #0, "L415" => %"v418")]:
    => br %"v420" ? "L422" : "L78" };
  ir_blk{ @"L422":
    %"v431" : W = (Cmp Ult W) %"v29", #77
    => br %"v431" ? "L432" : "L433" };
  ir_blk{ @"L432":
    %"v434" : W = (Cmp Eq W) %"v29", #55
    => br %"v434" ? "L78" : "L435" };
  ir_blk{ @"L435":
    %"v436" : W = (Cmp Eq W) %"v29", #74
    => br %"v436" ? "L78" : "L437" };
  ir_blk{ @"L437":
    => goto "L78" };
  ir_blk{ @"L433":
    %"v438" : W = (Cmp Eq W) %"v29", #77
    => br %"v438" ? "L78" : "L439" };
  ir_blk{ @"L439":
    %"v440" : W = (Cmp Eq W) %"v29", #90
    => br %"v440" ? "L78" : "L441" };
  ir_blk{ @"L441":
    %"v442" : W = (Cmp Eq W) %"v29", #93
    => br %"v442" ? "L78" : "L443" };
  ir_blk{ @"L443":
    => goto "L78" };
  ir_blk{ @"L394":
    => br %"pr.24" ? "L78" : "L445" };
  ir_blk{ @"L445":
    => goto "L78" };
  ir_blk{ @"L154" [%"pr.40" : W = phi("L148" => %"pr.45", "L65" => #1); %"pr.1" : W = phi("L148" => %"pr.15", "L65" => #0)]:
    %"v450" = %"v17" +p #20;
    %"v452" = %"v450" +p #4;
    %"chk26" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v452";
    %"v453" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v454" : W = Shr %"v453", #16;
    %"v455" : W = And %"v454", #255
    => goto "L78" };
  ir_blk{ @"L78" [%"pr.44" : W = phi("L154" => %"pr.40", "L441" => %"pr.41", "L439" => %"pr.41", "L433" => %"pr.41", "L435" => %"pr.41", "L432" => %"pr.41", "L437" => %"pr.41", "L443" => %"pr.41", "L416" => %"pr.41", "L393" => %"pr.41", "L445" => %"pr.41", "L394" => %"pr.41"); %"pr.39" : W = phi("L154" => %"v455", "L441" => #2, "L439" => #2, "L433" => #2, "L435" => #2, "L432" => #2, "L437" => %"pr.11", "L443" => %"pr.11", "L416" => %"pr.11", "L393" => %"v38", "L445" => %"v38", "L394" => %"pr.24"); %"pr.14" : W = phi("L154" => %"pr.1", "L441" => %"pr.11", "L439" => %"pr.11", "L433" => %"pr.11", "L435" => %"pr.11", "L432" => %"pr.11", "L437" => %"pr.11", "L443" => %"pr.11", "L416" => %"pr.11", "L393" => %"pr.11", "L445" => %"pr.11", "L394" => %"pr.11")]:
    %"v460" : W = (Cmp Sgt L) %"pr.31", #0
    => br %"v460" ? "L461" : "L462" };
  ir_blk{ @"L461":
    %"v464" : W = (Cmp Ugt W) %"pr.39", #0
    => goto "L462" };
  ir_blk{ @"L462" [%"v466" : W = phi("L78" => #0, "L461" => %"v464")]:
    => br %"v466" ? "L456" : "L67" };
  ir_blk{ @"L456":
    %"v469" : L = (Ext Uw) %"pr.39";
    %"v470" : L = Div %"pr.31", %"v469"
    => goto "L67" };
  ir_blk{ @"L67" [%"pr.43" : W = phi("L456" => %"pr.44", "L462" => %"pr.44", "L59" => #1); %"pr.38" : W = phi("L456" => %"pr.39", "L462" => %"pr.39", "L59" => %"v38"); %"pr.32" : L = phi("L456" => %"v470", "L462" => %"pr.31", "L59" => %"pr.31"); %"pr.13" : W = phi("L456" => %"pr.14", "L462" => %"pr.14", "L59" => #0)]:
    %"v474" : W = (Ext Ub) %"pr.43";
    %"v475" : W = (Cmp Eq W) %"v474", #0
    => br %"v475" ? "L471" : "L473" };
  ir_blk{ @"L471":
    %"v481" : W = (Cmp Sgt W) %"pr.13", #0
    => br %"v481" ? "L477" : "L479" };
  ir_blk{ @"L477":
    %"v484" : L = (Ext Sw) %"pr.13";
    %"v485" : L = Div %"v6", %"v484"
    => goto "L479" };
  ir_blk{ @"L479" [%"v487" : L = phi("L477" => %"v485", "L471" => %"v6")]:
    %"v490" : L = Add %"pr.32", %"v487";
    %"v493" : L = Add %"pr.28", %"v6"
    => goto "L473" };
  ir_blk{ @"L473" [%"pr.30" : L = phi("L479" => %"v490", "L67" => %"pr.32"); %"pr.27" : L = phi("L479" => %"v493", "L67" => %"pr.28")]:
    %"chk27" : A = (Renew 0 8 Write 1) %"chk3", %"v0";
    store Wl [%"chk27" + 0] <- %"pr.27";
    %"chk28" : A = (Renew 0 8 Write 1) %"chk4", %"v2";
    store Wl [%"chk28" + 0] <- %"pr.30";
    %"chk29" : A = (Renew 0 4 Write 1) %"chk5", %"v4";
    store Ww [%"chk29" + 0] <- %"pr.38"
    => ret void }])) }.

Definition hi_fn_glibc_libc_start'23get_common_indices : func :=
  ir_fn{ "local" "glibc_libc_start#get_common_indices"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> RVoid {
  @"start":
    %"v16" : P = (Alloc 4) #4;
    %"v14" : L = Ptoi %"v2";
    %"v15" : W = (Cmp Ne L) %"v14", #0
    => br %"v15" ? "L10" : "L12";
  @"L10":
    %"v18" = %"v0" +p #20;
    %"v20" = %"v18" +p #4;
    %"v24" = %"v18" +p #8;
    %"v28" = %"v18" +p #12;
    call void $"zcpuid"(W #1, P %"v16", P %"v20", P %"v24", P %"v28");
    %"chk0" : A = (Check 0 4 Read 1) %"v16";
    %"v32" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk1" + 0] <- %"v32";
    %"v34" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v35" : W = Shr %"v34", #8;
    %"v36" : W = And %"v35", #15;
    %"chk3" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk3" + 0] <- %"v36";
    %"v38" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v39" : W = Shr %"v38", #4;
    %"v40" : W = And %"v39", #15;
    %"chk5" : A = (Check 0 4 Write 1) %"v4";
    store Ww [%"chk5" + 0] <- %"v40";
    %"v42" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v43" : W = Shr %"v42", #12;
    %"v44" : W = And %"v43", #240;
    %"chk7" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk7" + 0] <- %"v44";
    %"v46" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v47" : W = And %"v46", #15;
    %"chk9" : A = (Check 0 4 Write 1) %"v8";
    store Ww [%"chk9" + 0] <- %"v47";
    %"v52" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v53" : W = (Cmp Eq W) %"v52", #15
    => br %"v53" ? "L48" : "L12";
  @"L48":
    %"v55" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v56" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v57" : W = Shr %"v56", #20;
    %"v58" : W = And %"v57", #255;
    %"v59" : W = Add %"v55", %"v58";
    store Ww [%"chk3" + 0] <- %"v59";
    %"v61" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v63" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v64" : W = Add %"v61", %"v63";
    store Ww [%"chk5" + 0] <- %"v64"
    => goto "L12";
  @"L12":
    %"v69" = %"v0" +p #4;
    %"chk17" : A = (Check 0 4 Read 1) %"v69";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v71" : W = (Cmp Sge W) %"v70", #7
    => br %"v71" ? "L65" : "L67";
  @"L65":
    %"v73" = %"v0" +p #20;
    %"v74" = %"v73" +p #32;
    %"v78" = %"v74" +p #4;
    %"v82" = %"v74" +p #8;
    %"v86" = %"v74" +p #12;
    call void $"zcpuid_count"(W #7, W #0, P %"v74", P %"v78", P %"v82", P %"v86");
    %"v89" = %"v73" +p #192;
    %"v93" = %"v89" +p #4;
    %"v97" = %"v89" +p #8;
    %"v101" = %"v89" +p #12;
    call void $"zcpuid_count"(W #7, W #1, P %"v89", P %"v93", P %"v97", P %"v101")
    => goto "L67";
  @"L67":
    %"v106" = %"v0" +p #4;
    %"chk18" : A = (Renew 0 4 Read 1) %"chk17", %"v106";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v108" : W = (Cmp Sge W) %"v107", #13
    => br %"v108" ? "L102" : "L104";
  @"L102":
    %"v110" = %"v0" +p #20;
    %"v111" = %"v110" +p #96;
    %"v115" = %"v111" +p #4;
    %"v119" = %"v111" +p #8;
    %"v123" = %"v111" +p #12;
    call void $"zcpuid_count"(W #13, W #1, P %"v111", P %"v115", P %"v119", P %"v123")
    => goto "L104";
  @"L104":
    %"v128" = %"v0" +p #4;
    %"chk19" : A = (Renew 0 4 Read 1) %"chk17", %"v128";
    %"v129" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v130" : W = (Cmp Sge W) %"v129", #20
    => br %"v130" ? "L124" : "L126";
  @"L124":
    %"v132" = %"v0" +p #20;
    %"v133" = %"v132" +p #256;
    %"v137" = %"v133" +p #4;
    %"v141" = %"v133" +p #8;
    %"v145" = %"v133" +p #12;
    call void $"zcpuid_count"(W #20, W #0, P %"v133", P %"v137", P %"v141", P %"v145")
    => goto "L126";
  @"L126":
    %"v150" = %"v0" +p #4;
    %"chk20" : A = (Renew 0 4 Read 1) %"chk17", %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"v152" : W = (Cmp Sge W) %"v151", #25
    => br %"v152" ? "L146" : "iw_1.start";
  @"L146":
    %"v154" = %"v0" +p #20;
    %"v155" = %"v154" +p #224;
    %"v159" = %"v155" +p #4;
    %"v163" = %"v155" +p #8;
    %"v167" = %"v155" +p #12;
    call void $"zcpuid_count"(W #25, W #0, P %"v155", P %"v159", P %"v163", P %"v167")
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v40" : P = (Alloc 4) #4;
    %"iw_1.v41" : P = (Alloc 4) #4;
    %"iw_1.v42" : P = (Alloc 4) #4;
    %"iw_1.v43" : P = (Alloc 4) #4;
    %"iw_1.v5" : P = Copy $"_dl_minsigstacksize";
    %"chk21" : A = (Check 0 8 Read 1) %"iw_1.v5";
    %"iw_1.v6" : L = (RawLoad LdL 0) %"chk21";
    %"iw_1.v7" : W = (Cmp Ne L) %"iw_1.v6", #0
    => br %"iw_1.v7" ? "iw_1.join" : "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v13" = %"v0" +p #4;
    %"chk22" : A = (Renew 0 4 Read 1) %"chk17", %"iw_1.v13";
    %"iw_1.v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"iw_1.v15" : W = (Cmp Sge W) %"iw_1.v14", #13
    => br %"iw_1.v15" ? "iw_1.L16" : "iw_1.L17";
  @"iw_1.L16":
    %"iw_1.v19" = %"v0" +p #20;
    %"iw_1.v21" = %"iw_1.v19" +p #8;
    %"chk23" : A = (HalfCheck Upper 0 4 Read 1) %"chk17", %"iw_1.v21";
    %"iw_1.v22" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"iw_1.v24" : W = And %"iw_1.v22", #134217728;
    %"iw_1.v25" : W = (Cmp Ne W) %"iw_1.v24", #0
    => goto "iw_1.L17";
  @"iw_1.L17" [%"iw_1.v27" : W = phi("iw_1.L4" => #0, "iw_1.L16" => %"iw_1.v25")]:
    => br %"iw_1.v27" ? "iw_1.L9" : "iw_1.L10";
  @"iw_1.L9":
    call void $"zcpuid_count"(W #13, W #0, P %"iw_1.v40", P %"iw_1.v41", P %"iw_1.v42", P %"iw_1.v43");
    %"chk24" : A = (Check 0 4 Read 1) %"iw_1.v41";
    %"iw_1.v45" : W = (RawLoad (LdNarrow Uw) 0) %"chk24";
    %"iw_1.v46" : W = Add %"iw_1.v45", #512;
    %"iw_1.v48" : L = (Ext Uw) %"iw_1.v46";
    %"iw_1.v49" : L = Add %"iw_1.v48", #4;
    %"iw_1.v50" : P = Copy $"_dl_minsigstacksize";
    %"iw_1.v51" : W = Copy %"iw_1.v49";
    %"iw_1.v52" : L = (Ext Uw) %"iw_1.v51";
    %"chk25" : A = (Check 0 8 Write 1) %"iw_1.v50";
    store Wl [%"chk25" + 0] <- %"iw_1.v52"
    => goto "iw_1.join";
  @"iw_1.L10":
    %"iw_1.v53" : P = Copy $"_dl_minsigstacksize";
    %"chk26" : A = (Check 0 8 Write 1) %"iw_1.v53";
    store Wl [%"chk26" + 0] <- #2048
    => goto "iw_1.join";
  @"iw_1.join":
    => ret void
} }.

Definition hi_fn___getrandom_early_init : func :=
  ir_fn{ "export" "__getrandom_early_init"(W %"v0") -> RVoid {
  @"start":
    => ret void
} }.

Definition hi_fn___GI___getrlimit64 : func :=
  ir_fn{ "export" "__GI___getrlimit64"(W %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : W = $"zsys_getrlimit"(W %"v0", P %"v2")
    => ret %"v6"
} }.
