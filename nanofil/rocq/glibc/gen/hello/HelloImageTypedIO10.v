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

Definition hello_image_fn___GI__IO_wfile_seekoff : func :=
  ir_fn{ "export" "__GI__IO_wfile_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v331" : P = (Alloc 8) #144;
    %"v16" : W = (Cmp Eq W) %"v6", #0
    => br %"v16" ? "iw_1.start" : "L14" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v166" : P = (Alloc 4) #8;
    %"iw_1.v240" : P = (Alloc 8) #8;
    %"iw_1.v242" : P = (Alloc 8) #8;
    %"iw_1.v249" : P = (Alloc 4) #8;
    %"iw_1.v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" = %"iw_1.v9" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" : L = Ptoi %"iw_1.v11";
    %"iw_1.v13" : L = Ptoi #0;
    %"iw_1.v14" : W = (Cmp Ne L) %"iw_1.v12", %"iw_1.v13"
    => br %"iw_1.v14" ? "iw_1.L4" : "iw_1.L6" };
  ir_blk{ @"iw_1.L4":
    %"iw_1.v20" = %"v0" +p #160;
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v22" = %"iw_1.v21" +p #32;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v22";
    %"iw_1.v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v27" = %"iw_1.v26" +p #24;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v27";
    %"iw_1.v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v29" : L = Ptoi %"iw_1.v23";
    %"iw_1.v30" : L = Ptoi %"iw_1.v28";
    %"iw_1.v31" : W = (Cmp Ugt L) %"iw_1.v29", %"iw_1.v30";
    %"chk6" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    %"iw_1.v36" : W = And %"iw_1.v35", #4096;
    %"iw_1.v37" : W = (Cmp Eq W) %"iw_1.v36", #4096
    => br %"iw_1.v31" ? "iw_1.L43" : "iw_1.L44" };
  ir_blk{ @"iw_1.L43":
    => goto "iw_1.L44" };
  ir_blk{ @"iw_1.L44" [%"iw_1.v47" : W = phi("iw_1.L4" => #0, "iw_1.L43" => %"iw_1.v37")]:
    => br %"iw_1.v47" ? "iw_1.L39" : "iw_1.L41" };
  ir_blk{ @"iw_1.L39":
    %"iw_1.v49" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v49";
    %"iw_1.v50" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v50";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v52" = %"iw_1.v50" +p #128;
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v52";
    %"iw_1.v53" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"iw_1.v53";
    rawcall %"iw_1.v55" : L = %"chk9"(P %"v0", L #0, W #2);
    %"iw_1.v62" : W = (Cmp Eq L) %"iw_1.v55", #18446744073709551615
    => br %"iw_1.v62" ? "iw_1.join" : "iw_1.L57" };
  ir_blk{ @"iw_1.L57":
    %"iw_1.v67" = %"v0" +p #144;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"iw_1.v67";
    store Wl [%"chk10" + 0] <- %"iw_1.v55"
    => goto "iw_1.L41" };
  ir_blk{ @"iw_1.L41":
    %"chk11" : A = (Renew 0 4 Read 1) %"chk6", %"v0";
    %"iw_1.v73" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"iw_1.v74" : W = And %"iw_1.v73", #256
    => br %"iw_1.v74" ? "iw_1.L69" : "iw_1.L70" };
  ir_blk{ @"iw_1.L69":
    %"iw_1.v79" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Read 8) %"iw_1.v80";
    %"iw_1.v81" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v84" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v85" = %"iw_1.v84" +p #8;
    %"chk15" : A = (Check 0 8 Read 8) %"iw_1.v85";
    %"iw_1.v86" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_1.v87" : L = Ptoi %"iw_1.v81";
    %"iw_1.v88" : L = Ptoi %"iw_1.v86";
    %"iw_1.v89" : W = (Cmp Ult L) %"iw_1.v87", %"iw_1.v88"
    => br %"iw_1.v89" ? "iw_1.L75" : "iw_1.L77" };
  ir_blk{ @"iw_1.L75":
    %"iw_1.v90" : P = Copy $"__libc_errno";
    %"chk16" : A = (Check 0 4 Write 1) %"iw_1.v90";
    store Ww [%"chk16" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L77":
    %"iw_1.v95" = %"v0" +p #160;
    %"iw_1.v96" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v97" = %"iw_1.v96" +p #64;
    %"chk18" : A = (Check 0 8 Read 8) %"iw_1.v97";
    %"iw_1.v98" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"iw_1.v102" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v103" = %"iw_1.v102" +p #80;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_1.v103";
    %"iw_1.v104" : P = (RawLoadPointer 0 load_effects) %"chk20"
    => goto "iw_1.L71" };
  ir_blk{ @"iw_1.L70":
    %"iw_1.v106" = %"v0" +p #160;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v106";
    %"iw_1.v107" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v108" = %"iw_1.v107" +p #16;
    %"chk22" : A = (Check 0 8 Read 8) %"iw_1.v108";
    %"iw_1.v109" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_1.v112" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk24" : A = (Check 0 8 Read 8) %"iw_1.v112";
    %"iw_1.v113" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v116" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_1.v117" = %"iw_1.v116" +p #8;
    %"chk26" : A = (Check 0 8 Read 8) %"iw_1.v117";
    %"iw_1.v118" : P = (RawLoadPointer 0 load_effects) %"chk26"
    => goto "iw_1.L71" };
  ir_blk{ @"iw_1.L71" [%"iw_1.pr.9" : P = phi("iw_1.L70" => %"iw_1.v118", "iw_1.L77" => %"iw_1.v104"); %"iw_1.pr.8" : P = phi("iw_1.L70" => %"iw_1.v113", "iw_1.L77" => %"iw_1.v98"); %"iw_1.pr.7" : P = phi("iw_1.L70" => %"iw_1.v109", "iw_1.L77" => %"iw_1.v98")]:
    %"iw_1.v121" = %"v0" +p #152;
    %"chk27" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v121";
    %"iw_1.v122" : P = (RawLoadPointer 0 load_effects) %"chk27";
    call %"iw_1.v125" : W = $"__libio_codecvt_encoding"(P %"iw_1.v122");
    %"iw_1.v130" : W = (Cmp Ule L) %"iw_1.v29", %"iw_1.v30"
    => br %"iw_1.v130" ? "iw_1.L126" : "iw_1.L127" };
  ir_blk{ @"iw_1.L126":
    %"iw_1.v135" : W = (Cmp Sgt W) %"iw_1.v125", #0
    => br %"iw_1.v135" ? "iw_1.L131" : "iw_1.L132" };
  ir_blk{ @"iw_1.L131":
    %"iw_1.v139" : L = Ptoi %"iw_1.pr.9";
    %"iw_1.v140" : L = Ptoi %"iw_1.pr.8";
    %"iw_1.v141" : L = Sub %"iw_1.v139", %"iw_1.v140";
    %"iw_1.v142" : L = Div %"iw_1.v141", #4;
    %"iw_1.v144" : L = (Ext Sw) %"iw_1.v125";
    %"iw_1.v145" : L = Mul %"iw_1.v142", %"iw_1.v144";
    %"iw_1.v146" : L = Sub #0, %"iw_1.v145";
    %"iw_1.v149" = %"v0" +p #16;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v149";
    %"iw_1.v150" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_1.v152" = %"v0" +p #8;
    %"chk29" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v152";
    %"iw_1.v153" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_1.v154" : L = Ptoi %"iw_1.v150";
    %"iw_1.v155" : L = Ptoi %"iw_1.v153";
    %"iw_1.v156" : L = Sub %"iw_1.v154", %"iw_1.v155";
    %"iw_1.v157" : L = Sub %"iw_1.v146", %"iw_1.v156"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L132":
    %"iw_1.v162" : L = Ptoi %"iw_1.pr.8";
    %"iw_1.v163" : L = Ptoi %"iw_1.pr.7";
    %"iw_1.v164" : L = Sub %"iw_1.v162", %"iw_1.v163";
    %"iw_1.v165" : L = Div %"iw_1.v164", #4;
    %"iw_1.v168" = %"v0" +p #160;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v168";
    %"iw_1.v169" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_1.v170" = %"iw_1.v169" +p #96;
    %"chk31" : A = (Check 0 8 Read 1) %"iw_1.v170";
    %"iw_1.v171" : L = (RawLoad LdL 0) %"chk31";
    %"chk32" : A = (Check 0 8 Write 1) %"iw_1.v166";
    store Wl [%"chk32" + 0] <- %"iw_1.v171";
    %"iw_1.v174" = %"v0" +p #24;
    %"chk33" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v174";
    %"iw_1.v175" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"iw_1.v177" = %"v0" +p #16;
    %"chk34" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v177";
    %"iw_1.v178" : P = (RawLoadPointer 0 load_effects) %"chk34";
    call %"iw_1.v180" : W = $"__libio_codecvt_length"(P %"iw_1.v122", P %"iw_1.v166", P %"iw_1.v175", P %"iw_1.v178", L %"iw_1.v165");
    %"chk35" : A = (Renew 0 8 Read 8) %"chk34", %"iw_1.v177";
    %"iw_1.v184" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Read 8) %"chk33", %"iw_1.v174";
    %"iw_1.v187" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_1.v188" : L = Ptoi %"iw_1.v184";
    %"iw_1.v189" : L = Ptoi %"iw_1.v187";
    %"iw_1.v190" : L = Sub %"iw_1.v188", %"iw_1.v189";
    %"iw_1.v192" : L = (Ext Sw) %"iw_1.v180";
    %"iw_1.v193" : L = Sub %"iw_1.v190", %"iw_1.v192";
    %"iw_1.v194" : L = Sub #0, %"iw_1.v193"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L127":
    %"iw_1.v199" : W = (Cmp Sgt W) %"iw_1.v125", #0
    => br %"iw_1.v199" ? "iw_1.L195" : "iw_1.L196" };
  ir_blk{ @"iw_1.L195":
    %"iw_1.v202" = %"v0" +p #160;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v202";
    %"iw_1.v203" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_1.v204" = %"iw_1.v203" +p #32;
    %"chk38" : A = (Check 0 8 Read 8) %"iw_1.v204";
    %"iw_1.v205" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"iw_1.v208" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_1.v209" = %"iw_1.v208" +p #24;
    %"chk40" : A = (Check 0 8 Read 8) %"iw_1.v209";
    %"iw_1.v210" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"iw_1.v211" : L = Ptoi %"iw_1.v205";
    %"iw_1.v212" : L = Ptoi %"iw_1.v210";
    %"iw_1.v213" : L = Sub %"iw_1.v211", %"iw_1.v212";
    %"iw_1.v214" : L = Div %"iw_1.v213", #4;
    %"iw_1.v216" : L = (Ext Sw) %"iw_1.v125";
    %"iw_1.v217" : L = Mul %"iw_1.v214", %"iw_1.v216"
    => goto "iw_1.L197" };
  ir_blk{ @"iw_1.L196":
    %"iw_1.v221" = %"v0" +p #160;
    %"chk41" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v222" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_1.v223" = %"iw_1.v222" +p #32;
    %"chk42" : A = (Check 0 8 Read 8) %"iw_1.v223";
    %"iw_1.v224" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"iw_1.v227" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_1.v228" = %"iw_1.v227" +p #24;
    %"chk44" : A = (Check 0 8 Read 8) %"iw_1.v228";
    %"iw_1.v229" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"iw_1.v230" : L = Ptoi %"iw_1.v224";
    %"iw_1.v231" : L = Ptoi %"iw_1.v229";
    %"iw_1.v232" : L = Sub %"iw_1.v230", %"iw_1.v231";
    %"iw_1.v233" : L = Div %"iw_1.v232", #4;
    %"iw_1.v236" : L = Shl %"iw_1.v233", #2;
    call %"iw_1.v239" : P = $"malloc"(L %"iw_1.v236");
    %"chk45" : A = (Check 0 8 Write 8) %"iw_1.v240";
    store.ptr [%"chk45" + 0] <- %"iw_1.v239";
    %"chk46" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v245" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"iw_1.v246" = %"iw_1.v245" +p #24;
    %"chk47" : A = (Check 0 8 Read 8) %"iw_1.v246";
    %"iw_1.v247" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 8 Write 8) %"iw_1.v242";
    store.ptr [%"chk48" + 0] <- %"iw_1.v247";
    %"chk49" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v221";
    %"iw_1.v252" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_1.v253" = %"iw_1.v252" +p #96;
    %"chk50" : A = (Check 0 8 Read 1) %"iw_1.v253";
    %"iw_1.v254" : L = (RawLoad LdL 0) %"chk50";
    %"chk51" : A = (Check 0 8 Write 1) %"iw_1.v249";
    store Wl [%"chk51" + 0] <- %"iw_1.v254";
    %"chk52" : A = (Renew 0 8 Read 8) %"chk48", %"iw_1.v242";
    %"iw_1.v256" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v257" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"iw_1.v260" = %"iw_1.v257" +p %"iw_1.v236";
    %"iw_1.v264" = %"iw_1.v239" +p %"iw_1.v236";
    call %"iw_1.v265" : W = $"__libio_codecvt_out"(P %"iw_1.v122", P %"iw_1.v249", P %"iw_1.v256", P %"iw_1.v260", P %"iw_1.v242", P %"iw_1.v239", P %"iw_1.v264", P %"iw_1.v240");
    %"iw_1.v270" : W = (Cmp Ne W) %"iw_1.v265", #0
    => br %"iw_1.v270" ? "iw_1.L266" : "iw_1.L268" };
  ir_blk{ @"iw_1.L266":
    call void $"free"(P %"iw_1.v239")
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L268":
    %"chk54" : A = (Renew 0 8 Read 8) %"chk45", %"iw_1.v240";
    %"iw_1.v276" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"iw_1.v278" : L = Ptoi %"iw_1.v276";
    %"iw_1.v279" : L = Ptoi %"iw_1.v239";
    %"iw_1.v280" : L = Sub %"iw_1.v278", %"iw_1.v279";
    call void $"free"(P %"iw_1.v239")
    => goto "iw_1.L197" };
  ir_blk{ @"iw_1.L197" [%"iw_1.pr.4" : L = phi("iw_1.L195" => %"iw_1.v217", "iw_1.L268" => %"iw_1.v280")]:
    => br %"iw_1.v37" ? "iw_1.L283" : "iw_1.L284" };
  ir_blk{ @"iw_1.L283":
    %"iw_1.v289" = %"v0" +p #40;
    %"chk55" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v289";
    %"iw_1.v290" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"iw_1.v292" = %"v0" +p #32;
    %"chk56" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v292";
    %"iw_1.v293" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"iw_1.v294" : L = Ptoi %"iw_1.v290";
    %"iw_1.v295" : L = Ptoi %"iw_1.v293";
    %"iw_1.v296" : L = Sub %"iw_1.v294", %"iw_1.v295";
    %"iw_1.v297" : L = Add %"iw_1.pr.4", %"iw_1.v296"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L284":
    %"iw_1.v300" = %"v0" +p #40;
    %"chk57" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v300";
    %"iw_1.v301" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"iw_1.v303" = %"v0" +p #16;
    %"chk58" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v303";
    %"iw_1.v304" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"iw_1.v305" : L = Ptoi %"iw_1.v301";
    %"iw_1.v306" : L = Ptoi %"iw_1.v304";
    %"iw_1.v307" : L = Sub %"iw_1.v305", %"iw_1.v306";
    %"iw_1.v308" : L = Add %"iw_1.pr.4", %"iw_1.v307"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L6" [%"iw_1.pr.6" : L = phi("iw_1.L131" => %"iw_1.v157", "iw_1.L132" => %"iw_1.v194", "iw_1.L283" => %"iw_1.v297", "iw_1.L284" => %"iw_1.v308", "iw_1.start" => #0)]:
    %"iw_1.v313" = %"v0" +p #144;
    %"chk59" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"iw_1.v313";
    %"iw_1.v314" : L = (RawLoad LdL 0) %"chk59";
    %"iw_1.v317" : W = (Cmp Ne L) %"iw_1.v314", #18446744073709551615
    => br %"iw_1.v317" ? "iw_1.L309" : "iw_1.L310" };
  ir_blk{ @"iw_1.L309":
    %"iw_1.v319" = %"v0" +p #144;
    %"iw_1.v320" : L = (RawLoad LdL 0) %"chk59"
    => goto "iw_1.L311" };
  ir_blk{ @"iw_1.L310":
    %"iw_1.v322" = %"v0" +p #216;
    %"chk61" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v322";
    %"iw_1.v323" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"iw_1.iw_2.v4" : L = Ptoi %"iw_1.v323";
    %"iw_1.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_2.v8" : L = Ptoi %"iw_1.iw_2.v7";
    %"iw_1.iw_2.v9" : L = Sub %"iw_1.iw_2.v4", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v15" : W = (Cmp Uge L) %"iw_1.iw_2.v9", #2352
    => br %"iw_1.iw_2.v15" ? "iw_1.iw_2.L10" : "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.join":
    %"iw_1.v325" = %"iw_1.v323" +p #128;
    %"chk62" : A = (Check 0 8 Read 8) %"iw_1.v325";
    %"iw_1.v326" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : F = CheckFunction %"iw_1.v326";
    rawcall %"iw_1.v328" : L = %"chk63"(P %"v0", L #0, W #1)
    => goto "iw_1.L311" };
  ir_blk{ @"iw_1.L311" [%"iw_1.pr.1" : L = phi("iw_1.L309" => %"iw_1.v320", "iw_1.iw_2.join" => %"iw_1.v328")]:
    %"iw_1.v335" : W = (Cmp Eq L) %"iw_1.pr.1", #18446744073709551615
    => br %"iw_1.v335" ? "iw_1.join" : "iw_1.L331" };
  ir_blk{ @"iw_1.L331":
    %"iw_1.v340" : L = Add %"iw_1.pr.1", %"iw_1.pr.6";
    %"iw_1.v345" : W = (Cmp Slt L) %"iw_1.v340", #0
    => br %"iw_1.v345" ? "iw_1.L341" : "iw_1.join" };
  ir_blk{ @"iw_1.L341":
    %"iw_1.v346" : P = Copy $"__libc_errno";
    %"chk64" : A = (Check 0 4 Write 1) %"iw_1.v346";
    store Ww [%"chk64" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v18" : L = phi("iw_1.L75" => #18446744073709551615, "iw_1.L266" => #4294967295, "iw_1.L341" => #18446744073709551615, "iw_1.iw_1.join" => #18446744073709551615, "iw_1.L311" => %"iw_1.pr.1", "iw_1.L331" => %"iw_1.v340")]:
    => ret %"v18" };
  ir_blk{ @"L14":
    %"v22" = %"v0" +p #160;
    %"chk65" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v24" = %"v23" +p #16;
    %"chk66" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v29" = %"v28" +p #8;
    %"chk68" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"v31" : L = Ptoi %"v25";
    %"v32" : L = Ptoi %"v30";
    %"v33" : W = (Cmp Eq L) %"v31", %"v32"
    => br %"v33" ? "L34" : "L35" };
  ir_blk{ @"L34":
    %"v37" = %"v0" +p #160;
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v39" = %"v38" +p #24;
    %"chk70" : A = (Check 0 8 Read 8) %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v44" = %"v43" +p #32;
    %"chk72" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v46" : L = Ptoi %"v40";
    %"v47" : L = Ptoi %"v45";
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => goto "L35" };
  ir_blk{ @"L35" [%"v50" : W = phi("L14" => #0, "L34" => %"v48")]:
    %"v53" = %"v0" +p #160;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v55" = %"v54" +p #32;
    %"chk74" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk74";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v60" = %"v59" +p #24;
    %"chk76" : A = (Check 0 8 Read 8) %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v62" : L = Ptoi %"v56";
    %"v63" : L = Ptoi %"v61";
    %"v64" : W = (Cmp Ugt L) %"v62", %"v63"
    => br %"v64" ? "L66" : "L65" };
  ir_blk{ @"L65":
    %"chk77" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v68" : W = (RawLoad (LdNarrow Sw) 0) %"chk77";
    %"v69" : W = And %"v68", #2048;
    %"v70" : W = (Cmp Ne W) %"v69", #0
    => goto "L66" };
  ir_blk{ @"L66" [%"v71" : W = phi("L35" => #1, "L65" => %"v70")]:
    => br %"v71" ? "L77" : "L78" };
  ir_blk{ @"L77":
    call %"v80" : W = $"__GI__IO_switch_to_wget_mode"(P %"v0");
    %"v81" : W = (Cmp Ne W) %"v80", #0
    => goto "L78" };
  ir_blk{ @"L78" [%"v82" : W = phi("L66" => #0, "L77" => %"v81")]:
    => br %"v82" ? "L73" : "L75" };
  ir_blk{ @"L73":
    => ret #4294967295 };
  ir_blk{ @"L75":
    %"v88" = %"v0" +p #160;
    %"chk78" : A = (Renew 0 8 Read 8) %"chk65", %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v90" = %"v89" +p #48;
    %"chk79" : A = (Check 0 8 Read 8) %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v92" : L = Ptoi %"v91";
    %"v93" : L = Ptoi #0;
    %"v94" : W = (Cmp Eq L) %"v92", %"v93"
    => br %"v94" ? "L84" : "L192" };
  ir_blk{ @"L84":
    %"v99" = %"v0" +p #160;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v101" = %"v100" +p #16;
    %"chk81" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"v103" : L = Ptoi %"v102";
    %"v105" : W = (Cmp Ne L) %"v103", %"v93"
    => br %"v105" ? "L95" : "L97" };
  ir_blk{ @"L95":
    %"v107" = %"v0" +p #160;
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v109" = %"v108" +p #16;
    %"chk83" : A = (Check 0 8 Read 8) %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk83";
    call void $"free"(P %"v110");
    %"chk84" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v112" : W = (RawLoad (LdNarrow Sw) 0) %"chk84";
    %"v114" : W = And %"v112", #4294967039;
    %"chk85" : A = (Renew 0 4 Write 1) %"chk84", %"v0";
    store Ww [%"chk85" + 0] <- %"v114"
    => goto "L97" };
  ir_blk{ @"L97":
    code ((app ir[ call void $"__GI__IO_doallocbuf"(P %"v0");
      %"v117" = %"v0" +p #32;
      %"v119" = %"v0" +p #40;
      %"v121" = %"v0" +p #56;
      %"chk86" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v121";
      %"v122" : P = (RawLoadPointer 0 load_effects) %"chk86";
      %"chk87" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v119";
      store.ptr [%"chk87" + 0] <- %"v122";
      %"chk88" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v117";
      store.ptr [%"chk88" + 0] <- %"v122";
      %"v124" = %"v0" +p #48;
      %"chk89" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v127" : P = (RawLoadPointer 0 load_effects) %"chk89";
      %"chk90" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v124";
      store.ptr [%"chk90" + 0] <- %"v127";
      %"v129" = %"v0" +p #24;
      %"chk91" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v132" : P = (RawLoadPointer 0 load_effects) %"chk91";
      %"chk92" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v129";
      store.ptr [%"chk92" + 0] <- %"v132";
      %"v134" = %"v0" +p #8;
      %"chk93" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v137" : P = (RawLoadPointer 0 load_effects) %"chk93";
      %"chk94" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v134";
      store.ptr [%"chk94" + 0] <- %"v137";
      %"v139" = %"v0" +p #16;
      %"chk95" : A = (Renew 0 8 Read 8) %"chk86", %"v121";
      %"v142" : P = (RawLoadPointer 0 load_effects) %"chk95";
      %"chk96" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v139";
      store.ptr [%"chk96" + 0] <- %"v142";
      %"v144" = %"v0" +p #160;
      %"chk97" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v145" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v146" = %"v145" +p #24;
      %"v149" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v150" = %"v149" +p #32;
      %"v153" : P = (RawLoadPointer 0 load_effects) %"chk97";
      %"v154" = %"v153" +p #48;
      %"chk100" : A = (Check 0 8 Read 8) %"v154"] ir[ %"v155" : P = (RawLoadPointer 0 load_effects) %"chk100";
      %"chk101" : A = (Check 0 8 Write 8) %"v150";
      store.ptr [%"chk101" + 0] <- %"v155";
      %"chk102" : A = (Check 0 8 Write 8) %"v146";
      store.ptr [%"chk102" + 0] <- %"v155";
      %"chk103" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v158" : P = (RawLoadPointer 0 load_effects) %"chk103";
      %"v159" = %"v158" +p #40;
      %"v162" : P = (RawLoadPointer 0 load_effects) %"chk103";
      %"v163" = %"v162" +p #48;
      %"chk105" : A = (Check 0 8 Read 8) %"v163";
      %"v164" : P = (RawLoadPointer 0 load_effects) %"chk105";
      %"chk106" : A = (Check 0 8 Write 8) %"v159";
      store.ptr [%"chk106" + 0] <- %"v164";
      %"chk107" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v167" : P = (RawLoadPointer 0 load_effects) %"chk107";
      %"v168" = %"v167" +p #16;
      %"v171" : P = (RawLoadPointer 0 load_effects) %"chk107";
      %"v172" = %"v171" +p #48;
      %"chk109" : A = (Check 0 8 Read 8) %"v172";
      %"v173" : P = (RawLoadPointer 0 load_effects) %"chk109";
      %"chk110" : A = (Check 0 8 Write 8) %"v168";
      store.ptr [%"chk110" + 0] <- %"v173";
      %"chk111" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v176" : P = (RawLoadPointer 0 load_effects) %"chk111";
      %"v179" : P = (RawLoadPointer 0 load_effects) %"chk111";
      %"v180" = %"v179" +p #48;
      %"chk113" : A = (Check 0 8 Read 8) %"v180";
      %"v181" : P = (RawLoadPointer 0 load_effects) %"chk113";
      %"chk114" : A = (Check 0 8 Write 8) %"v176";
      store.ptr [%"chk114" + 0] <- %"v181";
      %"chk115" : A = (Renew 0 8 Read 8) %"chk65", %"v144";
      %"v184" : P = (RawLoadPointer 0 load_effects) %"chk115";
      %"v185" = %"v184" +p #8;
      %"v188" : P = (RawLoadPointer 0 load_effects) %"chk115";
      %"v189" = %"v188" +p #48;
      %"chk117" : A = (Check 0 8 Read 8) %"v189";
      %"v190" : P = (RawLoadPointer 0 load_effects) %"chk117";
      %"chk118" : A = (Check 0 8 Write 8) %"v185";
      store.ptr [%"chk118" + 0] <- %"v190"]))
    => goto "L192" };
  ir_blk{ @"L196":
    %"v198" = %"v0" +p #152;
    %"chk119" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk119";
    call %"v201" : W = $"__libio_codecvt_encoding"(P %"v199");
    %"v206" : W = (Cmp Ne W) %"v6", #0
    => br %"v206" ? "L208" : "L207" };
  ir_blk{ @"L207":
    %"v210" : W = (Cmp Eq W) %"v71", #0
    => goto "L208" };
  ir_blk{ @"L208" [%"v212" : W = phi("L196" => #1, "L207" => %"v210")]:
    => br %"v212" ? "L202" : "L204" };
  ir_blk{ @"L202":
    %"v217" : W = (Cmp Sgt W) %"v201", #0
    => br %"v217" ? "L213" : "L214" };
  ir_blk{ @"L213":
    %"v220" = %"v0" +p #160;
    %"chk120" : A = (Renew 0 8 Read 8) %"chk65", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"v222" = %"v221" +p #8;
    %"chk121" : A = (Check 0 8 Read 8) %"v222";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk121";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"chk123" : A = (Check 0 8 Read 8) %"v226";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk123";
    %"v228" : L = Ptoi %"v223";
    %"v229" : L = Ptoi %"v227";
    %"v230" : L = Sub %"v228", %"v229";
    %"v231" : L = Div %"v230", #4;
    %"v233" : L = (Ext Sw) %"v201";
    %"v234" : L = Mul %"v231", %"v233";
    %"v235" : L = Sub %"v2", %"v234";
    %"v238" = %"v0" +p #16;
    %"chk124" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v238";
    %"v239" : P = (RawLoadPointer 0 load_effects) %"chk124";
    %"v241" = %"v0" +p #8;
    %"chk125" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk125";
    %"v243" : L = Ptoi %"v239";
    %"v244" : L = Ptoi %"v242";
    %"v245" : L = Sub %"v243", %"v244";
    %"v246" : L = Sub %"v235", %"v245"
    => goto "L204" };
  ir_blk{ @"L214":
    %"v249" = %"v0" +p #160;
    %"chk126" : A = (Renew 0 8 Read 8) %"chk65", %"v249";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"chk127" : A = (Check 0 8 Read 8) %"v250";
    %"v251" : P = (RawLoadPointer 0 load_effects) %"chk127";
    %"v254" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v255" = %"v254" +p #16;
    %"chk129" : A = (Check 0 8 Read 8) %"v255";
    %"v256" : P = (RawLoadPointer 0 load_effects) %"chk129";
    %"v257" : L = Ptoi %"v251";
    %"v258" : L = Ptoi %"v256";
    %"v259" : L = Sub %"v257", %"v258";
    %"v260" : L = Div %"v259", #4;
    %"v263" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v264" = %"v263" +p #88;
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v268" = %"v267" +p #96;
    %"chk132" : A = (Check 0 8 Read 1) %"v268";
    %"v269" : L = (RawLoad LdL 0) %"chk132";
    %"chk133" : A = (Check 0 8 Write 1) %"v264";
    store Wl [%"chk133" + 0] <- %"v269";
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v274" = %"v273" +p #88;
    %"v276" = %"v0" +p #24;
    %"chk135" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v276";
    %"v277" : P = (RawLoadPointer 0 load_effects) %"chk135";
    %"v279" = %"v0" +p #16;
    %"chk136" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v279";
    %"v280" : P = (RawLoadPointer 0 load_effects) %"chk136";
    call %"v282" : W = $"__libio_codecvt_length"(P %"v199", P %"v274", P %"v277", P %"v280", L %"v260");
    %"v284" = %"v0" +p #8;
    %"chk137" : A = (Renew 0 8 Read 8) %"chk135", %"v276";
    %"v287" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"v289" : L = (Ext Sw) %"v282";
    %"v290" = %"v287" +p %"v289";
    %"chk138" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v284";
    store.ptr [%"chk138" + 0] <- %"v290";
    %"chk139" : A = (Renew 0 8 Read 8) %"chk65", %"v249";
    %"v293" : P = (RawLoadPointer 0 load_effects) %"chk139";
    %"v294" = %"v293" +p #8;
    %"v297" : P = (RawLoadPointer 0 load_effects) %"chk139";
    %"chk141" : A = (Check 0 8 Read 8) %"v297";
    %"v298" : P = (RawLoadPointer 0 load_effects) %"chk141";
    %"chk142" : A = (Check 0 8 Write 8) %"v294";
    store.ptr [%"chk142" + 0] <- %"v298";
    %"chk143" : A = (Renew 0 8 Read 8) %"chk136", %"v279";
    %"v302" : P = (RawLoadPointer 0 load_effects) %"chk143";
    %"chk144" : A = (Renew 0 8 Read 8) %"chk135", %"v276";
    %"v305" : P = (RawLoadPointer 0 load_effects) %"chk144";
    %"v306" : L = Ptoi %"v302";
    %"v307" : L = Ptoi %"v305";
    %"v308" : L = Sub %"v306", %"v307";
    %"v311" : L = Sub %"v308", %"v289";
    %"v312" : L = Sub %"v2", %"v311"
    => goto "L204" };
  ir_blk{ @"L204" [%"pr.2" : L = phi("L213" => %"v246", "L214" => %"v312", "L208" => %"v2")]:
    %"v317" = %"v0" +p #144;
    %"chk145" : A = (HalfCheck Lower 0 8 Read 1) %"chk65", %"v317";
    %"v318" : L = (RawLoad LdL 0) %"chk145";
    %"v321" : W = (Cmp Eq L) %"v318", #18446744073709551615
    => br %"v321" ? "L322" : "L315" };
  ir_blk{ @"L315":
    %"v326" = %"v0" +p #144;
    %"v327" : L = (RawLoad LdL 0) %"chk145";
    %"v328" : L = Add %"pr.2", %"v327"
    => goto "L193" };
  ir_blk{ @"L330":
    %"v336" = %"v0" +p #216;
    %"chk147" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v336";
    %"v337" : P = (RawLoadPointer 0 load_effects) %"chk147";
    %"iw_2.v4" : L = Ptoi %"v337";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join" }] [ir_blk{ @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"v339" = %"v337" +p #144;
    %"chk148" : A = (Check 0 8 Read 8) %"v339";
    %"v340" : P = (RawLoadPointer 0 load_effects) %"chk148";
    %"chk149" : F = CheckFunction %"v340";
    rawcall %"v342" : W = %"chk149"(P %"v0", P %"v331");
    %"v343" : W = (Cmp Eq W) %"v342", #0
    => br %"v343" ? "L344" : "L345" };
  ir_blk{ @"L344":
    %"v346" = %"v331" +p #24;
    %"chk150" : A = (Check 0 4 Read 1) %"v346";
    %"v347" : W = (RawLoad (LdNarrow Uw) 0) %"chk150";
    %"v348" : W = And %"v347", #61440;
    %"v349" : W = (Cmp Eq W) %"v348", #32768
    => goto "L345" };
  ir_blk{ @"L345" [%"v351" : W = phi("iw_2.join" => #0, "L344" => %"v349")]:
    => br %"v351" ? "L332" : "L322" };
  ir_blk{ @"L332":
    %"v353" = %"v331" +p #48;
    %"chk151" : A = (Check 0 8 Read 1) %"v353";
    %"v354" : L = (RawLoad LdL 0) %"chk151";
    %"v355" : L = Add %"v2", %"v354"
    => goto "L193" };
  ir_blk{ @"L192":
    %"v356" : W = (Cmp Eq W) %"v4", #1
    => br %"v356" ? poll "L196" : "L357" };
  ir_blk{ @"L357":
    %"v358" : W = (Cmp Eq W) %"v4", #0
    => br %"v358" ? "L193" : "L359" };
  ir_blk{ @"L359":
    %"v360" : W = (Cmp Eq W) %"v4", #2
    => br %"v360" ? poll "L330" : "L193" };
  ir_blk{ @"L193" [%"pr.5" : W = phi("L315" => #0, "L357" => %"v4", "L332" => #0, "L359" => %"v4"); %"pr.1" : L = phi("L315" => %"v328", "L357" => %"v2", "L332" => %"v355", "L359" => %"v2")]:
    call void $"__GI__IO_free_wbackup_area"(P %"v0");
    %"v367" = %"v0" +p #144;
    %"chk152" : A = (HalfCheck Lower 0 8 Read 1) %"chk65", %"v367";
    %"v368" : L = (RawLoad LdL 0) %"chk152";
    %"v371" : W = (Cmp Ne L) %"v368", #18446744073709551615
    => br %"v371" ? "L372" : "L373" };
  ir_blk{ @"L372":
    %"v375" = %"v0" +p #24;
    %"chk153" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v375";
    %"v376" : P = (RawLoadPointer 0 load_effects) %"chk153";
    %"v377" : L = Ptoi %"v376";
    %"v379" : W = (Cmp Ne L) %"v377", %"v93"
    => goto "L373" };
  ir_blk{ @"L373" [%"v381" : W = phi("L193" => #0, "L372" => %"v379")]:
    => br %"v381" ? "L382" : "L383" };
  ir_blk{ @"L382":
    %"chk154" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v385" : W = (RawLoad (LdNarrow Sw) 0) %"chk154";
    %"v386" : W = And %"v385", #256;
    %"v387" : W = (Cmp Eq W) %"v386", #0
    => goto "L383" };
  ir_blk{ @"L383" [%"v389" : W = phi("L373" => #0, "L382" => %"v387")]:
    => br %"v389" ? "L363" : "L365" };
  ir_blk{ @"L363":
    %"v392" = %"v0" +p #144;
    %"v393" : L = (RawLoad LdL 0) %"chk152";
    %"v395" = %"v0" +p #16;
    %"chk156" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v395";
    %"v396" : P = (RawLoadPointer 0 load_effects) %"chk156";
    %"v398" = %"v0" +p #56;
    %"v399" : P = (RawLoadPointer 40 load_effects) %"chk156";
    %"v400" : L = Ptoi %"v396";
    %"v401" : L = Ptoi %"v399";
    %"v402" : L = Sub %"v400", %"v401";
    %"v403" : L = Sub %"v393", %"v402";
    %"v409" : W = (Cmp Sge L) %"pr.1", %"v403"
    => br %"v409" ? "L410" : "L411" };
  ir_blk{ @"L410":
    %"v414" = %"v0" +p #144;
    %"v415" : L = (RawLoad LdL 0) %"chk152";
    %"v416" : W = (Cmp Slt L) %"pr.1", %"v415"
    => goto "L411" };
  ir_blk{ @"L411" [%"v418" : W = phi("L363" => #0, "L410" => %"v416")]:
    => br %"v418" ? "L404" : "L365" };
  ir_blk{ @"L404":
    code ((app ir[ %"v420" = %"v0" +p #24;
      %"v422" = %"v0" +p #56;
      %"v423" : P = (RawLoadPointer 40 load_effects) %"chk156";
      %"chk160" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v420";
      store.ptr [%"chk160" + 0] <- %"v423";
      %"v425" = %"v0" +p #8;
      %"chk161" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v422";
      %"v428" : P = (RawLoadPointer 0 load_effects) %"chk161";
      %"v431" : L = Sub %"pr.1", %"v403";
      %"v432" = %"v428" +p %"v431";
      %"chk162" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v425";
      store.ptr [%"chk162" + 0] <- %"v432";
      %"v434" = %"v0" +p #16;
      %"chk163" : A = (Renew 0 8 Read 8) %"chk156", %"v434";
      %"v437" : P = (RawLoadPointer 0 load_effects) %"chk163";
      %"chk164" : A = (Renew 0 8 Write 8) %"chk156", %"v434";
      store.ptr [%"chk164" + 0] <- %"v437";
      %"v439" = %"v0" +p #32;
      %"v441" = %"v0" +p #40;
      %"chk165" : A = (Renew 0 8 Read 8) %"chk161", %"v422";
      %"v444" : P = (RawLoadPointer 0 load_effects) %"chk165";
      %"chk166" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v441";
      store.ptr [%"chk166" + 0] <- %"v444";
      %"chk167" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v439";
      store.ptr [%"chk167" + 0] <- %"v444";
      %"v446" = %"v0" +p #48;
      %"chk168" : A = (Renew 0 8 Read 8) %"chk161", %"v422";
      %"v449" : P = (RawLoadPointer 0 load_effects) %"chk168";
      %"chk169" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v446";
      store.ptr [%"chk169" + 0] <- %"v449";
      %"v451" = %"v0" +p #160;
      %"chk170" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v452" : P = (RawLoadPointer 0 load_effects) %"chk170";
      %"v453" = %"v452" +p #16;
      %"v456" : P = (RawLoadPointer 0 load_effects) %"chk170";
      %"v457" = %"v456" +p #48;
      %"chk172" : A = (Check 0 8 Read 8) %"v457";
      %"v458" : P = (RawLoadPointer 0 load_effects) %"chk172";
      %"chk173" : A = (Check 0 8 Write 8) %"v453";
      store.ptr [%"chk173" + 0] <- %"v458";
      %"chk174" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v461" : P = (RawLoadPointer 0 load_effects) %"chk174"] ir[ %"v464" : P = (RawLoadPointer 0 load_effects) %"chk174";
      %"v465" = %"v464" +p #48;
      %"chk176" : A = (Check 0 8 Read 8) %"v465";
      %"v466" : P = (RawLoadPointer 0 load_effects) %"chk176";
      %"chk177" : A = (Check 0 8 Write 8) %"v461";
      store.ptr [%"chk177" + 0] <- %"v466";
      %"chk178" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v469" : P = (RawLoadPointer 0 load_effects) %"chk178";
      %"v470" = %"v469" +p #8;
      %"v473" : P = (RawLoadPointer 0 load_effects) %"chk178";
      %"v474" = %"v473" +p #48;
      %"chk180" : A = (Check 0 8 Read 8) %"v474";
      %"v475" : P = (RawLoadPointer 0 load_effects) %"chk180";
      %"chk181" : A = (Check 0 8 Write 8) %"v470";
      store.ptr [%"chk181" + 0] <- %"v475";
      %"chk182" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v478" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v479" = %"v478" +p #24;
      %"v482" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v483" = %"v482" +p #32;
      %"v486" : P = (RawLoadPointer 0 load_effects) %"chk182";
      %"v487" = %"v486" +p #48;
      %"chk185" : A = (Check 0 8 Read 8) %"v487";
      %"v488" : P = (RawLoadPointer 0 load_effects) %"chk185";
      %"chk186" : A = (Check 0 8 Write 8) %"v483";
      store.ptr [%"chk186" + 0] <- %"v488";
      %"chk187" : A = (Check 0 8 Write 8) %"v479";
      store.ptr [%"chk187" + 0] <- %"v488";
      %"chk188" : A = (Renew 0 8 Read 8) %"chk65", %"v451";
      %"v491" : P = (RawLoadPointer 0 load_effects) %"chk188";
      %"v492" = %"v491" +p #40;
      %"v495" : P = (RawLoadPointer 0 load_effects) %"chk188";
      %"v496" = %"v495" +p #48;
      %"chk190" : A = (Check 0 8 Read 8) %"v496";
      %"v497" : P = (RawLoadPointer 0 load_effects) %"chk190";
      %"chk191" : A = (Check 0 8 Write 8) %"v492";
      store.ptr [%"chk191" + 0] <- %"v497";
      %"iw_3.v44" : P = (Alloc 8) #8;
      %"iw_3.v6" = %"v0" +p #152;
      %"chk192" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"iw_3.v6";
      %"iw_3.v7" : P = (RawLoadPointer 0 load_effects) %"chk192";
      call %"iw_3.v10" : W = $"__libio_codecvt_encoding"(P %"iw_3.v7");
      %"iw_3.v19" : W = (Cmp Sgt W) %"iw_3.v10", #0]))
    => br %"iw_3.v19" ? "iw_3.L11" : "iw_3.L13" };
  ir_blk{ @"iw_3.L11":
    %"iw_3.v23" = %"v0" +p #160;
    %"chk193" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v23";
    %"iw_3.v24" : P = (RawLoadPointer 0 load_effects) %"chk193";
    %"iw_3.v25" = %"iw_3.v24" +p #8;
    %"chk194" : A = (Check 0 8 Read 8) %"iw_3.v25";
    %"iw_3.v26" : P = (RawLoadPointer 0 load_effects) %"chk194";
    %"iw_3.v28" = %"v0" +p #8;
    %"chk195" : A = (Renew 0 8 Read 8) %"chk162", %"iw_3.v28";
    %"iw_3.v29" : P = (RawLoadPointer 0 load_effects) %"chk195";
    %"iw_3.v31" = %"v0" +p #24;
    %"iw_3.v32" : P = (RawLoadPointer 16 load_effects) %"chk195";
    %"iw_3.v33" : L = Ptoi %"iw_3.v29";
    %"iw_3.v34" : L = Ptoi %"iw_3.v32";
    %"iw_3.v35" : L = Sub %"iw_3.v33", %"iw_3.v34";
    %"iw_3.v37" : L = (Ext Sw) %"iw_3.v10";
    %"iw_3.v38" : L = Div %"iw_3.v35", %"iw_3.v37";
    %"iw_3.v39" : L = Shl %"iw_3.v38", #2;
    %"iw_3.v40" = %"iw_3.v26" +p %"iw_3.v39";
    %"chk197" : A = (Renew 0 8 Write 8) %"chk194", %"iw_3.v25";
    store.ptr [%"chk197" + 0] <- %"iw_3.v40"
    => goto "iw_3.L41" };
  ir_blk{ @"iw_3.L13":
    %"iw_3.v46" = %"v0" +p #24;
    %"chk198" : A = (Renew 0 8 Read 8) %"chk160", %"iw_3.v46";
    %"iw_3.v47" : P = (RawLoadPointer 0 load_effects) %"chk198";
    %"chk199" : A = (Check 0 8 Write 8) %"iw_3.v44";
    store.ptr [%"chk199" + 0] <- %"iw_3.v47"
    => goto "iw_3.L48" };
  ir_blk{ @"iw_3.L48":
    %"iw_3.v52" = %"v0" +p #160;
    %"chk200" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v52";
    %"iw_3.v53" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v54" = %"iw_3.v53" +p #96;
    %"iw_3.v57" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v58" = %"iw_3.v57" +p #88;
    %"chk202" : A = (Check 0 8 Read 1) %"iw_3.v58";
    %"iw_3.v59" : L = (RawLoad LdL 0) %"chk202";
    %"chk203" : A = (Check 0 8 Write 1) %"iw_3.v54";
    store Wl [%"chk203" + 0] <- %"iw_3.v59";
    %"iw_3.v63" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v64" = %"iw_3.v63" +p #88;
    %"iw_3.v66" = %"v0" +p #24;
    %"chk205" : A = (Renew 0 8 Read 8) %"chk160", %"iw_3.v66";
    %"iw_3.v67" : P = (RawLoadPointer 0 load_effects) %"chk205";
    %"iw_3.v69" = %"v0" +p #8;
    %"chk206" : A = (Renew 0 8 Read 8) %"chk162", %"iw_3.v69";
    %"iw_3.v70" : P = (RawLoadPointer 0 load_effects) %"chk206";
    %"iw_3.v73" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v74" = %"iw_3.v73" +p #16;
    %"chk208" : A = (Check 0 8 Read 8) %"iw_3.v74";
    %"iw_3.v75" : P = (RawLoadPointer 0 load_effects) %"chk208";
    %"iw_3.v78" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v79" = %"iw_3.v78" +p #56;
    %"chk210" : A = (Check 0 8 Read 8) %"iw_3.v79";
    %"iw_3.v80" : P = (RawLoadPointer 0 load_effects) %"chk210";
    %"iw_3.v83" : P = (RawLoadPointer 0 load_effects) %"chk200";
    %"iw_3.v84" = %"iw_3.v83" +p #8;
    call %"iw_3.v85" : W = $"__libio_codecvt_in"(P %"iw_3.v7", P %"iw_3.v64", P %"iw_3.v67", P %"iw_3.v70", P %"iw_3.v44", P %"iw_3.v75", P %"iw_3.v80", P %"iw_3.v84");
    %"iw_3.v90" : W = (Cmp Eq W) %"iw_3.v85", #2
    => br %"iw_3.v90" ? "iw_3.L86" : "iw_3.L49" };
  ir_blk{ @"iw_3.L86":
    %"chk212" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"iw_3.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk212";
    %"iw_3.v95" : W = Or %"iw_3.v94", #32;
    %"chk213" : A = (Renew 0 4 Write 1) %"chk212", %"v0";
    store Ww [%"chk213" + 0] <- %"iw_3.v95"
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.L49":
    %"iw_3.v99" : W = (Cmp Eq W) %"iw_3.v85", #1
    => br %"iw_3.v99" ? poll "iw_3.L48" : "iw_3.L41" };
  ir_blk{ @"iw_3.L41":
    %"iw_3.v103" = %"v0" +p #160;
    %"chk214" : A = (Renew 0 8 Read 8) %"chk65", %"iw_3.v103";
    %"iw_3.v104" : P = (RawLoadPointer 0 load_effects) %"chk214";
    %"iw_3.v107" : P = (RawLoadPointer 0 load_effects) %"chk214";
    %"iw_3.v108" = %"iw_3.v107" +p #8;
    %"chk216" : A = (Check 0 8 Read 8) %"iw_3.v108";
    %"iw_3.v109" : P = (RawLoadPointer 0 load_effects) %"chk216";
    %"chk217" : A = (Check 0 8 Write 8) %"iw_3.v104";
    store.ptr [%"chk217" + 0] <- %"iw_3.v109"
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join" [%"v503" : W = phi("iw_3.L86" => #4294967295, "iw_3.L41" => #0)]:
    => br %"v503" ? "L322" : "L500" };
  ir_blk{ @"L500":
    %"chk218" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v507" : W = (RawLoad (LdNarrow Sw) 0) %"chk218";
    %"v509" : W = And %"v507", #4294967279;
    %"chk219" : A = (Renew 0 4 Write 1) %"chk218", %"v0";
    store Ww [%"chk219" + 0] <- %"v509";
    %"v826" = %"v0" +p #144;
    %"chk220" : A = (Renew 0 8 Read 1) %"chk152", %"v826";
    %"v827" : L = (RawLoad LdL 0) %"chk220";
    %"v828" : W = (Cmp Sge L) %"v827", #0
    => br %"v828" ? "L822" : "L824" };
  ir_blk{ @"L365":
    %"chk221" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
    %"v518" : W = (RawLoad (LdNarrow Sw) 0) %"chk221";
    %"v519" : W = And %"v518", #4
    => br %"v519" ? "L322" : "L516" };
  ir_blk{ @"L516":
    %"v523" = %"v0" +p #64;
    %"chk222" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v523";
    %"v524" : P = (RawLoadPointer 0 load_effects) %"chk222";
    %"v526" = %"v0" +p #56;
    %"v527" : P = (RawLoadPointer (-8) load_effects) %"chk222";
    %"v528" : L = Ptoi %"v524";
    %"v529" : L = Ptoi %"v527";
    %"v530" : L = Sub %"v528", %"v529";
    %"v531" : L = Sub %"v530", #1;
    %"v532" : L = Xor %"v531", #(-1);
    %"v533" : L = And %"pr.1", %"v532";
    %"v536" : L = Sub %"pr.1", %"v533";
    %"v543" : P = (RawLoadPointer 0 load_effects) %"chk222";
    %"v546" : P = (RawLoadPointer (-8) load_effects) %"chk222";
    %"v547" : L = Ptoi %"v543";
    %"v548" : L = Ptoi %"v546";
    %"v549" : L = Sub %"v547", %"v548";
    %"v550" : W = (Cmp Sgt L) %"v536", %"v549"
    => br %"v550" ? "L539" : "L538" };
  ir_blk{ @"L538":
    => goto "L539" };
  ir_blk{ @"L539" [%"pr.8" : L = phi("L538" => %"v533", "L516" => %"pr.1"); %"pr.7" : L = phi("L538" => %"v536", "L516" => #0)]:
    %"v553" = %"v0" +p #216;
    %"chk226" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v553";
    %"v554" : P = (RawLoadPointer 0 load_effects) %"chk226";
    %"iw_4.v4" : L = Ptoi %"v554";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v556" = %"v554" +p #128;
    %"chk227" : A = (Check 0 8 Read 8) %"v556";
    %"v557" : P = (RawLoadPointer 0 load_effects) %"chk227";
    %"chk228" : F = CheckFunction %"v557";
    rawcall %"v560" : L = %"chk228"(P %"v0", L %"pr.8", W #0);
    %"v565" : W = (Cmp Slt L) %"v560", #0
    => br %"v565" ? "L561" : "L563" };
  ir_blk{ @"L561":
    => ret #18446744073709551615 };
  ir_blk{ @"L563":
    %"v573" : W = (Cmp Eq L) %"pr.7", #0
    => br %"v573" ? "L571" : "L570" };
  ir_blk{ @"L570":
    %"v575" = %"v0" +p #216;
    %"chk229" : A = (Renew 0 8 Read 8) %"chk226", %"v575";
    %"v576" : P = (RawLoadPointer 0 load_effects) %"chk229";
    %"iw_5.v4" : L = Ptoi %"v576";
    %"iw_5.v7" : P = Copy $"__io_vtables";
    %"iw_5.v8" : L = Ptoi %"iw_5.v7";
    %"iw_5.v9" : L = Sub %"iw_5.v4", %"iw_5.v8";
    %"iw_5.v15" : W = (Cmp Uge L) %"iw_5.v9", #2352
    => br %"iw_5.v15" ? "iw_5.L10" : "iw_5.join" };
  ir_blk{ @"iw_5.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_5.join" };
  ir_blk{ @"iw_5.join":
    %"v578" = %"v576" +p #112;
    %"chk230" : A = (Check 0 8 Read 8) %"v578";
    %"v579" : P = (RawLoadPointer 0 load_effects) %"chk230";
    %"v582" = %"v0" +p #56;
    %"chk231" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v582";
    %"v583" : P = (RawLoadPointer 0 load_effects) %"chk231"
    => br %"v50" ? "L586" : "L585" };
  ir_blk{ @"L585":
    %"v590" = %"v0" +p #64;
    %"chk232" : A = (Renew 0 8 Read 8) %"chk222", %"v590";
    %"v591" : P = (RawLoadPointer 0 load_effects) %"chk232";
    %"v593" = %"v0" +p #56;
    %"v594" : P = (RawLoadPointer 0 load_effects) %"chk231";
    %"v595" : L = Ptoi %"v591";
    %"v596" : L = Ptoi %"v594";
    %"v597" : L = Sub %"v595", %"v596"
    => goto "L586" };
  ir_blk{ @"L586" [%"v598" : L = phi("L585" => %"v597", "iw_5.join" => %"pr.7")]:
    %"chk234" : F = CheckFunction %"v579";
    rawcall %"v599" : L = %"chk234"(P %"v0", P %"v583", L %"v598");
    %"v605" : W = (Cmp Slt L) %"v599", %"pr.7"
    => br %"v605" ? "L600" : "L571" };
  ir_blk{ @"L600":
    %"v612" : W = (Cmp Eq L) %"v599", #18446744073709551615
    => br %"v612" ? "L322" : "L607" };
  ir_blk{ @"L607":
    %"v616" : L = Sub %"pr.7", %"v599"
    => goto "L322" };
  ir_blk{ @"L571" [%"pr.9" : L = phi("L563" => #0, "L586" => %"v599")]:
    code ((app ir[ %"v620" = %"v0" +p #24;
      %"v622" = %"v0" +p #56;
      %"chk235" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v622";
      %"v623" : P = (RawLoadPointer 0 load_effects) %"chk235";
      %"chk236" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v620";
      store.ptr [%"chk236" + 0] <- %"v623";
      %"v625" = %"v0" +p #8;
      %"chk237" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v628" : P = (RawLoadPointer 0 load_effects) %"chk237";
      %"v630" = %"v628" +p %"pr.7";
      %"chk238" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v625";
      store.ptr [%"chk238" + 0] <- %"v630";
      %"v632" = %"v0" +p #16;
      %"chk239" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v635" : P = (RawLoadPointer 0 load_effects) %"chk239";
      %"v637" = %"v635" +p %"pr.9";
      %"chk240" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v632";
      store.ptr [%"chk240" + 0] <- %"v637";
      %"v639" = %"v0" +p #32;
      %"v641" = %"v0" +p #40;
      %"chk241" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v644" : P = (RawLoadPointer 0 load_effects) %"chk241";
      %"chk242" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v641";
      store.ptr [%"chk242" + 0] <- %"v644";
      %"chk243" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v639";
      store.ptr [%"chk243" + 0] <- %"v644";
      %"v646" = %"v0" +p #48;
      %"chk244" : A = (Renew 0 8 Read 8) %"chk235", %"v622";
      %"v649" : P = (RawLoadPointer 0 load_effects) %"chk244";
      %"chk245" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v646";
      store.ptr [%"chk245" + 0] <- %"v649";
      %"v651" = %"v0" +p #160;
      %"chk246" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v652" : P = (RawLoadPointer 0 load_effects) %"chk246";
      %"v653" = %"v652" +p #16;
      %"v656" : P = (RawLoadPointer 0 load_effects) %"chk246";
      %"v657" = %"v656" +p #48;
      %"chk248" : A = (Check 0 8 Read 8) %"v657";
      %"v658" : P = (RawLoadPointer 0 load_effects) %"chk248";
      %"chk249" : A = (Check 0 8 Write 8) %"v653";
      store.ptr [%"chk249" + 0] <- %"v658";
      %"chk250" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v661" : P = (RawLoadPointer 0 load_effects) %"chk250";
      %"v664" : P = (RawLoadPointer 0 load_effects) %"chk250";
      %"v665" = %"v664" +p #48] ir[ %"chk252" : A = (Check 0 8 Read 8) %"v665";
      %"v666" : P = (RawLoadPointer 0 load_effects) %"chk252";
      %"chk253" : A = (Check 0 8 Write 8) %"v661";
      store.ptr [%"chk253" + 0] <- %"v666";
      %"chk254" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v669" : P = (RawLoadPointer 0 load_effects) %"chk254";
      %"v670" = %"v669" +p #8;
      %"v673" : P = (RawLoadPointer 0 load_effects) %"chk254";
      %"v674" = %"v673" +p #48;
      %"chk256" : A = (Check 0 8 Read 8) %"v674";
      %"v675" : P = (RawLoadPointer 0 load_effects) %"chk256";
      %"chk257" : A = (Check 0 8 Write 8) %"v670";
      store.ptr [%"chk257" + 0] <- %"v675";
      %"chk258" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v678" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v679" = %"v678" +p #24;
      %"v682" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v683" = %"v682" +p #32;
      %"v686" : P = (RawLoadPointer 0 load_effects) %"chk258";
      %"v687" = %"v686" +p #48;
      %"chk261" : A = (Check 0 8 Read 8) %"v687";
      %"v688" : P = (RawLoadPointer 0 load_effects) %"chk261";
      %"chk262" : A = (Check 0 8 Write 8) %"v683";
      store.ptr [%"chk262" + 0] <- %"v688";
      %"chk263" : A = (Check 0 8 Write 8) %"v679";
      store.ptr [%"chk263" + 0] <- %"v688";
      %"chk264" : A = (Renew 0 8 Read 8) %"chk65", %"v651";
      %"v691" : P = (RawLoadPointer 0 load_effects) %"chk264";
      %"v692" = %"v691" +p #40;
      %"v695" : P = (RawLoadPointer 0 load_effects) %"chk264";
      %"v696" = %"v695" +p #48;
      %"chk266" : A = (Check 0 8 Read 8) %"v696";
      %"v697" : P = (RawLoadPointer 0 load_effects) %"chk266";
      %"chk267" : A = (Check 0 8 Write 8) %"v692";
      store.ptr [%"chk267" + 0] <- %"v697";
      %"iw_6.v44" : P = (Alloc 8) #8;
      %"iw_6.v6" = %"v0" +p #152;
      %"chk268" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"iw_6.v6";
      %"iw_6.v7" : P = (RawLoadPointer 0 load_effects) %"chk268";
      call %"iw_6.v10" : W = $"__libio_codecvt_encoding"(P %"iw_6.v7");
      %"iw_6.v46" = %"v0" +p #24;
      %"chk269" : A = (Renew 0 8 Read 8) %"chk236", %"iw_6.v46";
      %"iw_6.v47" : P = (RawLoadPointer 0 load_effects) %"chk269";
      %"chk270" : A = (Check 0 8 Write 8) %"iw_6.v44";
      store.ptr [%"chk270" + 0] <- %"iw_6.v47"]))
    => goto "iw_6.L48" };
  ir_blk{ @"iw_6.L48":
    %"iw_6.v52" = %"v0" +p #160;
    %"chk271" : A = (Renew 0 8 Read 8) %"chk65", %"iw_6.v52";
    %"iw_6.v53" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v54" = %"iw_6.v53" +p #96;
    %"iw_6.v57" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v58" = %"iw_6.v57" +p #88;
    %"chk273" : A = (Check 0 8 Read 1) %"iw_6.v58";
    %"iw_6.v59" : L = (RawLoad LdL 0) %"chk273";
    %"chk274" : A = (Check 0 8 Write 1) %"iw_6.v54";
    store Wl [%"chk274" + 0] <- %"iw_6.v59";
    %"iw_6.v63" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v64" = %"iw_6.v63" +p #88;
    %"iw_6.v66" = %"v0" +p #24;
    %"chk276" : A = (Renew 0 8 Read 8) %"chk236", %"iw_6.v66";
    %"iw_6.v67" : P = (RawLoadPointer 0 load_effects) %"chk276";
    %"iw_6.v69" = %"v0" +p #8;
    %"chk277" : A = (Renew 0 8 Read 8) %"chk238", %"iw_6.v69";
    %"iw_6.v70" : P = (RawLoadPointer 0 load_effects) %"chk277";
    %"iw_6.v73" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v74" = %"iw_6.v73" +p #16;
    %"chk279" : A = (Check 0 8 Read 8) %"iw_6.v74";
    %"iw_6.v75" : P = (RawLoadPointer 0 load_effects) %"chk279";
    %"iw_6.v78" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v79" = %"iw_6.v78" +p #56;
    %"chk281" : A = (Check 0 8 Read 8) %"iw_6.v79";
    %"iw_6.v80" : P = (RawLoadPointer 0 load_effects) %"chk281";
    %"iw_6.v83" : P = (RawLoadPointer 0 load_effects) %"chk271";
    %"iw_6.v84" = %"iw_6.v83" +p #8;
    call %"iw_6.v85" : W = $"__libio_codecvt_in"(P %"iw_6.v7", P %"iw_6.v64", P %"iw_6.v67", P %"iw_6.v70", P %"iw_6.v44", P %"iw_6.v75", P %"iw_6.v80", P %"iw_6.v84");
    %"iw_6.v90" : W = (Cmp Eq W) %"iw_6.v85", #2
    => br %"iw_6.v90" ? "iw_6.L86" : "iw_6.L49" };
  ir_blk{ @"iw_6.L86":
    %"chk283" : A = (Renew 0 4 Read 1) %"chk221", %"v0";
    %"iw_6.v94" : W = (RawLoad (LdNarrow Sw) 0) %"chk283";
    %"iw_6.v95" : W = Or %"iw_6.v94", #32;
    %"chk284" : A = (Renew 0 4 Write 1) %"chk221", %"v0";
    store Ww [%"chk284" + 0] <- %"iw_6.v95"
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.L49":
    %"iw_6.v99" : W = (Cmp Eq W) %"iw_6.v85", #1
    => br %"iw_6.v99" ? poll "iw_6.L48" : "iw_6.L41" };
  ir_blk{ @"iw_6.L41":
    %"iw_6.v103" = %"v0" +p #160;
    %"chk285" : A = (Renew 0 8 Read 8) %"chk65", %"iw_6.v103";
    %"iw_6.v104" : P = (RawLoadPointer 0 load_effects) %"chk285";
    %"iw_6.v107" : P = (RawLoadPointer 0 load_effects) %"chk285";
    %"iw_6.v108" = %"iw_6.v107" +p #8;
    %"chk287" : A = (Check 0 8 Read 8) %"iw_6.v108";
    %"iw_6.v109" : P = (RawLoadPointer 0 load_effects) %"chk287";
    %"chk288" : A = (Check 0 8 Write 8) %"iw_6.v104";
    store.ptr [%"chk288" + 0] <- %"iw_6.v109"
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.join" [%"v703" : W = phi("iw_6.L86" => #4294967295, "iw_6.L41" => #0)]:
    => br %"v703" ? "L322" : "L700" };
  ir_blk{ @"L700":
    %"v706" = %"v0" +p #144;
    %"v709" : L = Add %"v560", %"pr.9";
    %"chk289" : A = (Renew 0 8 Write 1) %"chk152", %"v706";
    store Wl [%"chk289" + 0] <- %"v709";
    %"chk290" : A = (Renew 0 4 Read 1) %"chk221", %"v0";
    %"v712" : W = (RawLoad (LdNarrow Sw) 0) %"chk290";
    %"v714" : W = And %"v712", #4294967279;
    store Ww [%"chk290" + 0] <- %"v714"
    => ret %"pr.1" };
  ir_blk{ @"L322" [%"pr.6" : W = phi("L204" => %"v4", "L345" => %"v4", "iw_3.join" => %"pr.5", "L365" => %"pr.5", "L607" => #1, "L600" => #1, "iw_6.join" => %"pr.5"); %"pr.4" : L = phi("L204" => %"pr.2", "L345" => %"v2", "iw_3.join" => %"pr.1", "L365" => %"pr.1", "L607" => %"v616", "L600" => %"pr.7", "iw_6.join" => %"pr.1")]:
    call void $"__GI__IO_unsave_markers"(P %"v0");
    %"v720" = %"v0" +p #216;
    %"chk292" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v720";
    %"v721" : P = (RawLoadPointer 0 load_effects) %"chk292";
    %"iw_7.v4" : L = Ptoi %"v721";
    %"iw_7.v7" : P = Copy $"__io_vtables";
    %"iw_7.v8" : L = Ptoi %"iw_7.v7";
    %"iw_7.v9" : L = Sub %"iw_7.v4", %"iw_7.v8";
    %"iw_7.v15" : W = (Cmp Uge L) %"iw_7.v9", #2352
    => br %"iw_7.v15" ? "iw_7.L10" : "iw_7.join" };
  ir_blk{ @"iw_7.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join":
    %"v723" = %"v721" +p #128;
    %"chk293" : A = (Check 0 8 Read 8) %"v723";
    %"v724" : P = (RawLoadPointer 0 load_effects) %"chk293";
    %"chk294" : F = CheckFunction %"v724";
    rawcall %"v728" : L = %"chk294"(P %"v0", L %"pr.4", W %"pr.6");
    %"v735" : W = (Cmp Ne L) %"v728", #18446744073709551615
    => br %"v735" ? "L729" : "L731" };
  ir_blk{ @"L729":
    code ((app ir[ %"chk295" : A = (HalfCheck Lower 0 4 Read 1) %"chk65", %"v0";
      %"v738" : W = (RawLoad (LdNarrow Sw) 0) %"chk295";
      %"v740" : W = And %"v738", #4294967279;
      %"chk296" : A = (Renew 0 4 Write 1) %"chk295", %"v0";
      store Ww [%"chk296" + 0] <- %"v740";
      %"v744" = %"v0" +p #144;
      %"chk297" : A = (HalfCheck Lower 0 8 Write 1) %"chk65", %"v744";
      store Wl [%"chk297" + 0] <- %"v728";
      %"v747" = %"v0" +p #24;
      %"v749" = %"v0" +p #56;
      %"chk298" : A = (HalfCheck Lower 0 8 Read 8) %"chk65", %"v749";
      %"v750" : P = (RawLoadPointer 0 load_effects) %"chk298";
      %"chk299" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v747";
      store.ptr [%"chk299" + 0] <- %"v750";
      %"v752" = %"v0" +p #8;
      %"chk300" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v755" : P = (RawLoadPointer 0 load_effects) %"chk300";
      %"chk301" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v752";
      store.ptr [%"chk301" + 0] <- %"v755";
      %"v757" = %"v0" +p #16;
      %"chk302" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v760" : P = (RawLoadPointer 0 load_effects) %"chk302";
      %"chk303" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v757";
      store.ptr [%"chk303" + 0] <- %"v760";
      %"v762" = %"v0" +p #32;
      %"v764" = %"v0" +p #40;
      %"chk304" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v767" : P = (RawLoadPointer 0 load_effects) %"chk304";
      %"chk305" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v764";
      store.ptr [%"chk305" + 0] <- %"v767";
      %"chk306" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v762";
      store.ptr [%"chk306" + 0] <- %"v767";
      %"v769" = %"v0" +p #48;
      %"chk307" : A = (Renew 0 8 Read 8) %"chk298", %"v749";
      %"v772" : P = (RawLoadPointer 0 load_effects) %"chk307";
      %"chk308" : A = (HalfCheck Lower 0 8 Write 8) %"chk65", %"v769";
      store.ptr [%"chk308" + 0] <- %"v772";
      %"v774" = %"v0" +p #160;
      %"chk309" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v775" : P = (RawLoadPointer 0 load_effects) %"chk309";
      %"v776" = %"v775" +p #16;
      %"v779" : P = (RawLoadPointer 0 load_effects) %"chk309";
      %"v780" = %"v779" +p #48] ir[ %"chk311" : A = (Check 0 8 Read 8) %"v780";
      %"v781" : P = (RawLoadPointer 0 load_effects) %"chk311";
      %"chk312" : A = (Check 0 8 Write 8) %"v776";
      store.ptr [%"chk312" + 0] <- %"v781";
      %"chk313" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v784" : P = (RawLoadPointer 0 load_effects) %"chk313";
      %"v787" : P = (RawLoadPointer 0 load_effects) %"chk313";
      %"v788" = %"v787" +p #48;
      %"chk315" : A = (Check 0 8 Read 8) %"v788";
      %"v789" : P = (RawLoadPointer 0 load_effects) %"chk315";
      %"chk316" : A = (Check 0 8 Write 8) %"v784";
      store.ptr [%"chk316" + 0] <- %"v789";
      %"chk317" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v792" : P = (RawLoadPointer 0 load_effects) %"chk317";
      %"v793" = %"v792" +p #8;
      %"v796" : P = (RawLoadPointer 0 load_effects) %"chk317";
      %"v797" = %"v796" +p #48;
      %"chk319" : A = (Check 0 8 Read 8) %"v797";
      %"v798" : P = (RawLoadPointer 0 load_effects) %"chk319";
      %"chk320" : A = (Check 0 8 Write 8) %"v793";
      store.ptr [%"chk320" + 0] <- %"v798";
      %"chk321" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v801" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v802" = %"v801" +p #24;
      %"v805" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v806" = %"v805" +p #32;
      %"v809" : P = (RawLoadPointer 0 load_effects) %"chk321";
      %"v810" = %"v809" +p #48;
      %"chk324" : A = (Check 0 8 Read 8) %"v810";
      %"v811" : P = (RawLoadPointer 0 load_effects) %"chk324";
      %"chk325" : A = (Check 0 8 Write 8) %"v806";
      store.ptr [%"chk325" + 0] <- %"v811";
      %"chk326" : A = (Check 0 8 Write 8) %"v802";
      store.ptr [%"chk326" + 0] <- %"v811";
      %"chk327" : A = (Renew 0 8 Read 8) %"chk65", %"v774";
      %"v814" : P = (RawLoadPointer 0 load_effects) %"chk327";
      %"v815" = %"v814" +p #40;
      %"v818" : P = (RawLoadPointer 0 load_effects) %"chk327";
      %"v819" = %"v818" +p #48;
      %"chk329" : A = (Check 0 8 Read 8) %"v819";
      %"v820" : P = (RawLoadPointer 0 load_effects) %"chk329";
      %"chk330" : A = (Check 0 8 Write 8) %"v815";
      store.ptr [%"chk330" + 0] <- %"v820"]))
    => goto "L731" };
  ir_blk{ @"L731":
    => ret %"v728" };
  ir_blk{ @"L822":
    %"v830" = %"v0" +p #216;
    %"chk331" : A = (HalfCheck Upper 0 8 Read 8) %"chk65", %"v830";
    %"v831" : P = (RawLoadPointer 0 load_effects) %"chk331";
    %"iw_8.v4" : L = Ptoi %"v831";
    %"iw_8.v7" : P = Copy $"__io_vtables";
    %"iw_8.v8" : L = Ptoi %"iw_8.v7";
    %"iw_8.v9" : L = Sub %"iw_8.v4", %"iw_8.v8";
    %"iw_8.v15" : W = (Cmp Uge L) %"iw_8.v9", #2352
    => br %"iw_8.v15" ? "iw_8.L10" : "iw_8.join" };
  ir_blk{ @"iw_8.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_8.join" };
  ir_blk{ @"iw_8.join":
    %"v833" = %"v831" +p #128;
    %"chk332" : A = (Check 0 8 Read 8) %"v833";
    %"v834" : P = (RawLoadPointer 0 load_effects) %"chk332";
    %"v837" = %"v0" +p #144;
    %"chk333" : A = (Renew 0 8 Read 1) %"chk152", %"v837";
    %"v838" : L = (RawLoad LdL 0) %"chk333";
    %"chk334" : F = CheckFunction %"v834";
    rawcall %"v839" : L = %"chk334"(P %"v0", L %"v838", W #0)
    => goto "L824" };
  ir_blk{ @"L824":
    => ret %"pr.1" }])) }.
