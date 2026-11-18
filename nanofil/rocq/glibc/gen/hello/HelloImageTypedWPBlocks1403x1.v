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

Definition hello_image_fn___wprintf_buffer'blocks1 : list block :=
  (app (app (app [ir_blk{ @"start":
    %"v10" : P = (Alloc 8) #8;
    %"v13" : P = (Alloc 4) #1000;
    %"v15" : P = (Alloc 8) #24;
    %"v86" : P = (Alloc 16) #16;
    %"v488" : P = (Alloc 8) #8;
    %"v638" : P = (Alloc 8) #8;
    %"v1300" : P = (Alloc 8) #24;
    %"v1922" : P = (Alloc 4) #20;
    %"v2058" : P = (Alloc 8) #8;
    %"v18" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    (Flight (a "v23") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 8 Write 8) %"v15";
    store.ptr [%"chk2" + 0] <- %"v25";
    call %"v27" : P = $"glibc_vfwprintf_internal#__find_specwc.gnu_inline"(P %"v2");
    %"chk3" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk3" + 0] <- %"v27";
    %"v32" : L = Ptoi %"v27";
    %"v33" : L = Ptoi %"v2";
    %"v34" : L = Sub %"v32", %"v33";
    %"v35" : L = Div %"v34", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"v2", L %"v35");
    call %"v40" : W = $"glibc_vfwprintf_internal#__wprintf_buffer_has_failed"(P %"v0");
    %"v41" : W = (Ext Ub) %"v40"
    => br %"v41" ? "L36" : "L38" };
  ir_blk{ @"L36":
    => ret void };
  ir_blk{ @"L38":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 4 Read 1) %"v46";
    %"v47" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"v48" : W = (Cmp Eq W) %"v47", #0
    => br %"v48" ? "L43" : "L45" };
  ir_blk{ @"L43":
    => ret void };
  ir_blk{ @"L45":
    %"v53" : P = Copy $"__printf_function_table";
    %"chk6" : A = (Check 0 8 Read 8) %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v55" : L = Ptoi %"v54";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Ne L) %"v55", %"v56"
    => br %"v57" ? "L59" : "L58" };
  ir_blk{ @"L58":
    %"v60" : P = Copy $"__printf_modifier_table";
    %"chk7" : A = (Check 0 8 Read 8) %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v62" : L = Ptoi %"v61";
    %"v64" : W = (Cmp Ne L) %"v62", %"v56"
    => goto "L59" };
  ir_blk{ @"L59" [%"v66" : W = phi("L45" => #1, "L58" => %"v64")]:
    => br %"v66" ? "L68" : "L67" };
  ir_blk{ @"L67":
    %"v69" : P = Copy $"__printf_va_arg_table";
    %"chk8" : A = (Check 0 8 Read 8) %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v71" : L = Ptoi %"v70";
    %"v73" : W = (Cmp Ne L) %"v71", %"v56"
    => goto "L68" };
  ir_blk{ @"L68" [%"v75" : W = phi("L59" => #1, "L67" => %"v73")]:
    => br %"v75" ? "L78" : "L80" };
  ir_blk{ @"L80" [%"pr.16" : W = phi("L2087" => %"pr.12", "L68" => #0); %"pr.11" : W = phi("L2087" => %"v2071", "L68" => #0); %"pr.9" : P = phi("L2087" => %"pr.5", "L68" => %"v23"); %"pr.4" : W = phi("L2087" => %"pr.1", "L68" => #0)]:
    %"v103" = %"v13" +p #1000;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v109" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v110" = %"v109" +p #4;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk10" + 0] <- %"v110";
    %"chk11" : A = (Check 0 4 Read 1) %"v110";
    %"v111" : W = (RawLoad (LdNarrow Uw) 0) %"chk11";
    %"v116" : W = (Cmp Slt W) %"v111", #32
    => br %"v116" ? "L118" : "L117" };
  ir_blk{ @"L117":
    %"v120" : W = (Cmp Sgt W) %"v111", #122
    => goto "L118" };
  ir_blk{ @"L118" [%"v122" : W = phi("L80" => #1, "L117" => %"v120")]:
    => br %"v122" ? "L114" : "L113" };
  ir_blk{ @"L113":
    %"v126" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v127" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v129" : W = Sub %"v111", #32;
    %"v130" : L = (Ext Uw) %"v129";
    %"v131" = %"v127" +p %"v130";
    %"chk12" : A = (Check 0 1 Read 1) %"v131";
    %"v132" : W = (RawLoad (LdNarrow Ub) 0) %"chk12";
    %"v133" : L = (Ext Uw) %"v132";
    %"v134" : L = Shl %"v133", #2;
    %"v135" = %"v126" +p %"v134";
    %"chk13" : A = (Check 0 4 Read 1) %"v135";
    %"v136" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v137" : L = (Ext Sw) %"v136"
    => goto "L114" };
  ir_blk{ @"L114" [%"v138" : L = phi("L113" => %"v137", "L118" => #0)]:
    %"v139" : W = Copy %"v138";
    %"v140" : L = (Ext Sw) %"v139";
    %"v141" = #1 +p %"v140";
    %"v143" : L = Ptoi %"v141"
    => goto "L144" };
  ir_blk{ @"L147":
    %"chk14" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v153" = %"v152" +p #4;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk15" + 0] <- %"v153";
    %"chk16" : A = (Check 0 4 Read 1) %"v153";
    %"v154" : W = (RawLoad (LdNarrow Uw) 0) %"chk16";
    %"v159" : W = (Cmp Slt W) %"v154", #32
    => br %"v159" ? "L161" : "L160" };
  ir_blk{ @"L160":
    %"v163" : W = (Cmp Sgt W) %"v154", #122
    => goto "L161" };
  ir_blk{ @"L161" [%"v165" : W = phi("L147" => #1, "L160" => %"v163")]:
    => br %"v165" ? "L157" : "L156" };
  ir_blk{ @"L156":
    %"v169" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v170" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v172" : W = Sub %"v154", #32;
    %"v173" : L = (Ext Uw) %"v172";
    %"v174" = %"v170" +p %"v173";
    %"chk17" : A = (Check 0 1 Read 1) %"v174";
    %"v175" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v176" : L = (Ext Uw) %"v175";
    %"v177" : L = Shl %"v176", #2;
    %"v178" = %"v169" +p %"v177";
    %"chk18" : A = (Check 0 4 Read 1) %"v178";
    %"v179" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v180" : L = (Ext Sw) %"v179"
    => goto "L157" };
  ir_blk{ @"L157" [%"v181" : L = phi("L156" => %"v180", "L161" => #0)]:
    %"v182" : W = Copy %"v181";
    %"v183" : L = (Ext Sw) %"v182";
    %"v184" = #1 +p %"v183";
    %"v186" : L = Ptoi %"v184"
    => goto "L144" };
  ir_blk{ @"L188":
    %"chk19" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v194" = %"v193" +p #4;
    %"chk20" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk20" + 0] <- %"v194";
    %"chk21" : A = (Check 0 4 Read 1) %"v194";
    %"v195" : W = (RawLoad (LdNarrow Uw) 0) %"chk21";
    %"v200" : W = (Cmp Slt W) %"v195", #32
    => br %"v200" ? "L202" : "L201" };
  ir_blk{ @"L201":
    %"v204" : W = (Cmp Sgt W) %"v195", #122
    => goto "L202" };
  ir_blk{ @"L202" [%"v206" : W = phi("L188" => #1, "L201" => %"v204")]:
    => br %"v206" ? "L198" : "L197" };
  ir_blk{ @"L197":
    %"v210" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v211" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v213" : W = Sub %"v195", #32;
    %"v214" : L = (Ext Uw) %"v213";
    %"v215" = %"v211" +p %"v214";
    %"chk22" : A = (Check 0 1 Read 1) %"v215";
    %"v216" : W = (RawLoad (LdNarrow Ub) 0) %"chk22";
    %"v217" : L = (Ext Uw) %"v216";
    %"v218" : L = Shl %"v217", #2;
    %"v219" = %"v210" +p %"v218";
    %"chk23" : A = (Check 0 4 Read 1) %"v219";
    %"v220" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v221" : L = (Ext Sw) %"v220"
    => goto "L198" };
  ir_blk{ @"L198" [%"v222" : L = phi("L197" => %"v221", "L202" => #0)]:
    %"v223" : W = Copy %"v222";
    %"v224" : L = (Ext Sw) %"v223";
    %"v225" = #1 +p %"v224";
    %"v227" : L = Ptoi %"v225"
    => goto "L144" };
  ir_blk{ @"L229":
    %"chk24" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v234" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v235" = %"v234" +p #4;
    %"chk25" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk25" + 0] <- %"v235";
    %"chk26" : A = (Check 0 4 Read 1) %"v235";
    %"v236" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v241" : W = (Cmp Slt W) %"v236", #32
    => br %"v241" ? "L243" : "L242" };
  ir_blk{ @"L242":
    %"v245" : W = (Cmp Sgt W) %"v236", #122
    => goto "L243" };
  ir_blk{ @"L243" [%"v247" : W = phi("L229" => #1, "L242" => %"v245")]:
    => br %"v247" ? "L239" : "L238" };
  ir_blk{ @"L238":
    %"v251" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v252" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v254" : W = Sub %"v236", #32;
    %"v255" : L = (Ext Uw) %"v254";
    %"v256" = %"v252" +p %"v255";
    %"chk27" : A = (Check 0 1 Read 1) %"v256";
    %"v257" : W = (RawLoad (LdNarrow Ub) 0) %"chk27";
    %"v258" : L = (Ext Uw) %"v257";
    %"v259" : L = Shl %"v258", #2;
    %"v260" = %"v251" +p %"v259";
    %"chk28" : A = (Check 0 4 Read 1) %"v260";
    %"v261" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v262" : L = (Ext Sw) %"v261"
    => goto "L239" };
  ir_blk{ @"L239" [%"v263" : L = phi("L238" => %"v262", "L243" => #0)]:
    %"v264" : W = Copy %"v263";
    %"v265" : L = (Ext Sw) %"v264";
    %"v266" = #1 +p %"v265";
    %"v268" : L = Ptoi %"v266"
    => goto "L144" };
  ir_blk{ @"L270":
    %"chk29" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v275" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v276" = %"v275" +p #4;
    %"chk30" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk30" + 0] <- %"v276";
    %"chk31" : A = (Check 0 4 Read 1) %"v276";
    %"v277" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v282" : W = (Cmp Slt W) %"v277", #32
    => br %"v282" ? "L284" : "L283" };
  ir_blk{ @"L283":
    %"v286" : W = (Cmp Sgt W) %"v277", #122
    => goto "L284" };
  ir_blk{ @"L284" [%"v288" : W = phi("L270" => #1, "L283" => %"v286")]:
    => br %"v288" ? "L280" : "L279" };
  ir_blk{ @"L279":
    %"v292" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v293" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v295" : W = Sub %"v277", #32;
    %"v296" : L = (Ext Uw) %"v295";
    %"v297" = %"v293" +p %"v296";
    %"chk32" : A = (Check 0 1 Read 1) %"v297";
    %"v298" : W = (RawLoad (LdNarrow Ub) 0) %"chk32";
    %"v299" : L = (Ext Uw) %"v298";
    %"v300" : L = Shl %"v299", #2;
    %"v301" = %"v292" +p %"v300";
    %"chk33" : A = (Check 0 4 Read 1) %"v301";
    %"v302" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v303" : L = (Ext Sw) %"v302"
    => goto "L280" };
  ir_blk{ @"L280" [%"v304" : L = phi("L279" => %"v303", "L284" => #0)]:
    %"v305" : W = Copy %"v304";
    %"v306" : L = (Ext Sw) %"v305";
    %"v307" = #1 +p %"v306";
    %"v309" : L = Ptoi %"v307"
    => goto "L144" };
  ir_blk{ @"L310":
    %"v315" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v315" ? "L313" : "L312" };
  ir_blk{ @"L312":
    => goto "L313" };
  ir_blk{ @"L313" [%"pr.93" : W = phi("L312" => %"pr.92", "L310" => #48)]:
    %"chk34" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v321" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v322" = %"v321" +p #4;
    %"chk35" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk35" + 0] <- %"v322";
    %"chk36" : A = (Check 0 4 Read 1) %"v322";
    %"v323" : W = (RawLoad (LdNarrow Uw) 0) %"chk36";
    %"v328" : W = (Cmp Slt W) %"v323", #32
    => br %"v328" ? "L330" : "L329" };
  ir_blk{ @"L329":
    %"v332" : W = (Cmp Sgt W) %"v323", #122
    => goto "L330" };
  ir_blk{ @"L330" [%"v334" : W = phi("L313" => #1, "L329" => %"v332")]:
    => br %"v334" ? "L326" : "L325" };
  ir_blk{ @"L325":
    %"v338" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v339" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v341" : W = Sub %"v323", #32;
    %"v342" : L = (Ext Uw) %"v341";
    %"v343" = %"v339" +p %"v342";
    %"chk37" : A = (Check 0 1 Read 1) %"v343";
    %"v344" : W = (RawLoad (LdNarrow Ub) 0) %"chk37";
    %"v345" : L = (Ext Uw) %"v344";
    %"v346" : L = Shl %"v345", #2;
    %"v347" = %"v338" +p %"v346";
    %"chk38" : A = (Check 0 4 Read 1) %"v347";
    %"v348" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v349" : L = (Ext Sw) %"v348"
    => goto "L326" }] [ir_blk{ @"L326" [%"v350" : L = phi("L325" => %"v349", "L330" => #0)]:
    %"v351" : W = Copy %"v350";
    %"v352" : L = (Ext Sw) %"v351";
    %"v353" = #1 +p %"v352";
    %"v355" : L = Ptoi %"v353"
    => goto "L144" };
  ir_blk{ @"L356":
    (Flight (a "v363") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v364" : L = Ptoi %"pr.5";
    %"v365" : L = Ptoi %"v363";
    %"v366" : W = (Cmp Eq L) %"v364", %"v365"
    => br %"v366" ? "L357" : "L359" };
  ir_blk{ @"L357":
    %"v367" : P = Copy $"__libc_tsd_LOCALE";
    %"chk39" : A = (Check 0 8 Read 8) %"v367";
    %"v368" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v369" = %"v368" +p #8;
    %"chk40" : A = (Check 0 8 Read 8) %"v369";
    %"v370" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v371" = %"v370" +p #56;
    %"v375" = %"v371" +p #32;
    %"chk41" : A = (Check 0 4 Read 1) %"v375";
    %"v376" : W = (RawLoad (LdNarrow Uw) 0) %"chk41";
    %"v377" : P = Copy $"__libc_tsd_LOCALE";
    %"chk42" : A = (Check 0 8 Read 8) %"v377";
    %"v378" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v379" = %"v378" +p #8;
    %"chk43" : A = (Check 0 8 Read 8) %"v379";
    %"v380" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v381" = %"v380" +p #56;
    %"v385" = %"v381" +p #16;
    %"chk44" : A = (Check 0 8 Read 8) %"v385";
    %"v386" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 1 Read 1) %"v386";
    %"v391" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v392" : W = (Cmp Eq W) %"v391", #0
    => br %"v392" ? "L394" : "L393" };
  ir_blk{ @"L393":
    %"v396" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v397" : W = (Cmp Eq W) %"v396", #127
    => goto "L394" };
  ir_blk{ @"L394" [%"v399" : W = phi("L357" => #1, "L393" => %"v397")]:
    => br %"v399" ? "L401" : "L400" };
  ir_blk{ @"L400":
    %"v403" : W = (Cmp Eq W) %"v376", #0
    => goto "L401" };
  ir_blk{ @"L401" [%"v405" : W = phi("L394" => #1, "L400" => %"v403")]:
    => br %"v405" ? "L359" : "L388" };
  ir_blk{ @"L388":
    => goto "L359" };
  ir_blk{ @"L359" [%"pr.6" : P = phi("L388" => %"v386", "L401" => #0, "L356" => %"pr.5"); %"pr.2" : W = phi("L388" => %"v376", "L401" => %"v376", "L356" => %"pr.1")]:
    %"chk47" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v411" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v412" = %"v411" +p #4;
    %"chk48" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk48" + 0] <- %"v412";
    %"chk49" : A = (Check 0 4 Read 1) %"v412";
    %"v413" : W = (RawLoad (LdNarrow Uw) 0) %"chk49";
    %"v418" : W = (Cmp Slt W) %"v413", #32
    => br %"v418" ? "L420" : "L419" };
  ir_blk{ @"L419":
    %"v422" : W = (Cmp Sgt W) %"v413", #122
    => goto "L420" };
  ir_blk{ @"L420" [%"v424" : W = phi("L359" => #1, "L419" => %"v422")]:
    => br %"v424" ? "L416" : "L415" };
  ir_blk{ @"L415":
    %"v428" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v429" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v431" : W = Sub %"v413", #32;
    %"v432" : L = (Ext Uw) %"v431";
    %"v433" = %"v429" +p %"v432";
    %"chk50" : A = (Check 0 1 Read 1) %"v433";
    %"v434" : W = (RawLoad (LdNarrow Ub) 0) %"chk50";
    %"v435" : L = (Ext Uw) %"v434";
    %"v436" : L = Shl %"v435", #2;
    %"v437" = %"v428" +p %"v436";
    %"chk51" : A = (Check 0 4 Read 1) %"v437";
    %"v438" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"v439" : L = (Ext Sw) %"v438"
    => goto "L416" };
  ir_blk{ @"L416" [%"v440" : L = phi("L415" => %"v439", "L420" => #0)]:
    %"v441" : W = Copy %"v440";
    %"v442" : L = (Ext Sw) %"v441";
    %"v443" = #1 +p %"v442";
    %"v445" : L = Ptoi %"v443"
    => goto "L144" };
  ir_blk{ @"L447":
    %"chk52" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v452" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v453" = %"v452" +p #4;
    %"chk53" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk53" + 0] <- %"v453";
    %"chk54" : A = (Check 0 4 Read 1) %"v453";
    %"v454" : W = (RawLoad (LdNarrow Uw) 0) %"chk54";
    %"v459" : W = (Cmp Slt W) %"v454", #32
    => br %"v459" ? "L461" : "L460" };
  ir_blk{ @"L460":
    %"v463" : W = (Cmp Sgt W) %"v454", #122
    => goto "L461" };
  ir_blk{ @"L461" [%"v465" : W = phi("L447" => #1, "L460" => %"v463")]:
    => br %"v465" ? "L457" : "L456" };
  ir_blk{ @"L456":
    %"v469" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step0_jumps.278";
    %"v470" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v472" : W = Sub %"v454", #32;
    %"v473" : L = (Ext Uw) %"v472";
    %"v474" = %"v470" +p %"v473";
    %"chk55" : A = (Check 0 1 Read 1) %"v474";
    %"v475" : W = (RawLoad (LdNarrow Ub) 0) %"chk55";
    %"v476" : L = (Ext Uw) %"v475";
    %"v477" : L = Shl %"v476", #2;
    %"v478" = %"v469" +p %"v477";
    %"chk56" : A = (Check 0 4 Read 1) %"v478";
    %"v479" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v480" : L = (Ext Sw) %"v479"
    => goto "L457" };
  ir_blk{ @"L457" [%"v481" : L = phi("L456" => %"v480", "L461" => #0)]:
    %"v482" : W = Copy %"v481";
    %"v483" : L = (Ext Sw) %"v482";
    %"v484" = #1 +p %"v483";
    %"v486" : L = Ptoi %"v484"
    => goto "L144" };
  ir_blk{ @"L487":
    %"chk57" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v489" : P = (RawLoadPointer 0 load_effects) %"chk57";
    %"v490" = %"v489" +p #4;
    %"chk58" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk58" + 0] <- %"v490";
    %"chk59" : A = (Check 0 8 Write 8) %"v488";
    store.ptr [%"chk59" + 0] <- %"v490";
    %"chk60" : A = (Renew 0 8 Read 8) %"chk59", %"v488";
    %"v494" : P = (RawLoadPointer 0 load_effects) %"chk60";
    %"chk61" : A = (Check 0 4 Read 1) %"v494";
    %"v495" : W = (RawLoad (LdNarrow Uw) 0) %"chk61";
    %"v496" : W = Sub %"v495", #48;
    %"v497" : W = (Cmp Ult W) %"v496", #10
    => br %"v497" ? "L491" : "L493" };
  ir_blk{ @"L491":
    call %"v499" : W = $"glibc_vfwprintf_internal#read_int"(P %"v488");
    %"v505" : W = (Cmp Eq W) %"v499", #4294967295
    => br %"v505" ? "L500" : "L502" };
  ir_blk{ @"L500":
    %"v506" : P = Copy $"__libc_errno";
    %"chk62" : A = (Check 0 4 Write 1) %"v506";
    store Ww [%"chk62" + 0] <- #75;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L502":
    => br %"v499" ? "L514" : "L515" };
  ir_blk{ @"L514":
    %"chk63" : A = (Renew 0 8 Read 8) %"chk59", %"v488";
    %"v516" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"chk64" : A = (Check 0 4 Read 1) %"v516";
    %"v517" : W = (RawLoad (LdNarrow Uw) 0) %"chk64";
    %"v518" : W = (Cmp Eq W) %"v517", #36
    => goto "L515" };
  ir_blk{ @"L515" [%"v520" : W = phi("L502" => #0, "L514" => %"v518")]:
    => br %"v520" ? "L78" : "L493" };
  ir_blk{ @"L493":
    %"v523" : W = VaArg %"v4";
    %"v528" : W = (Cmp Slt W) %"v523", #0
    => br %"v528" ? "L524" : "L526" };
  ir_blk{ @"L524":
    %"v530" : W = Neg %"v523"
    => goto "L526" };
  ir_blk{ @"L526" [%"pr.94" : W = phi("L524" => #32, "L493" => %"pr.92"); %"pr.76" : W = phi("L524" => %"v530", "L493" => %"v523"); %"pr.48" : W = phi("L524" => #1, "L493" => %"pr.47")]:
    %"chk65" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v536" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Check 0 4 Read 1) %"v536";
    %"v537" : W = (RawLoad (LdNarrow Uw) 0) %"chk66";
    %"v542" : W = (Cmp Slt W) %"v537", #32
    => br %"v542" ? "L544" : "L543" };
  ir_blk{ @"L543":
    %"v546" : W = (Cmp Sgt W) %"v537", #122
    => goto "L544" };
  ir_blk{ @"L544" [%"v548" : W = phi("L526" => #1, "L543" => %"v546")]:
    => br %"v548" ? "L540" : "L539" };
  ir_blk{ @"L539":
    %"v552" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step1_jumps.279";
    %"v553" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v555" : W = Sub %"v537", #32;
    %"v556" : L = (Ext Uw) %"v555";
    %"v557" = %"v553" +p %"v556";
    %"chk67" : A = (Check 0 1 Read 1) %"v557";
    %"v558" : W = (RawLoad (LdNarrow Ub) 0) %"chk67";
    %"v559" : L = (Ext Uw) %"v558";
    %"v560" : L = Shl %"v559", #2;
    %"v561" = %"v552" +p %"v560";
    %"chk68" : A = (Check 0 4 Read 1) %"v561";
    %"v562" : W = (RawLoad (LdNarrow Sw) 0) %"chk68";
    %"v563" : L = (Ext Sw) %"v562"
    => goto "L540" };
  ir_blk{ @"L540" [%"v564" : L = phi("L539" => %"v563", "L544" => #0)]:
    %"v565" : W = Copy %"v564";
    %"v566" : L = (Ext Sw) %"v565";
    %"v567" = #1 +p %"v566";
    %"v569" : L = Ptoi %"v567"
    => goto "L144" };
  ir_blk{ @"L570":
    call %"v571" : W = $"glibc_vfwprintf_internal#read_int"(P %"v10");
    %"v577" : W = (Cmp Eq W) %"v571", #4294967295
    => br %"v577" ? "L572" : "L574" };
  ir_blk{ @"L572":
    %"v580" : P = Copy $"__libc_errno";
    %"chk69" : A = (Check 0 4 Write 1) %"v580";
    store Ww [%"chk69" + 0] <- #75;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L574":
    %"chk70" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v586" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"chk71" : A = (Check 0 4 Read 1) %"v586";
    %"v587" : W = (RawLoad (LdNarrow Uw) 0) %"chk71";
    %"v588" : W = (Cmp Eq W) %"v587", #36
    => br %"v588" ? "L78" : "L590" };
  ir_blk{ @"L590":
    %"v595" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"chk73" : A = (Check 0 4 Read 1) %"v595";
    %"v596" : W = (RawLoad (LdNarrow Uw) 0) %"chk73";
    %"v601" : W = (Cmp Slt W) %"v596", #32
    => br %"v601" ? "L603" : "L602" };
  ir_blk{ @"L602":
    %"v605" : W = (Cmp Sgt W) %"v596", #122
    => goto "L603" };
  ir_blk{ @"L603" [%"v607" : W = phi("L590" => #1, "L602" => %"v605")]:
    => br %"v607" ? "L599" : "L598" };
  ir_blk{ @"L598":
    %"v611" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step1_jumps.279";
    %"v612" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v614" : W = Sub %"v596", #32;
    %"v615" : L = (Ext Uw) %"v614";
    %"v616" = %"v612" +p %"v615";
    %"chk74" : A = (Check 0 1 Read 1) %"v616";
    %"v617" : W = (RawLoad (LdNarrow Ub) 0) %"chk74";
    %"v618" : L = (Ext Uw) %"v617";
    %"v619" : L = Shl %"v618", #2;
    %"v620" = %"v611" +p %"v619";
    %"chk75" : A = (Check 0 4 Read 1) %"v620";
    %"v621" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v622" : L = (Ext Sw) %"v621"
    => goto "L599" };
  ir_blk{ @"L599" [%"v623" : L = phi("L598" => %"v622", "L603" => #0)]:
    %"v624" : W = Copy %"v623";
    %"v625" : L = (Ext Sw) %"v624";
    %"v626" = #1 +p %"v625";
    %"v628" : L = Ptoi %"v626"
    => goto "L144" };
  ir_blk{ @"L629":
    %"chk76" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v630" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v631" = %"v630" +p #4;
    %"chk77" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk77" + 0] <- %"v631";
    %"chk78" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v635" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"chk79" : A = (Check 0 4 Read 1) %"v635";
    %"v636" : W = (RawLoad (LdNarrow Uw) 0) %"chk79";
    %"v637" : W = (Cmp Eq W) %"v636", #42
    => br %"v637" ? "L632" : "L633" }]) (app [ir_blk{ @"L632":
    %"v639" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v640" = %"v639" +p #4;
    %"chk81" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk81" + 0] <- %"v640";
    %"chk82" : A = (Check 0 8 Write 8) %"v638";
    store.ptr [%"chk82" + 0] <- %"v640";
    %"chk83" : A = (Renew 0 8 Read 8) %"chk82", %"v638";
    %"v644" : P = (RawLoadPointer 0 load_effects) %"chk83";
    %"chk84" : A = (Check 0 4 Read 1) %"v644";
    %"v645" : W = (RawLoad (LdNarrow Uw) 0) %"chk84";
    %"v646" : W = Sub %"v645", #48;
    %"v647" : W = (Cmp Ult W) %"v646", #10
    => br %"v647" ? "L641" : "L643" };
  ir_blk{ @"L641":
    call %"v649" : W = $"glibc_vfwprintf_internal#read_int"(P %"v638");
    %"v655" : W = (Cmp Eq W) %"v649", #4294967295
    => br %"v655" ? "L650" : "L652" };
  ir_blk{ @"L650":
    %"v656" : P = Copy $"__libc_errno";
    %"chk85" : A = (Check 0 4 Write 1) %"v656";
    store Ww [%"chk85" + 0] <- #75;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L652":
    => br %"v649" ? "L663" : "L664" };
  ir_blk{ @"L663":
    %"chk86" : A = (Renew 0 8 Read 8) %"chk82", %"v638";
    %"v665" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"chk87" : A = (Check 0 4 Read 1) %"v665";
    %"v666" : W = (RawLoad (LdNarrow Uw) 0) %"chk87";
    %"v667" : W = (Cmp Eq W) %"v666", #36
    => goto "L664" };
  ir_blk{ @"L664" [%"v669" : W = phi("L652" => #0, "L663" => %"v667")]:
    => br %"v669" ? "L78" : "L643" };
  ir_blk{ @"L643":
    %"v672" : W = VaArg %"v4";
    %"v677" : W = (Cmp Slt W) %"v672", #0
    => br %"v677" ? "L634" : "L674" };
  ir_blk{ @"L674":
    => goto "L634" };
  ir_blk{ @"L633":
    %"v682" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"chk89" : A = (Check 0 4 Read 1) %"v682";
    %"v683" : W = (RawLoad (LdNarrow Uw) 0) %"chk89";
    %"v684" : W = Sub %"v683", #48;
    %"v685" : W = (Cmp Ult W) %"v684", #10
    => br %"v685" ? "L679" : "L634" };
  ir_blk{ @"L679":
    call %"v686" : W = $"glibc_vfwprintf_internal#read_int"(P %"v10");
    %"v692" : W = (Cmp Eq W) %"v686", #4294967295
    => br %"v692" ? "L687" : "L634" };
  ir_blk{ @"L687":
    %"v693" : P = Copy $"__libc_errno";
    %"chk90" : A = (Check 0 4 Write 1) %"v693";
    store Ww [%"chk90" + 0] <- #75;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L634" [%"pr.85" : W = phi("L674" => %"v672", "L643" => #4294967295, "L679" => %"v686", "L633" => #0)]:
    %"chk91" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v701" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"chk92" : A = (Check 0 4 Read 1) %"v701";
    %"v702" : W = (RawLoad (LdNarrow Uw) 0) %"chk92";
    %"v707" : W = (Cmp Slt W) %"v702", #32
    => br %"v707" ? "L709" : "L708" };
  ir_blk{ @"L708":
    %"v711" : W = (Cmp Sgt W) %"v702", #122
    => goto "L709" };
  ir_blk{ @"L709" [%"v713" : W = phi("L634" => #1, "L708" => %"v711")]:
    => br %"v713" ? "L705" : "L704" };
  ir_blk{ @"L704":
    %"v717" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step2_jumps.280";
    %"v718" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v720" : W = Sub %"v702", #32;
    %"v721" : L = (Ext Uw) %"v720";
    %"v722" = %"v718" +p %"v721";
    %"chk93" : A = (Check 0 1 Read 1) %"v722";
    %"v723" : W = (RawLoad (LdNarrow Ub) 0) %"chk93";
    %"v724" : L = (Ext Uw) %"v723";
    %"v725" : L = Shl %"v724", #2;
    %"v726" = %"v717" +p %"v725";
    %"chk94" : A = (Check 0 4 Read 1) %"v726";
    %"v727" : W = (RawLoad (LdNarrow Sw) 0) %"chk94";
    %"v728" : L = (Ext Sw) %"v727"
    => goto "L705" };
  ir_blk{ @"L705" [%"v729" : L = phi("L704" => %"v728", "L709" => #0)]:
    %"v730" : W = Copy %"v729";
    %"v731" : L = (Ext Sw) %"v730";
    %"v732" = #1 +p %"v731";
    %"v734" : L = Ptoi %"v732"
    => goto "L144" };
  ir_blk{ @"L736":
    %"chk95" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v741" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"v742" = %"v741" +p #4;
    %"chk96" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk96" + 0] <- %"v742";
    %"chk97" : A = (Check 0 4 Read 1) %"v742";
    %"v743" : W = (RawLoad (LdNarrow Uw) 0) %"chk97";
    %"v748" : W = (Cmp Slt W) %"v743", #32
    => br %"v748" ? "L750" : "L749" };
  ir_blk{ @"L749":
    %"v752" : W = (Cmp Sgt W) %"v743", #122
    => goto "L750" };
  ir_blk{ @"L750" [%"v754" : W = phi("L736" => #1, "L749" => %"v752")]:
    => br %"v754" ? "L746" : "L745" };
  ir_blk{ @"L745":
    %"v758" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step3a_jumps.281";
    %"v759" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v761" : W = Sub %"v743", #32;
    %"v762" : L = (Ext Uw) %"v761";
    %"v763" = %"v759" +p %"v762";
    %"chk98" : A = (Check 0 1 Read 1) %"v763";
    %"v764" : W = (RawLoad (LdNarrow Ub) 0) %"chk98";
    %"v765" : L = (Ext Uw) %"v764";
    %"v766" : L = Shl %"v765", #2;
    %"v767" = %"v758" +p %"v766";
    %"chk99" : A = (Check 0 4 Read 1) %"v767";
    %"v768" : W = (RawLoad (LdNarrow Sw) 0) %"chk99";
    %"v769" : L = (Ext Sw) %"v768"
    => goto "L746" };
  ir_blk{ @"L746" [%"v770" : L = phi("L745" => %"v769", "L750" => #0)]:
    %"v771" : W = Copy %"v770";
    %"v772" : L = (Ext Sw) %"v771";
    %"v773" = #1 +p %"v772";
    %"v775" : L = Ptoi %"v773"
    => goto "L144" };
  ir_blk{ @"L777":
    %"chk100" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v782" : P = (RawLoadPointer 0 load_effects) %"chk100";
    %"v783" = %"v782" +p #4;
    %"chk101" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk101" + 0] <- %"v783";
    %"chk102" : A = (Check 0 4 Read 1) %"v783";
    %"v784" : W = (RawLoad (LdNarrow Uw) 0) %"chk102";
    %"v789" : W = (Cmp Slt W) %"v784", #32
    => br %"v789" ? "L791" : "L790" };
  ir_blk{ @"L790":
    %"v793" : W = (Cmp Sgt W) %"v784", #122
    => goto "L791" };
  ir_blk{ @"L791" [%"v795" : W = phi("L777" => #1, "L790" => %"v793")]:
    => br %"v795" ? "L787" : "L786" };
  ir_blk{ @"L786":
    %"v799" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v800" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v802" : W = Sub %"v784", #32;
    %"v803" : L = (Ext Uw) %"v802";
    %"v804" = %"v800" +p %"v803";
    %"chk103" : A = (Check 0 1 Read 1) %"v804";
    %"v805" : W = (RawLoad (LdNarrow Ub) 0) %"chk103";
    %"v806" : L = (Ext Uw) %"v805";
    %"v807" : L = Shl %"v806", #2;
    %"v808" = %"v799" +p %"v807";
    %"chk104" : A = (Check 0 4 Read 1) %"v808";
    %"v809" : W = (RawLoad (LdNarrow Sw) 0) %"chk104";
    %"v810" : L = (Ext Sw) %"v809"
    => goto "L787" };
  ir_blk{ @"L787" [%"v811" : L = phi("L786" => %"v810", "L791" => #0)]:
    %"v812" : W = Copy %"v811";
    %"v813" : L = (Ext Sw) %"v812";
    %"v814" = #1 +p %"v813";
    %"v816" : L = Ptoi %"v814"
    => goto "L144" };
  ir_blk{ @"L818":
    %"chk105" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v823" : P = (RawLoadPointer 0 load_effects) %"chk105";
    %"v824" = %"v823" +p #4;
    %"chk106" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk106" + 0] <- %"v824";
    %"chk107" : A = (Check 0 4 Read 1) %"v824";
    %"v825" : W = (RawLoad (LdNarrow Uw) 0) %"chk107";
    %"v830" : W = (Cmp Slt W) %"v825", #32
    => br %"v830" ? "L832" : "L831" };
  ir_blk{ @"L831":
    %"v834" : W = (Cmp Sgt W) %"v825", #122
    => goto "L832" };
  ir_blk{ @"L832" [%"v836" : W = phi("L818" => #1, "L831" => %"v834")]:
    => br %"v836" ? "L828" : "L827" };
  ir_blk{ @"L827":
    %"v840" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step3b_jumps.282";
    %"v841" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v843" : W = Sub %"v825", #32;
    %"v844" : L = (Ext Uw) %"v843";
    %"v845" = %"v841" +p %"v844";
    %"chk108" : A = (Check 0 1 Read 1) %"v845";
    %"v846" : W = (RawLoad (LdNarrow Ub) 0) %"chk108";
    %"v847" : L = (Ext Uw) %"v846";
    %"v848" : L = Shl %"v847", #2;
    %"v849" = %"v840" +p %"v848";
    %"chk109" : A = (Check 0 4 Read 1) %"v849";
    %"v850" : W = (RawLoad (LdNarrow Sw) 0) %"chk109";
    %"v851" : L = (Ext Sw) %"v850"
    => goto "L828" };
  ir_blk{ @"L828" [%"v852" : L = phi("L827" => %"v851", "L832" => #0)]:
    %"v853" : W = Copy %"v852";
    %"v854" : L = (Ext Sw) %"v853";
    %"v855" = #1 +p %"v854";
    %"v857" : L = Ptoi %"v855"
    => goto "L144" };
  ir_blk{ @"L859":
    %"chk110" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v864" : P = (RawLoadPointer 0 load_effects) %"chk110";
    %"v865" = %"v864" +p #4;
    %"chk111" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk111" + 0] <- %"v865";
    %"chk112" : A = (Check 0 4 Read 1) %"v865";
    %"v866" : W = (RawLoad (LdNarrow Uw) 0) %"chk112";
    %"v871" : W = (Cmp Slt W) %"v866", #32
    => br %"v871" ? "L873" : "L872" };
  ir_blk{ @"L872":
    %"v875" : W = (Cmp Sgt W) %"v866", #122
    => goto "L873" };
  ir_blk{ @"L873" [%"v877" : W = phi("L859" => #1, "L872" => %"v875")]:
    => br %"v877" ? "L869" : "L868" };
  ir_blk{ @"L868":
    %"v881" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v882" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v884" : W = Sub %"v866", #32;
    %"v885" : L = (Ext Uw) %"v884";
    %"v886" = %"v882" +p %"v885";
    %"chk113" : A = (Check 0 1 Read 1) %"v886";
    %"v887" : W = (RawLoad (LdNarrow Ub) 0) %"chk113";
    %"v888" : L = (Ext Uw) %"v887";
    %"v889" : L = Shl %"v888", #2;
    %"v890" = %"v881" +p %"v889";
    %"chk114" : A = (Check 0 4 Read 1) %"v890";
    %"v891" : W = (RawLoad (LdNarrow Sw) 0) %"chk114";
    %"v892" : L = (Ext Sw) %"v891"
    => goto "L869" };
  ir_blk{ @"L869" [%"v893" : L = phi("L868" => %"v892", "L873" => #0)]:
    %"v894" : W = Copy %"v893";
    %"v895" : L = (Ext Sw) %"v894";
    %"v896" = #1 +p %"v895";
    %"v898" : L = Ptoi %"v896"
    => goto "L144" };
  ir_blk{ @"L902":
    %"chk115" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v907" : P = (RawLoadPointer 0 load_effects) %"chk115";
    %"v908" = %"v907" +p #4;
    %"chk116" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk116" + 0] <- %"v908";
    %"chk117" : A = (Check 0 4 Read 1) %"v908";
    %"v909" : W = (RawLoad (LdNarrow Uw) 0) %"chk117";
    %"v914" : W = (Cmp Slt W) %"v909", #32
    => br %"v914" ? "L916" : "L915" };
  ir_blk{ @"L915":
    %"v918" : W = (Cmp Sgt W) %"v909", #122
    => goto "L916" };
  ir_blk{ @"L916" [%"v920" : W = phi("L902" => #1, "L915" => %"v918")]:
    => br %"v920" ? "L912" : "L911" };
  ir_blk{ @"L911":
    %"v924" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v925" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v927" : W = Sub %"v909", #32;
    %"v928" : L = (Ext Uw) %"v927";
    %"v929" = %"v925" +p %"v928";
    %"chk118" : A = (Check 0 1 Read 1) %"v929";
    %"v930" : W = (RawLoad (LdNarrow Ub) 0) %"chk118";
    %"v931" : L = (Ext Uw) %"v930";
    %"v932" : L = Shl %"v931", #2;
    %"v933" = %"v924" +p %"v932";
    %"chk119" : A = (Check 0 4 Read 1) %"v933";
    %"v934" : W = (RawLoad (LdNarrow Sw) 0) %"chk119";
    %"v935" : L = (Ext Sw) %"v934"
    => goto "L912" }] [ir_blk{ @"L912" [%"v936" : L = phi("L911" => %"v935", "L916" => #0)]:
    %"v937" : W = Copy %"v936";
    %"v938" : L = (Ext Sw) %"v937";
    %"v939" = #1 +p %"v938";
    %"v941" : L = Ptoi %"v939"
    => goto "L144" };
  ir_blk{ @"L945":
    %"chk120" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v950" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"v951" = %"v950" +p #4;
    %"chk121" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk121" + 0] <- %"v951";
    %"chk122" : A = (Check 0 4 Read 1) %"v951";
    %"v952" : W = (RawLoad (LdNarrow Uw) 0) %"chk122";
    %"v957" : W = (Cmp Slt W) %"v952", #32
    => br %"v957" ? "L959" : "L958" };
  ir_blk{ @"L958":
    %"v961" : W = (Cmp Sgt W) %"v952", #122
    => goto "L959" };
  ir_blk{ @"L959" [%"v963" : W = phi("L945" => #1, "L958" => %"v961")]:
    => br %"v963" ? "L955" : "L954" };
  ir_blk{ @"L954":
    %"v967" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v968" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v970" : W = Sub %"v952", #32;
    %"v971" : L = (Ext Uw) %"v970";
    %"v972" = %"v968" +p %"v971";
    %"chk123" : A = (Check 0 1 Read 1) %"v972";
    %"v973" : W = (RawLoad (LdNarrow Ub) 0) %"chk123";
    %"v974" : L = (Ext Uw) %"v973";
    %"v975" : L = Shl %"v974", #2;
    %"v976" = %"v967" +p %"v975";
    %"chk124" : A = (Check 0 4 Read 1) %"v976";
    %"v977" : W = (RawLoad (LdNarrow Sw) 0) %"chk124";
    %"v978" : L = (Ext Sw) %"v977"
    => goto "L955" };
  ir_blk{ @"L955" [%"v979" : L = phi("L954" => %"v978", "L959" => #0)]:
    %"v980" : W = Copy %"v979";
    %"v981" : L = (Ext Sw) %"v980";
    %"v982" = #1 +p %"v981";
    %"v984" : L = Ptoi %"v982"
    => goto "L144" };
  ir_blk{ @"L988":
    %"chk125" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v993" : P = (RawLoadPointer 0 load_effects) %"chk125";
    %"v994" = %"v993" +p #4;
    %"chk126" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk126" + 0] <- %"v994";
    %"chk127" : A = (Check 0 4 Read 1) %"v994";
    %"v995" : W = (RawLoad (LdNarrow Uw) 0) %"chk127";
    %"v1000" : W = (Cmp Slt W) %"v995", #32
    => br %"v1000" ? "L1002" : "L1001" };
  ir_blk{ @"L1001":
    %"v1004" : W = (Cmp Sgt W) %"v995", #122
    => goto "L1002" };
  ir_blk{ @"L1002" [%"v1006" : W = phi("L988" => #1, "L1001" => %"v1004")]:
    => br %"v1006" ? "L998" : "L997" };
  ir_blk{ @"L997":
    %"v1010" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v1011" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v1013" : W = Sub %"v995", #32;
    %"v1014" : L = (Ext Uw) %"v1013";
    %"v1015" = %"v1011" +p %"v1014";
    %"chk128" : A = (Check 0 1 Read 1) %"v1015";
    %"v1016" : W = (RawLoad (LdNarrow Ub) 0) %"chk128";
    %"v1017" : L = (Ext Uw) %"v1016";
    %"v1018" : L = Shl %"v1017", #2;
    %"v1019" = %"v1010" +p %"v1018";
    %"chk129" : A = (Check 0 4 Read 1) %"v1019";
    %"v1020" : W = (RawLoad (LdNarrow Sw) 0) %"chk129";
    %"v1021" : L = (Ext Sw) %"v1020"
    => goto "L998" };
  ir_blk{ @"L998" [%"v1022" : L = phi("L997" => %"v1021", "L1002" => #0)]:
    %"v1023" : W = Copy %"v1022";
    %"v1024" : L = (Ext Sw) %"v1023";
    %"v1025" = #1 +p %"v1024";
    %"v1027" : L = Ptoi %"v1025"
    => goto "L144" };
  ir_blk{ @"L1028":
    %"chk130" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1029" : P = (RawLoadPointer 0 load_effects) %"chk130";
    %"v1030" = %"v1029" +p #4;
    %"chk131" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk131" + 0] <- %"v1030";
    %"chk132" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1036" : P = (RawLoadPointer 0 load_effects) %"chk132";
    %"chk133" : A = (Check 0 4 Read 1) %"v1036";
    %"v1037" : W = (RawLoad (LdNarrow Uw) 0) %"chk133";
    %"v1038" : W = (Cmp Eq W) %"v1037", #102
    => br %"v1038" ? "L1033" : "L1035" };
  ir_blk{ @"L1033":
    %"v1039" : P = (RawLoadPointer 0 load_effects) %"chk132";
    %"v1040" = %"v1039" +p #4;
    %"chk135" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk135" + 0] <- %"v1040"
    => goto "L1035" };
  ir_blk{ @"L1035" [%"pr.99" : W = phi("L1033" => #1, "L1028" => #0)]:
    %"chk136" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1046" : P = (RawLoadPointer 0 load_effects) %"chk136";
    %"chk137" : A = (Check 0 4 Read 1) %"v1046";
    %"v1047" : W = (RawLoad (LdNarrow Uw) 0) %"chk137";
    %"v1048" : W = Sub %"v1047", #48;
    %"v1049" : W = (Cmp Ult W) %"v1048", #10
    => br %"v1049" ? "L1043" : "L1045" };
  ir_blk{ @"L1043":
    call %"v1050" : W = $"glibc_vfwprintf_internal#read_int"(P %"v10")
    => goto "L1045" };
  ir_blk{ @"L1045" [%"pr.100" : W = phi("L1043" => %"v1050", "L1035" => #0)]:
    => br %"pr.99" ? "L1056" : "L1053" };
  ir_blk{ @"L1056":
    %"v1063" : W = (Cmp Eq W) %"pr.100", #8
    => br %"v1063" ? "L1053" : "L1064" };
  ir_blk{ @"L1064":
    %"v1065" : W = (Cmp Eq W) %"pr.100", #16
    => br %"v1065" ? "L1053" : "L1066" };
  ir_blk{ @"L1066":
    %"v1067" : W = (Cmp Eq W) %"pr.100", #32
    => br %"v1067" ? "L1053" : "L1068" };
  ir_blk{ @"L1068":
    %"v1069" : W = (Cmp Eq W) %"pr.100", #64
    => br %"v1069" ? "L1053" : "L1070" };
  ir_blk{ @"L1070":
    => goto "L1053" };
  ir_blk{ @"L1053" [%"pr.101" : W = phi("L1070" => %"pr.100", "L1056" => #8, "L1064" => #64, "L1066" => #64, "L1068" => #64, "L1045" => %"pr.100")]:
    %"v1082" : W = (Cmp Eq W) %"pr.101", #8
    => br %"v1082" ? "L1073" : "L1083" };
  ir_blk{ @"L1078":
    %"v1079" : P = Copy $"__libc_errno";
    %"chk138" : A = (Check 0 4 Write 1) %"v1079";
    store Ww [%"chk138" + 0] <- #22;
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0")
    => goto "L508" };
  ir_blk{ @"L1083":
    %"v1084" : W = (Cmp Eq W) %"pr.101", #16
    => br %"v1084" ? "L1073" : "L1085" };
  ir_blk{ @"L1085":
    %"v1086" : W = (Cmp Eq W) %"pr.101", #32
    => br %"v1086" ? "L1073" : "L1087" };
  ir_blk{ @"L1087":
    %"v1088" : W = (Cmp Eq W) %"pr.101", #64
    => br %"v1088" ? "L1073" : poll "L1078" };
  ir_blk{ @"L1073" [%"pr.64" : W = phi("L1053" => #1, "L1083" => %"pr.65", "L1085" => %"pr.65", "L1087" => %"pr.65"); %"pr.61" : W = phi("L1053" => %"pr.62", "L1083" => %"pr.62", "L1085" => %"pr.62", "L1087" => #1); %"pr.59" : W = phi("L1053" => %"pr.60", "L1083" => #1, "L1085" => %"pr.60", "L1087" => %"pr.60"); %"pr.56" : W = phi("L1053" => %"pr.57", "L1083" => %"pr.57", "L1085" => %"pr.57", "L1087" => #1)]:
    %"chk139" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1095" : P = (RawLoadPointer 0 load_effects) %"chk139";
    %"chk140" : A = (Check 0 4 Read 1) %"v1095";
    %"v1096" : W = (RawLoad (LdNarrow Uw) 0) %"chk140";
    %"v1101" : W = (Cmp Slt W) %"v1096", #32
    => br %"v1101" ? "L1103" : "L1102" };
  ir_blk{ @"L1102":
    %"v1105" : W = (Cmp Sgt W) %"v1096", #122
    => goto "L1103" };
  ir_blk{ @"L1103" [%"v1107" : W = phi("L1073" => #1, "L1102" => %"v1105")]:
    => br %"v1107" ? "L1099" : "L1098" };
  ir_blk{ @"L1098":
    %"v1111" : P = Copy $"glibc_vfwprintf_internal#__wprintf_buffer.step4_jumps.283";
    %"v1112" : P = Copy $"glibc_vfwprintf_internal#jump_table";
    %"v1114" : W = Sub %"v1096", #32;
    %"v1115" : L = (Ext Uw) %"v1114";
    %"v1116" = %"v1112" +p %"v1115";
    %"chk141" : A = (Check 0 1 Read 1) %"v1116";
    %"v1117" : W = (RawLoad (LdNarrow Ub) 0) %"chk141";
    %"v1118" : L = (Ext Uw) %"v1117";
    %"v1119" : L = Shl %"v1118", #2;
    %"v1120" = %"v1111" +p %"v1119";
    %"chk142" : A = (Check 0 4 Read 1) %"v1120";
    %"v1121" : W = (RawLoad (LdNarrow Sw) 0) %"chk142";
    %"v1122" : L = (Ext Sw) %"v1121"
    => goto "L1099" };
  ir_blk{ @"L1099" [%"v1123" : L = phi("L1098" => %"v1122", "L1103" => #0)]:
    %"v1124" : W = Copy %"v1123";
    %"v1125" : L = (Ext Sw) %"v1124";
    %"v1126" = #1 +p %"v1125";
    %"v1128" : L = Ptoi %"v1126"
    => goto "L144" };
  ir_blk{ @"L1132":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #37)
    => goto "L1131" };
  ir_blk{ @"L1136":
    => br %"pr.62" ? "L1154" : "L1155" };
  ir_blk{ @"L1154":
    %"v1159" : L = VaArg %"v4"
    => goto "L1156" };
  ir_blk{ @"L1155":
    => br %"pr.65" ? "L1160" : "L1161" };
  ir_blk{ @"L1160":
    %"v1165" : W = VaArg %"v4";
    %"v1166" : W = (Ext Sb) %"v1165";
    %"v1167" : L = (Ext Sw) %"v1166"
    => goto "L1156" };
  ir_blk{ @"L1161":
    %"v1172" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1172" ? "L1168" : "L1169" };
  ir_blk{ @"L1168":
    %"v1174" : W = VaArg %"v4";
    %"v1175" : L = (Ext Sw) %"v1174"
    => goto "L1156" };
  ir_blk{ @"L1169":
    %"v1177" : W = VaArg %"v4";
    %"v1178" : W = (Ext Sh) %"v1177";
    %"v1179" : L = (Ext Sw) %"v1178"
    => goto "L1156" };
  ir_blk{ @"L1156" [%"pr.103" : L = phi("L1154" => %"v1159", "L1160" => %"v1167", "L1168" => %"v1175", "L1169" => %"v1179")]:
    %"v1181" : W = (Cmp Slt L) %"pr.103", #0
    => br %"v1181" ? "L1182" : "L1190" }])) (app (app [ir_blk{ @"L1182":
    %"v1187" : L = Neg %"pr.103"
    => goto "L1190" };
  ir_blk{ @"L1192" [%"pr.29" : W = phi("L2154" => #10, "L2157" => #8, "L2159" => #16, "L2185" => #2)]:
    => br %"pr.62" ? "L1239" : "L1240" };
  ir_blk{ @"L1239":
    %"v1244" : L = VaArg %"v4"
    => goto "L1190" };
  ir_blk{ @"L1240":
    => br %"pr.65" ? "L1245" : "L1246" };
  ir_blk{ @"L1245":
    %"v1250" : W = VaArg %"v4";
    %"v1251" : W = (Ext Ub) %"v1250";
    %"v1252" : L = (Ext Uw) %"v1251"
    => goto "L1190" };
  ir_blk{ @"L1246":
    %"v1257" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1257" ? "L1253" : "L1254" };
  ir_blk{ @"L1253":
    %"v1259" : W = VaArg %"v4";
    %"v1260" : L = (Ext Uw) %"v1259"
    => goto "L1190" };
  ir_blk{ @"L1254":
    %"v1262" : W = VaArg %"v4";
    %"v1263" : W = (Ext Uh) %"v1262";
    %"v1264" : L = (Ext Uw) %"v1263"
    => goto "L1190" };
  ir_blk{ @"L1190" [%"pr.95" : W = phi("L1182" => %"pr.97", "L1156" => %"pr.97", "L1239" => %"pr.97", "L1245" => %"pr.97", "L1253" => %"pr.97", "L1254" => %"pr.97", "L1648" => #120, "L1763" => %"pr.97", "L1752" => %"pr.97"); %"pr.53" : W = phi("L1182" => %"pr.55", "L1156" => %"pr.55", "L1239" => %"pr.55", "L1245" => %"pr.55", "L1253" => %"pr.55", "L1254" => %"pr.55", "L1648" => #0, "L1763" => %"pr.55", "L1752" => %"pr.55"); %"pr.50" : W = phi("L1182" => %"pr.52", "L1156" => %"pr.52", "L1239" => #0, "L1245" => #0, "L1253" => #0, "L1254" => #0, "L1648" => %"pr.52", "L1763" => %"pr.52", "L1752" => %"pr.52"); %"pr.44" : W = phi("L1182" => %"pr.46", "L1156" => %"pr.46", "L1239" => #0, "L1245" => #0, "L1253" => #0, "L1254" => #0, "L1648" => %"pr.46", "L1763" => %"pr.46", "L1752" => %"pr.46"); %"pr.40" : W = phi("L1182" => %"pr.42", "L1156" => %"pr.42", "L1239" => %"pr.42", "L1245" => %"pr.42", "L1253" => %"pr.42", "L1254" => %"pr.42", "L1648" => #1, "L1763" => %"pr.42", "L1752" => %"pr.42"); %"pr.28" : W = phi("L1182" => #10, "L1156" => #10, "L1239" => %"pr.29", "L1245" => %"pr.29", "L1253" => %"pr.29", "L1254" => %"pr.29", "L1648" => #16, "L1763" => #10, "L1752" => #10); %"pr.21" : L = phi("L1182" => %"v1187", "L1156" => %"pr.103", "L1239" => %"v1244", "L1245" => %"v1252", "L1253" => %"v1260", "L1254" => %"v1264", "L1648" => %"v1656", "L1763" => %"v1768", "L1752" => %"v1762"); %"pr.18" : W = phi("L1182" => %"v1181", "L1156" => %"v1181", "L1239" => #0, "L1245" => #0, "L1253" => #0, "L1254" => #0, "L1648" => #0, "L1763" => %"v1760", "L1752" => %"v1760")]:
    %"v1269" : W = (Cmp Slt W) %"pr.82", #0
    => br %"v1269" ? "L1267" : "L1266" };
  ir_blk{ @"L1266":
    => goto "L1267" };
  ir_blk{ @"L1267" [%"pr.91" : W = phi("L1266" => #32, "L1190" => %"pr.92"); %"pr.81" : W = phi("L1266" => %"pr.82", "L1190" => #1)]:
    %"v1274" : W = (Cmp Eq W) %"pr.81", #0
    => br %"v1274" ? "L1275" : "L1276" };
  ir_blk{ @"L1275":
    %"v1278" : W = (Cmp Eq L) %"pr.21", #0
    => goto "L1276" };
  ir_blk{ @"L1276" [%"v1280" : W = phi("L1267" => #0, "L1275" => %"v1278")]:
    => br %"v1280" ? "L1270" : "L1271" };
  ir_blk{ @"L1270":
    %"v1286" : W = (Cmp Eq W) %"pr.28", #8
    => br %"v1286" ? "L1287" : "L1288" };
  ir_blk{ @"L1287":
    => goto "L1288" };
  ir_blk{ @"L1288" [%"v1291" : W = phi("L1270" => #0, "L1287" => %"pr.40")]:
    => br %"v1291" ? "L1282" : "L1272" };
  ir_blk{ @"L1282":
    (Flight (a "v1293") Sub [(FAddress (t "v103")); (FValue (Const 4))] (LowerOf (t "v103")));
    %"chk143" : A = (Check 0 4 Write 1) %"v1293";
    store Ww [%"chk143" + 0] <- #48
    => goto "L1272" };
  ir_blk{ @"L1271":
    %"v1298" : W = (Cmp Eq W) %"pr.95", #88
    => br %"v1298" ? "iw_2.L9" : "iw_2.L10" };
  ir_blk{ @"iw_2.L9":
    %"iw_2.v13" : P = Copy $"_itowa_upper_digits"
    => goto "iw_2.L11" };
  ir_blk{ @"iw_2.L10":
    %"iw_2.v14" : P = Copy $"_itowa_lower_digits"
    => goto "iw_2.L11" };
  ir_blk{ @"iw_2.L11" [%"iw_2.v15" : P = phi("iw_2.L9" => %"iw_2.v13", "iw_2.L10" => %"iw_2.v14")]:
    %"iw_2.v85" : W = (Cmp Eq W) %"pr.28", #10
    => br %"iw_2.v85" ? "iw_2.L22" : "iw_2.L86" };
  ir_blk{ @"iw_2.L22" [%"iw_2.pr.6" : P = phi("iw_2.L22" => %"iw_2.v26", "iw_2.L11" => %"v103"); %"iw_2.pr.1" : L = phi("iw_2.L22" => %"iw_2.v34", "iw_2.L11" => %"pr.21")]:
    (Flight (a "iw_2.v26") Sub [(FAddress (t "iw_2.pr.6")); (FValue (Const 4))] (LowerOf (t "iw_2.pr.6")));
    %"iw_2.v29" : L = Urem %"iw_2.pr.1", #10;
    %"iw_2.v30" : L = Shl %"iw_2.v29", #2;
    %"iw_2.v31" = %"iw_2.v15" +p %"iw_2.v30";
    %"chk144" : A = (Check 0 4 Read 1) %"iw_2.v31";
    %"iw_2.v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk144";
    %"chk145" : A = (Check 0 4 Write 1) %"iw_2.v26";
    store Ww [%"chk145" + 0] <- %"iw_2.v32";
    %"iw_2.v34" : L = Udiv %"iw_2.pr.1", #10;
    %"iw_2.v35" : W = (Cmp Ne L) %"iw_2.v34", #0
    => br %"iw_2.v35" ? poll "iw_2.L22" : "iw_2.L20" };
  ir_blk{ @"iw_2.L37" [%"iw_2.pr.7" : P = phi("iw_2.L37" => %"iw_2.v41", "iw_2.L86" => %"v103"); %"iw_2.pr.2" : L = phi("iw_2.L37" => %"iw_2.v49", "iw_2.L86" => %"pr.21")]:
    (Flight (a "iw_2.v41") Sub [(FAddress (t "iw_2.pr.7")); (FValue (Const 4))] (LowerOf (t "iw_2.pr.7")));
    %"iw_2.v44" : L = And %"iw_2.pr.2", #15;
    %"iw_2.v45" : L = Shl %"iw_2.v44", #2;
    %"iw_2.v46" = %"iw_2.v15" +p %"iw_2.v45";
    %"chk146" : A = (Check 0 4 Read 1) %"iw_2.v46";
    %"iw_2.v47" : W = (RawLoad (LdNarrow Sw) 0) %"chk146";
    %"chk147" : A = (Check 0 4 Write 1) %"iw_2.v41";
    store Ww [%"chk147" + 0] <- %"iw_2.v47";
    %"iw_2.v49" : L = Shr %"iw_2.pr.2", #4;
    %"iw_2.v50" : W = (Cmp Ne L) %"iw_2.v49", #0
    => br %"iw_2.v50" ? poll "iw_2.L37" : "iw_2.L20" };
  ir_blk{ @"iw_2.L52" [%"iw_2.pr.8" : P = phi("iw_2.L52" => %"iw_2.v56", "iw_2.L88" => %"v103"); %"iw_2.pr.3" : L = phi("iw_2.L52" => %"iw_2.v64", "iw_2.L88" => %"pr.21")]:
    (Flight (a "iw_2.v56") Sub [(FAddress (t "iw_2.pr.8")); (FValue (Const 4))] (LowerOf (t "iw_2.pr.8")));
    %"iw_2.v59" : L = And %"iw_2.pr.3", #7;
    %"iw_2.v60" : L = Shl %"iw_2.v59", #2;
    %"iw_2.v61" = %"iw_2.v15" +p %"iw_2.v60";
    %"chk148" : A = (Check 0 4 Read 1) %"iw_2.v61";
    %"iw_2.v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk148";
    %"chk149" : A = (Check 0 4 Write 1) %"iw_2.v56";
    store Ww [%"chk149" + 0] <- %"iw_2.v62";
    %"iw_2.v64" : L = Shr %"iw_2.pr.3", #3;
    %"iw_2.v65" : W = (Cmp Ne L) %"iw_2.v64", #0
    => br %"iw_2.v65" ? poll "iw_2.L52" : "iw_2.L20" };
  ir_blk{ @"iw_2.L67" [%"iw_2.pr.9" : P = phi("iw_2.L67" => %"iw_2.v71", "iw_2.L88" => %"v103"); %"iw_2.pr.4" : L = phi("iw_2.L67" => %"iw_2.v83", "iw_2.L88" => %"pr.21")]:
    (Flight (a "iw_2.v71") Sub [(FAddress (t "iw_2.pr.9")); (FValue (Const 4))] (LowerOf (t "iw_2.pr.9")));
    %"iw_2.v75" : L = (Ext Uw) %"pr.28";
    %"iw_2.v76" : L = Urem %"iw_2.pr.4", %"iw_2.v75";
    %"iw_2.v77" : L = Shl %"iw_2.v76", #2;
    %"iw_2.v78" = %"iw_2.v15" +p %"iw_2.v77";
    %"chk150" : A = (Check 0 4 Read 1) %"iw_2.v78";
    %"iw_2.v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk150";
    %"chk151" : A = (Check 0 4 Write 1) %"iw_2.v71";
    store Ww [%"chk151" + 0] <- %"iw_2.v79";
    %"iw_2.v83" : L = Udiv %"iw_2.pr.4", %"iw_2.v75";
    %"iw_2.v84" : W = (Cmp Ne L) %"iw_2.v83", #0
    => br %"iw_2.v84" ? poll "iw_2.L67" : "iw_2.L20" };
  ir_blk{ @"iw_2.L86":
    %"iw_2.v87" : W = (Cmp Eq W) %"pr.28", #16
    => br %"iw_2.v87" ? poll "iw_2.L37" : "iw_2.L88" };
  ir_blk{ @"iw_2.L88":
    %"iw_2.v89" : W = (Cmp Eq W) %"pr.28", #8
    => br %"iw_2.v89" ? poll "iw_2.L52" : poll "iw_2.L67" };
  ir_blk{ @"iw_2.L20" [%"iw_2.pr.5" : P = phi("iw_2.L22" => %"iw_2.v26", "iw_2.L37" => %"iw_2.v41", "iw_2.L52" => %"iw_2.v56", "iw_2.L67" => %"iw_2.v71")]:
    => goto "L1272" };
  ir_blk{ @"L1272" [%"pr.34" : P = phi("L1282" => %"v1293", "L1288" => %"v103", "iw_2.L20" => %"iw_2.pr.5")]:
    => br %"pr.53" ? "L1304" : "L1303" };
  ir_blk{ @"L1303":
    => br %"pr.88" ? "L1306" : "L1304" };
  ir_blk{ @"L1306":
    %"v1309" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1304" };
  ir_blk{ @"L1304" [%"v1313" : W = phi("L1272" => #1, "L1303" => #0, "L1306" => %"v1309")]:
    => br %"pr.53" ? "L1315" : "L1316" };
  ir_blk{ @"L1315":
    %"v1319" : P = Copy $"__libc_tsd_LOCALE";
    %"chk152" : A = (Check 0 8 Read 8) %"v1319";
    %"v1320" : P = (RawLoadPointer 0 load_effects) %"chk152";
    %"v1323" : L = Ptoi %"v103";
    %"v1324" : L = Ptoi %"pr.34";
    %"v1325" : L = Sub %"v1323", %"v1324";
    %"v1326" : L = Div %"v1325", #4;
    call %"v1327" : W = $"__grouping_iterator_init"(P %"v1300", W #1, P %"v1320", W %"v1326")
    => goto "L1317" };
  ir_blk{ @"L1316":
    => br %"pr.88" ? "L1333" : "L1334" };
  ir_blk{ @"L1333":
    %"v1336" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1334" };
  ir_blk{ @"L1334" [%"v1338" : W = phi("L1316" => #0, "L1333" => %"v1336")]:
    => br %"v1338" ? "L1329" : "L1317" };
  ir_blk{ @"L1329":
    %"v1341" : L = Ptoi %"v103";
    %"v1342" : L = Ptoi %"pr.34";
    %"v1343" : L = Sub %"v1341", %"v1342";
    %"v1344" : L = Div %"v1343", #4;
    call %"v1345" : W = $"__grouping_iterator_init_none"(P %"v1300", W %"v1344")
    => goto "L1317" };
  ir_blk{ @"L1317":
    %"v1350" : L = Ptoi %"v103";
    %"v1351" : L = Ptoi %"pr.34";
    %"v1352" : L = Sub %"v1350", %"v1351";
    %"v1353" : L = Div %"v1352", #4
    => br %"pr.53" ? "L1358" : "L1359" };
  ir_blk{ @"L1358":
    %"v1361" : W = (Cmp Ne W) %"pr.1", #0
    => goto "L1359" };
  ir_blk{ @"L1359" [%"v1363" : W = phi("L1317" => #0, "L1358" => %"v1361")]:
    => br %"v1363" ? "L1354" : "L1356" }] [ir_blk{ @"L1354":
    %"v1364" : W = Copy %"v1353";
    %"v1365" = %"v1300" +p #20;
    %"chk153" : A = (Check 0 4 Read 1) %"v1365";
    %"v1366" : W = (RawLoad (LdNarrow Uw) 0) %"chk153";
    %"v1367" : W = Add %"v1364", %"v1366"
    => goto "L1356" };
  ir_blk{ @"L1356" [%"pr.106" : W = phi("L1354" => %"v1367", "L1359" => %"v1353")]:
    %"v1371" : W = (Cmp Sle W) %"pr.81", %"pr.106"
    => br %"v1371" ? "L1372" : "L1373" };
  ir_blk{ @"L1372":
    %"v1375" : W = (Cmp Ne L) %"pr.21", #0
    => goto "L1373" };
  ir_blk{ @"L1373" [%"v1377" : W = phi("L1356" => #0, "L1372" => %"v1375")]:
    => br %"v1377" ? "L1378" : "L1379" };
  ir_blk{ @"L1378":
    => goto "L1379" };
  ir_blk{ @"L1379" [%"v1382" : W = phi("L1373" => #0, "L1378" => %"pr.40")]:
    => br %"v1382" ? "L1383" : "L1384" };
  ir_blk{ @"L1383":
    %"v1386" : W = (Cmp Eq W) %"pr.28", #8
    => goto "L1384" };
  ir_blk{ @"L1384" [%"v1388" : W = phi("L1379" => #0, "L1383" => %"v1386")]:
    %"v1400" : L = Div %"v1352", #4;
    %"v1401" : L = (Ext Sw) %"pr.81";
    %"v1402" : L = Sub %"v1401", %"v1400";
    %"v1403" : W = (Cmp Slt L) %"v1402", #0
    => br %"v1403" ? "L1393" : "L1392" };
  ir_blk{ @"L1392":
    %"v1410" : L = Div %"v1352", #4;
    %"v1412" : L = Sub %"v1401", %"v1410"
    => goto "L1393" };
  ir_blk{ @"L1393" [%"v1413" : L = phi("L1392" => %"v1412", "L1384" => #0)]:
    %"v1418" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1418" ? "L1414" : "L1415" };
  ir_blk{ @"L1414":
    %"v1421" : W = Copy %"v1413";
    %"v1422" : W = Add %"pr.106", %"v1421";
    %"v1423" : W = Sub %"pr.67", %"v1422";
    %"v1428" : W = (Cmp Ne L) %"pr.21", #0
    => br %"v1428" ? "L1429" : "L1430" };
  ir_blk{ @"L1429":
    => goto "L1430" };
  ir_blk{ @"L1430" [%"v1433" : W = phi("L1414" => #0, "L1429" => %"pr.40")]:
    => br %"v1433" ? "L1434" : "L1435" };
  ir_blk{ @"L1434":
    %"v1437" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1437" ? "L1435" : "L1438" };
  ir_blk{ @"L1438":
    %"v1441" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1435" };
  ir_blk{ @"L1435" [%"v1445" : W = phi("L1430" => #0, "L1434" => #1, "L1438" => %"v1441")]:
    => br %"v1445" ? "L1424" : "L1426" };
  ir_blk{ @"L1424":
    %"v1447" : W = Sub %"v1423", #2
    => goto "L1426" };
  ir_blk{ @"L1426" [%"pr.66" : W = phi("L1424" => %"v1447", "L1435" => %"v1423")]:
    => br %"v1388" ? "L1448" : "L1450" };
  ir_blk{ @"L1448":
    %"v1453" : W = Sub %"pr.66", #1
    => goto "L1450" };
  ir_blk{ @"L1450" [%"pr.68" : W = phi("L1448" => %"v1453", "L1426" => %"pr.66")]:
    => br %"pr.18" ? "L1459" : "L1458" };
  ir_blk{ @"L1458":
    => goto "L1459" };
  ir_blk{ @"L1459" [%"v1462" : W = phi("L1450" => #1, "L1458" => %"pr.50")]:
    => br %"v1462" ? "L1464" : "L1463" };
  ir_blk{ @"L1463":
    => goto "L1464" };
  ir_blk{ @"L1464" [%"v1467" : W = phi("L1459" => #1, "L1463" => %"pr.44")]:
    => br %"v1467" ? "L1454" : "L1456" };
  ir_blk{ @"L1454":
    %"v1469" : W = Sub %"pr.68", #1
    => goto "L1456" };
  ir_blk{ @"L1456" [%"pr.69" : W = phi("L1454" => %"v1469", "L1464" => %"pr.68")]:
    %"v1474" : W = (Cmp Eq W) %"pr.91", #32
    => br %"v1474" ? "L1470" : "L1472" };
  ir_blk{ @"L1470":
    %"v1477" : L = (Ext Sw) %"pr.69";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1477")
    => goto "L1472" };
  ir_blk{ @"L1472" [%"pr.70" : W = phi("L1470" => #0, "L1456" => %"pr.69")]:
    => br %"pr.18" ? "L1478" : "L1479" };
  ir_blk{ @"L1478":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #45)
    => goto "L1480" };
  ir_blk{ @"L1479":
    => br %"pr.50" ? "L1483" : "L1484" };
  ir_blk{ @"L1483":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #43)
    => goto "L1480" };
  ir_blk{ @"L1484":
    => br %"pr.44" ? "L1488" : "L1480" };
  ir_blk{ @"L1488":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #32)
    => goto "L1480" };
  ir_blk{ @"L1480":
    => br %"v1428" ? "L1498" : "L1499" };
  ir_blk{ @"L1498":
    => goto "L1499" };
  ir_blk{ @"L1499" [%"v1502" : W = phi("L1480" => #0, "L1498" => %"pr.40")]:
    => br %"v1502" ? "L1503" : "L1504" };
  ir_blk{ @"L1503":
    %"v1506" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1506" ? "L1504" : "L1507" };
  ir_blk{ @"L1507":
    %"v1510" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1504" };
  ir_blk{ @"L1504" [%"v1514" : W = phi("L1499" => #0, "L1503" => #1, "L1507" => %"v1510")]:
    => br %"v1514" ? "L1493" : "L1495" };
  ir_blk{ @"L1493":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48);
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"pr.95")
    => goto "L1495" }]) (app [ir_blk{ @"L1495":
    %"v1519" : W = Copy %"v1413";
    %"v1520" : W = Add %"pr.70", %"v1519";
    %"v1523" : L = (Ext Sw) %"v1520";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #48, L %"v1523")
    => br %"v1388" ? "L1524" : "L1526" };
  ir_blk{ @"L1524":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48)
    => goto "L1526" };
  ir_blk{ @"L1526":
    => br %"v1313" ? "L1529" : "L1530" };
  ir_blk{ @"L1529":
    => br %"pr.88" ? "L1538" : "L1539" };
  ir_blk{ @"L1538":
    %"v1541" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1539" };
  ir_blk{ @"L1539" [%"v1543" : W = phi("L1529" => #0, "L1538" => %"v1541")]:
    call void $"glibc_vfwprintf_internal#group_number"(P %"v0", P %"v1300", P %"pr.34", P %"v103", W %"pr.1", W %"v1543")
    => goto "L1131" };
  ir_blk{ @"L1530":
    %"v1552" : L = Div %"v1352", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.34", L %"v1552")
    => goto "L1131" };
  ir_blk{ @"L1415":
    => br %"pr.18" ? "L1554" : "L1555" };
  ir_blk{ @"L1554":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #45);
    %"v1560" : W = Sub %"pr.67", #1
    => goto "L1556" };
  ir_blk{ @"L1555":
    => br %"pr.50" ? "L1561" : "L1562" };
  ir_blk{ @"L1561":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #43);
    %"v1567" : W = Sub %"pr.67", #1
    => goto "L1556" };
  ir_blk{ @"L1562":
    => br %"pr.44" ? "L1568" : "L1556" };
  ir_blk{ @"L1568":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #32);
    %"v1574" : W = Sub %"pr.67", #1
    => goto "L1556" };
  ir_blk{ @"L1556" [%"pr.71" : W = phi("L1554" => %"v1560", "L1561" => %"v1567", "L1568" => %"v1574", "L1562" => %"pr.67")]:
    %"v1579" : W = (Cmp Ne L) %"pr.21", #0
    => br %"v1579" ? "L1580" : "L1581" };
  ir_blk{ @"L1580":
    => goto "L1581" };
  ir_blk{ @"L1581" [%"v1584" : W = phi("L1556" => #0, "L1580" => %"pr.40")]:
    => br %"v1584" ? "L1585" : "L1586" };
  ir_blk{ @"L1585":
    %"v1588" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1588" ? "L1586" : "L1589" };
  ir_blk{ @"L1589":
    %"v1592" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1586" };
  ir_blk{ @"L1586" [%"v1596" : W = phi("L1581" => #0, "L1585" => #1, "L1589" => %"v1592")]:
    => br %"v1596" ? "L1575" : "L1577" };
  ir_blk{ @"L1575":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48);
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"pr.95");
    %"v1601" : W = Sub %"pr.71", #2
    => goto "L1577" };
  ir_blk{ @"L1577" [%"pr.74" : W = phi("L1575" => %"v1601", "L1586" => %"pr.71")]:
    => br %"v1388" ? "L1602" : "L1604" };
  ir_blk{ @"L1602":
    %"v1607" : W = Sub %"pr.74", #1
    => goto "L1604" };
  ir_blk{ @"L1604" [%"pr.75" : W = phi("L1602" => %"v1607", "L1577" => %"pr.74")]:
    %"v1610" : W = Copy %"v1413";
    %"v1611" : W = Add %"pr.106", %"v1610";
    %"v1612" : W = Sub %"pr.75", %"v1611";
    %"v1614" : W = Copy %"v1413";
    %"v1615" : L = (Ext Uw) %"v1614";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #48, L %"v1615")
    => br %"v1388" ? "L1616" : "L1618" };
  ir_blk{ @"L1616":
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W #48)
    => goto "L1618" };
  ir_blk{ @"L1618":
    => br %"v1313" ? "L1621" : "L1622" };
  ir_blk{ @"L1621":
    => br %"pr.88" ? "L1630" : "L1631" };
  ir_blk{ @"L1630":
    %"v1633" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1631" };
  ir_blk{ @"L1631" [%"v1635" : W = phi("L1621" => #0, "L1630" => %"v1633")]:
    call void $"glibc_vfwprintf_internal#group_number"(P %"v0", P %"v1300", P %"pr.34", P %"v103", W %"pr.1", W %"v1635")
    => goto "L1623" };
  ir_blk{ @"L1622":
    %"v1644" : L = Div %"v1352", #4;
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.34", L %"v1644")
    => goto "L1623" };
  ir_blk{ @"L1623":
    %"v1647" : L = (Ext Sw) %"v1612";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1647")
    => goto "L1131" };
  ir_blk{ @"L1648":
    %"v1651" : P = VaArg %"v4";
    %"v1656" : L = Ptoi %"v1651";
    %"v1658" : W = (Cmp Ne L) %"v1656", %"v56"
    => br %"v1658" ? poll "L1190" : "L1653" };
  ir_blk{ @"L1653":
    %"v1662" : P = Copy $"glibc_vfwprintf_internal#str.285";
    %"v1667" : W = (Cmp Slt W) %"pr.82", #5
    => br %"v1667" ? "L1669" : "L1664" };
  ir_blk{ @"L1664":
    => goto "L1669" };
  ir_blk{ @"L1670":
    %"v1675" : W = And %"v6", #2;
    %"v1676" : W = (Cmp Ne W) %"v1675", #0
    => br %"v1676" ? "L1671" : "L1673" };
  ir_blk{ @"L1671":
    %"v1681" : W = (Cmp Eq W) %"pr.16", #0
    => br %"v1681" ? "L1677" : "L1679" };
  ir_blk{ @"L1677":
    call %"v1684" : L = $"__wcslen"(P %"v2");
    %"v1685" : L = Add %"v1684", #1;
    %"v1686" : L = Shl %"v1685", #2;
    call %"v1687" : W = $"__readonly_area"(P %"v2", L %"v1686")
    => goto "L1679" };
  ir_blk{ @"L1679" [%"pr.14" : W = phi("L1677" => %"v1687", "L1671" => %"pr.16")]:
    %"v1698" : W = (Cmp Eq W) %"pr.14", #1
    => br %"v1698" ? "L1691" : "L1699" };
  ir_blk{ @"L1691":
    %"v1692" : P = Copy $"glibc_vfwprintf_internal#str.286";
    call void $"__GI___libc_fatal"(P %"v1692")
    => goto "L1693" };
  ir_blk{ @"L1693":
    %"v1694" : P = Copy $"glibc_vfwprintf_internal#str.287";
    call void $"__GI___libc_fatal"(P %"v1694")
    => goto "L1673" };
  ir_blk{ @"L1699":
    %"v1700" : W = (Cmp Eq W) %"pr.14", #3
    => br %"v1700" ? poll "L1693" : "L1701" }] [ir_blk{ @"L1701":
    %"v1702" : W = (Cmp Eq W) %"pr.14", #2
    => br %"v1702" ? "L1673" : "L1703" };
  ir_blk{ @"L1703":
    %"v1704" : W = (Cmp Eq W) %"pr.14", #0
    => br %"v1704" ? "L1673" : "L1705" };
  ir_blk{ @"L1705":
    => goto "L1673" };
  ir_blk{ @"L1673" [%"pr.13" : W = phi("L1705" => %"pr.14", "L1703" => %"pr.14", "L1693" => %"pr.14", "L1701" => %"pr.14", "L1670" => %"pr.16")]:
    %"v1708" : P = VaArg %"v4";
    call %"v1711" : W = $"__wprintf_buffer_done"(P %"v0")
    => br %"pr.62" ? "L1718" : "L1719" };
  ir_blk{ @"L1718":
    %"v1724" : L = (Ext Uw) %"v1711";
    %"chk154" : A = (Check 0 8 Write 1) %"v1708";
    store Wl [%"chk154" + 0] <- %"v1724"
    => goto "L1131" };
  ir_blk{ @"L1719":
    => br %"pr.65" ? "L1725" : "L1726" };
  ir_blk{ @"L1725":
    %"v1731" : W = (Ext Sb) %"v1711";
    %"chk155" : A = (Check 0 1 Write 1) %"v1708";
    store Wb [%"chk155" + 0] <- %"v1731"
    => goto "L1131" };
  ir_blk{ @"L1726":
    %"v1736" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1736" ? "L1732" : "L1733" };
  ir_blk{ @"L1732":
    %"chk156" : A = (Check 0 4 Write 1) %"v1708";
    store Ww [%"chk156" + 0] <- %"v1711"
    => goto "L1131" };
  ir_blk{ @"L1733":
    %"v1741" : W = (Ext Sh) %"v1711";
    %"chk157" : A = (Check 0 2 Write 1) %"v1708";
    store Wh [%"chk157" + 0] <- %"v1741"
    => goto "L1131" };
  ir_blk{ @"L1742":
    => br %"pr.42" ? "L1743" : "L1744" };
  ir_blk{ @"L1743":
    call %"v1748" : P = $"__get_errname"(W %"v19")
    => goto "L1745" };
  ir_blk{ @"L1744":
    call %"v1751" : P = $"__GI___strerror_r"(W %"v19", P %"v13", L #1000)
    => goto "L1745" };
  ir_blk{ @"L1745" [%"pr.37" : P = phi("L1743" => %"v1748", "L1744" => %"v1751")]:
    %"v1756" : L = Ptoi %"pr.37";
    %"v1758" : W = (Cmp Eq L) %"v1756", %"v56"
    => br %"v1758" ? "L1752" : "L1669" };
  ir_blk{ @"L1752":
    %"v1760" : W = (Cmp Slt W) %"v19", #0;
    %"v1762" : L = (Ext Sw) %"v19"
    => br %"v1760" ? "L1763" : poll "L1190" };
  ir_blk{ @"L1763":
    %"v1768" : L = Neg %"v1762"
    => goto poll "L1190" };
  ir_blk{ @"L1770":
    => br %"pr.62" ? "L1775" : "L1773" };
  ir_blk{ @"L1773":
    %"v1778" : W = Sub %"pr.67", #1;
    %"v1783" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1783" ? "L1779" : "L1781" };
  ir_blk{ @"L1779":
    %"v1786" : L = (Ext Sw) %"v1778";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1786")
    => goto "L1781" };
  ir_blk{ @"L1781":
    %"v1789" : W = VaArg %"v4";
    %"v1790" : W = (Ext Ub) %"v1789";
    call %"v1791" : W = $"__btowc"(W %"v1790");
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v1791")
    => br %"pr.47" ? "L1792" : "L1131" };
  ir_blk{ @"L1792":
    %"v1798" : L = (Ext Sw) %"v1778";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1798")
    => goto "L1131" };
  ir_blk{ @"L1799":
    %"v1802" : P = VaArg %"v4"
    => goto "L1669" };
  ir_blk{ @"L1669" [%"pr.84" : W = phi("L1799" => %"pr.82", "L1664" => %"pr.82", "L1653" => #5, "L1745" => %"pr.82"); %"pr.63" : W = phi("L1799" => %"pr.62", "L1664" => #1, "L1653" => #1, "L1745" => #0); %"pr.36" : P = phi("L1799" => %"v1802", "L1664" => %"v1662", "L1653" => %"v1662", "L1745" => %"pr.37")]:
    %"v1807" : L = Ptoi %"pr.36";
    %"v1809" : W = (Cmp Eq L) %"v1807", %"v56"
    => br %"v1809" ? "L1803" : "L1804" };
  ir_blk{ @"L1803":
    %"v1815" : W = (Cmp Eq W) %"pr.84", #4294967295
    => br %"v1815" ? "L1817" : "L1816" };
  ir_blk{ @"L1816":
    %"v1823" : W = (Cmp Sge W) %"pr.84", #6
    => goto "L1817" };
  ir_blk{ @"L1817" [%"v1825" : W = phi("L1803" => #1, "L1816" => %"v1823")]:
    => br %"v1825" ? "L1810" : "L1811" };
  ir_blk{ @"L1810":
    %"v1826" : P = Copy $"glibc_vfwprintf_internal#null"
    => goto "L1805" };
  ir_blk{ @"L1811":
    %"v1831" : P = Copy $"glibc_vfwprintf_internal#str.290"
    => goto "L1805" };
  ir_blk{ @"L1804":
    %"v1836" : W = (Cmp Eq W) %"pr.63", #0
    => br %"v1836" ? "L1837" : "L1838" };
  ir_blk{ @"L1837":
    %"v1840" : W = (Cmp Ne W) %"pr.97", #83
    => goto "L1838" };
  ir_blk{ @"L1838" [%"v1842" : W = phi("L1804" => #0, "L1837" => %"v1840")]:
    => br %"v1842" ? "L1832" : "L1833" };
  ir_blk{ @"L1832":
    %"v1848" : W = (Cmp Ne W) %"pr.47", #0;
    call void $"glibc_vfwprintf_internal#outstring_converted_wide_string"(P %"v0", P %"pr.36", W %"pr.84", W %"pr.67", W %"v1848")
    => goto "L1131" };
  ir_blk{ @"L1833":
    %"v1855" : W = (Cmp Ne W) %"pr.84", #4294967295
    => br %"v1855" ? "L1850" : "L1851" };
  ir_blk{ @"L1850":
    %"v1858" : L = (Ext Sw) %"pr.84";
    call %"v1859" : L = $"__wcsnlen"(P %"pr.36", L %"v1858")
    => goto "L1852" };
  ir_blk{ @"L1851":
    call %"v1861" : L = $"__wcslen"(P %"pr.36")
    => goto "L1852" };
  ir_blk{ @"L1852" [%"pr.109" : L = phi("L1850" => %"v1859", "L1851" => %"v1861")]:
    => goto "L1805" };
  ir_blk{ @"L1805" [%"pr.107" : L = phi("L1810" => #6, "L1811" => #0, "L1852" => %"pr.109"); %"pr.38" : P = phi("L1810" => %"v1826", "L1811" => %"v1831", "L1852" => %"pr.36")]:
    %"v1867" : L = (Ext Sw) %"pr.67";
    %"v1868" : L = Sub %"v1867", %"pr.107";
    %"v1869" : W = (Cmp Slt W) %"v1868", #0
    => br %"v1869" ? "L1862" : "L1864" };
  ir_blk{ @"L1862":
    call void $"__wprintf_buffer_write"(P %"v0", P %"pr.38", L %"pr.107")
    => goto "L1131" };
  ir_blk{ @"L1864":
    %"v1878" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1878" ? "L1874" : "L1876" };
  ir_blk{ @"L1874":
    %"v1880" : W = Copy %"v1868";
    %"v1881" : L = (Ext Sw) %"v1880";
    call void $"glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W #32, L %"v1881")
    => goto "L1876" }]))).
