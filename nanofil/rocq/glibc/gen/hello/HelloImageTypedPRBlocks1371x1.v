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

Definition hello_image_fn___printf_buffer'blocks1 : list block :=
  (app (app (app [ir_blk{ @"start":
    %"v10" : P = (Alloc 8) #8;
    %"v13" : P = (Alloc 4) #1000;
    %"v15" : P = (Alloc 8) #24;
    %"v85" : P = (Alloc 16) #16;
    %"v496" : P = (Alloc 8) #8;
    %"v648" : P = (Alloc 8) #8;
    %"v1319" : P = (Alloc 8) #24;
    %"v1917" : P = (Alloc 4) #16;
    %"v1918" : P = (Alloc 4) #8;
    %"v1964" : P = (Alloc 4) #20;
    %"v2100" : P = (Alloc 8) #8;
    %"v18" : P = Copy $"__libc_errno";
    %"chk0" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    (Flight (a "v23") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 8 Write 8) %"v15";
    store.ptr [%"chk2" + 0] <- %"v25";
    call %"v27" : P = $"glibc_vfprintf_internal#__find_specmb.gnu_inline"(P %"v2");
    %"chk3" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk3" + 0] <- %"v27";
    %"v32" : L = Ptoi %"v27";
    %"v33" : L = Ptoi %"v2";
    %"v34" : L = Sub %"v32", %"v33";
    call void $"__printf_buffer_write"(P %"v0", P %"v2", L %"v34");
    call %"v39" : W = $"glibc_vfprintf_internal#__printf_buffer_has_failed"(P %"v0");
    %"v40" : W = (Ext Ub) %"v39"
    => br %"v40" ? "L35" : "L37" };
  ir_blk{ @"L35":
    => ret void };
  ir_blk{ @"L37":
    %"chk4" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 1 Read 1) %"v45";
    %"v46" : W = (RawLoad (LdNarrow Ub) 0) %"chk5";
    %"v47" : W = (Cmp Eq W) %"v46", #0
    => br %"v47" ? "L42" : "L44" };
  ir_blk{ @"L42":
    => ret void };
  ir_blk{ @"L44":
    %"v52" : P = Copy $"__printf_function_table";
    %"chk6" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v54" : L = Ptoi %"v53";
    %"v55" : L = Ptoi #0;
    %"v56" : W = (Cmp Ne L) %"v54", %"v55"
    => br %"v56" ? "L58" : "L57" };
  ir_blk{ @"L57":
    %"v59" : P = Copy $"__printf_modifier_table";
    %"chk7" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v61" : L = Ptoi %"v60";
    %"v63" : W = (Cmp Ne L) %"v61", %"v55"
    => goto "L58" };
  ir_blk{ @"L58" [%"v65" : W = phi("L44" => #1, "L57" => %"v63")]:
    => br %"v65" ? "L67" : "L66" };
  ir_blk{ @"L66":
    %"v68" : P = Copy $"__printf_va_arg_table";
    %"chk8" : A = (Check 0 8 Read 8) %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v70" : L = Ptoi %"v69";
    %"v72" : W = (Cmp Ne L) %"v70", %"v55"
    => goto "L67" };
  ir_blk{ @"L67" [%"v74" : W = phi("L58" => #1, "L66" => %"v72")]:
    => br %"v74" ? "L77" : "L79" };
  ir_blk{ @"L79" [%"pr.16" : W = phi("L2128" => %"pr.12", "L67" => #0); %"pr.11" : W = phi("L2128" => %"v2113", "L67" => #0); %"pr.9" : P = phi("L2128" => %"pr.5", "L67" => %"v23"); %"pr.4" : P = phi("L2128" => %"pr.1", "L67" => #0)]:
    %"v102" = %"v13" +p #1000;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v109" = %"v108" +p #1;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk10" + 0] <- %"v109";
    %"chk11" : A = (Check 0 1 Read 1) %"v109";
    %"v110" : W = (RawLoad (LdNarrow Ub) 0) %"chk11";
    %"v111" : W = (Ext Sb) %"v110";
    %"v116" : W = (Cmp Slt W) %"v111", #32
    => br %"v116" ? "L118" : "L117" };
  ir_blk{ @"L117":
    %"v120" : W = (Cmp Sgt W) %"v111", #122
    => goto "L118" };
  ir_blk{ @"L118" [%"v122" : W = phi("L79" => #1, "L117" => %"v120")]:
    => br %"v122" ? "L114" : "L113" };
  ir_blk{ @"L113":
    %"v126" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v127" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v129" : W = Sub %"v111", #32;
    %"v130" : L = (Ext Sw) %"v129";
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
    %"v153" = %"v152" +p #1;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk15" + 0] <- %"v153";
    %"chk16" : A = (Check 0 1 Read 1) %"v153";
    %"v154" : W = (RawLoad (LdNarrow Ub) 0) %"chk16";
    %"v155" : W = (Ext Sb) %"v154";
    %"v160" : W = (Cmp Slt W) %"v155", #32
    => br %"v160" ? "L162" : "L161" };
  ir_blk{ @"L161":
    %"v164" : W = (Cmp Sgt W) %"v155", #122
    => goto "L162" };
  ir_blk{ @"L162" [%"v166" : W = phi("L147" => #1, "L161" => %"v164")]:
    => br %"v166" ? "L158" : "L157" };
  ir_blk{ @"L157":
    %"v170" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v171" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v173" : W = Sub %"v155", #32;
    %"v174" : L = (Ext Sw) %"v173";
    %"v175" = %"v171" +p %"v174";
    %"chk17" : A = (Check 0 1 Read 1) %"v175";
    %"v176" : W = (RawLoad (LdNarrow Ub) 0) %"chk17";
    %"v177" : L = (Ext Uw) %"v176";
    %"v178" : L = Shl %"v177", #2;
    %"v179" = %"v170" +p %"v178";
    %"chk18" : A = (Check 0 4 Read 1) %"v179";
    %"v180" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v181" : L = (Ext Sw) %"v180"
    => goto "L158" };
  ir_blk{ @"L158" [%"v182" : L = phi("L157" => %"v181", "L162" => #0)]:
    %"v183" : W = Copy %"v182";
    %"v184" : L = (Ext Sw) %"v183";
    %"v185" = #1 +p %"v184";
    %"v187" : L = Ptoi %"v185"
    => goto "L144" };
  ir_blk{ @"L189":
    %"chk19" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v195" = %"v194" +p #1;
    %"chk20" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk20" + 0] <- %"v195";
    %"chk21" : A = (Check 0 1 Read 1) %"v195";
    %"v196" : W = (RawLoad (LdNarrow Ub) 0) %"chk21";
    %"v197" : W = (Ext Sb) %"v196";
    %"v202" : W = (Cmp Slt W) %"v197", #32
    => br %"v202" ? "L204" : "L203" };
  ir_blk{ @"L203":
    %"v206" : W = (Cmp Sgt W) %"v197", #122
    => goto "L204" };
  ir_blk{ @"L204" [%"v208" : W = phi("L189" => #1, "L203" => %"v206")]:
    => br %"v208" ? "L200" : "L199" };
  ir_blk{ @"L199":
    %"v212" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v213" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v215" : W = Sub %"v197", #32;
    %"v216" : L = (Ext Sw) %"v215";
    %"v217" = %"v213" +p %"v216";
    %"chk22" : A = (Check 0 1 Read 1) %"v217";
    %"v218" : W = (RawLoad (LdNarrow Ub) 0) %"chk22";
    %"v219" : L = (Ext Uw) %"v218";
    %"v220" : L = Shl %"v219", #2;
    %"v221" = %"v212" +p %"v220";
    %"chk23" : A = (Check 0 4 Read 1) %"v221";
    %"v222" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v223" : L = (Ext Sw) %"v222"
    => goto "L200" };
  ir_blk{ @"L200" [%"v224" : L = phi("L199" => %"v223", "L204" => #0)]:
    %"v225" : W = Copy %"v224";
    %"v226" : L = (Ext Sw) %"v225";
    %"v227" = #1 +p %"v226";
    %"v229" : L = Ptoi %"v227"
    => goto "L144" };
  ir_blk{ @"L231":
    %"chk24" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v236" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v237" = %"v236" +p #1;
    %"chk25" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk25" + 0] <- %"v237";
    %"chk26" : A = (Check 0 1 Read 1) %"v237";
    %"v238" : W = (RawLoad (LdNarrow Ub) 0) %"chk26";
    %"v239" : W = (Ext Sb) %"v238";
    %"v244" : W = (Cmp Slt W) %"v239", #32
    => br %"v244" ? "L246" : "L245" };
  ir_blk{ @"L245":
    %"v248" : W = (Cmp Sgt W) %"v239", #122
    => goto "L246" };
  ir_blk{ @"L246" [%"v250" : W = phi("L231" => #1, "L245" => %"v248")]:
    => br %"v250" ? "L242" : "L241" };
  ir_blk{ @"L241":
    %"v254" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v255" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v257" : W = Sub %"v239", #32;
    %"v258" : L = (Ext Sw) %"v257";
    %"v259" = %"v255" +p %"v258";
    %"chk27" : A = (Check 0 1 Read 1) %"v259";
    %"v260" : W = (RawLoad (LdNarrow Ub) 0) %"chk27";
    %"v261" : L = (Ext Uw) %"v260";
    %"v262" : L = Shl %"v261", #2;
    %"v263" = %"v254" +p %"v262";
    %"chk28" : A = (Check 0 4 Read 1) %"v263";
    %"v264" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v265" : L = (Ext Sw) %"v264"
    => goto "L242" };
  ir_blk{ @"L242" [%"v266" : L = phi("L241" => %"v265", "L246" => #0)]:
    %"v267" : W = Copy %"v266";
    %"v268" : L = (Ext Sw) %"v267";
    %"v269" = #1 +p %"v268";
    %"v271" : L = Ptoi %"v269"
    => goto "L144" };
  ir_blk{ @"L273":
    %"chk29" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v278" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v279" = %"v278" +p #1;
    %"chk30" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk30" + 0] <- %"v279";
    %"chk31" : A = (Check 0 1 Read 1) %"v279";
    %"v280" : W = (RawLoad (LdNarrow Ub) 0) %"chk31";
    %"v281" : W = (Ext Sb) %"v280";
    %"v286" : W = (Cmp Slt W) %"v281", #32
    => br %"v286" ? "L288" : "L287" };
  ir_blk{ @"L287":
    %"v290" : W = (Cmp Sgt W) %"v281", #122
    => goto "L288" };
  ir_blk{ @"L288" [%"v292" : W = phi("L273" => #1, "L287" => %"v290")]:
    => br %"v292" ? "L284" : "L283" };
  ir_blk{ @"L283":
    %"v296" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v297" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v299" : W = Sub %"v281", #32;
    %"v300" : L = (Ext Sw) %"v299";
    %"v301" = %"v297" +p %"v300";
    %"chk32" : A = (Check 0 1 Read 1) %"v301";
    %"v302" : W = (RawLoad (LdNarrow Ub) 0) %"chk32";
    %"v303" : L = (Ext Uw) %"v302";
    %"v304" : L = Shl %"v303", #2;
    %"v305" = %"v296" +p %"v304";
    %"chk33" : A = (Check 0 4 Read 1) %"v305";
    %"v306" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v307" : L = (Ext Sw) %"v306"
    => goto "L284" };
  ir_blk{ @"L284" [%"v308" : L = phi("L283" => %"v307", "L288" => #0)]:
    %"v309" : W = Copy %"v308";
    %"v310" : L = (Ext Sw) %"v309";
    %"v311" = #1 +p %"v310";
    %"v313" : L = Ptoi %"v311"
    => goto "L144" };
  ir_blk{ @"L314":
    %"v319" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v319" ? "L317" : "L316" };
  ir_blk{ @"L316":
    => goto "L317" };
  ir_blk{ @"L317" [%"pr.93" : W = phi("L316" => %"pr.92", "L314" => #48)]:
    %"chk34" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v326" = %"v325" +p #1;
    %"chk35" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk35" + 0] <- %"v326";
    %"chk36" : A = (Check 0 1 Read 1) %"v326";
    %"v327" : W = (RawLoad (LdNarrow Ub) 0) %"chk36";
    %"v328" : W = (Ext Sb) %"v327";
    %"v333" : W = (Cmp Slt W) %"v328", #32
    => br %"v333" ? "L335" : "L334" };
  ir_blk{ @"L334":
    %"v337" : W = (Cmp Sgt W) %"v328", #122
    => goto "L335" };
  ir_blk{ @"L335" [%"v339" : W = phi("L317" => #1, "L334" => %"v337")]:
    => br %"v339" ? "L331" : "L330" };
  ir_blk{ @"L330":
    %"v343" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v344" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v346" : W = Sub %"v328", #32;
    %"v347" : L = (Ext Sw) %"v346";
    %"v348" = %"v344" +p %"v347";
    %"chk37" : A = (Check 0 1 Read 1) %"v348";
    %"v349" : W = (RawLoad (LdNarrow Ub) 0) %"chk37";
    %"v350" : L = (Ext Uw) %"v349";
    %"v351" : L = Shl %"v350", #2;
    %"v352" = %"v343" +p %"v351";
    %"chk38" : A = (Check 0 4 Read 1) %"v352";
    %"v353" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v354" : L = (Ext Sw) %"v353"
    => goto "L331" }] [ir_blk{ @"L331" [%"v355" : L = phi("L330" => %"v354", "L335" => #0)]:
    %"v356" : W = Copy %"v355";
    %"v357" : L = (Ext Sw) %"v356";
    %"v358" = #1 +p %"v357";
    %"v360" : L = Ptoi %"v358"
    => goto "L144" };
  ir_blk{ @"L361":
    (Flight (a "v368") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v369" : L = Ptoi %"pr.5";
    %"v370" : L = Ptoi %"v368";
    %"v371" : W = (Cmp Eq L) %"v369", %"v370"
    => br %"v371" ? "L362" : "L364" };
  ir_blk{ @"L362":
    %"v372" : P = Copy $"__libc_tsd_LOCALE";
    %"chk39" : A = (Check 0 8 Read 8) %"v372";
    %"v373" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v374" = %"v373" +p #8;
    %"chk40" : A = (Check 0 8 Read 8) %"v374";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v376" = %"v375" +p #56;
    %"v380" = %"v376" +p #8;
    %"chk41" : A = (Check 0 8 Read 8) %"v380";
    %"v381" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v382" : P = Copy $"__libc_tsd_LOCALE";
    %"chk42" : A = (Check 0 8 Read 8) %"v382";
    %"v383" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"v384" = %"v383" +p #8;
    %"chk43" : A = (Check 0 8 Read 8) %"v384";
    %"v385" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v386" = %"v385" +p #56;
    %"v390" = %"v386" +p #16;
    %"chk44" : A = (Check 0 8 Read 8) %"v390";
    %"v391" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 1 Read 1) %"v391";
    %"v396" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v397" : W = (Cmp Eq W) %"v396", #0
    => br %"v397" ? "L399" : "L398" };
  ir_blk{ @"L398":
    %"v401" : W = (RawLoad (LdNarrow Sb) 0) %"chk45";
    %"v402" : W = (Cmp Eq W) %"v401", #127
    => goto "L399" };
  ir_blk{ @"L399" [%"v404" : W = phi("L362" => #1, "L398" => %"v402")]:
    => br %"v404" ? "L406" : "L405" };
  ir_blk{ @"L405":
    %"chk47" : A = (Check 0 1 Read 1) %"v381";
    %"v408" : W = (RawLoad (LdNarrow Sb) 0) %"chk47";
    %"v409" : W = (Cmp Eq W) %"v408", #0
    => goto "L406" };
  ir_blk{ @"L406" [%"v411" : W = phi("L399" => #1, "L405" => %"v409")]:
    => br %"v411" ? "L364" : "L393" };
  ir_blk{ @"L393":
    => goto "L364" };
  ir_blk{ @"L364" [%"pr.6" : P = phi("L393" => %"v391", "L406" => #0, "L361" => %"pr.5"); %"pr.2" : P = phi("L393" => %"v381", "L406" => %"v381", "L361" => %"pr.1")]:
    %"chk48" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v417" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v418" = %"v417" +p #1;
    %"chk49" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk49" + 0] <- %"v418";
    %"chk50" : A = (Check 0 1 Read 1) %"v418";
    %"v419" : W = (RawLoad (LdNarrow Ub) 0) %"chk50";
    %"v420" : W = (Ext Sb) %"v419";
    %"v425" : W = (Cmp Slt W) %"v420", #32
    => br %"v425" ? "L427" : "L426" };
  ir_blk{ @"L426":
    %"v429" : W = (Cmp Sgt W) %"v420", #122
    => goto "L427" };
  ir_blk{ @"L427" [%"v431" : W = phi("L364" => #1, "L426" => %"v429")]:
    => br %"v431" ? "L423" : "L422" };
  ir_blk{ @"L422":
    %"v435" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v436" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v438" : W = Sub %"v420", #32;
    %"v439" : L = (Ext Sw) %"v438";
    %"v440" = %"v436" +p %"v439";
    %"chk51" : A = (Check 0 1 Read 1) %"v440";
    %"v441" : W = (RawLoad (LdNarrow Ub) 0) %"chk51";
    %"v442" : L = (Ext Uw) %"v441";
    %"v443" : L = Shl %"v442", #2;
    %"v444" = %"v435" +p %"v443";
    %"chk52" : A = (Check 0 4 Read 1) %"v444";
    %"v445" : W = (RawLoad (LdNarrow Sw) 0) %"chk52";
    %"v446" : L = (Ext Sw) %"v445"
    => goto "L423" };
  ir_blk{ @"L423" [%"v447" : L = phi("L422" => %"v446", "L427" => #0)]:
    %"v448" : W = Copy %"v447";
    %"v449" : L = (Ext Sw) %"v448";
    %"v450" = #1 +p %"v449";
    %"v452" : L = Ptoi %"v450"
    => goto "L144" };
  ir_blk{ @"L454":
    %"chk53" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v459" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v460" = %"v459" +p #1;
    %"chk54" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk54" + 0] <- %"v460";
    %"chk55" : A = (Check 0 1 Read 1) %"v460";
    %"v461" : W = (RawLoad (LdNarrow Ub) 0) %"chk55";
    %"v462" : W = (Ext Sb) %"v461";
    %"v467" : W = (Cmp Slt W) %"v462", #32
    => br %"v467" ? "L469" : "L468" };
  ir_blk{ @"L468":
    %"v471" : W = (Cmp Sgt W) %"v462", #122
    => goto "L469" };
  ir_blk{ @"L469" [%"v473" : W = phi("L454" => #1, "L468" => %"v471")]:
    => br %"v473" ? "L465" : "L464" };
  ir_blk{ @"L464":
    %"v477" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
    %"v478" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v480" : W = Sub %"v462", #32;
    %"v481" : L = (Ext Sw) %"v480";
    %"v482" = %"v478" +p %"v481";
    %"chk56" : A = (Check 0 1 Read 1) %"v482";
    %"v483" : W = (RawLoad (LdNarrow Ub) 0) %"chk56";
    %"v484" : L = (Ext Uw) %"v483";
    %"v485" : L = Shl %"v484", #2;
    %"v486" = %"v477" +p %"v485";
    %"chk57" : A = (Check 0 4 Read 1) %"v486";
    %"v487" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"v488" : L = (Ext Sw) %"v487"
    => goto "L465" };
  ir_blk{ @"L465" [%"v489" : L = phi("L464" => %"v488", "L469" => #0)]:
    %"v490" : W = Copy %"v489";
    %"v491" : L = (Ext Sw) %"v490";
    %"v492" = #1 +p %"v491";
    %"v494" : L = Ptoi %"v492"
    => goto "L144" };
  ir_blk{ @"L495":
    %"chk58" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v497" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v498" = %"v497" +p #1;
    %"chk59" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk59" + 0] <- %"v498";
    %"chk60" : A = (Check 0 8 Write 8) %"v496";
    store.ptr [%"chk60" + 0] <- %"v498";
    %"chk61" : A = (Renew 0 8 Read 8) %"chk60", %"v496";
    %"v502" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"chk62" : A = (Check 0 1 Read 1) %"v502";
    %"v503" : W = (RawLoad (LdNarrow Ub) 0) %"chk62";
    %"v504" : W = Sub %"v503", #48;
    %"v505" : W = (Cmp Ult W) %"v504", #10
    => br %"v505" ? "L499" : "L501" };
  ir_blk{ @"L499":
    call %"v507" : W = $"glibc_vfprintf_internal#read_int"(P %"v496");
    %"v513" : W = (Cmp Eq W) %"v507", #4294967295
    => br %"v513" ? "L508" : "L510" };
  ir_blk{ @"L508":
    %"v514" : P = Copy $"__libc_errno";
    %"chk63" : A = (Check 0 4 Write 1) %"v514";
    store Ww [%"chk63" + 0] <- #75;
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L510":
    => br %"v507" ? "L522" : "L523" };
  ir_blk{ @"L522":
    %"chk64" : A = (Renew 0 8 Read 8) %"chk60", %"v496";
    %"v524" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"chk65" : A = (Check 0 1 Read 1) %"v524";
    %"v525" : W = (RawLoad (LdNarrow Ub) 0) %"chk65";
    %"v526" : W = (Cmp Eq W) %"v525", #36
    => goto "L523" };
  ir_blk{ @"L523" [%"v528" : W = phi("L510" => #0, "L522" => %"v526")]:
    => br %"v528" ? "L77" : "L501" };
  ir_blk{ @"L501":
    %"v531" : W = VaArg %"v4";
    %"v536" : W = (Cmp Slt W) %"v531", #0
    => br %"v536" ? "L532" : "L534" };
  ir_blk{ @"L532":
    %"v538" : W = Neg %"v531"
    => goto "L534" };
  ir_blk{ @"L534" [%"pr.94" : W = phi("L532" => #32, "L501" => %"pr.92"); %"pr.76" : W = phi("L532" => %"v538", "L501" => %"v531"); %"pr.48" : W = phi("L532" => #1, "L501" => %"pr.47")]:
    %"chk66" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v544" : P = (RawLoadPointer 0 load_effects) %"chk66";
    %"chk67" : A = (Check 0 1 Read 1) %"v544";
    %"v545" : W = (RawLoad (LdNarrow Ub) 0) %"chk67";
    %"v546" : W = (Ext Sb) %"v545";
    %"v551" : W = (Cmp Slt W) %"v546", #32
    => br %"v551" ? "L553" : "L552" };
  ir_blk{ @"L552":
    %"v555" : W = (Cmp Sgt W) %"v546", #122
    => goto "L553" };
  ir_blk{ @"L553" [%"v557" : W = phi("L534" => #1, "L552" => %"v555")]:
    => br %"v557" ? "L549" : "L548" };
  ir_blk{ @"L548":
    %"v561" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step1_jumps.278";
    %"v562" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v564" : W = Sub %"v546", #32;
    %"v565" : L = (Ext Sw) %"v564";
    %"v566" = %"v562" +p %"v565";
    %"chk68" : A = (Check 0 1 Read 1) %"v566";
    %"v567" : W = (RawLoad (LdNarrow Ub) 0) %"chk68";
    %"v568" : L = (Ext Uw) %"v567";
    %"v569" : L = Shl %"v568", #2;
    %"v570" = %"v561" +p %"v569";
    %"chk69" : A = (Check 0 4 Read 1) %"v570";
    %"v571" : W = (RawLoad (LdNarrow Sw) 0) %"chk69";
    %"v572" : L = (Ext Sw) %"v571"
    => goto "L549" };
  ir_blk{ @"L549" [%"v573" : L = phi("L548" => %"v572", "L553" => #0)]:
    %"v574" : W = Copy %"v573";
    %"v575" : L = (Ext Sw) %"v574";
    %"v576" = #1 +p %"v575";
    %"v578" : L = Ptoi %"v576"
    => goto "L144" };
  ir_blk{ @"L579":
    call %"v580" : W = $"glibc_vfprintf_internal#read_int"(P %"v10");
    %"v586" : W = (Cmp Eq W) %"v580", #4294967295
    => br %"v586" ? "L581" : "L583" };
  ir_blk{ @"L581":
    %"v589" : P = Copy $"__libc_errno";
    %"chk70" : A = (Check 0 4 Write 1) %"v589";
    store Ww [%"chk70" + 0] <- #75;
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L583":
    %"chk71" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v595" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"chk72" : A = (Check 0 1 Read 1) %"v595";
    %"v596" : W = (RawLoad (LdNarrow Ub) 0) %"chk72";
    %"v597" : W = (Cmp Eq W) %"v596", #36
    => br %"v597" ? "L77" : "L599" };
  ir_blk{ @"L599":
    %"v604" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"chk74" : A = (Check 0 1 Read 1) %"v604";
    %"v605" : W = (RawLoad (LdNarrow Ub) 0) %"chk74";
    %"v606" : W = (Ext Sb) %"v605";
    %"v611" : W = (Cmp Slt W) %"v606", #32
    => br %"v611" ? "L613" : "L612" };
  ir_blk{ @"L612":
    %"v615" : W = (Cmp Sgt W) %"v606", #122
    => goto "L613" };
  ir_blk{ @"L613" [%"v617" : W = phi("L599" => #1, "L612" => %"v615")]:
    => br %"v617" ? "L609" : "L608" };
  ir_blk{ @"L608":
    %"v621" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step1_jumps.278";
    %"v622" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v624" : W = Sub %"v606", #32;
    %"v625" : L = (Ext Sw) %"v624";
    %"v626" = %"v622" +p %"v625";
    %"chk75" : A = (Check 0 1 Read 1) %"v626";
    %"v627" : W = (RawLoad (LdNarrow Ub) 0) %"chk75";
    %"v628" : L = (Ext Uw) %"v627";
    %"v629" : L = Shl %"v628", #2;
    %"v630" = %"v621" +p %"v629";
    %"chk76" : A = (Check 0 4 Read 1) %"v630";
    %"v631" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"v632" : L = (Ext Sw) %"v631"
    => goto "L609" };
  ir_blk{ @"L609" [%"v633" : L = phi("L608" => %"v632", "L613" => #0)]:
    %"v634" : W = Copy %"v633";
    %"v635" : L = (Ext Sw) %"v634";
    %"v636" = #1 +p %"v635";
    %"v638" : L = Ptoi %"v636"
    => goto "L144" };
  ir_blk{ @"L639":
    %"chk77" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v640" : P = (RawLoadPointer 0 load_effects) %"chk77";
    %"v641" = %"v640" +p #1;
    %"chk78" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk78" + 0] <- %"v641";
    %"chk79" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v645" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"chk80" : A = (Check 0 1 Read 1) %"v645";
    %"v646" : W = (RawLoad (LdNarrow Ub) 0) %"chk80";
    %"v647" : W = (Cmp Eq W) %"v646", #42
    => br %"v647" ? "L642" : "L643" }]) (app [ir_blk{ @"L642":
    %"v649" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"v650" = %"v649" +p #1;
    %"chk82" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk82" + 0] <- %"v650";
    %"chk83" : A = (Check 0 8 Write 8) %"v648";
    store.ptr [%"chk83" + 0] <- %"v650";
    %"chk84" : A = (Renew 0 8 Read 8) %"chk83", %"v648";
    %"v654" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"chk85" : A = (Check 0 1 Read 1) %"v654";
    %"v655" : W = (RawLoad (LdNarrow Ub) 0) %"chk85";
    %"v656" : W = Sub %"v655", #48;
    %"v657" : W = (Cmp Ult W) %"v656", #10
    => br %"v657" ? "L651" : "L653" };
  ir_blk{ @"L651":
    call %"v659" : W = $"glibc_vfprintf_internal#read_int"(P %"v648");
    %"v665" : W = (Cmp Eq W) %"v659", #4294967295
    => br %"v665" ? "L660" : "L662" };
  ir_blk{ @"L660":
    %"v666" : P = Copy $"__libc_errno";
    %"chk86" : A = (Check 0 4 Write 1) %"v666";
    store Ww [%"chk86" + 0] <- #75;
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L662":
    => br %"v659" ? "L673" : "L674" };
  ir_blk{ @"L673":
    %"chk87" : A = (Renew 0 8 Read 8) %"chk83", %"v648";
    %"v675" : P = (RawLoadPointer 0 load_effects) %"chk87";
    %"chk88" : A = (Check 0 1 Read 1) %"v675";
    %"v676" : W = (RawLoad (LdNarrow Ub) 0) %"chk88";
    %"v677" : W = (Cmp Eq W) %"v676", #36
    => goto "L674" };
  ir_blk{ @"L674" [%"v679" : W = phi("L662" => #0, "L673" => %"v677")]:
    => br %"v679" ? "L77" : "L653" };
  ir_blk{ @"L653":
    %"v682" : W = VaArg %"v4";
    %"v687" : W = (Cmp Slt W) %"v682", #0
    => br %"v687" ? "L644" : "L684" };
  ir_blk{ @"L684":
    => goto "L644" };
  ir_blk{ @"L643":
    %"v692" : P = (RawLoadPointer 0 load_effects) %"chk79";
    %"chk90" : A = (Check 0 1 Read 1) %"v692";
    %"v693" : W = (RawLoad (LdNarrow Ub) 0) %"chk90";
    %"v694" : W = Sub %"v693", #48;
    %"v695" : W = (Cmp Ult W) %"v694", #10
    => br %"v695" ? "L689" : "L644" };
  ir_blk{ @"L689":
    call %"v696" : W = $"glibc_vfprintf_internal#read_int"(P %"v10");
    %"v702" : W = (Cmp Eq W) %"v696", #4294967295
    => br %"v702" ? "L697" : "L644" };
  ir_blk{ @"L697":
    %"v703" : P = Copy $"__libc_errno";
    %"chk91" : A = (Check 0 4 Write 1) %"v703";
    store Ww [%"chk91" + 0] <- #75;
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L644" [%"pr.85" : W = phi("L684" => %"v682", "L653" => #4294967295, "L689" => %"v696", "L643" => #0)]:
    %"chk92" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v711" : P = (RawLoadPointer 0 load_effects) %"chk92";
    %"chk93" : A = (Check 0 1 Read 1) %"v711";
    %"v712" : W = (RawLoad (LdNarrow Ub) 0) %"chk93";
    %"v713" : W = (Ext Sb) %"v712";
    %"v718" : W = (Cmp Slt W) %"v713", #32
    => br %"v718" ? "L720" : "L719" };
  ir_blk{ @"L719":
    %"v722" : W = (Cmp Sgt W) %"v713", #122
    => goto "L720" };
  ir_blk{ @"L720" [%"v724" : W = phi("L644" => #1, "L719" => %"v722")]:
    => br %"v724" ? "L716" : "L715" };
  ir_blk{ @"L715":
    %"v728" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step2_jumps.279";
    %"v729" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v731" : W = Sub %"v713", #32;
    %"v732" : L = (Ext Sw) %"v731";
    %"v733" = %"v729" +p %"v732";
    %"chk94" : A = (Check 0 1 Read 1) %"v733";
    %"v734" : W = (RawLoad (LdNarrow Ub) 0) %"chk94";
    %"v735" : L = (Ext Uw) %"v734";
    %"v736" : L = Shl %"v735", #2;
    %"v737" = %"v728" +p %"v736";
    %"chk95" : A = (Check 0 4 Read 1) %"v737";
    %"v738" : W = (RawLoad (LdNarrow Sw) 0) %"chk95";
    %"v739" : L = (Ext Sw) %"v738"
    => goto "L716" };
  ir_blk{ @"L716" [%"v740" : L = phi("L715" => %"v739", "L720" => #0)]:
    %"v741" : W = Copy %"v740";
    %"v742" : L = (Ext Sw) %"v741";
    %"v743" = #1 +p %"v742";
    %"v745" : L = Ptoi %"v743"
    => goto "L144" };
  ir_blk{ @"L747":
    %"chk96" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v752" : P = (RawLoadPointer 0 load_effects) %"chk96";
    %"v753" = %"v752" +p #1;
    %"chk97" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk97" + 0] <- %"v753";
    %"chk98" : A = (Check 0 1 Read 1) %"v753";
    %"v754" : W = (RawLoad (LdNarrow Ub) 0) %"chk98";
    %"v755" : W = (Ext Sb) %"v754";
    %"v760" : W = (Cmp Slt W) %"v755", #32
    => br %"v760" ? "L762" : "L761" };
  ir_blk{ @"L761":
    %"v764" : W = (Cmp Sgt W) %"v755", #122
    => goto "L762" };
  ir_blk{ @"L762" [%"v766" : W = phi("L747" => #1, "L761" => %"v764")]:
    => br %"v766" ? "L758" : "L757" };
  ir_blk{ @"L757":
    %"v770" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step3a_jumps.280";
    %"v771" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v773" : W = Sub %"v755", #32;
    %"v774" : L = (Ext Sw) %"v773";
    %"v775" = %"v771" +p %"v774";
    %"chk99" : A = (Check 0 1 Read 1) %"v775";
    %"v776" : W = (RawLoad (LdNarrow Ub) 0) %"chk99";
    %"v777" : L = (Ext Uw) %"v776";
    %"v778" : L = Shl %"v777", #2;
    %"v779" = %"v770" +p %"v778";
    %"chk100" : A = (Check 0 4 Read 1) %"v779";
    %"v780" : W = (RawLoad (LdNarrow Sw) 0) %"chk100";
    %"v781" : L = (Ext Sw) %"v780"
    => goto "L758" };
  ir_blk{ @"L758" [%"v782" : L = phi("L757" => %"v781", "L762" => #0)]:
    %"v783" : W = Copy %"v782";
    %"v784" : L = (Ext Sw) %"v783";
    %"v785" = #1 +p %"v784";
    %"v787" : L = Ptoi %"v785"
    => goto "L144" };
  ir_blk{ @"L789":
    %"chk101" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v794" : P = (RawLoadPointer 0 load_effects) %"chk101";
    %"v795" = %"v794" +p #1;
    %"chk102" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk102" + 0] <- %"v795";
    %"chk103" : A = (Check 0 1 Read 1) %"v795";
    %"v796" : W = (RawLoad (LdNarrow Ub) 0) %"chk103";
    %"v797" : W = (Ext Sb) %"v796";
    %"v802" : W = (Cmp Slt W) %"v797", #32
    => br %"v802" ? "L804" : "L803" };
  ir_blk{ @"L803":
    %"v806" : W = (Cmp Sgt W) %"v797", #122
    => goto "L804" };
  ir_blk{ @"L804" [%"v808" : W = phi("L789" => #1, "L803" => %"v806")]:
    => br %"v808" ? "L800" : "L799" };
  ir_blk{ @"L799":
    %"v812" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v813" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v815" : W = Sub %"v797", #32;
    %"v816" : L = (Ext Sw) %"v815";
    %"v817" = %"v813" +p %"v816";
    %"chk104" : A = (Check 0 1 Read 1) %"v817";
    %"v818" : W = (RawLoad (LdNarrow Ub) 0) %"chk104";
    %"v819" : L = (Ext Uw) %"v818";
    %"v820" : L = Shl %"v819", #2;
    %"v821" = %"v812" +p %"v820";
    %"chk105" : A = (Check 0 4 Read 1) %"v821";
    %"v822" : W = (RawLoad (LdNarrow Sw) 0) %"chk105";
    %"v823" : L = (Ext Sw) %"v822"
    => goto "L800" };
  ir_blk{ @"L800" [%"v824" : L = phi("L799" => %"v823", "L804" => #0)]:
    %"v825" : W = Copy %"v824";
    %"v826" : L = (Ext Sw) %"v825";
    %"v827" = #1 +p %"v826";
    %"v829" : L = Ptoi %"v827"
    => goto "L144" };
  ir_blk{ @"L831":
    %"chk106" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v836" : P = (RawLoadPointer 0 load_effects) %"chk106";
    %"v837" = %"v836" +p #1;
    %"chk107" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk107" + 0] <- %"v837";
    %"chk108" : A = (Check 0 1 Read 1) %"v837";
    %"v838" : W = (RawLoad (LdNarrow Ub) 0) %"chk108";
    %"v839" : W = (Ext Sb) %"v838";
    %"v844" : W = (Cmp Slt W) %"v839", #32
    => br %"v844" ? "L846" : "L845" };
  ir_blk{ @"L845":
    %"v848" : W = (Cmp Sgt W) %"v839", #122
    => goto "L846" };
  ir_blk{ @"L846" [%"v850" : W = phi("L831" => #1, "L845" => %"v848")]:
    => br %"v850" ? "L842" : "L841" };
  ir_blk{ @"L841":
    %"v854" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step3b_jumps.281";
    %"v855" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v857" : W = Sub %"v839", #32;
    %"v858" : L = (Ext Sw) %"v857";
    %"v859" = %"v855" +p %"v858";
    %"chk109" : A = (Check 0 1 Read 1) %"v859";
    %"v860" : W = (RawLoad (LdNarrow Ub) 0) %"chk109";
    %"v861" : L = (Ext Uw) %"v860";
    %"v862" : L = Shl %"v861", #2;
    %"v863" = %"v854" +p %"v862";
    %"chk110" : A = (Check 0 4 Read 1) %"v863";
    %"v864" : W = (RawLoad (LdNarrow Sw) 0) %"chk110";
    %"v865" : L = (Ext Sw) %"v864"
    => goto "L842" };
  ir_blk{ @"L842" [%"v866" : L = phi("L841" => %"v865", "L846" => #0)]:
    %"v867" : W = Copy %"v866";
    %"v868" : L = (Ext Sw) %"v867";
    %"v869" = #1 +p %"v868";
    %"v871" : L = Ptoi %"v869"
    => goto "L144" };
  ir_blk{ @"L873":
    %"chk111" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v878" : P = (RawLoadPointer 0 load_effects) %"chk111";
    %"v879" = %"v878" +p #1;
    %"chk112" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk112" + 0] <- %"v879";
    %"chk113" : A = (Check 0 1 Read 1) %"v879";
    %"v880" : W = (RawLoad (LdNarrow Ub) 0) %"chk113";
    %"v881" : W = (Ext Sb) %"v880";
    %"v886" : W = (Cmp Slt W) %"v881", #32
    => br %"v886" ? "L888" : "L887" };
  ir_blk{ @"L887":
    %"v890" : W = (Cmp Sgt W) %"v881", #122
    => goto "L888" };
  ir_blk{ @"L888" [%"v892" : W = phi("L873" => #1, "L887" => %"v890")]:
    => br %"v892" ? "L884" : "L883" };
  ir_blk{ @"L883":
    %"v896" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v897" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v899" : W = Sub %"v881", #32;
    %"v900" : L = (Ext Sw) %"v899";
    %"v901" = %"v897" +p %"v900";
    %"chk114" : A = (Check 0 1 Read 1) %"v901";
    %"v902" : W = (RawLoad (LdNarrow Ub) 0) %"chk114";
    %"v903" : L = (Ext Uw) %"v902";
    %"v904" : L = Shl %"v903", #2;
    %"v905" = %"v896" +p %"v904";
    %"chk115" : A = (Check 0 4 Read 1) %"v905";
    %"v906" : W = (RawLoad (LdNarrow Sw) 0) %"chk115";
    %"v907" : L = (Ext Sw) %"v906"
    => goto "L884" };
  ir_blk{ @"L884" [%"v908" : L = phi("L883" => %"v907", "L888" => #0)]:
    %"v909" : W = Copy %"v908";
    %"v910" : L = (Ext Sw) %"v909";
    %"v911" = #1 +p %"v910";
    %"v913" : L = Ptoi %"v911"
    => goto "L144" };
  ir_blk{ @"L917":
    %"chk116" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v922" : P = (RawLoadPointer 0 load_effects) %"chk116";
    %"v923" = %"v922" +p #1;
    %"chk117" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk117" + 0] <- %"v923";
    %"chk118" : A = (Check 0 1 Read 1) %"v923";
    %"v924" : W = (RawLoad (LdNarrow Ub) 0) %"chk118";
    %"v925" : W = (Ext Sb) %"v924";
    %"v930" : W = (Cmp Slt W) %"v925", #32
    => br %"v930" ? "L932" : "L931" };
  ir_blk{ @"L931":
    %"v934" : W = (Cmp Sgt W) %"v925", #122
    => goto "L932" };
  ir_blk{ @"L932" [%"v936" : W = phi("L917" => #1, "L931" => %"v934")]:
    => br %"v936" ? "L928" : "L927" };
  ir_blk{ @"L927":
    %"v940" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v941" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v943" : W = Sub %"v925", #32;
    %"v944" : L = (Ext Sw) %"v943";
    %"v945" = %"v941" +p %"v944";
    %"chk119" : A = (Check 0 1 Read 1) %"v945";
    %"v946" : W = (RawLoad (LdNarrow Ub) 0) %"chk119";
    %"v947" : L = (Ext Uw) %"v946";
    %"v948" : L = Shl %"v947", #2;
    %"v949" = %"v940" +p %"v948";
    %"chk120" : A = (Check 0 4 Read 1) %"v949";
    %"v950" : W = (RawLoad (LdNarrow Sw) 0) %"chk120";
    %"v951" : L = (Ext Sw) %"v950"
    => goto "L928" }] [ir_blk{ @"L928" [%"v952" : L = phi("L927" => %"v951", "L932" => #0)]:
    %"v953" : W = Copy %"v952";
    %"v954" : L = (Ext Sw) %"v953";
    %"v955" = #1 +p %"v954";
    %"v957" : L = Ptoi %"v955"
    => goto "L144" };
  ir_blk{ @"L961":
    %"chk121" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v966" : P = (RawLoadPointer 0 load_effects) %"chk121";
    %"v967" = %"v966" +p #1;
    %"chk122" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk122" + 0] <- %"v967";
    %"chk123" : A = (Check 0 1 Read 1) %"v967";
    %"v968" : W = (RawLoad (LdNarrow Ub) 0) %"chk123";
    %"v969" : W = (Ext Sb) %"v968";
    %"v974" : W = (Cmp Slt W) %"v969", #32
    => br %"v974" ? "L976" : "L975" };
  ir_blk{ @"L975":
    %"v978" : W = (Cmp Sgt W) %"v969", #122
    => goto "L976" };
  ir_blk{ @"L976" [%"v980" : W = phi("L961" => #1, "L975" => %"v978")]:
    => br %"v980" ? "L972" : "L971" };
  ir_blk{ @"L971":
    %"v984" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v985" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v987" : W = Sub %"v969", #32;
    %"v988" : L = (Ext Sw) %"v987";
    %"v989" = %"v985" +p %"v988";
    %"chk124" : A = (Check 0 1 Read 1) %"v989";
    %"v990" : W = (RawLoad (LdNarrow Ub) 0) %"chk124";
    %"v991" : L = (Ext Uw) %"v990";
    %"v992" : L = Shl %"v991", #2;
    %"v993" = %"v984" +p %"v992";
    %"chk125" : A = (Check 0 4 Read 1) %"v993";
    %"v994" : W = (RawLoad (LdNarrow Sw) 0) %"chk125";
    %"v995" : L = (Ext Sw) %"v994"
    => goto "L972" };
  ir_blk{ @"L972" [%"v996" : L = phi("L971" => %"v995", "L976" => #0)]:
    %"v997" : W = Copy %"v996";
    %"v998" : L = (Ext Sw) %"v997";
    %"v999" = #1 +p %"v998";
    %"v1001" : L = Ptoi %"v999"
    => goto "L144" };
  ir_blk{ @"L1005":
    %"chk126" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1010" : P = (RawLoadPointer 0 load_effects) %"chk126";
    %"v1011" = %"v1010" +p #1;
    %"chk127" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk127" + 0] <- %"v1011";
    %"chk128" : A = (Check 0 1 Read 1) %"v1011";
    %"v1012" : W = (RawLoad (LdNarrow Ub) 0) %"chk128";
    %"v1013" : W = (Ext Sb) %"v1012";
    %"v1018" : W = (Cmp Slt W) %"v1013", #32
    => br %"v1018" ? "L1020" : "L1019" };
  ir_blk{ @"L1019":
    %"v1022" : W = (Cmp Sgt W) %"v1013", #122
    => goto "L1020" };
  ir_blk{ @"L1020" [%"v1024" : W = phi("L1005" => #1, "L1019" => %"v1022")]:
    => br %"v1024" ? "L1016" : "L1015" };
  ir_blk{ @"L1015":
    %"v1028" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v1029" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v1031" : W = Sub %"v1013", #32;
    %"v1032" : L = (Ext Sw) %"v1031";
    %"v1033" = %"v1029" +p %"v1032";
    %"chk129" : A = (Check 0 1 Read 1) %"v1033";
    %"v1034" : W = (RawLoad (LdNarrow Ub) 0) %"chk129";
    %"v1035" : L = (Ext Uw) %"v1034";
    %"v1036" : L = Shl %"v1035", #2;
    %"v1037" = %"v1028" +p %"v1036";
    %"chk130" : A = (Check 0 4 Read 1) %"v1037";
    %"v1038" : W = (RawLoad (LdNarrow Sw) 0) %"chk130";
    %"v1039" : L = (Ext Sw) %"v1038"
    => goto "L1016" };
  ir_blk{ @"L1016" [%"v1040" : L = phi("L1015" => %"v1039", "L1020" => #0)]:
    %"v1041" : W = Copy %"v1040";
    %"v1042" : L = (Ext Sw) %"v1041";
    %"v1043" = #1 +p %"v1042";
    %"v1045" : L = Ptoi %"v1043"
    => goto "L144" };
  ir_blk{ @"L1046":
    %"chk131" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1047" : P = (RawLoadPointer 0 load_effects) %"chk131";
    %"v1048" = %"v1047" +p #1;
    %"chk132" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk132" + 0] <- %"v1048";
    %"chk133" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1054" : P = (RawLoadPointer 0 load_effects) %"chk133";
    %"chk134" : A = (Check 0 1 Read 1) %"v1054";
    %"v1055" : W = (RawLoad (LdNarrow Ub) 0) %"chk134";
    %"v1056" : W = (Cmp Eq W) %"v1055", #102
    => br %"v1056" ? "L1051" : "L1053" };
  ir_blk{ @"L1051":
    %"v1057" : P = (RawLoadPointer 0 load_effects) %"chk133";
    %"v1058" = %"v1057" +p #1;
    %"chk136" : A = (Renew 0 8 Write 8) %"chk3", %"v10";
    store.ptr [%"chk136" + 0] <- %"v1058"
    => goto "L1053" };
  ir_blk{ @"L1053" [%"pr.99" : W = phi("L1051" => #1, "L1046" => #0)]:
    %"chk137" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1064" : P = (RawLoadPointer 0 load_effects) %"chk137";
    %"chk138" : A = (Check 0 1 Read 1) %"v1064";
    %"v1065" : W = (RawLoad (LdNarrow Ub) 0) %"chk138";
    %"v1066" : W = Sub %"v1065", #48;
    %"v1067" : W = (Cmp Ult W) %"v1066", #10
    => br %"v1067" ? "L1061" : "L1063" };
  ir_blk{ @"L1061":
    call %"v1068" : W = $"glibc_vfprintf_internal#read_int"(P %"v10")
    => goto "L1063" };
  ir_blk{ @"L1063" [%"pr.100" : W = phi("L1061" => %"v1068", "L1053" => #0)]:
    => br %"pr.99" ? "L1074" : "L1071" };
  ir_blk{ @"L1074":
    %"v1081" : W = (Cmp Eq W) %"pr.100", #8
    => br %"v1081" ? "L1071" : "L1082" };
  ir_blk{ @"L1082":
    %"v1083" : W = (Cmp Eq W) %"pr.100", #16
    => br %"v1083" ? "L1071" : "L1084" };
  ir_blk{ @"L1084":
    %"v1085" : W = (Cmp Eq W) %"pr.100", #32
    => br %"v1085" ? "L1071" : "L1086" };
  ir_blk{ @"L1086":
    %"v1087" : W = (Cmp Eq W) %"pr.100", #64
    => br %"v1087" ? "L1071" : "L1088" };
  ir_blk{ @"L1088":
    => goto "L1071" };
  ir_blk{ @"L1071" [%"pr.101" : W = phi("L1088" => %"pr.100", "L1074" => #8, "L1082" => #64, "L1084" => #64, "L1086" => #64, "L1063" => %"pr.100")]:
    %"v1100" : W = (Cmp Eq W) %"pr.101", #8
    => br %"v1100" ? "L1091" : "L1101" };
  ir_blk{ @"L1096":
    %"v1097" : P = Copy $"__libc_errno";
    %"chk139" : A = (Check 0 4 Write 1) %"v1097";
    store Ww [%"chk139" + 0] <- #22;
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L1101":
    %"v1102" : W = (Cmp Eq W) %"pr.101", #16
    => br %"v1102" ? "L1091" : "L1103" };
  ir_blk{ @"L1103":
    %"v1104" : W = (Cmp Eq W) %"pr.101", #32
    => br %"v1104" ? "L1091" : "L1105" };
  ir_blk{ @"L1105":
    %"v1106" : W = (Cmp Eq W) %"pr.101", #64
    => br %"v1106" ? "L1091" : poll "L1096" };
  ir_blk{ @"L1091" [%"pr.64" : W = phi("L1071" => #1, "L1101" => %"pr.65", "L1103" => %"pr.65", "L1105" => %"pr.65"); %"pr.61" : W = phi("L1071" => %"pr.62", "L1101" => %"pr.62", "L1103" => %"pr.62", "L1105" => #1); %"pr.59" : W = phi("L1071" => %"pr.60", "L1101" => #1, "L1103" => %"pr.60", "L1105" => %"pr.60"); %"pr.56" : W = phi("L1071" => %"pr.57", "L1101" => %"pr.57", "L1103" => %"pr.57", "L1105" => #1)]:
    %"chk140" : A = (Renew 0 8 Read 8) %"chk3", %"v10";
    %"v1113" : P = (RawLoadPointer 0 load_effects) %"chk140";
    %"chk141" : A = (Check 0 1 Read 1) %"v1113";
    %"v1114" : W = (RawLoad (LdNarrow Ub) 0) %"chk141";
    %"v1115" : W = (Ext Sb) %"v1114";
    %"v1120" : W = (Cmp Slt W) %"v1115", #32
    => br %"v1120" ? "L1122" : "L1121" };
  ir_blk{ @"L1121":
    %"v1124" : W = (Cmp Sgt W) %"v1115", #122
    => goto "L1122" };
  ir_blk{ @"L1122" [%"v1126" : W = phi("L1091" => #1, "L1121" => %"v1124")]:
    => br %"v1126" ? "L1118" : "L1117" };
  ir_blk{ @"L1117":
    %"v1130" : P = Copy $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
    %"v1131" : P = Copy $"glibc_vfprintf_internal#jump_table";
    %"v1133" : W = Sub %"v1115", #32;
    %"v1134" : L = (Ext Sw) %"v1133";
    %"v1135" = %"v1131" +p %"v1134";
    %"chk142" : A = (Check 0 1 Read 1) %"v1135";
    %"v1136" : W = (RawLoad (LdNarrow Ub) 0) %"chk142";
    %"v1137" : L = (Ext Uw) %"v1136";
    %"v1138" : L = Shl %"v1137", #2;
    %"v1139" = %"v1130" +p %"v1138";
    %"chk143" : A = (Check 0 4 Read 1) %"v1139";
    %"v1140" : W = (RawLoad (LdNarrow Sw) 0) %"chk143";
    %"v1141" : L = (Ext Sw) %"v1140"
    => goto "L1118" };
  ir_blk{ @"L1118" [%"v1142" : L = phi("L1117" => %"v1141", "L1122" => #0)]:
    %"v1143" : W = Copy %"v1142";
    %"v1144" : L = (Ext Sw) %"v1143";
    %"v1145" = #1 +p %"v1144";
    %"v1147" : L = Ptoi %"v1145"
    => goto "L144" };
  ir_blk{ @"L1151":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #37)
    => goto "L1150" };
  ir_blk{ @"L1155":
    => br %"pr.62" ? "L1173" : "L1174" };
  ir_blk{ @"L1173":
    %"v1178" : L = VaArg %"v4"
    => goto "L1175" };
  ir_blk{ @"L1174":
    => br %"pr.65" ? "L1179" : "L1180" };
  ir_blk{ @"L1179":
    %"v1184" : W = VaArg %"v4";
    %"v1185" : W = (Ext Sb) %"v1184";
    %"v1186" : L = (Ext Sw) %"v1185"
    => goto "L1175" };
  ir_blk{ @"L1180":
    %"v1191" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1191" ? "L1187" : "L1188" };
  ir_blk{ @"L1187":
    %"v1193" : W = VaArg %"v4";
    %"v1194" : L = (Ext Sw) %"v1193"
    => goto "L1175" };
  ir_blk{ @"L1188":
    %"v1196" : W = VaArg %"v4";
    %"v1197" : W = (Ext Sh) %"v1196";
    %"v1198" : L = (Ext Sw) %"v1197"
    => goto "L1175" };
  ir_blk{ @"L1175" [%"pr.103" : L = phi("L1173" => %"v1178", "L1179" => %"v1186", "L1187" => %"v1194", "L1188" => %"v1198")]:
    %"v1200" : W = (Cmp Slt L) %"pr.103", #0
    => br %"v1200" ? "L1201" : "L1209" };
  ir_blk{ @"L1201":
    %"v1206" : L = Neg %"pr.103"
    => goto "L1209" }])) (app (app [ir_blk{ @"L1211" [%"pr.29" : W = phi("L2195" => #10, "L2198" => #8, "L2200" => #16, "L2226" => #2)]:
    => br %"pr.62" ? "L1258" : "L1259" };
  ir_blk{ @"L1258":
    %"v1263" : L = VaArg %"v4"
    => goto "L1209" };
  ir_blk{ @"L1259":
    => br %"pr.65" ? "L1264" : "L1265" };
  ir_blk{ @"L1264":
    %"v1269" : W = VaArg %"v4";
    %"v1270" : W = (Ext Ub) %"v1269";
    %"v1271" : L = (Ext Uw) %"v1270"
    => goto "L1209" };
  ir_blk{ @"L1265":
    %"v1276" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1276" ? "L1272" : "L1273" };
  ir_blk{ @"L1272":
    %"v1278" : W = VaArg %"v4";
    %"v1279" : L = (Ext Uw) %"v1278"
    => goto "L1209" };
  ir_blk{ @"L1273":
    %"v1281" : W = VaArg %"v4";
    %"v1282" : W = (Ext Uh) %"v1281";
    %"v1283" : L = (Ext Uw) %"v1282"
    => goto "L1209" };
  ir_blk{ @"L1209" [%"pr.95" : W = phi("L1201" => %"pr.97", "L1175" => %"pr.97", "L1258" => %"pr.97", "L1264" => %"pr.97", "L1272" => %"pr.97", "L1273" => %"pr.97", "L1674" => #120, "L1789" => %"pr.97", "L1778" => %"pr.97"); %"pr.53" : W = phi("L1201" => %"pr.55", "L1175" => %"pr.55", "L1258" => %"pr.55", "L1264" => %"pr.55", "L1272" => %"pr.55", "L1273" => %"pr.55", "L1674" => #0, "L1789" => %"pr.55", "L1778" => %"pr.55"); %"pr.50" : W = phi("L1201" => %"pr.52", "L1175" => %"pr.52", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => %"pr.52", "L1789" => %"pr.52", "L1778" => %"pr.52"); %"pr.44" : W = phi("L1201" => %"pr.46", "L1175" => %"pr.46", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => %"pr.46", "L1789" => %"pr.46", "L1778" => %"pr.46"); %"pr.40" : W = phi("L1201" => %"pr.42", "L1175" => %"pr.42", "L1258" => %"pr.42", "L1264" => %"pr.42", "L1272" => %"pr.42", "L1273" => %"pr.42", "L1674" => #1, "L1789" => %"pr.42", "L1778" => %"pr.42"); %"pr.28" : W = phi("L1201" => #10, "L1175" => #10, "L1258" => %"pr.29", "L1264" => %"pr.29", "L1272" => %"pr.29", "L1273" => %"pr.29", "L1674" => #16, "L1789" => #10, "L1778" => #10); %"pr.21" : L = phi("L1201" => %"v1206", "L1175" => %"pr.103", "L1258" => %"v1263", "L1264" => %"v1271", "L1272" => %"v1279", "L1273" => %"v1283", "L1674" => %"v1682", "L1789" => %"v1794", "L1778" => %"v1788"); %"pr.18" : W = phi("L1201" => %"v1200", "L1175" => %"v1200", "L1258" => #0, "L1264" => #0, "L1272" => #0, "L1273" => #0, "L1674" => #0, "L1789" => %"v1786", "L1778" => %"v1786")]:
    %"v1288" : W = (Cmp Slt W) %"pr.82", #0
    => br %"v1288" ? "L1286" : "L1285" };
  ir_blk{ @"L1285":
    => goto "L1286" };
  ir_blk{ @"L1286" [%"pr.91" : W = phi("L1285" => #32, "L1209" => %"pr.92"); %"pr.81" : W = phi("L1285" => %"pr.82", "L1209" => #1)]:
    %"v1293" : W = (Cmp Eq W) %"pr.81", #0
    => br %"v1293" ? "L1294" : "L1295" };
  ir_blk{ @"L1294":
    %"v1297" : W = (Cmp Eq L) %"pr.21", #0
    => goto "L1295" };
  ir_blk{ @"L1295" [%"v1299" : W = phi("L1286" => #0, "L1294" => %"v1297")]:
    => br %"v1299" ? "L1289" : "L1290" };
  ir_blk{ @"L1289":
    %"v1305" : W = (Cmp Eq W) %"pr.28", #8
    => br %"v1305" ? "L1306" : "L1307" };
  ir_blk{ @"L1306":
    => goto "L1307" };
  ir_blk{ @"L1307" [%"v1310" : W = phi("L1289" => #0, "L1306" => %"pr.40")]:
    => br %"v1310" ? "L1301" : "L1291" };
  ir_blk{ @"L1301":
    (Flight (a "v1312") Sub [(FAddress (t "v102")); (FValue (Const 1))] (LowerOf (t "v102")));
    %"chk144" : A = (Check 0 1 Write 1) %"v1312";
    store Wb [%"chk144" + 0] <- #48
    => goto "L1291" };
  ir_blk{ @"L1290":
    %"v1316" : W = (Ext Sb) %"pr.95";
    %"v1317" : W = (Cmp Eq W) %"v1316", #88;
    call %"v1318" : P = $"_itoa_word"(L %"pr.21", P %"v102", W %"pr.28", W %"v1317")
    => goto "L1291" };
  ir_blk{ @"L1291" [%"pr.34" : P = phi("L1290" => %"v1318", "L1301" => %"v1312", "L1307" => %"v102")]:
    => br %"pr.53" ? "L1323" : "L1322" };
  ir_blk{ @"L1322":
    => br %"pr.88" ? "L1325" : "L1323" };
  ir_blk{ @"L1325":
    %"v1328" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1323" };
  ir_blk{ @"L1323" [%"v1332" : W = phi("L1291" => #1, "L1322" => #0, "L1325" => %"v1328")]:
    => br %"pr.53" ? "L1334" : "L1335" };
  ir_blk{ @"L1334":
    %"v1338" : P = Copy $"__libc_tsd_LOCALE";
    %"chk145" : A = (Check 0 8 Read 8) %"v1338";
    %"v1339" : P = (RawLoadPointer 0 load_effects) %"chk145";
    %"v1342" : L = Ptoi %"v102";
    %"v1343" : L = Ptoi %"pr.34";
    %"v1344" : L = Sub %"v1342", %"v1343";
    call %"v1345" : W = $"__grouping_iterator_init"(P %"v1319", W #1, P %"v1339", W %"v1344")
    => goto "L1336" };
  ir_blk{ @"L1335":
    => br %"pr.88" ? "L1351" : "L1352" };
  ir_blk{ @"L1351":
    %"v1354" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1352" };
  ir_blk{ @"L1352" [%"v1356" : W = phi("L1335" => #0, "L1351" => %"v1354")]:
    => br %"v1356" ? "L1347" : "L1336" };
  ir_blk{ @"L1347":
    %"v1359" : L = Ptoi %"v102";
    %"v1360" : L = Ptoi %"pr.34";
    %"v1361" : L = Sub %"v1359", %"v1360";
    call %"v1362" : W = $"__grouping_iterator_init_none"(P %"v1319", W %"v1361")
    => goto "L1336" };
  ir_blk{ @"L1336":
    => br %"pr.88" ? "L1369" : "L1370" };
  ir_blk{ @"L1369":
    %"v1372" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1370" };
  ir_blk{ @"L1370" [%"v1374" : W = phi("L1336" => #0, "L1369" => %"v1372")]:
    => br %"v1374" ? "L1365" : "L1366" };
  ir_blk{ @"L1365":
    %"v1375" : P = Copy $"__libc_tsd_LOCALE";
    %"chk146" : A = (Check 0 8 Read 8) %"v1375";
    %"v1376" : P = (RawLoadPointer 0 load_effects) %"chk146";
    call %"v1379" : W = $"__translated_number_width"(P %"v1376", P %"pr.34", P %"v102")
    => goto "L1367" };
  ir_blk{ @"L1366":
    %"v1382" : L = Ptoi %"v102";
    %"v1383" : L = Ptoi %"pr.34";
    %"v1384" : L = Sub %"v1382", %"v1383"
    => goto "L1367" };
  ir_blk{ @"L1367" [%"pr.106" : W = phi("L1365" => %"v1379", "L1366" => %"v1384")]:
    => br %"pr.53" ? "L1385" : "L1387" };
  ir_blk{ @"L1385":
    %"v1390" = %"v1319" +p #20;
    %"chk147" : A = (Check 0 4 Read 1) %"v1390";
    %"v1391" : W = (RawLoad (LdNarrow Uw) 0) %"chk147";
    call %"v1393" : L = $"__GI_strlen"(P %"pr.1");
    %"v1394" : L = (Ext Uw) %"v1391";
    %"v1395" : L = Mul %"v1394", %"v1393";
    %"v1396" : L = (Ext Sw) %"pr.106";
    %"v1397" : L = Add %"v1396", %"v1395"
    => goto "L1387" };
  ir_blk{ @"L1387" [%"pr.107" : W = phi("L1385" => %"v1397", "L1367" => %"pr.106")]:
    %"v1401" : W = (Cmp Sle W) %"pr.81", %"pr.107"
    => br %"v1401" ? "L1402" : "L1403" };
  ir_blk{ @"L1402":
    %"v1405" : W = (Cmp Ne L) %"pr.21", #0
    => goto "L1403" };
  ir_blk{ @"L1403" [%"v1407" : W = phi("L1387" => #0, "L1402" => %"v1405")]:
    => br %"v1407" ? "L1408" : "L1409" };
  ir_blk{ @"L1408":
    => goto "L1409" };
  ir_blk{ @"L1409" [%"v1412" : W = phi("L1403" => #0, "L1408" => %"pr.40")]:
    => br %"v1412" ? "L1413" : "L1414" };
  ir_blk{ @"L1413":
    %"v1416" : W = (Cmp Eq W) %"pr.28", #8
    => goto "L1414" };
  ir_blk{ @"L1414" [%"v1418" : W = phi("L1409" => #0, "L1413" => %"v1416")]:
    %"v1427" : L = Ptoi %"v102";
    %"v1428" : L = Ptoi %"pr.34";
    %"v1429" : L = Sub %"v1427", %"v1428";
    %"v1430" : L = (Ext Sw) %"pr.81";
    %"v1431" : L = Sub %"v1430", %"v1429";
    %"v1432" : W = (Cmp Slt L) %"v1431", #0
    => br %"v1432" ? "L1423" : "L1422" }] [ir_blk{ @"L1422":
    => goto "L1423" };
  ir_blk{ @"L1423" [%"v1441" : L = phi("L1422" => %"v1431", "L1414" => #0)]:
    %"v1446" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1446" ? "L1442" : "L1443" };
  ir_blk{ @"L1442":
    %"v1449" : W = Copy %"v1441";
    %"v1450" : W = Add %"pr.107", %"v1449";
    %"v1451" : W = Sub %"pr.66", %"v1450";
    %"v1456" : W = (Cmp Ne L) %"pr.21", #0
    => br %"v1456" ? "L1457" : "L1458" };
  ir_blk{ @"L1457":
    => goto "L1458" };
  ir_blk{ @"L1458" [%"v1461" : W = phi("L1442" => #0, "L1457" => %"pr.40")]:
    => br %"v1461" ? "L1462" : "L1463" };
  ir_blk{ @"L1462":
    %"v1465" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1465" ? "L1463" : "L1466" };
  ir_blk{ @"L1466":
    %"v1469" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1463" };
  ir_blk{ @"L1463" [%"v1473" : W = phi("L1458" => #0, "L1462" => #1, "L1466" => %"v1469")]:
    => br %"v1473" ? "L1452" : "L1454" };
  ir_blk{ @"L1452":
    %"v1475" : W = Sub %"v1451", #2
    => goto "L1454" };
  ir_blk{ @"L1454" [%"pr.67" : W = phi("L1452" => %"v1475", "L1463" => %"v1451")]:
    => br %"v1418" ? "L1476" : "L1478" };
  ir_blk{ @"L1476":
    %"v1481" : W = Sub %"pr.67", #1
    => goto "L1478" };
  ir_blk{ @"L1478" [%"pr.68" : W = phi("L1476" => %"v1481", "L1454" => %"pr.67")]:
    => br %"pr.18" ? "L1487" : "L1486" };
  ir_blk{ @"L1486":
    => goto "L1487" };
  ir_blk{ @"L1487" [%"v1490" : W = phi("L1478" => #1, "L1486" => %"pr.50")]:
    => br %"v1490" ? "L1492" : "L1491" };
  ir_blk{ @"L1491":
    => goto "L1492" };
  ir_blk{ @"L1492" [%"v1495" : W = phi("L1487" => #1, "L1491" => %"pr.44")]:
    => br %"v1495" ? "L1482" : "L1484" };
  ir_blk{ @"L1482":
    %"v1497" : W = Sub %"pr.68", #1
    => goto "L1484" };
  ir_blk{ @"L1484" [%"pr.69" : W = phi("L1482" => %"v1497", "L1492" => %"pr.68")]:
    %"v1501" : W = (Ext Ub) %"pr.91";
    %"v1502" : W = (Cmp Eq W) %"v1501", #32
    => br %"v1502" ? "L1498" : "L1500" };
  ir_blk{ @"L1498":
    %"v1505" : L = (Ext Sw) %"pr.69";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1505")
    => goto "L1500" };
  ir_blk{ @"L1500" [%"pr.70" : W = phi("L1498" => #0, "L1484" => %"pr.69")]:
    => br %"pr.18" ? "L1506" : "L1507" };
  ir_blk{ @"L1506":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #45)
    => goto "L1508" };
  ir_blk{ @"L1507":
    => br %"pr.50" ? "L1511" : "L1512" };
  ir_blk{ @"L1511":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #43)
    => goto "L1508" };
  ir_blk{ @"L1512":
    => br %"pr.44" ? "L1516" : "L1508" };
  ir_blk{ @"L1516":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #32)
    => goto "L1508" };
  ir_blk{ @"L1508":
    => br %"v1456" ? "L1526" : "L1527" };
  ir_blk{ @"L1526":
    => goto "L1527" };
  ir_blk{ @"L1527" [%"v1530" : W = phi("L1508" => #0, "L1526" => %"pr.40")]:
    => br %"v1530" ? "L1531" : "L1532" };
  ir_blk{ @"L1531":
    %"v1534" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1534" ? "L1532" : "L1535" };
  ir_blk{ @"L1535":
    %"v1538" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1532" };
  ir_blk{ @"L1532" [%"v1542" : W = phi("L1527" => #0, "L1531" => #1, "L1535" => %"v1538")]:
    => br %"v1542" ? "L1521" : "L1523" };
  ir_blk{ @"L1521":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48);
    %"v1545" : W = (Ext Sb) %"pr.95";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1545")
    => goto "L1523" };
  ir_blk{ @"L1523":
    %"v1547" : W = Copy %"v1441";
    %"v1548" : W = Add %"pr.70", %"v1547";
    %"v1551" : L = (Ext Sw) %"v1548";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #48, L %"v1551")
    => br %"v1418" ? "L1552" : "L1554" };
  ir_blk{ @"L1552":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48)
    => goto "L1554" };
  ir_blk{ @"L1554":
    => br %"v1332" ? "L1557" : "L1558" };
  ir_blk{ @"L1557":
    => br %"pr.88" ? "L1566" : "L1567" };
  ir_blk{ @"L1566":
    %"v1569" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1567" };
  ir_blk{ @"L1567" [%"v1571" : W = phi("L1557" => #0, "L1566" => %"v1569")]:
    call void $"glibc_vfprintf_internal#group_number"(P %"v0", P %"v1319", P %"pr.34", P %"v102", P %"pr.1", W %"v1571")
    => goto "L1150" };
  ir_blk{ @"L1558":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.34", L %"v1429")
    => goto "L1150" };
  ir_blk{ @"L1443":
    => br %"pr.18" ? "L1581" : "L1582" };
  ir_blk{ @"L1581":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #45);
    %"v1587" : W = Sub %"pr.66", #1
    => goto "L1583" }]) (app [ir_blk{ @"L1582":
    => br %"pr.50" ? "L1588" : "L1589" };
  ir_blk{ @"L1588":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #43);
    %"v1594" : W = Sub %"pr.66", #1
    => goto "L1583" };
  ir_blk{ @"L1589":
    => br %"pr.44" ? "L1595" : "L1583" };
  ir_blk{ @"L1595":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #32);
    %"v1601" : W = Sub %"pr.66", #1
    => goto "L1583" };
  ir_blk{ @"L1583" [%"pr.71" : W = phi("L1581" => %"v1587", "L1588" => %"v1594", "L1595" => %"v1601", "L1589" => %"pr.66")]:
    %"v1606" : W = (Cmp Ne L) %"pr.21", #0
    => br %"v1606" ? "L1607" : "L1608" };
  ir_blk{ @"L1607":
    => goto "L1608" };
  ir_blk{ @"L1608" [%"v1611" : W = phi("L1583" => #0, "L1607" => %"pr.40")]:
    => br %"v1611" ? "L1612" : "L1613" };
  ir_blk{ @"L1612":
    %"v1615" : W = (Cmp Eq W) %"pr.28", #16
    => br %"v1615" ? "L1613" : "L1616" };
  ir_blk{ @"L1616":
    %"v1619" : W = (Cmp Eq W) %"pr.28", #2
    => goto "L1613" };
  ir_blk{ @"L1613" [%"v1623" : W = phi("L1608" => #0, "L1612" => #1, "L1616" => %"v1619")]:
    => br %"v1623" ? "L1602" : "L1604" };
  ir_blk{ @"L1602":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48);
    %"v1626" : W = (Ext Sb) %"pr.95";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1626");
    %"v1628" : W = Sub %"pr.71", #2
    => goto "L1604" };
  ir_blk{ @"L1604" [%"pr.74" : W = phi("L1602" => %"v1628", "L1613" => %"pr.71")]:
    => br %"v1418" ? "L1629" : "L1631" };
  ir_blk{ @"L1629":
    %"v1634" : W = Sub %"pr.74", #1
    => goto "L1631" };
  ir_blk{ @"L1631" [%"pr.75" : W = phi("L1629" => %"v1634", "L1604" => %"pr.74")]:
    %"v1637" : W = Copy %"v1441";
    %"v1638" : W = Add %"pr.107", %"v1637";
    %"v1639" : W = Sub %"pr.75", %"v1638";
    %"v1641" : W = Copy %"v1441";
    %"v1642" : L = (Ext Uw) %"v1641";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #48, L %"v1642")
    => br %"v1418" ? "L1643" : "L1645" };
  ir_blk{ @"L1643":
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W #48)
    => goto "L1645" };
  ir_blk{ @"L1645":
    => br %"v1332" ? "L1648" : "L1649" };
  ir_blk{ @"L1648":
    => br %"pr.88" ? "L1657" : "L1658" };
  ir_blk{ @"L1657":
    %"v1660" : W = (Cmp Eq W) %"pr.28", #10
    => goto "L1658" };
  ir_blk{ @"L1658" [%"v1662" : W = phi("L1648" => #0, "L1657" => %"v1660")]:
    call void $"glibc_vfprintf_internal#group_number"(P %"v0", P %"v1319", P %"pr.34", P %"v102", P %"pr.1", W %"v1662")
    => goto "L1650" };
  ir_blk{ @"L1649":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.34", L %"v1429")
    => goto "L1650" };
  ir_blk{ @"L1650":
    %"v1673" : L = (Ext Sw) %"v1639";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1673")
    => goto "L1150" };
  ir_blk{ @"L1674":
    %"v1677" : P = VaArg %"v4";
    %"v1682" : L = Ptoi %"v1677";
    %"v1684" : W = (Cmp Ne L) %"v1682", %"v55"
    => br %"v1684" ? poll "L1209" : "L1679" };
  ir_blk{ @"L1679":
    %"v1688" : P = Copy $"glibc_vfprintf_internal#str.284";
    %"v1693" : W = (Cmp Slt W) %"pr.82", #5
    => br %"v1693" ? "L1695" : "L1690" };
  ir_blk{ @"L1690":
    => goto "L1695" };
  ir_blk{ @"L1696":
    %"v1701" : W = And %"v6", #2;
    %"v1702" : W = (Cmp Ne W) %"v1701", #0
    => br %"v1702" ? "L1697" : "L1699" };
  ir_blk{ @"L1697":
    %"v1707" : W = (Cmp Eq W) %"pr.16", #0
    => br %"v1707" ? "L1703" : "L1705" };
  ir_blk{ @"L1703":
    call %"v1710" : L = $"__GI_strlen"(P %"v2");
    %"v1711" : L = Add %"v1710", #1;
    call %"v1713" : W = $"__readonly_area"(P %"v2", L %"v1711")
    => goto "L1705" };
  ir_blk{ @"L1705" [%"pr.14" : W = phi("L1703" => %"v1713", "L1697" => %"pr.16")]:
    %"v1724" : W = (Cmp Eq W) %"pr.14", #1
    => br %"v1724" ? "L1717" : "L1725" };
  ir_blk{ @"L1717":
    %"v1718" : P = Copy $"glibc_vfprintf_internal#str.285";
    call void $"__GI___libc_fatal"(P %"v1718")
    => goto "L1719" };
  ir_blk{ @"L1719":
    %"v1720" : P = Copy $"glibc_vfprintf_internal#str.286";
    call void $"__GI___libc_fatal"(P %"v1720")
    => goto "L1699" };
  ir_blk{ @"L1725":
    %"v1726" : W = (Cmp Eq W) %"pr.14", #3
    => br %"v1726" ? poll "L1719" : "L1727" };
  ir_blk{ @"L1727":
    %"v1728" : W = (Cmp Eq W) %"pr.14", #2
    => br %"v1728" ? "L1699" : "L1729" };
  ir_blk{ @"L1729":
    %"v1730" : W = (Cmp Eq W) %"pr.14", #0
    => br %"v1730" ? "L1699" : "L1731" };
  ir_blk{ @"L1731":
    => goto "L1699" };
  ir_blk{ @"L1699" [%"pr.13" : W = phi("L1731" => %"pr.14", "L1729" => %"pr.14", "L1719" => %"pr.14", "L1727" => %"pr.14", "L1696" => %"pr.16")]:
    %"v1734" : P = VaArg %"v4";
    call %"v1737" : W = $"__printf_buffer_done"(P %"v0")
    => br %"pr.62" ? "L1744" : "L1745" };
  ir_blk{ @"L1744":
    %"v1750" : L = (Ext Uw) %"v1737";
    %"chk148" : A = (Check 0 8 Write 1) %"v1734";
    store Wl [%"chk148" + 0] <- %"v1750"
    => goto "L1150" };
  ir_blk{ @"L1745":
    => br %"pr.65" ? "L1751" : "L1752" };
  ir_blk{ @"L1751":
    %"v1757" : W = (Ext Sb) %"v1737";
    %"chk149" : A = (Check 0 1 Write 1) %"v1734";
    store Wb [%"chk149" + 0] <- %"v1757"
    => goto "L1150" };
  ir_blk{ @"L1752":
    %"v1762" : W = (Cmp Eq W) %"pr.60", #0
    => br %"v1762" ? "L1758" : "L1759" };
  ir_blk{ @"L1758":
    %"chk150" : A = (Check 0 4 Write 1) %"v1734";
    store Ww [%"chk150" + 0] <- %"v1737"
    => goto "L1150" }] [ir_blk{ @"L1759":
    %"v1767" : W = (Ext Sh) %"v1737";
    %"chk151" : A = (Check 0 2 Write 1) %"v1734";
    store Wh [%"chk151" + 0] <- %"v1767"
    => goto "L1150" };
  ir_blk{ @"L1768":
    => br %"pr.42" ? "L1769" : "L1770" };
  ir_blk{ @"L1769":
    call %"v1774" : P = $"__get_errname"(W %"v19")
    => goto "L1771" };
  ir_blk{ @"L1770":
    call %"v1777" : P = $"__GI___strerror_r"(W %"v19", P %"v13", L #1000)
    => goto "L1771" };
  ir_blk{ @"L1771" [%"pr.37" : P = phi("L1769" => %"v1774", "L1770" => %"v1777")]:
    %"v1782" : L = Ptoi %"pr.37";
    %"v1784" : W = (Cmp Eq L) %"v1782", %"v55"
    => br %"v1784" ? "L1778" : "L1695" };
  ir_blk{ @"L1778":
    %"v1786" : W = (Cmp Slt W) %"v19", #0;
    %"v1788" : L = (Ext Sw) %"v19"
    => br %"v1786" ? "L1789" : poll "L1209" };
  ir_blk{ @"L1789":
    %"v1794" : L = Neg %"v1788"
    => goto poll "L1209" };
  ir_blk{ @"L1796":
    => br %"pr.62" ? "L1801" : "L1799" };
  ir_blk{ @"L1799":
    %"v1804" : W = Sub %"pr.66", #1;
    %"v1809" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1809" ? "L1805" : "L1807" };
  ir_blk{ @"L1805":
    %"v1812" : L = (Ext Sw) %"v1804";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1812")
    => goto "L1807" };
  ir_blk{ @"L1807":
    %"v1815" : W = VaArg %"v4";
    %"v1816" : W = (Ext Ub) %"v1815";
    %"v1817" : W = (Ext Sb) %"v1816";
    call void $"glibc_vfprintf_internal#__printf_buffer_putc"(P %"v0", W %"v1817")
    => br %"pr.47" ? "L1818" : "L1150" };
  ir_blk{ @"L1818":
    %"v1824" : L = (Ext Sw) %"v1804";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1824")
    => goto "L1150" };
  ir_blk{ @"L1825":
    %"v1828" : P = VaArg %"v4"
    => goto "L1695" };
  ir_blk{ @"L1695" [%"pr.84" : W = phi("L1825" => %"pr.82", "L1690" => %"pr.82", "L1679" => #5, "L1771" => %"pr.82"); %"pr.63" : W = phi("L1825" => %"pr.62", "L1690" => #0, "L1679" => #0, "L1771" => #0); %"pr.36" : P = phi("L1825" => %"v1828", "L1690" => %"v1688", "L1679" => %"v1688", "L1771" => %"pr.37")]:
    %"v1833" : L = Ptoi %"pr.36";
    %"v1835" : W = (Cmp Eq L) %"v1833", %"v55"
    => br %"v1835" ? "L1829" : "L1830" };
  ir_blk{ @"L1829":
    %"v1841" : W = (Cmp Eq W) %"pr.84", #4294967295
    => br %"v1841" ? "L1843" : "L1842" };
  ir_blk{ @"L1842":
    %"v1849" : W = (Cmp Sge W) %"pr.84", #6
    => goto "L1843" };
  ir_blk{ @"L1843" [%"v1851" : W = phi("L1829" => #1, "L1842" => %"v1849")]:
    => br %"v1851" ? "L1836" : "L1837" };
  ir_blk{ @"L1836":
    %"v1852" : P = Copy $"glibc_vfprintf_internal#null"
    => goto "L1831" };
  ir_blk{ @"L1837":
    %"v1857" : P = Copy $"glibc_vfprintf_internal#str.289"
    => goto "L1831" };
  ir_blk{ @"L1830":
    %"v1862" : W = (Cmp Eq W) %"pr.63", #0
    => br %"v1862" ? "L1863" : "L1864" };
  ir_blk{ @"L1863":
    %"v1865" : W = (Ext Sb) %"pr.97";
    %"v1866" : W = (Cmp Ne W) %"v1865", #83
    => goto "L1864" };
  ir_blk{ @"L1864" [%"v1868" : W = phi("L1830" => #0, "L1863" => %"v1866")]:
    => br %"v1868" ? "L1858" : "L1859" };
  ir_blk{ @"L1858":
    %"v1874" : W = (Cmp Ne W) %"pr.84", #4294967295
    => br %"v1874" ? "L1869" : "L1870" };
  ir_blk{ @"L1869":
    %"v1877" : L = (Ext Sw) %"pr.84";
    call %"v1878" : L = $"__GI___strnlen"(P %"pr.36", L %"v1877")
    => goto "L1871" };
  ir_blk{ @"L1870":
    call %"v1880" : L = $"__GI_strlen"(P %"pr.36")
    => goto "L1871" };
  ir_blk{ @"L1871" [%"pr.111" : L = phi("L1869" => %"v1878", "L1870" => %"v1880")]:
    => goto "L1831" };
  ir_blk{ @"L1859":
    %"v1886" : W = (Cmp Ne W) %"pr.47", #0;
    call void $"glibc_vfprintf_internal#outstring_converted_wide_string"(P %"v0", P %"pr.36", W %"pr.84", W %"pr.66", W %"v1886")
    => goto "L1150" };
  ir_blk{ @"L1831" [%"pr.109" : L = phi("L1836" => #6, "L1837" => #0, "L1871" => %"pr.111"); %"pr.38" : P = phi("L1836" => %"v1852", "L1837" => %"v1857", "L1871" => %"pr.36")]:
    %"v1892" : L = (Ext Sw) %"pr.66";
    %"v1893" : L = Sub %"v1892", %"pr.109";
    %"v1894" : W = (Cmp Slt W) %"v1893", #0
    => br %"v1894" ? "L1887" : "L1889" };
  ir_blk{ @"L1887":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.38", L %"pr.109")
    => goto "L1150" };
  ir_blk{ @"L1889":
    %"v1903" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1903" ? "L1899" : "L1901" };
  ir_blk{ @"L1899":
    %"v1905" : W = Copy %"v1893";
    %"v1906" : L = (Ext Sw) %"v1905";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1906")
    => goto "L1901" };
  ir_blk{ @"L1901":
    call void $"__printf_buffer_write"(P %"v0", P %"pr.38", L %"pr.109")
    => br %"pr.47" ? "L1910" : "L1150" };
  ir_blk{ @"L1910":
    %"v1915" : W = Copy %"v1893";
    %"v1916" : L = (Ext Sw) %"v1915";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1916")
    => goto "L1150" };
  ir_blk{ @"L1801":
    call %"v1920" : P = $"__GI_memset"(P %"v1918", W #0, L #8);
    %"v1922" : W = VaArg %"v4";
    call %"v1923" : L = $"__wcrtomb"(P %"v1917", W %"v1922", P %"v1918");
    %"v1930" : W = (Cmp Eq L) %"v1923", #18446744073709551615
    => br %"v1930" ? "L1924" : "L1926" };
  ir_blk{ @"L1924":
    call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"(P %"v0")
    => goto "L516" };
  ir_blk{ @"L1926":
    %"v1935" : L = (Ext Sw) %"pr.66";
    %"v1936" : L = Sub %"v1935", %"v1923";
    %"v1941" : W = (Cmp Eq W) %"pr.47", #0
    => br %"v1941" ? "L1937" : "L1939" };
  ir_blk{ @"L1937":
    %"v1943" : W = Copy %"v1936";
    %"v1944" : L = (Ext Sw) %"v1943";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1944")
    => goto "L1939" };
  ir_blk{ @"L1939":
    call void $"__printf_buffer_write"(P %"v0", P %"v1917", L %"v1923")
    => br %"pr.47" ? "L1947" : "L1150" };
  ir_blk{ @"L1947":
    %"v1952" : W = Copy %"v1936";
    %"v1953" : L = (Ext Sw) %"v1952";
    call void $"glibc_vfprintf_internal#__printf_buffer_pad"(P %"v0", W #32, L %"v1953")
    => goto "L1150" };
  ir_blk{ @"L1955":
    %"v1960" : W = And %"v6", #1
    => br %"v1960" ? "L1958" : "L1957" };
  ir_blk{ @"L1957":
    => goto "L1958" }]))).
