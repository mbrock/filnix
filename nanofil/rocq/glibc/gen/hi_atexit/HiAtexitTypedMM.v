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

Definition hi_fn_glibc_fileops'23mmap_remap_check : func :=
  ir_fn{ "local" "glibc_fileops#mmap_remap_check"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 8) #144;
    %"v7" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v8";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v10" = %"v8" +p #144;
    %"chk1" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v13" : W = %"chk2"(P %"v0", P %"v2");
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v17" = %"v2" +p #24;
    %"chk3" : A = (Check 0 4 Read 1) %"v17";
    %"v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v19" : W = And %"v18", #61440;
    %"v20" : W = (Cmp Eq W) %"v19", #32768
    => goto "L16";
  @"L16" [%"v22" : W = phi("iw_1.join" => #0, "L15" => %"v20")]:
    => br %"v22" ? "L23" : "L24";
  @"L23":
    %"v25" = %"v2" +p #48;
    %"chk4" : A = (Check 0 8 Read 1) %"v25";
    %"v26" : L = (RawLoad LdL 0) %"chk4";
    %"v27" : W = (Cmp Ne L) %"v26", #0
    => goto "L24";
  @"L24" [%"v29" : W = phi("L16" => #0, "L23" => %"v27")]:
    => br %"v29" ? "L34" : "L31";
  @"L34":
    => goto "L31";
  @"L31" [%"v44" : W = phi("L24" => #0, "L34" => #1)]:
    => br %"v44" ? "L3" : "L4";
  @"L3":
    call %"v46" : W = $"__GI___getpagesize"();
    %"v47" : L = (Ext Sw) %"v46";
    %"v51" = %"v2" +p #48;
    %"chk5" : A = (Check 0 8 Read 1) %"v51";
    %"v52" : L = (RawLoad LdL 0) %"chk5";
    %"v54" : L = Add %"v52", %"v47";
    %"v55" : L = Sub %"v54", #1;
    %"v57" : L = Sub %"v47", #1;
    %"v58" : L = Xor %"v57", #(-1);
    %"v59" : L = And %"v55", %"v58";
    %"v61" = %"v0" +p #64;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v64" = %"v0" +p #56;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v66" : L = Ptoi %"v62";
    %"v67" : L = Ptoi %"v65";
    %"v68" : L = Sub %"v66", %"v67";
    %"v70" : L = Add %"v68", %"v47";
    %"v71" : L = Sub %"v70", #1;
    %"v75" : L = And %"v71", %"v58";
    %"v76" : W = (Cmp Ult L) %"v59", %"v75"
    => br %"v76" ? "L48" : "L49";
  @"L48":
    %"v78" = %"v0" +p #56;
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v80" = %"v2" +p #48;
    %"v81" : L = (RawLoad LdL 0) %"chk5";
    %"v83" : L = Add %"v81", %"v47";
    %"v84" : L = Sub %"v83", #1;
    %"v88" : L = And %"v84", %"v58";
    %"v89" = %"v79" +p %"v88";
    %"v91" = %"v0" +p #64;
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v96" : L = Ptoi %"v92";
    %"v97" : L = Ptoi %"v95";
    %"v98" : L = Sub %"v96", %"v97";
    %"v100" : L = Add %"v98", %"v47";
    %"v101" : L = Sub %"v100", #1;
    %"v105" : L = And %"v101", %"v58";
    %"v107" : L = (RawLoad LdL 0) %"chk5";
    %"v109" : L = Add %"v107", %"v47";
    %"v110" : L = Sub %"v109", #1;
    %"v114" : L = And %"v110", %"v58";
    %"v115" : L = Sub %"v105", %"v114";
    call %"v116" : W = $"__GI___munmap"(P %"v89", L %"v115");
    %"chk13" : A = (Renew 0 8 Read 8) %"chk7", %"v78";
    %"v121" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Renew 0 8 Read 1) %"chk5", %"v80";
    %"v123" : L = (RawLoad LdL 0) %"chk14";
    %"v124" = %"v121" +p %"v123";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk6", %"v91";
    store.ptr [%"chk15" + 0] <- %"v124"
    => goto "L50";
  @"L49":
    %"v128" = %"v2" +p #48;
    %"v129" : L = (RawLoad LdL 0) %"chk5";
    %"v131" : L = Add %"v129", %"v47";
    %"v132" : L = Sub %"v131", #1;
    %"v136" : L = And %"v132", %"v58";
    %"v138" = %"v0" +p #64;
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v141" = %"v0" +p #56;
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v143" : L = Ptoi %"v139";
    %"v144" : L = Ptoi %"v142";
    %"v145" : L = Sub %"v143", %"v144";
    %"v147" : L = Add %"v145", %"v47";
    %"v148" : L = Sub %"v147", #1;
    %"v152" : L = And %"v148", %"v58";
    %"v153" : W = (Cmp Ugt L) %"v136", %"v152"
    => br %"v153" ? "L125" : "L126";
  @"L125":
    %"v156" = %"v0" +p #56;
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v159" = %"v0" +p #64;
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v164" : L = Ptoi %"v160";
    %"v165" : L = Ptoi %"v163";
    %"v166" : L = Sub %"v164", %"v165";
    %"v168" : L = Add %"v166", %"v47";
    %"v169" : L = Sub %"v168", #1;
    %"v173" : L = And %"v169", %"v58";
    %"v174" = %"v2" +p #48;
    %"v175" : L = (RawLoad LdL 0) %"chk5";
    %"v177" : L = Add %"v175", %"v47";
    %"v178" : L = Sub %"v177", #1;
    %"v182" : L = And %"v178", %"v58";
    call %"v183" : P = $"__GI___mremap"(P %"v157", L %"v173", L %"v182", W #1);
    (Flight (a "v190") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v191" : L = Ptoi %"v183";
    %"v192" : L = Ptoi %"v190";
    %"v193" : W = (Cmp Eq L) %"v191", %"v192"
    => br %"v193" ? "L184" : "L186";
  @"L184":
    %"v195" = %"v0" +p #56;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk7", %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v198" = %"v0" +p #64;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk6", %"v198";
    %"v199" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v203" : L = Ptoi %"v199";
    %"v204" : L = Ptoi %"v202";
    %"v205" : L = Sub %"v203", %"v204";
    call %"v206" : W = $"__GI___munmap"(P %"v196", L %"v205")
    => goto "L207";
  @"L186":
    %"v210" = %"v0" +p #56;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk7", %"v210";
    store.ptr [%"chk26" + 0] <- %"v183";
    %"v213" = %"v0" +p #64;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk7", %"v210";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v217" = %"v2" +p #48;
    %"chk28" : A = (Renew 0 8 Read 1) %"chk5", %"v217";
    %"v218" : L = (RawLoad LdL 0) %"chk28";
    %"v219" = %"v216" +p %"v218";
    %"chk29" : A = (Renew 0 8 Write 8) %"chk6", %"v213";
    store.ptr [%"chk29" + 0] <- %"v219"
    => goto "L50";
  @"L126":
    %"v221" = %"v0" +p #64;
    %"v223" = %"v0" +p #56;
    %"v224" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v225" = %"v2" +p #48;
    %"v226" : L = (RawLoad LdL 0) %"chk5";
    %"v227" = %"v224" +p %"v226";
    %"chk32" : A = (Renew 0 8 Write 8) %"chk6", %"v221";
    store.ptr [%"chk32" + 0] <- %"v227"
    => goto "L50";
  @"L50":
    %"v229" = %"v0" +p #144;
    %"chk33" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v229";
    %"v230" : L = (RawLoad LdL 0) %"chk33";
    %"v232" = %"v0" +p #16;
    %"chk34" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v232";
    %"v233" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v235" = %"v0" +p #8;
    %"chk35" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v235";
    %"v236" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v237" : L = Ptoi %"v233";
    %"v238" : L = Ptoi %"v236";
    %"v239" : L = Sub %"v237", %"v238";
    %"v240" : L = Sub %"v230", %"v239";
    %"chk36" : A = (Renew 0 8 Write 1) %"chk33", %"v229";
    store Wl [%"chk36" + 0] <- %"v240";
    %"v242" = %"v0" +p #24;
    %"v244" = %"v0" +p #56;
    %"v245" : P = (RawLoadPointer 40 load_effects) %"chk34";
    %"chk38" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v242";
    store.ptr [%"chk38" + 0] <- %"v245";
    %"chk39" : A = (Renew 0 8 Read 1) %"chk33", %"v229";
    %"v253" : L = (RawLoad LdL 0) %"chk39";
    %"v255" = %"v0" +p #64;
    %"chk40" : A = (Renew 0 8 Read 8) %"chk6", %"v255";
    %"v256" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (Renew 0 8 Read 8) %"chk7", %"v244";
    %"v259" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v260" : L = Ptoi %"v256";
    %"v261" : L = Ptoi %"v259";
    %"v262" : L = Sub %"v260", %"v261";
    %"v263" : W = (Cmp Slt L) %"v253", %"v262"
    => br %"v263" ? "L248" : "L249";
  @"L248":
    %"v265" = %"v0" +p #56;
    %"v266" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v268" = %"v0" +p #144;
    %"v269" : L = (RawLoad LdL 0) %"chk39";
    %"v270" = %"v266" +p %"v269"
    => goto "L250";
  @"L249":
    %"v272" = %"v0" +p #64;
    %"v273" : P = (RawLoadPointer 0 load_effects) %"chk40"
    => goto "L250";
  @"L250" [%"v274" : P = phi("L248" => %"v270", "L249" => %"v273")]:
    %"chk45" : A = (Renew 0 8 Write 8) %"chk35", %"v235";
    store.ptr [%"chk45" + 0] <- %"v274";
    %"v276" = %"v0" +p #16;
    %"v278" = %"v0" +p #64;
    %"chk46" : A = (Renew 0 8 Read 8) %"chk6", %"v278";
    %"v279" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"chk47" : A = (Renew 0 8 Write 8) %"chk34", %"v276";
    store.ptr [%"chk47" + 0] <- %"v279";
    %"v284" = %"v0" +p #144;
    %"chk48" : A = (Renew 0 8 Read 1) %"chk33", %"v284";
    %"v285" : L = (RawLoad LdL 0) %"chk48";
    %"chk49" : A = (Renew 0 8 Read 8) %"chk6", %"v278";
    %"v288" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v290" = %"v0" +p #56;
    %"chk50" : A = (Renew 0 8 Read 8) %"chk7", %"v290";
    %"v291" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v292" : L = Ptoi %"v288";
    %"v293" : L = Ptoi %"v291";
    %"v294" : L = Sub %"v292", %"v293";
    %"v295" : W = (Cmp Slt L) %"v285", %"v294"
    => br %"v295" ? "L280" : "L282";
  @"L280":
    %"v300" = %"v0" +p #112;
    %"v301" : W = (RawLoad (LdNarrow Sw) (-32)) %"chk48";
    %"v303" = %"v0" +p #64;
    %"v304" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"v306" = %"v0" +p #56;
    %"v307" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v308" : L = Ptoi %"v304";
    %"v309" : L = Ptoi %"v307";
    %"v310" : L = Sub %"v308", %"v309";
    call %"v311" : L = $"__lseek64"(W %"v301", L %"v310", W #0);
    %"chk54" : A = (Renew 0 8 Read 8) %"chk6", %"v303";
    %"v314" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk55" : A = (Renew 0 8 Read 8) %"chk7", %"v306";
    %"v317" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v318" : L = Ptoi %"v314";
    %"v319" : L = Ptoi %"v317";
    %"v320" : L = Sub %"v318", %"v319";
    %"v321" : W = (Cmp Ne L) %"v311", %"v320"
    => br %"v321" ? "L296" : "L297";
  @"L296":
    %"chk56" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v323" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v324" : W = Or %"v323", #32;
    %"chk57" : A = (Renew 0 4 Write 1) %"chk56", %"v0";
    store Ww [%"chk57" + 0] <- %"v324"
    => goto "L282";
  @"L297":
    %"v326" = %"v0" +p #144;
    %"v328" = %"v0" +p #64;
    %"v329" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v331" = %"v0" +p #56;
    %"v332" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v333" : L = Ptoi %"v329";
    %"v334" : L = Ptoi %"v332";
    %"v335" : L = Sub %"v333", %"v334";
    %"chk60" : A = (Renew 0 8 Write 1) %"chk33", %"v326";
    store Wl [%"chk60" + 0] <- %"v335"
    => goto "L282";
  @"L282":
    => ret #0;
  @"L4":
    %"v338" = %"v0" +p #56;
    %"chk61" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v338";
    %"v339" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v341" = %"v0" +p #64;
    %"chk62" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v341";
    %"v342" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"v345" : P = (RawLoadPointer 0 load_effects) %"chk61";
    %"v346" : L = Ptoi %"v342";
    %"v347" : L = Ptoi %"v345";
    %"v348" : L = Sub %"v346", %"v347";
    call %"v349" : W = $"__GI___munmap"(P %"v339", L %"v348")
    => goto "L207";
  @"L207":
    %"v351" = %"v0" +p #56;
    %"v353" = %"v0" +p #64;
    %"chk64" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v353";
    store.ptr [%"chk64" + 0] <- #0;
    %"chk65" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v351";
    store.ptr [%"chk65" + 0] <- #0;
    %"v355" = %"v0" +p #24;
    %"chk66" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v355";
    store.ptr [%"chk66" + 0] <- #0;
    %"v357" = %"v0" +p #8;
    %"chk67" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v357";
    store.ptr [%"chk67" + 0] <- #0;
    %"v359" = %"v0" +p #16;
    %"chk68" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v359";
    store.ptr [%"chk68" + 0] <- #0;
    %"v364" = %"v0" +p #192;
    %"chk69" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v364";
    %"v365" : W = (RawLoad (LdNarrow Sw) 0) %"chk69";
    %"v366" : W = (Cmp Sle W) %"v365", #0
    => br %"v366" ? "L360" : "L361";
  @"L360":
    %"v368" = %"v0" +p #216;
    %"v369" : P = Copy $"__io_vtables";
    %"v370" = %"v369" +p #336;
    %"chk70" : A = (Renew 0 8 Write 8) %"chk0", %"v368";
    store.ptr [%"chk70" + 0] <- %"v370"
    => goto "L362";
  @"L361":
    %"v372" = %"v0" +p #216;
    %"v373" : P = Copy $"__io_vtables";
    %"v374" = %"v373" +p #840;
    %"chk71" : A = (Renew 0 8 Write 8) %"chk0", %"v372";
    store.ptr [%"chk71" + 0] <- %"v374"
    => goto "L362";
  @"L362":
    %"v376" = %"v0" +p #160;
    %"chk72" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v376";
    %"v377" : P = (RawLoadPointer 0 load_effects) %"chk72";
    %"v378" = %"v377" +p #224;
    %"v379" : P = Copy $"__io_vtables";
    %"v380" = %"v379" +p #840;
    %"chk73" : A = (Check 0 8 Write 8) %"v378";
    store.ptr [%"chk73" + 0] <- %"v380"
    => ret #1
} }.
