(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_02 : list term :=
  [
        cap_blk{ @"start":
          %"v10" : "p" = op "alloc"(int 8) #8;
          %"v13" : "p" = op "alloc"(int 4) #1000;
          %"v15" : "p" = op "alloc"(int 8) #24;
          %"v85" : "p" = op "alloc"(int 16) #16;
          %"v496" : "p" = op "alloc"(int 8) #8;
          %"v648" : "p" = op "alloc"(int 8) #8;
          %"v1319" : "p" = op "alloc"(int 8) #24;
          %"v1917" : "p" = op "alloc"(int 4) #16;
          %"v1918" : "p" = op "alloc"(int 4) #8;
          %"v1964" : "p" = op "alloc"(int 4) #20;
          %"v2100" : "p" = op "alloc"(int 8) #8;
          %"v18" : "p" = "copy" $"__libc_errno";
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v18";
          %"v19" : "w" = op "raw_load"("sw", int 0) %"chk0";
          (op "flight"(%"v23", "copy", [#18446744073709551615], "none"));
          %"chk1" : "a" = op "check"(int 0, int 8, "read", int 8) %"v4";
          %"v25" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"chk2" : "a" = op "check"(int 0, int 8, "write", int 8) %"v15";
          store.ptr [%"chk2" + 0] <- %"v25";
          call %"v27" : "p" = $"glibc_vfprintf_internal#__find_specmb.gnu_inline"("p" %"v2");
          %"chk3" : "a" = op "check"(int 0, int 8, "write", int 8) %"v10";
          store.ptr [%"chk3" + 0] <- %"v27";
          %"v32" : "l" = "ptoi" %"v27";
          %"v33" : "l" = "ptoi" %"v2";
          %"v34" : "l" = "sub" %"v32", %"v33";
          call void $"__printf_buffer_write"("p" %"v0", "p" %"v2", "l" %"v34");
          call %"v39" : "w" = $"glibc_vfprintf_internal#__printf_buffer_has_failed"("p" %"v0");
          %"v40" : "w" = op "ext"("ub") %"v39"
          => br %"v40" ? "L35" : "L37" };
        cap_blk{ @"L35":
          => ret void };
        cap_blk{ @"L37":
          %"chk4" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v45" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"chk5" : "a" = op "check"(int 0, int 1, "read", int 1) %"v45";
          %"v46" : "w" = op "raw_load"("ub", int 0) %"chk5";
          %"v47" : "w" = op "cmp"("eq", "w") %"v46", #0
          => br %"v47" ? "L42" : "L44" };
        cap_blk{ @"L42":
          => ret void };
        cap_blk{ @"L44":
          %"v52" : "p" = "copy" $"__printf_function_table";
          %"chk6" : "a" = op "check"(int 0, int 8, "read", int 8) %"v52";
          %"v53" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"v54" : "l" = "ptoi" %"v53";
          %"v55" : "l" = "ptoi" #0;
          %"v56" : "w" = op "cmp"("ne", "l") %"v54", %"v55"
          => br %"v56" ? "L58" : "L57" };
        cap_blk{ @"L57":
          %"v59" : "p" = "copy" $"__printf_modifier_table";
          %"chk7" : "a" = op "check"(int 0, int 8, "read", int 8) %"v59";
          %"v60" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"v61" : "l" = "ptoi" %"v60";
          %"v63" : "w" = op "cmp"("ne", "l") %"v61", %"v55"
          => goto "L58" };
        cap_blk{ @"L58" [phi %"v65" : "w" = ("L44" => #1, "L57" => %"v63")]:
          => br %"v65" ? "L67" : "L66" };
        cap_blk{ @"L66":
          %"v68" : "p" = "copy" $"__printf_va_arg_table";
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"v68";
          %"v69" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v70" : "l" = "ptoi" %"v69";
          %"v72" : "w" = op "cmp"("ne", "l") %"v70", %"v55"
          => goto "L67" };
        cap_blk{ @"L67" [phi %"v74" : "w" = ("L58" => #1, "L66" => %"v72")]:
          => br %"v74" ? "L77" : "L79" };
        cap_blk{ @"L79" [phi %"pr.16" : "w" = ("L2128" => %"pr.12", "L67" => #0); phi %"pr.11" : "w" = ("L2128" => %"v2113", "L67" => #0); phi %"pr.9" : "p" = ("L2128" => %"pr.5", "L67" => %"v23"); phi %"pr.4" : "p" = ("L2128" => %"pr.1", "L67" => #0)]:
          %"v102" = %"v13" +p #1000;
          %"chk9" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v108" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk9";
          %"v109" = %"v108" +p #1;
          %"chk10" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk10" + 0] <- %"v109";
          %"chk11" : "a" = op "check"(int 0, int 1, "read", int 1) %"v109";
          %"v110" : "w" = op "raw_load"("ub", int 0) %"chk11";
          %"v111" : "w" = op "ext"("sb") %"v110";
          %"v116" : "w" = op "cmp"("slt", "w") %"v111", #32
          => br %"v116" ? "L118" : "L117" };
        cap_blk{ @"L117":
          %"v120" : "w" = op "cmp"("sgt", "w") %"v111", #122
          => goto "L118" };
        cap_blk{ @"L118" [phi %"v122" : "w" = ("L79" => #1, "L117" => %"v120")]:
          => br %"v122" ? "L114" : "L113" };
        cap_blk{ @"L113":
          %"v126" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v127" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v129" : "w" = "sub" %"v111", #32;
          %"v130" : "l" = op "ext"("sw") %"v129";
          %"v131" = %"v127" +p %"v130";
          %"chk12" : "a" = op "check"(int 0, int 1, "read", int 1) %"v131";
          %"v132" : "w" = op "raw_load"("ub", int 0) %"chk12";
          %"v133" : "l" = op "ext"("uw") %"v132";
          %"v134" : "l" = "shl" %"v133", #2;
          %"v135" = %"v126" +p %"v134";
          %"chk13" : "a" = op "check"(int 0, int 4, "read", int 1) %"v135";
          %"v136" : "w" = op "raw_load"("sw", int 0) %"chk13";
          %"v137" : "l" = op "ext"("sw") %"v136"
          => goto "L114" };
        cap_blk{ @"L114" [phi %"v138" : "l" = ("L113" => %"v137", "L118" => #0)]:
          %"v139" : "w" = "copy" %"v138";
          %"v140" : "l" = op "ext"("sw") %"v139";
          %"v141" = #1 +p %"v140";
          %"v143" : "l" = "ptoi" %"v141"
          => goto "L144" };
        cap_blk{ @"L147":
          %"chk14" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v152" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk14";
          %"v153" = %"v152" +p #1;
          %"chk15" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk15" + 0] <- %"v153";
          %"chk16" : "a" = op "check"(int 0, int 1, "read", int 1) %"v153";
          %"v154" : "w" = op "raw_load"("ub", int 0) %"chk16";
          %"v155" : "w" = op "ext"("sb") %"v154";
          %"v160" : "w" = op "cmp"("slt", "w") %"v155", #32
          => br %"v160" ? "L162" : "L161" };
        cap_blk{ @"L161":
          %"v164" : "w" = op "cmp"("sgt", "w") %"v155", #122
          => goto "L162" };
        cap_blk{ @"L162" [phi %"v166" : "w" = ("L147" => #1, "L161" => %"v164")]:
          => br %"v166" ? "L158" : "L157" };
        cap_blk{ @"L157":
          %"v170" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v171" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v173" : "w" = "sub" %"v155", #32;
          %"v174" : "l" = op "ext"("sw") %"v173";
          %"v175" = %"v171" +p %"v174";
          %"chk17" : "a" = op "check"(int 0, int 1, "read", int 1) %"v175";
          %"v176" : "w" = op "raw_load"("ub", int 0) %"chk17";
          %"v177" : "l" = op "ext"("uw") %"v176";
          %"v178" : "l" = "shl" %"v177", #2;
          %"v179" = %"v170" +p %"v178";
          %"chk18" : "a" = op "check"(int 0, int 4, "read", int 1) %"v179";
          %"v180" : "w" = op "raw_load"("sw", int 0) %"chk18";
          %"v181" : "l" = op "ext"("sw") %"v180"
          => goto "L158" };
        cap_blk{ @"L158" [phi %"v182" : "l" = ("L157" => %"v181", "L162" => #0)]:
          %"v183" : "w" = "copy" %"v182";
          %"v184" : "l" = op "ext"("sw") %"v183";
          %"v185" = #1 +p %"v184";
          %"v187" : "l" = "ptoi" %"v185"
          => goto "L144" };
        cap_blk{ @"L189":
          %"chk19" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v194" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"v195" = %"v194" +p #1;
          %"chk20" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk20" + 0] <- %"v195";
          %"chk21" : "a" = op "check"(int 0, int 1, "read", int 1) %"v195";
          %"v196" : "w" = op "raw_load"("ub", int 0) %"chk21";
          %"v197" : "w" = op "ext"("sb") %"v196";
          %"v202" : "w" = op "cmp"("slt", "w") %"v197", #32
          => br %"v202" ? "L204" : "L203" };
        cap_blk{ @"L203":
          %"v206" : "w" = op "cmp"("sgt", "w") %"v197", #122
          => goto "L204" };
        cap_blk{ @"L204" [phi %"v208" : "w" = ("L189" => #1, "L203" => %"v206")]:
          => br %"v208" ? "L200" : "L199" };
        cap_blk{ @"L199":
          %"v212" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v213" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v215" : "w" = "sub" %"v197", #32;
          %"v216" : "l" = op "ext"("sw") %"v215";
          %"v217" = %"v213" +p %"v216";
          %"chk22" : "a" = op "check"(int 0, int 1, "read", int 1) %"v217";
          %"v218" : "w" = op "raw_load"("ub", int 0) %"chk22";
          %"v219" : "l" = op "ext"("uw") %"v218";
          %"v220" : "l" = "shl" %"v219", #2;
          %"v221" = %"v212" +p %"v220";
          %"chk23" : "a" = op "check"(int 0, int 4, "read", int 1) %"v221";
          %"v222" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"v223" : "l" = op "ext"("sw") %"v222"
          => goto "L200" };
        cap_blk{ @"L200" [phi %"v224" : "l" = ("L199" => %"v223", "L204" => #0)]:
          %"v225" : "w" = "copy" %"v224";
          %"v226" : "l" = op "ext"("sw") %"v225";
          %"v227" = #1 +p %"v226";
          %"v229" : "l" = "ptoi" %"v227"
          => goto "L144" };
        cap_blk{ @"L231":
          %"chk24" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v236" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          %"v237" = %"v236" +p #1;
          %"chk25" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk25" + 0] <- %"v237";
          %"chk26" : "a" = op "check"(int 0, int 1, "read", int 1) %"v237";
          %"v238" : "w" = op "raw_load"("ub", int 0) %"chk26";
          %"v239" : "w" = op "ext"("sb") %"v238";
          %"v244" : "w" = op "cmp"("slt", "w") %"v239", #32
          => br %"v244" ? "L246" : "L245" };
        cap_blk{ @"L245":
          %"v248" : "w" = op "cmp"("sgt", "w") %"v239", #122
          => goto "L246" };
        cap_blk{ @"L246" [phi %"v250" : "w" = ("L231" => #1, "L245" => %"v248")]:
          => br %"v250" ? "L242" : "L241" };
        cap_blk{ @"L241":
          %"v254" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v255" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v257" : "w" = "sub" %"v239", #32;
          %"v258" : "l" = op "ext"("sw") %"v257";
          %"v259" = %"v255" +p %"v258";
          %"chk27" : "a" = op "check"(int 0, int 1, "read", int 1) %"v259";
          %"v260" : "w" = op "raw_load"("ub", int 0) %"chk27";
          %"v261" : "l" = op "ext"("uw") %"v260";
          %"v262" : "l" = "shl" %"v261", #2;
          %"v263" = %"v254" +p %"v262";
          %"chk28" : "a" = op "check"(int 0, int 4, "read", int 1) %"v263";
          %"v264" : "w" = op "raw_load"("sw", int 0) %"chk28";
          %"v265" : "l" = op "ext"("sw") %"v264"
          => goto "L242" };
        cap_blk{ @"L242" [phi %"v266" : "l" = ("L241" => %"v265", "L246" => #0)]:
          %"v267" : "w" = "copy" %"v266";
          %"v268" : "l" = op "ext"("sw") %"v267";
          %"v269" = #1 +p %"v268";
          %"v271" : "l" = "ptoi" %"v269"
          => goto "L144" };
        cap_blk{ @"L273":
          %"chk29" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v278" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk29";
          %"v279" = %"v278" +p #1;
          %"chk30" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk30" + 0] <- %"v279";
          %"chk31" : "a" = op "check"(int 0, int 1, "read", int 1) %"v279";
          %"v280" : "w" = op "raw_load"("ub", int 0) %"chk31";
          %"v281" : "w" = op "ext"("sb") %"v280";
          %"v286" : "w" = op "cmp"("slt", "w") %"v281", #32
          => br %"v286" ? "L288" : "L287" };
        cap_blk{ @"L287":
          %"v290" : "w" = op "cmp"("sgt", "w") %"v281", #122
          => goto "L288" };
        cap_blk{ @"L288" [phi %"v292" : "w" = ("L273" => #1, "L287" => %"v290")]:
          => br %"v292" ? "L284" : "L283" };
        cap_blk{ @"L283":
          %"v296" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v297" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v299" : "w" = "sub" %"v281", #32;
          %"v300" : "l" = op "ext"("sw") %"v299";
          %"v301" = %"v297" +p %"v300";
          %"chk32" : "a" = op "check"(int 0, int 1, "read", int 1) %"v301";
          %"v302" : "w" = op "raw_load"("ub", int 0) %"chk32";
          %"v303" : "l" = op "ext"("uw") %"v302";
          %"v304" : "l" = "shl" %"v303", #2;
          %"v305" = %"v296" +p %"v304";
          %"chk33" : "a" = op "check"(int 0, int 4, "read", int 1) %"v305";
          %"v306" : "w" = op "raw_load"("sw", int 0) %"chk33";
          %"v307" : "l" = op "ext"("sw") %"v306"
          => goto "L284" };
        cap_blk{ @"L284" [phi %"v308" : "l" = ("L283" => %"v307", "L288" => #0)]:
          %"v309" : "w" = "copy" %"v308";
          %"v310" : "l" = op "ext"("sw") %"v309";
          %"v311" = #1 +p %"v310";
          %"v313" : "l" = "ptoi" %"v311"
          => goto "L144" };
        cap_blk{ @"L314":
          %"v319" : "w" = op "cmp"("eq", "w") %"pr.47", #0
          => br %"v319" ? "L317" : "L316" };
        cap_blk{ @"L316":
          => goto "L317" };
        cap_blk{ @"L317" [phi %"pr.93" : "w" = ("L316" => %"pr.92", "L314" => #48)]:
          %"chk34" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v325" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk34";
          %"v326" = %"v325" +p #1;
          %"chk35" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk35" + 0] <- %"v326";
          %"chk36" : "a" = op "check"(int 0, int 1, "read", int 1) %"v326";
          %"v327" : "w" = op "raw_load"("ub", int 0) %"chk36";
          %"v328" : "w" = op "ext"("sb") %"v327";
          %"v333" : "w" = op "cmp"("slt", "w") %"v328", #32
          => br %"v333" ? "L335" : "L334" };
        cap_blk{ @"L334":
          %"v337" : "w" = op "cmp"("sgt", "w") %"v328", #122
          => goto "L335" };
        cap_blk{ @"L335" [phi %"v339" : "w" = ("L317" => #1, "L334" => %"v337")]:
          => br %"v339" ? "L331" : "L330" };
        cap_blk{ @"L330":
          %"v343" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v344" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v346" : "w" = "sub" %"v328", #32;
          %"v347" : "l" = op "ext"("sw") %"v346";
          %"v348" = %"v344" +p %"v347";
          %"chk37" : "a" = op "check"(int 0, int 1, "read", int 1) %"v348";
          %"v349" : "w" = op "raw_load"("ub", int 0) %"chk37";
          %"v350" : "l" = op "ext"("uw") %"v349";
          %"v351" : "l" = "shl" %"v350", #2;
          %"v352" = %"v343" +p %"v351";
          %"chk38" : "a" = op "check"(int 0, int 4, "read", int 1) %"v352";
          %"v353" : "w" = op "raw_load"("sw", int 0) %"chk38";
          %"v354" : "l" = op "ext"("sw") %"v353"
          => goto "L331" };
        cap_blk{ @"L331" [phi %"v355" : "l" = ("L330" => %"v354", "L335" => #0)]:
          %"v356" : "w" = "copy" %"v355";
          %"v357" : "l" = op "ext"("sw") %"v356";
          %"v358" = #1 +p %"v357";
          %"v360" : "l" = "ptoi" %"v358"
          => goto "L144" };
        cap_blk{ @"L361":
          (op "flight"(%"v368", "copy", [#18446744073709551615], "none"));
          %"v369" : "l" = "ptoi" %"pr.5";
          %"v370" : "l" = "ptoi" %"v368";
          %"v371" : "w" = op "cmp"("eq", "l") %"v369", %"v370"
          => br %"v371" ? "L362" : "L364" };
        cap_blk{ @"L362":
          %"v372" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk39" : "a" = op "check"(int 0, int 8, "read", int 8) %"v372";
          %"v373" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk39";
          %"v374" = %"v373" +p #8;
          %"chk40" : "a" = op "check"(int 0, int 8, "read", int 8) %"v374";
          %"v375" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"v376" = %"v375" +p #56;
          %"v380" = %"v376" +p #8;
          %"chk41" : "a" = op "check"(int 0, int 8, "read", int 8) %"v380";
          %"v381" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk41";
          %"v382" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk42" : "a" = op "check"(int 0, int 8, "read", int 8) %"v382";
          %"v383" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk42";
          %"v384" = %"v383" +p #8;
          %"chk43" : "a" = op "check"(int 0, int 8, "read", int 8) %"v384";
          %"v385" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk43";
          %"v386" = %"v385" +p #56;
          %"v390" = %"v386" +p #16;
          %"chk44" : "a" = op "check"(int 0, int 8, "read", int 8) %"v390";
          %"v391" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk44";
          %"chk45" : "a" = op "check"(int 0, int 1, "read", int 1) %"v391";
          %"v396" : "w" = op "raw_load"("sb", int 0) %"chk45";
          %"v397" : "w" = op "cmp"("eq", "w") %"v396", #0
          => br %"v397" ? "L399" : "L398" };
        cap_blk{ @"L398":
          %"v401" : "w" = op "raw_load"("sb", int 0) %"chk45";
          %"v402" : "w" = op "cmp"("eq", "w") %"v401", #127
          => goto "L399" };
        cap_blk{ @"L399" [phi %"v404" : "w" = ("L362" => #1, "L398" => %"v402")]:
          => br %"v404" ? "L406" : "L405" };
        cap_blk{ @"L405":
          %"chk47" : "a" = op "check"(int 0, int 1, "read", int 1) %"v381";
          %"v408" : "w" = op "raw_load"("sb", int 0) %"chk47";
          %"v409" : "w" = op "cmp"("eq", "w") %"v408", #0
          => goto "L406" };
        cap_blk{ @"L406" [phi %"v411" : "w" = ("L399" => #1, "L405" => %"v409")]:
          => br %"v411" ? "L364" : "L393" };
        cap_blk{ @"L393":
          => goto "L364" };
        cap_blk{ @"L364" [phi %"pr.6" : "p" = ("L393" => %"v391", "L406" => #0, "L361" => %"pr.5"); phi %"pr.2" : "p" = ("L393" => %"v381", "L406" => %"v381", "L361" => %"pr.1")]:
          %"chk48" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v417" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk48";
          %"v418" = %"v417" +p #1;
          %"chk49" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk49" + 0] <- %"v418";
          %"chk50" : "a" = op "check"(int 0, int 1, "read", int 1) %"v418";
          %"v419" : "w" = op "raw_load"("ub", int 0) %"chk50";
          %"v420" : "w" = op "ext"("sb") %"v419";
          %"v425" : "w" = op "cmp"("slt", "w") %"v420", #32
          => br %"v425" ? "L427" : "L426" };
        cap_blk{ @"L426":
          %"v429" : "w" = op "cmp"("sgt", "w") %"v420", #122
          => goto "L427" };
        cap_blk{ @"L427" [phi %"v431" : "w" = ("L364" => #1, "L426" => %"v429")]:
          => br %"v431" ? "L423" : "L422" };
        cap_blk{ @"L422":
          %"v435" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v436" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v438" : "w" = "sub" %"v420", #32;
          %"v439" : "l" = op "ext"("sw") %"v438";
          %"v440" = %"v436" +p %"v439";
          %"chk51" : "a" = op "check"(int 0, int 1, "read", int 1) %"v440";
          %"v441" : "w" = op "raw_load"("ub", int 0) %"chk51";
          %"v442" : "l" = op "ext"("uw") %"v441";
          %"v443" : "l" = "shl" %"v442", #2;
          %"v444" = %"v435" +p %"v443";
          %"chk52" : "a" = op "check"(int 0, int 4, "read", int 1) %"v444";
          %"v445" : "w" = op "raw_load"("sw", int 0) %"chk52";
          %"v446" : "l" = op "ext"("sw") %"v445"
          => goto "L423" };
        cap_blk{ @"L423" [phi %"v447" : "l" = ("L422" => %"v446", "L427" => #0)]:
          %"v448" : "w" = "copy" %"v447";
          %"v449" : "l" = op "ext"("sw") %"v448";
          %"v450" = #1 +p %"v449";
          %"v452" : "l" = "ptoi" %"v450"
          => goto "L144" };
        cap_blk{ @"L454":
          %"chk53" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v459" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk53";
          %"v460" = %"v459" +p #1;
          %"chk54" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk54" + 0] <- %"v460";
          %"chk55" : "a" = op "check"(int 0, int 1, "read", int 1) %"v460";
          %"v461" : "w" = op "raw_load"("ub", int 0) %"chk55";
          %"v462" : "w" = op "ext"("sb") %"v461";
          %"v467" : "w" = op "cmp"("slt", "w") %"v462", #32
          => br %"v467" ? "L469" : "L468" };
        cap_blk{ @"L468":
          %"v471" : "w" = op "cmp"("sgt", "w") %"v462", #122
          => goto "L469" };
        cap_blk{ @"L469" [phi %"v473" : "w" = ("L454" => #1, "L468" => %"v471")]:
          => br %"v473" ? "L465" : "L464" };
        cap_blk{ @"L464":
          %"v477" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step0_jumps.277";
          %"v478" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v480" : "w" = "sub" %"v462", #32;
          %"v481" : "l" = op "ext"("sw") %"v480";
          %"v482" = %"v478" +p %"v481";
          %"chk56" : "a" = op "check"(int 0, int 1, "read", int 1) %"v482";
          %"v483" : "w" = op "raw_load"("ub", int 0) %"chk56";
          %"v484" : "l" = op "ext"("uw") %"v483";
          %"v485" : "l" = "shl" %"v484", #2;
          %"v486" = %"v477" +p %"v485";
          %"chk57" : "a" = op "check"(int 0, int 4, "read", int 1) %"v486";
          %"v487" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"v488" : "l" = op "ext"("sw") %"v487"
          => goto "L465" };
        cap_blk{ @"L465" [phi %"v489" : "l" = ("L464" => %"v488", "L469" => #0)]:
          %"v490" : "w" = "copy" %"v489";
          %"v491" : "l" = op "ext"("sw") %"v490";
          %"v492" = #1 +p %"v491";
          %"v494" : "l" = "ptoi" %"v492"
          => goto "L144" };
        cap_blk{ @"L495":
          %"chk58" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v497" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk58";
          %"v498" = %"v497" +p #1;
          %"chk59" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk59" + 0] <- %"v498";
          %"chk60" : "a" = op "check"(int 0, int 8, "write", int 8) %"v496";
          store.ptr [%"chk60" + 0] <- %"v498";
          %"chk61" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk60", %"v496";
          %"v502" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk61";
          %"chk62" : "a" = op "check"(int 0, int 1, "read", int 1) %"v502";
          %"v503" : "w" = op "raw_load"("ub", int 0) %"chk62";
          %"v504" : "w" = "sub" %"v503", #48;
          %"v505" : "w" = op "cmp"("ult", "w") %"v504", #10
          => br %"v505" ? "L499" : "L501" };
        cap_blk{ @"L499":
          call %"v507" : "w" = $"glibc_vfprintf_internal#read_int"("p" %"v496");
          %"v513" : "w" = op "cmp"("eq", "w") %"v507", #4294967295
          => br %"v513" ? "L508" : "L510" };
        cap_blk{ @"L508":
          %"v514" : "p" = "copy" $"__libc_errno";
          %"chk63" : "a" = op "check"(int 0, int 4, "write", int 1) %"v514";
          store "w" [%"chk63" + 0] <- #75;
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L516" };
        cap_blk{ @"L510":
          => br %"v507" ? "L522" : "L523" };
        cap_blk{ @"L522":
          %"chk64" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk60", %"v496";
          %"v524" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk64";
          %"chk65" : "a" = op "check"(int 0, int 1, "read", int 1) %"v524";
          %"v525" : "w" = op "raw_load"("ub", int 0) %"chk65";
          %"v526" : "w" = op "cmp"("eq", "w") %"v525", #36
          => goto "L523" };
        cap_blk{ @"L523" [phi %"v528" : "w" = ("L510" => #0, "L522" => %"v526")]:
          => br %"v528" ? "L77" : "L501" };
        cap_blk{ @"L501":
          %"v531" : "w" = "va_arg" %"v4";
          %"v536" : "w" = op "cmp"("slt", "w") %"v531", #0
          => br %"v536" ? "L532" : "L534" };
        cap_blk{ @"L532":
          %"v538" : "w" = "neg" %"v531"
          => goto "L534" };
        cap_blk{ @"L534" [phi %"pr.94" : "w" = ("L532" => #32, "L501" => %"pr.92"); phi %"pr.76" : "w" = ("L532" => %"v538", "L501" => %"v531"); phi %"pr.48" : "w" = ("L532" => #1, "L501" => %"pr.47")]:
          %"chk66" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v544" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk66";
          %"chk67" : "a" = op "check"(int 0, int 1, "read", int 1) %"v544";
          %"v545" : "w" = op "raw_load"("ub", int 0) %"chk67";
          %"v546" : "w" = op "ext"("sb") %"v545";
          %"v551" : "w" = op "cmp"("slt", "w") %"v546", #32
          => br %"v551" ? "L553" : "L552" };
        cap_blk{ @"L552":
          %"v555" : "w" = op "cmp"("sgt", "w") %"v546", #122
          => goto "L553" };
        cap_blk{ @"L553" [phi %"v557" : "w" = ("L534" => #1, "L552" => %"v555")]:
          => br %"v557" ? "L549" : "L548" };
        cap_blk{ @"L548":
          %"v561" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step1_jumps.278";
          %"v562" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v564" : "w" = "sub" %"v546", #32;
          %"v565" : "l" = op "ext"("sw") %"v564";
          %"v566" = %"v562" +p %"v565";
          %"chk68" : "a" = op "check"(int 0, int 1, "read", int 1) %"v566";
          %"v567" : "w" = op "raw_load"("ub", int 0) %"chk68";
          %"v568" : "l" = op "ext"("uw") %"v567";
          %"v569" : "l" = "shl" %"v568", #2;
          %"v570" = %"v561" +p %"v569";
          %"chk69" : "a" = op "check"(int 0, int 4, "read", int 1) %"v570";
          %"v571" : "w" = op "raw_load"("sw", int 0) %"chk69";
          %"v572" : "l" = op "ext"("sw") %"v571"
          => goto "L549" };
        cap_blk{ @"L549" [phi %"v573" : "l" = ("L548" => %"v572", "L553" => #0)]:
          %"v574" : "w" = "copy" %"v573";
          %"v575" : "l" = op "ext"("sw") %"v574";
          %"v576" = #1 +p %"v575";
          %"v578" : "l" = "ptoi" %"v576"
          => goto "L144" };
        cap_blk{ @"L579":
          call %"v580" : "w" = $"glibc_vfprintf_internal#read_int"("p" %"v10");
          %"v586" : "w" = op "cmp"("eq", "w") %"v580", #4294967295
          => br %"v586" ? "L581" : "L583" }
  ].
