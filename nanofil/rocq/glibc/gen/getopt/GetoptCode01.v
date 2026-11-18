(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition getopt_items_01 : list term :=
  [
    cap_fn{ "local" "glibc_getopt#process_long_option" [param "w" %"v0"; param "p" %"v2"; param "p" %"v4"; param "p" %"v6"; param "p" %"v8"; param "w" %"v10"; param "p" %"v12"; param "w" %"v14"; param "p" %"v16"] -> "w"
      {
        @"start":
          %"v25" = %"v12" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v25";
          %"v26" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0"
          => goto "L27";
        @"L27" [phi %"pr.1" : "p" = ("L29" => %"v41", "start" => %"v26")]:
          %"chk1" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.1";
          %"v32" : "w" = op "raw_load"("sb", int 0) %"chk1"
          => br %"v32" ? "L33" : "L34";
        @"L33":
          %"v36" : "w" = op "raw_load"("sb", int 0) %"chk1";
          %"v37" : "w" = op "cmp"("ne", "w") %"v36", #61
          => goto "L34";
        @"L34" [phi %"v39" : "w" = ("L27" => #0, "L33" => %"v37")]:
          => br %"v39" ? "L29" : "L30";
        @"L29":
          %"v41" = %"pr.1" +p #1
          => goto poll "L27";
        @"L30":
          %"v44" = %"v12" +p #32;
          %"chk3" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v44";
          %"v45" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk3";
          %"v46" : "l" = "ptoi" %"pr.1";
          %"v47" : "l" = "ptoi" %"v45";
          %"v48" : "l" = "sub" %"v46", %"v47"
          => goto "L50";
        @"L50" [phi %"pr.9" : "w" = ("L30" => #0, "L52" => %"v84"); phi %"pr.2" : "p" = ("L30" => %"v6", "L52" => %"v82")]:
          %"chk4" : "a" = op "check"(int 0, int 8, "read", int 8) %"pr.2";
          %"v55" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"v56" : "l" = "ptoi" %"v55";
          %"v57" : "w" = op "cmp"("ne", "l") %"v56", #0
          => br %"v57" ? "L51" : "L53";
        @"L51":
          %"v62" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"v64" = %"v12" +p #32;
          %"chk6" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v64";
          %"v65" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          call %"v67" : "w" = $"__GI_strncmp"("p" %"v62", "p" %"v65", "l" %"v48");
          %"v68" : "w" = op "cmp"("eq", "w") %"v67", #0
          => br %"v68" ? "L69" : "L70";
        @"L69":
          %"chk7" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk4", %"pr.2";
          %"v73" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          call %"v74" : "l" = $"__GI_strlen"("p" %"v73");
          %"v75" : "w" = op "cmp"("eq", "l") %"v48", %"v74"
          => goto "L70";
        @"L70" [phi %"v77" : "w" = ("L51" => #0, "L69" => %"v75")]:
          => br %"v77" ? "L53" : "L52";
        @"L52":
          %"v82" = %"pr.2" +p #32;
          %"v84" : "w" = "add" %"pr.9", #1
          => goto poll "L50";
        @"L53" [phi %"pr.11" : "w" = ("L50" => #0, "L70" => %"pr.9"); phi %"pr.6" : "p" = ("L50" => #0, "L70" => %"pr.2")]:
          %"v89" : "l" = "ptoi" %"pr.6";
          %"v90" : "l" = "ptoi" #0;
          %"v91" : "w" = op "cmp"("eq", "l") %"v89", %"v90"
          => br %"v91" ? "L98" : "L87";
        @"L98" [phi %"pr.42" : "w" = ("L108" => %"pr.40", "L53" => #4294967295); phi %"pr.39" : "w" = ("L108" => %"pr.31", "L53" => #0); phi %"pr.30" : "w" = ("L108" => %"pr.22", "L53" => #0); phi %"pr.21" : "p" = ("L108" => %"pr.14", "L53" => #0); phi %"pr.13" : "w" = ("L108" => %"v227", "L53" => #0); phi %"pr.8" : "p" = ("L108" => %"pr.4", "L53" => %"pr.6"); phi %"pr.3" : "p" = ("L108" => %"v225", "L53" => %"v6")]:
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"pr.3";
          %"v103" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v104" : "l" = "ptoi" %"v103";
          %"v105" : "w" = op "cmp"("ne", "l") %"v104", #0
          => br %"v105" ? "L99" : "L101";
        @"L99":
          %"v110" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v112" = %"v12" +p #32;
          %"chk10" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v112";
          %"v113" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk10";
          call %"v115" : "w" = $"__GI_strncmp"("p" %"v110", "p" %"v113", "l" %"v48");
          %"v116" : "w" = op "cmp"("eq", "w") %"v115", #0
          => br %"v116" ? "L106" : "L108";
        @"L106":
          %"v121" : "l" = "ptoi" %"pr.8";
          %"v123" : "w" = op "cmp"("eq", "l") %"v121", %"v90"
          => br %"v123" ? "L108" : "L118";
        @"L118":
          => br %"v10" ? "L131" : "L130";
        @"L130":
          %"v133" = %"pr.8" +p #8;
          %"chk11" : "a" = op "check"(int 0, int 4, "read", int 1) %"v133";
          %"v134" : "w" = op "raw_load"("sw", int 0) %"chk11";
          %"v136" = %"pr.3" +p #8;
          %"chk12" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk8", %"v136";
          %"v137" : "w" = op "raw_load"("sw", int 0) %"chk12";
          %"v138" : "w" = op "cmp"("ne", "w") %"v134", %"v137"
          => goto "L131";
        @"L131" [phi %"v140" : "w" = ("L118" => #1, "L130" => %"v138")]:
          => br %"v140" ? "L142" : "L141";
        @"L141":
          %"v144" = %"pr.8" +p #16;
          %"chk13" : "a" = op "check"(int 0, int 8, "read", int 8) %"v144";
          %"v145" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk13";
          %"v147" = %"pr.3" +p #16;
          %"chk14" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk8", %"v147";
          %"v148" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk14";
          %"v149" : "l" = "ptoi" %"v145";
          %"v150" : "l" = "ptoi" %"v148";
          %"v151" : "w" = op "cmp"("ne", "l") %"v149", %"v150"
          => goto "L142";
        @"L142" [phi %"v153" : "w" = ("L131" => #1, "L141" => %"v151")]:
          => br %"v153" ? "L155" : "L154";
        @"L154":
          %"v157" = %"pr.8" +p #24;
          %"chk15" : "a" = op "check"(int 0, int 4, "read", int 1) %"v157";
          %"v158" : "w" = op "raw_load"("sw", int 0) %"chk15";
          %"v160" = %"pr.3" +p #24;
          %"chk16" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk8", %"v160";
          %"v161" : "w" = op "raw_load"("sw", int 0) %"chk16";
          %"v162" : "w" = op "cmp"("ne", "w") %"v158", %"v161"
          => goto "L155";
        @"L155" [phi %"v164" : "w" = ("L142" => #1, "L154" => %"v162")]:
          => br %"v164" ? "L126" : "L108";
        @"L126":
          %"v169" : "w" = op "cmp"("eq", "w") %"pr.39", #0
          => br %"v169" ? "L165" : "L108";
        @"L165":
          %"v174" : "w" = op "cmp"("eq", "w") %"v14", #0
          => br %"v174" ? "L172" : "L171";
        @"L171":
          %"v179" : "l" = "ptoi" %"pr.21";
          %"v181" : "w" = op "cmp"("eq", "l") %"v179", #0
          => br %"v181" ? "L175" : "L172";
        @"L175":
          %"v186" : "l" = op "ext"("sw") %"pr.9";
          call %"iw_1.v3" : "w" = $"__GI___libc_alloca_cutoff"("l" %"v186");
          %"iw_1.v4" : "l" = op "ext"("sw") %"iw_1.v3";
          %"iw_1.v5" : "w" = op "cmp"("ne", "l") %"iw_1.v4", #0
          => br %"iw_1.v5" ? "iw_1.L7" : "iw_1.L6";
        @"iw_1.L6":
          %"iw_1.v11" : "w" = op "cmp"("ule", "l") %"v186", #4096
          => goto "iw_1.L7";
        @"iw_1.L7" [phi %"iw_1.v15" : "w" = ("L175" => #1, "iw_1.L6" => %"iw_1.v11")]:
          => br %"iw_1.v15" ? "L182" : "L183";
        @"L182":
          %"v190" : "p" = op "alloc"(int 16) %"v186"
          => goto "L184";
        @"L183":
          call %"v196" : "p" = $"malloc"("l" %"v186");
          %"v197" : "l" = "ptoi" %"v196";
          %"v199" : "w" = op "cmp"("eq", "l") %"v197", %"v90"
          => br %"v199" ? "L184" : "L192";
        @"L192":
          => goto "L184";
        @"L184" [phi %"pr.37" : "w" = ("L182" => %"pr.39", "L192" => %"pr.39", "L183" => #1); phi %"pr.28" : "w" = ("L182" => %"pr.30", "L192" => #1, "L183" => %"pr.30"); phi %"pr.20" : "p" = ("L182" => %"v190", "L192" => %"v196", "L183" => %"v196")]:
          %"v204" : "l" = "ptoi" %"pr.20";
          %"v205" : "w" = op "cmp"("ne", "l") %"v204", #0
          => br %"v205" ? "L200" : "L172";
        @"L200":
          call %"v209" : "p" = $"__GI_memset"("p" %"pr.20", "w" #0, "l" %"v186");
          %"v212" : "l" = op "ext"("sw") %"pr.42";
          %"v213" = %"pr.20" +p %"v212";
          %"chk17" : "a" = op "check"(int 0, int 1, "write", int 1) %"v213";
          store "b" [%"chk17" + 0] <- #1
          => goto "L172";
        @"L172" [phi %"pr.35" : "w" = ("L165" => #1, "L200" => %"pr.37", "L184" => %"pr.37", "L171" => %"pr.39"); phi %"pr.26" : "w" = ("L165" => %"pr.30", "L200" => %"pr.28", "L184" => %"pr.28", "L171" => %"pr.30"); phi %"pr.18" : "p" = ("L165" => %"pr.21", "L200" => %"pr.20", "L184" => %"pr.20", "L171" => %"pr.21")]:
          %"v218" : "l" = "ptoi" %"pr.18";
          %"v219" : "w" = op "cmp"("ne", "l") %"v218", #0
          => br %"v219" ? "L214" : "L108";
        @"L214":
          %"v222" : "l" = op "ext"("sw") %"pr.13";
          %"v223" = %"pr.18" +p %"v222";
          %"chk18" : "a" = op "check"(int 0, int 1, "write", int 1) %"v223";
          store "b" [%"chk18" + 0] <- #1
          => goto "L108";
        @"L108" [phi %"pr.40" : "w" = ("L106" => %"pr.13", "L214" => %"pr.42", "L172" => %"pr.42", "L126" => %"pr.42", "L155" => %"pr.42", "L99" => %"pr.42"); phi %"pr.31" : "w" = ("L106" => %"pr.39", "L214" => %"pr.35", "L172" => %"pr.35", "L126" => %"pr.39", "L155" => %"pr.39", "L99" => %"pr.39"); phi %"pr.22" : "w" = ("L106" => %"pr.30", "L214" => %"pr.26", "L172" => %"pr.26", "L126" => %"pr.30", "L155" => %"pr.30", "L99" => %"pr.30"); phi %"pr.14" : "p" = ("L106" => %"pr.21", "L214" => %"pr.18", "L172" => %"pr.18", "L126" => %"pr.21", "L155" => %"pr.21", "L99" => %"pr.21"); phi %"pr.4" : "p" = ("L106" => %"pr.3", "L214" => %"pr.8", "L172" => %"pr.8", "L126" => %"pr.8", "L155" => %"pr.8", "L99" => %"pr.8")]:
          %"v225" = %"pr.3" +p #32;
          %"v227" : "w" = "add" %"pr.13", #1
          => goto poll "L98";
        @"L101":
          %"v232" : "l" = "ptoi" %"pr.21";
          %"v233" : "w" = op "cmp"("ne", "l") %"v232", #0
          => br %"v233" ? "L235" : "L234";
        @"L234":
          %"v237" : "w" = op "cmp"("ne", "w") %"pr.39", #0
          => goto "L235";
        @"L235" [phi %"v238" : "w" = ("L101" => #1, "L234" => %"v237")]:
          => br %"v238" ? "L228" : "L87";
        @"L228":
          => br %"v14" ? "L239" : "L241";
        @"L239":
          => br %"pr.39" ? "L243" : "L244";
        @"L243":
          %"v247" : "p" = "copy" $"stderr";
          %"chk19" : "a" = op "check"(int 0, int 8, "read", int 8) %"v247";
          %"v248" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"v249" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v250" : "p" = "copy" $"glibc_getopt#str.138";
          call %"v251" : "p" = $"__GI___dcgettext"("p" %"v249", "p" %"v250", "w" #5);
          %"chk20" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v254" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk20";
          %"v257" = %"v12" +p #32;
          %"chk21" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v257";
          %"v258" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk21";
          call %"v259" : "w" = $"__fxprintf_nocancel"("p" %"v248", "p" %"v251", "p" %"v254", "p" %"v16", "p" %"v258")
          => goto "L241";
        @"L244":
          %"v260" : "p" = "copy" $"stderr";
          %"chk22" : "a" = op "check"(int 0, int 8, "read", int 8) %"v260";
          %"v261" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk22";
          %"v262" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v263" : "p" = "copy" $"glibc_getopt#str.139";
          call %"v264" : "p" = $"__GI___dcgettext"("p" %"v262", "p" %"v263", "w" #5);
          %"chk23" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v267" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk23";
          %"v270" = %"v12" +p #32;
          %"chk24" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v270";
          %"v271" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          call %"v272" : "w" = $"__fxprintf_nocancel"("p" %"v261", "p" %"v264", "p" %"v267", "p" %"v16", "p" %"v271")
          => goto "L273";
        @"L273" [phi %"pr.10" : "w" = ("L244" => #0, "L275" => %"v300")]:
          %"v279" : "w" = op "cmp"("slt", "w") %"pr.10", %"pr.9"
          => br %"v279" ? "L274" : "L276";
        @"L274":
          %"v285" : "l" = op "ext"("sw") %"pr.10";
          %"v286" = %"pr.21" +p %"v285";
          %"chk25" : "a" = op "check"(int 0, int 1, "read", int 1) %"v286";
          %"v287" : "w" = op "raw_load"("ub", int 0) %"chk25"
          => br %"v287" ? "L280" : "L275";
        @"L280":
          %"v288" : "p" = "copy" $"stderr";
          %"chk26" : "a" = op "check"(int 0, int 8, "read", int 8) %"v288";
          %"v289" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk26";
          %"v290" : "p" = "copy" $"glibc_getopt#str.140";
          %"v295" : "l" = "shl" %"v285", #5;
          %"v296" = %"v6" +p %"v295";
          %"chk27" : "a" = op "check"(int 0, int 8, "read", int 8) %"v296";
          %"v297" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk27";
          call %"v298" : "w" = $"__fxprintf_nocancel"("p" %"v289", "p" %"v290", "p" %"v16", "p" %"v297")
          => goto "L275";
        @"L275":
          %"v300" : "w" = "add" %"pr.10", #1
          => goto poll "L273";
        @"L276":
          %"v301" : "p" = "copy" $"stderr";
          %"chk28" : "a" = op "check"(int 0, int 8, "read", int 8) %"v301";
          %"v302" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk28";
          %"v303" : "p" = "copy" $"glibc_getopt#str.141";
          call %"v304" : "w" = $"__fxprintf_nocancel"("p" %"v302", "p" %"v303")
          => goto "L241";
        @"L241":
          => br %"pr.30" ? "L305" : "L307";
        @"L305":
          call void $"free"("p" %"pr.21")
          => goto "L307";
        @"L307":
          %"v311" = %"v12" +p #32;
          %"chk29" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v311";
          %"v312" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk29";
          %"v315" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk29";
          call %"v316" : "l" = $"__GI_strlen"("p" %"v315");
          %"v317" = %"v312" +p %"v316";
          %"chk31" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"v311";
          store.ptr [%"chk31" + 0] <- %"v317";
          %"chk32" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v12";
          %"v319" : "w" = op "raw_load"("sw", int 0) %"chk32";
          %"v320" : "w" = "add" %"v319", #1;
          %"chk33" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk32", %"v12";
          store "w" [%"chk33" + 0] <- %"v320";
          %"v322" = %"v12" +p #8;
          %"chk34" : "a" = op "half_check"("lower", int 0, int 4, "write", int 1) %"chk0", %"v322";
          store "w" [%"chk34" + 0] <- #0
          => ret #63;
        @"L87" [phi %"pr.12" : "w" = ("L235" => %"pr.42", "L53" => %"pr.11"); phi %"pr.7" : "p" = ("L235" => %"pr.8", "L53" => %"pr.6")]:
          %"v329" : "l" = "ptoi" %"pr.7";
          %"v331" : "w" = op "cmp"("eq", "l") %"v329", %"v90"
          => br %"v331" ? "L325" : "L327";
        @"L325":
          %"v336" : "w" = op "cmp"("eq", "w") %"v10", #0
          => br %"v336" ? "L338" : "L337";
        @"L337":
          %"chk35" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v12";
          %"v341" : "w" = op "raw_load"("sw", int 0) %"chk35";
          %"v342" : "l" = op "ext"("sw") %"v341";
          %"v343" : "l" = "shl" %"v342", #3;
          %"v344" = %"v2" +p %"v343";
          %"chk36" : "a" = op "check"(int 0, int 8, "read", int 8) %"v344";
          %"v345" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk36";
          %"v346" = %"v345" +p #1;
          %"chk37" : "a" = op "check"(int 0, int 1, "read", int 1) %"v346";
          %"v347" : "w" = op "raw_load"("sb", int 0) %"chk37";
          %"v348" : "w" = op "cmp"("eq", "w") %"v347", #45
          => goto "L338";
        @"L338" [phi %"v350" : "w" = ("L325" => #1, "L337" => %"v348")]:
          => br %"v350" ? "L352" : "L351";
        @"L351":
          %"v355" = %"v12" +p #32;
          %"chk38" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v355";
          %"v356" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk38";
          %"chk39" : "a" = op "check"(int 0, int 1, "read", int 1) %"v356";
          %"v357" : "w" = op "raw_load"("sb", int 0) %"chk39";
          call %"v358" : "p" = $"__GI_strchr"("p" %"v4", "w" %"v357");
          %"v359" : "l" = "ptoi" %"v358";
          %"v361" : "w" = op "cmp"("eq", "l") %"v359", %"v90"
          => goto "L352";
        @"L352" [phi %"v363" : "w" = ("L338" => #1, "L351" => %"v361")]:
          => br %"v363" ? "L332" : "L334";
        @"L332":
          => br %"v14" ? "L364" : "L366";
        @"L364":
          %"v368" : "p" = "copy" $"stderr";
          %"chk40" : "a" = op "check"(int 0, int 8, "read", int 8) %"v368";
          %"v369" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"v370" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v371" : "p" = "copy" $"glibc_getopt#str.142";
          call %"v372" : "p" = $"__GI___dcgettext"("p" %"v370", "p" %"v371", "w" #5);
          %"chk41" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v375" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk41";
          %"v378" = %"v12" +p #32;
          %"chk42" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v378";
          %"v379" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk42";
          call %"v380" : "w" = $"__fxprintf_nocancel"("p" %"v369", "p" %"v372", "p" %"v375", "p" %"v16", "p" %"v379")
          => goto "L366";
        @"L366":
          %"v382" = %"v12" +p #32;
          %"chk43" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"v382";
          store.ptr [%"chk43" + 0] <- #0;
          %"chk44" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v12";
          %"v384" : "w" = op "raw_load"("sw", int 0) %"chk44";
          %"v385" : "w" = "add" %"v384", #1;
          %"chk45" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk44", %"v12";
          store "w" [%"chk45" + 0] <- %"v385";
          %"v387" = %"v12" +p #8;
          %"chk46" : "a" = op "half_check"("lower", int 0, int 4, "write", int 1) %"chk0", %"v387";
          store "w" [%"chk46" + 0] <- #0
          => ret #63;
        @"L334":
          => ret #4294967295;
        @"L327":
          %"chk47" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v12";
          %"v392" : "w" = op "raw_load"("sw", int 0) %"chk47";
          %"v393" : "w" = "add" %"v392", #1;
          %"chk48" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk47", %"v12";
          store "w" [%"chk48" + 0] <- %"v393";
          %"v395" = %"v12" +p #32;
          %"chk49" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"v395";
          store.ptr [%"chk49" + 0] <- #0;
          %"chk50" : "a" = op "renew"(int 0, int 1, "read", int 1) %"chk1", %"pr.1";
          %"v400" : "w" = op "raw_load"("sb", int 0) %"chk50"
          => br %"v400" ? "L396" : "L397";
        @"L396":
          %"v405" = %"pr.7" +p #8;
          %"chk51" : "a" = op "check"(int 0, int 4, "read", int 1) %"v405";
          %"v406" : "w" = op "raw_load"("sw", int 0) %"chk51"
          => br %"v406" ? "L401" : "L402";
        @"L401":
          %"v408" = %"v12" +p #16;
          %"v410" = %"pr.1" +p #1;
          %"chk52" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v408";
          store.ptr [%"chk52" + 0] <- %"v410"
          => goto "L398";
        @"L402":
          => br %"v14" ? "L411" : "L413";
        @"L411":
          %"v415" : "p" = "copy" $"stderr";
          %"chk53" : "a" = op "check"(int 0, int 8, "read", int 8) %"v415";
          %"v416" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk53";
          %"v417" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v418" : "p" = "copy" $"glibc_getopt#str.143";
          call %"v419" : "p" = $"__GI___dcgettext"("p" %"v417", "p" %"v418", "w" #5);
          %"chk54" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v422" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk54";
          %"chk55" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk51", %"pr.7";
          %"v425" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk55";
          call %"v426" : "w" = $"__fxprintf_nocancel"("p" %"v416", "p" %"v419", "p" %"v422", "p" %"v16", "p" %"v425")
          => goto "L413";
        @"L413":
          %"v428" = %"v12" +p #8;
          %"v430" = %"pr.7" +p #24;
          %"chk56" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk51", %"v430";
          %"v431" : "w" = op "raw_load"("sw", int 0) %"chk56";
          %"chk57" : "a" = op "half_check"("lower", int 0, int 4, "write", int 1) %"chk0", %"v428";
          store "w" [%"chk57" + 0] <- %"v431"
          => ret #63;
        @"L397":
          %"v436" = %"pr.7" +p #8;
          %"chk58" : "a" = op "check"(int 0, int 4, "read", int 1) %"v436";
          %"v437" : "w" = op "raw_load"("sw", int 0) %"chk58";
          %"v438" : "w" = op "cmp"("eq", "w") %"v437", #1
          => br %"v438" ? "L432" : "L398";
        @"L432":
          %"chk59" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk47", %"v12";
          %"v443" : "w" = op "raw_load"("sw", int 0) %"chk59";
          %"v445" : "w" = op "cmp"("slt", "w") %"v443", %"v0"
          => br %"v445" ? "L439" : "L440";
        @"L439":
          %"v447" = %"v12" +p #16;
          %"v450" : "w" = op "raw_load"("sw", int 0) %"chk59";
          %"v451" : "w" = "add" %"v450", #1;
          %"chk61" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk47", %"v12";
          store "w" [%"chk61" + 0] <- %"v451";
          %"v452" : "l" = op "ext"("sw") %"v450";
          %"v453" : "l" = "shl" %"v452", #3;
          %"v454" = %"v2" +p %"v453";
          %"chk62" : "a" = op "check"(int 0, int 8, "read", int 8) %"v454";
          %"v455" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk62";
          %"chk63" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk0", %"v447";
          store.ptr [%"chk63" + 0] <- %"v455"
          => goto "L398";
        @"L440":
          => br %"v14" ? "L456" : "L458";
        @"L456":
          %"v460" : "p" = "copy" $"stderr";
          %"chk64" : "a" = op "check"(int 0, int 8, "read", int 8) %"v460";
          %"v461" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk64";
          %"v462" : "p" = "copy" $"__GI__libc_intl_domainname";
          %"v463" : "p" = "copy" $"glibc_getopt#str.144";
          call %"v464" : "p" = $"__GI___dcgettext"("p" %"v462", "p" %"v463", "w" #5);
          %"chk65" : "a" = op "check"(int 0, int 8, "read", int 8) %"v2";
          %"v467" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk65";
          %"chk66" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk58", %"pr.7";
          %"v470" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk66";
          call %"v471" : "w" = $"__fxprintf_nocancel"("p" %"v461", "p" %"v464", "p" %"v467", "p" %"v16", "p" %"v470")
          => goto "L458";
        @"L458":
          %"v473" = %"v12" +p #8;
          %"v475" = %"pr.7" +p #24;
          %"chk67" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk58", %"v475";
          %"v476" : "w" = op "raw_load"("sw", int 0) %"chk67";
          %"chk68" : "a" = op "half_check"("lower", int 0, int 4, "write", int 1) %"chk0", %"v473";
          store "w" [%"chk68" + 0] <- %"v476";
          %"chk69" : "a" = op "check"(int 0, int 1, "read", int 1) %"v4";
          %"v482" : "w" = op "raw_load"("sb", int 0) %"chk69";
          %"v483" : "w" = op "cmp"("eq", "w") %"v482", #58
          => br %"v483" ? "L479" : "L478";
        @"L478":
          => goto "L479";
        @"L479" [phi %"v484" : "w" = ("L478" => #63, "L458" => #58)]:
          => ret %"v484";
        @"L398":
          %"v489" : "l" = "ptoi" %"v8";
          %"v491" : "w" = op "cmp"("ne", "l") %"v489", %"v90"
          => br %"v491" ? "L485" : "L487";
        @"L485":
          %"chk70" : "a" = op "check"(int 0, int 4, "write", int 1) %"v8";
          store "w" [%"chk70" + 0] <- %"pr.12"
          => goto "L487";
        @"L487":
          %"v498" = %"pr.7" +p #16;
          %"chk71" : "a" = op "check"(int 0, int 8, "read", int 8) %"v498";
          %"v499" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk71";
          %"v500" : "l" = "ptoi" %"v499";
          %"v501" : "w" = op "cmp"("ne", "l") %"v500", #0
          => br %"v501" ? "L494" : "L496";
        @"L494":
          %"v503" = %"pr.7" +p #16;
          %"v504" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk71";
          %"v506" = %"pr.7" +p #24;
          %"chk73" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk71", %"v506";
          %"v507" : "w" = op "raw_load"("sw", int 0) %"chk73";
          %"chk74" : "a" = op "check"(int 0, int 4, "write", int 1) %"v504";
          store "w" [%"chk74" + 0] <- %"v507"
          => ret #0;
        @"L496":
          %"v510" = %"pr.7" +p #24;
          %"chk75" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk71", %"v510";
          %"v511" : "w" = op "raw_load"("sw", int 0) %"chk75"
          => ret %"v511"
      } }
  ].
