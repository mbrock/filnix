(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_07 : list term :=
  [
        cap_blk{ @"start":
          %"v24" : "p" = op "alloc"(int 16) #1040;
          %"v31" : "p" = op "alloc"(int 16) #1040;
          %"v34" : "p" = op "alloc"(int 8) #8;
          %"v107" : "p" = op "alloc"(int 4) #1;
          %"v1248" : "p" = op "alloc"(int 8) #24;
          %"v1887" : "p" = op "alloc"(int 4) #16;
          %"v1888" : "p" = op "alloc"(int 4) #8;
          %"v1936" : "p" = op "alloc"(int 8) #8;
          call void $"glibc_vfprintf_internal#scratch_buffer_init"("p" %"v24");
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v24";
          %"v26" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v28" = %"v24" +p #8;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "read", int 1) %"chk0", %"v28";
          %"v29" : "l" = op "raw_load"("l", int 0) %"chk1";
          %"v30" : "l" = "udiv" %"v29", #72;
          call void $"glibc_vfprintf_internal#scratch_buffer_init"("p" %"v31");
          %"chk2" : "a" = op "check"(int 0, int 8, "write", int 1) %"v34";
          store "l" [%"chk2" + 0] <- #0;
          (op "flight"(%"v42", "copy", [#18446744073709551615], "none"));
          %"v43" : "l" = "ptoi" %"v18";
          %"v44" : "l" = "ptoi" %"v42";
          %"v45" : "w" = op "cmp"("eq", "l") %"v43", %"v44"
          => br %"v45" ? "L36" : "L38" };
        cap_blk{ @"L36":
          %"v46" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk3" : "a" = op "check"(int 0, int 8, "read", int 8) %"v46";
          %"v47" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk3";
          %"v48" = %"v47" +p #8;
          %"chk4" : "a" = op "check"(int 0, int 8, "read", int 8) %"v48";
          %"v49" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"v50" = %"v49" +p #56;
          %"v54" = %"v50" +p #8;
          %"chk5" : "a" = op "check"(int 0, int 8, "read", int 8) %"v54";
          %"v55" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"v56" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk6" : "a" = op "check"(int 0, int 8, "read", int 8) %"v56";
          %"v57" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"v58" = %"v57" +p #8;
          %"chk7" : "a" = op "check"(int 0, int 8, "read", int 8) %"v58";
          %"v59" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"v60" = %"v59" +p #56;
          %"v64" = %"v60" +p #16;
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"v64";
          %"v65" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"chk9" : "a" = op "check"(int 0, int 1, "read", int 1) %"v65";
          %"v70" : "w" = op "raw_load"("sb", int 0) %"chk9";
          %"v71" : "w" = op "cmp"("eq", "w") %"v70", #0
          => br %"v71" ? "L73" : "L72" };
        cap_blk{ @"L72":
          %"v75" : "w" = op "raw_load"("sb", int 0) %"chk9";
          %"v76" : "w" = op "cmp"("eq", "w") %"v75", #127
          => goto "L73" };
        cap_blk{ @"L73" [phi %"v78" : "w" = ("L36" => #1, "L72" => %"v76")]:
          => br %"v78" ? "L38" : "L67" };
        cap_blk{ @"L67":
          => goto "L38" };
        cap_blk{ @"L38" [phi %"pr.6" : "p" = ("L67" => %"v55", "L73" => %"v55", "start" => %"v20")]:
          => goto "L81" };
        cap_blk{ @"L81" [phi %"pr.15" : "p" = ("L38" => %"v12", "L83" => %"v129"); phi %"pr.12" : "l" = ("L38" => #0, "L83" => %"v116"); phi %"pr.11" : "l" = ("L38" => #0, "L83" => %"v125"); phi %"pr.9" : "l" = ("L38" => %"v30", "L83" => %"pr.10"); phi %"pr.7" : "p" = ("L38" => %"v26", "L83" => %"pr.8")]:
          %"chk11" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.15";
          %"v86" : "w" = op "raw_load"("ub", int 0) %"chk11";
          %"v87" : "w" = op "cmp"("ne", "w") %"v86", #0
          => br %"v87" ? "L82" : "L84" };
        cap_blk{ @"L82":
          %"v93" : "w" = op "cmp"("eq", "l") %"pr.11", %"pr.9"
          => br %"v93" ? "iw_1.start" : "L90" };
        cap_blk{ @"iw_1.start":
          call %"iw_1.v3" : "w" = $"__GI___libc_scratch_buffer_grow_preserve"("p" %"v24");
          %"iw_1.v4" : "w" = op "ext"("ub") %"iw_1.v3";
          %"iw_1.v5" : "l" = op "ext"("uw") %"iw_1.v4";
          %"v99" : "w" = op "cmp"("eq", "l") %"iw_1.v5", #0
          => br %"v99" ? "L94" : "L96" };
        cap_blk{ @"L94":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L96":
          %"chk12" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v24";
          %"v103" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk12";
          %"v104" = %"v24" +p #8;
          %"chk13" : "a" = op "renew"(int 0, int 8, "read", int 1) %"chk1", %"v104";
          %"v105" : "l" = op "raw_load"("l", int 0) %"chk13";
          %"v106" : "l" = "udiv" %"v105", #72
          => goto "L90" };
        cap_blk{ @"L90" [phi %"pr.10" : "l" = ("L96" => %"v106", "L82" => %"pr.9"); phi %"pr.8" : "p" = ("L96" => %"v103", "L82" => %"pr.7")]:
          %"v113" : "l" = "mul" %"pr.11", #72;
          %"v114" = %"pr.8" +p %"v113";
          call %"v115" : "l" = $"__parse_one_specmb"("p" %"pr.15", "l" %"pr.12", "p" %"v114", "p" %"v34", "p" %"v107");
          %"v116" : "l" = "add" %"pr.12", %"v115";
          %"chk14" : "a" = op "check"(int 0, int 1, "read", int 1) %"v107";
          %"v120" : "w" = op "raw_load"("ub", int 0) %"chk14"
          => br %"v120" ? "L117" : "L83" };
        cap_blk{ @"L117":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L83":
          %"v125" : "l" = "add" %"pr.11", #1;
          %"v128" = %"v114" +p #32;
          %"chk15" : "a" = op "check"(int 0, int 8, "read", int 8) %"v128";
          %"v129" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk15"
          => goto poll "L81" };
        cap_blk{ @"L84":
          %"chk16" : "a" = op "renew"(int 0, int 8, "read", int 1) %"chk2", %"v34";
          %"v134" : "l" = op "raw_load"("l", int 0) %"chk16";
          %"v135" : "w" = op "cmp"("ugt", "l") %"pr.12", %"v134"
          => br %"v135" ? "L132" : "L131" };
        cap_blk{ @"L131":
          %"v137" : "l" = op "raw_load"("l", int 0) %"chk16"
          => goto "L132" };
        cap_blk{ @"L132" [phi %"v138" : "l" = ("L131" => %"v137", "L84" => %"pr.12")]:
          call %"iw_2.v9" : "w" = $"__GI___libc_scratch_buffer_set_array_size"("p" %"v31", "l" %"v138", "l" #24);
          %"iw_2.v10" : "w" = op "ext"("ub") %"iw_2.v9";
          %"iw_2.v11" : "l" = op "ext"("uw") %"iw_2.v10";
          %"v154" : "w" = op "cmp"("eq", "l") %"iw_2.v11", #0
          => br %"v154" ? "L147" : "L149" };
        cap_blk{ @"L147":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L149":
          %"chk18" : "a" = op "check"(int 0, int 8, "read", int 8) %"v31";
          %"v157" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk18";
          %"v160" : "l" = "shl" %"v138", #4;
          %"v161" = %"v157" +p %"v160";
          %"v164" : "l" = "shl" %"v138", #2;
          %"v165" = %"v161" +p %"v164";
          %"v169" = %"v165" +p %"v164";
          %"v175" : "w" = "and" %"v22", #2;
          %"v176" : "w" = op "cmp"("ne", "w") %"v175", #0
          => br %"v176" ? "L173" : "L172" };
        cap_blk{ @"L172":
          => goto "L173" };
        cap_blk{ @"L173" [phi %"v177" : "w" = ("L172" => #0, "L149" => #(-1))]:
          call %"v180" : "p" = $"__GI_memset"("p" %"v165", "w" %"v177", "l" %"v164")
          => goto "L181" };
        cap_blk{ @"L181" [phi %"pr.13" : "l" = ("L173" => #0, "L183" => %"v322")]:
          %"v187" : "w" = op "cmp"("ult", "l") %"pr.13", %"pr.11"
          => br %"v187" ? "L182" : "L323" };
        cap_blk{ @"L182":
          %"v193" : "l" = "mul" %"pr.13", #72;
          %"v194" = %"pr.7" +p %"v193";
          %"v195" = %"v194" +p #44;
          %"chk19" : "a" = op "check"(int 0, int 4, "read", int 1) %"v195";
          %"v196" : "w" = op "raw_load"("sw", int 0) %"chk19";
          %"v198" : "w" = op "cmp"("ne", "w") %"v196", #4294967295
          => br %"v198" ? "L188" : "L190" };
        cap_blk{ @"L188":
          %"v204" = %"v194" +p #44;
          %"v205" : "w" = op "raw_load"("sw", int 0) %"chk19";
          %"v206" : "l" = op "ext"("sw") %"v205";
          %"v207" : "l" = "shl" %"v206", #2;
          %"v208" = %"v165" +p %"v207";
          %"chk21" : "a" = op "check"(int 0, int 4, "write", int 1) %"v208";
          store "w" [%"chk21" + 0] <- #0
          => goto "L190" };
        cap_blk{ @"L190":
          %"v216" = %"v194" +p #40;
          %"chk22" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk19", %"v216";
          %"v217" : "w" = op "raw_load"("sw", int 0) %"chk22";
          %"v219" : "w" = op "cmp"("ne", "w") %"v217", #4294967295
          => br %"v219" ? "L209" : "L211" };
        cap_blk{ @"L209":
          %"v225" = %"v194" +p #40;
          %"v226" : "w" = op "raw_load"("sw", int 0) %"chk22";
          %"v227" : "l" = op "ext"("sw") %"v226";
          %"v228" : "l" = "shl" %"v227", #2;
          %"v229" = %"v165" +p %"v228";
          %"chk24" : "a" = op "check"(int 0, int 4, "write", int 1) %"v229";
          store "w" [%"chk24" + 0] <- #0
          => goto "L211" };
        cap_blk{ @"L211":
          %"v234" = %"v194" +p #56;
          %"chk25" : "a" = op "half_check"("upper", int 0, int 8, "read", int 1) %"chk19", %"v234";
          %"v235" : "l" = op "raw_load"("l", int 0) %"chk25";
          %"v317" : "w" = op "cmp"("eq", "l") %"v235", #0
          => br %"v317" ? "L183" : "L318" };
        cap_blk{ @"L239":
          %"v245" = %"v194" +p #48;
          %"chk26" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk19", %"v245";
          %"v246" : "w" = op "raw_load"("sw", int 0) %"chk26";
          %"v247" : "l" = op "ext"("sw") %"v246";
          %"v248" : "l" = "shl" %"v247", #2;
          %"v249" = %"v165" +p %"v248";
          %"v254" = %"v194" +p #52;
          %"chk27" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk19", %"v254";
          %"v255" : "w" = op "raw_load"("sw", int 0) %"chk27";
          %"chk28" : "a" = op "check"(int 0, int 4, "write", int 1) %"v249";
          store "w" [%"chk28" + 0] <- %"v255";
          %"v262" : "w" = op "raw_load"("sw", int 0) %"chk26";
          %"v263" : "l" = op "ext"("sw") %"v262";
          %"v264" : "l" = "shl" %"v263", #2;
          %"v265" = %"v161" +p %"v264";
          %"v270" = %"v194" +p #64;
          %"chk30" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk19", %"v270";
          %"v271" : "w" = op "raw_load"("sw", int 0) %"chk30";
          %"chk31" : "a" = op "check"(int 0, int 4, "write", int 1) %"v265";
          store "w" [%"chk31" + 0] <- %"v271"
          => goto "L183" };
        cap_blk{ @"L272":
          %"v273" : "p" = "copy" $"__printf_arginfo_table";
          %"chk32" : "a" = op "check"(int 0, int 8, "read", int 8) %"v273";
          %"v274" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk32";
          %"v279" = %"v194" +p #8;
          %"chk33" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk19", %"v279";
          %"v280" : "w" = op "raw_load"("sw", int 0) %"chk33";
          %"v281" : "l" = op "ext"("sw") %"v280";
          %"v282" : "l" = "shl" %"v281", #3;
          %"v283" = %"v274" +p %"v282";
          %"chk34" : "a" = op "check"(int 0, int 8, "read", int 8) %"v283";
          %"v284" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk34";
          %"v293" = %"v194" +p #56;
          %"chk35" : "a" = op "renew"(int 0, int 8, "read", int 1) %"chk25", %"v293";
          %"v294" : "l" = op "raw_load"("l", int 0) %"chk35";
          %"v300" = %"v194" +p #48;
          %"v301" : "w" = op "raw_load"("sw", int (-8)) %"chk35";
          %"v302" : "l" = op "ext"("sw") %"v301";
          %"v303" : "l" = "shl" %"v302", #2;
          %"v304" = %"v165" +p %"v303";
          %"v311" : "w" = op "raw_load"("sw", int (-8)) %"chk35";
          %"v312" : "l" = op "ext"("sw") %"v311";
          %"v313" : "l" = "shl" %"v312", #2;
          %"v314" = %"v161" +p %"v313";
          %"chk38" : "f" = "check_function" %"v284";
          rawcall %"v315" : "w" = %"chk38"("p" %"v194", "l" %"v294", "p" %"v304", "p" %"v314")
          => goto "L183" };
        cap_blk{ @"L318":
          %"v319" : "w" = op "cmp"("eq", "l") %"v235", #1
          => br %"v319" ? poll "L239" : poll "L272" };
        cap_blk{ @"L183":
          %"v322" : "l" = "add" %"pr.13", #1
          => goto poll "L181" };
        cap_blk{ @"L323" [phi %"pr.31" : "p" = ("L336" => %"pr.32", "L181" => %"v169"); phi %"pr.26" : "p" = ("L336" => %"pr.27", "L181" => %"v165"); phi %"pr.21" : "p" = ("L336" => %"pr.22", "L181" => %"v161"); phi %"pr.16" : "p" = ("L336" => %"pr.17", "L181" => %"v157"); phi %"pr.14" : "l" = ("L336" => %"v586", "L181" => #0)]:
          %"v329" : "w" = op "cmp"("ult", "l") %"pr.14", %"v138"
          => br %"v329" ? "L324" : "L587" };
        cap_blk{ @"L324":
          %"v332" : "l" = "shl" %"pr.14", #2;
          %"v333" = %"pr.26" +p %"v332";
          %"chk39" : "a" = op "check"(int 0, int 4, "read", int 1) %"v333";
          %"v334" : "w" = op "raw_load"("sw", int 0) %"chk39";
          %"v550" : "w" = op "cmp"("slt", "w") %"v334", #5
          => br %"v550" ? "L551" : "L552" };
        cap_blk{ @"L337":
          %"v340" : "l" = "shl" %"pr.14", #4;
          %"v341" = %"pr.16" +p %"v340";
          %"v343" : "w" = "va_arg" %"v8";
          %"chk40" : "a" = op "check"(int 0, int 4, "write", int 1) %"v341";
          store "w" [%"chk40" + 0] <- %"v343"
          => goto "L336" };
        cap_blk{ @"L346":
          %"v349" : "l" = "shl" %"pr.14", #4;
          %"v350" = %"pr.16" +p %"v349";
          %"v352" : "w" = "va_arg" %"v8";
          %"chk41" : "a" = op "check"(int 0, int 4, "write", int 1) %"v350";
          store "w" [%"chk41" + 0] <- %"v352"
          => goto "L336" };
        cap_blk{ @"L354":
          %"v357" : "l" = "shl" %"pr.14", #4;
          %"v358" = %"pr.16" +p %"v357";
          %"v360" : "l" = "va_arg" %"v8";
          %"chk42" : "a" = op "check"(int 0, int 8, "write", int 1) %"v358";
          store "l" [%"chk42" + 0] <- %"v360"
          => goto "L336" };
        cap_blk{ @"L362":
          %"v365" : "l" = "shl" %"pr.14", #4;
          %"v366" = %"pr.16" +p %"v365";
          %"v368" : "d" = "va_arg" %"v8";
          %"chk43" : "a" = op "check"(int 0, int 8, "write", int 1) %"v366";
          store "d" [%"chk43" + 0] <- %"v368"
          => goto "L336" };
        cap_blk{ @"L369":
          %"v374" : "w" = "and" %"v22", #1
          => br %"v374" ? "L370" : "L371" };
        cap_blk{ @"L370":
          %"v380" : "l" = "shl" %"pr.14", #4;
          %"v381" = %"pr.16" +p %"v380";
          %"v383" : "d" = "va_arg" %"v8";
          %"chk44" : "a" = op "check"(int 0, int 8, "write", int 1) %"v381";
          store "d" [%"chk44" + 0] <- %"v383";
          %"chk45" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk39", %"v333";
          %"v388" : "w" = op "raw_load"("sw", int 0) %"chk45";
          %"v391" : "w" = "and" %"v388", #4294967039;
          %"chk46" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk39", %"v333";
          store "w" [%"chk46" + 0] <- %"v391"
          => goto "L336" };
        cap_blk{ @"L371":
          %"v394" : "l" = "shl" %"pr.14", #4;
          %"v395" = %"pr.16" +p %"v394";
          %"v397" : "x" = "va_arg" %"v8";
          %"chk47" : "a" = op "check"(int 0, int 10, "write", int 8) %"v395";
          store "x" [%"chk47" + 0] <- %"v397"
          => goto "L336" };
        cap_blk{ @"L400":
          %"v403" : "l" = "shl" %"pr.14", #4;
          %"v404" = %"pr.16" +p %"v403";
          %"v406" : "p" = "va_arg" %"v8";
          %"chk48" : "a" = op "check"(int 0, int 8, "write", int 8) %"v404";
          store.ptr [%"chk48" + 0] <- %"v406"
          => goto "L336" };
        cap_blk{ @"L407":
          %"chk49" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk39", %"v333";
          %"v415" : "w" = op "raw_load"("sw", int 0) %"chk49";
          %"v417" : "w" = "and" %"v415", #2048;
          %"v418" : "w" = op "cmp"("ne", "w") %"v417", #0
          => br %"v418" ? "L408" : "L409" };
        cap_blk{ @"L408":
          %"v421" : "l" = "shl" %"pr.14", #4;
          %"v422" = %"pr.16" +p %"v421";
          %"v424" : "p" = "va_arg" %"v8";
          %"chk50" : "a" = op "check"(int 0, int 8, "write", int 8) %"v422";
          store.ptr [%"chk50" + 0] <- %"v424"
          => goto "L336" };
        cap_blk{ @"L409":
          %"v428" : "p" = "copy" $"__printf_va_arg_table";
          %"chk51" : "a" = op "check"(int 0, int 8, "read", int 8) %"v428";
          %"v429" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk51";
          %"v430" : "l" = "ptoi" %"v429";
          %"v431" : "l" = "ptoi" #0;
          %"v432" : "w" = op "cmp"("ne", "l") %"v430", %"v431"
          => br %"v432" ? "L435" : "L436" };
        cap_blk{ @"L435":
          %"v437" : "p" = "copy" $"__printf_va_arg_table";
          %"chk52" : "a" = op "check"(int 0, int 8, "read", int 8) %"v437";
          %"v438" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk52";
          %"chk53" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk39", %"v333";
          %"v443" : "w" = op "raw_load"("sw", int 0) %"chk53";
          %"v444" : "w" = "sub" %"v443", #8;
          %"v445" : "l" = op "ext"("sw") %"v444";
          %"v446" : "l" = "shl" %"v445", #3;
          %"v447" = %"v438" +p %"v446";
          %"chk54" : "a" = op "check"(int 0, int 8, "read", int 8) %"v447";
          %"v448" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk54";
          %"v449" : "l" = "ptoi" %"v448";
          %"v451" : "w" = op "cmp"("ne", "l") %"v449", %"v431"
          => goto "L436" };
        cap_blk{ @"L436" [phi %"v453" : "w" = ("L409" => #0, "L435" => %"v451")]:
          => br %"v453" ? "L454" : "L426" };
        cap_blk{ @"L454" [phi %"pr.35" : "p" = ("L482" => %"v502", "L436" => %"pr.31"); phi %"pr.30" : "p" = ("L482" => %"v496", "L436" => %"pr.26"); phi %"pr.25" : "p" = ("L482" => %"v492", "L436" => %"pr.21"); phi %"pr.20" : "p" = ("L482" => %"v488", "L436" => %"pr.16")]:
          %"v461" = %"pr.25" +p %"v332";
          %"chk55" : "a" = op "check"(int 0, int 4, "read", int 1) %"v461";
          %"v462" : "w" = op "raw_load"("sw", int 0) %"chk55";
          %"v463" : "l" = op "ext"("sw") %"v462";
          %"v464" = %"pr.35" +p %"v463";
          %"chk56" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk18", %"v31";
          %"v465" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk56";
          %"v466" = %"v31" +p #8;
          %"chk57" : "a" = op "half_check"("upper", int 0, int 8, "read", int 1) %"chk18", %"v466";
          %"v467" : "l" = op "raw_load"("l", int 0) %"chk57";
          %"v468" = %"v465" +p %"v467";
          %"v469" : "l" = "ptoi" %"v464";
          %"v470" : "l" = "ptoi" %"v468";
          %"v471" : "w" = op "cmp"("ugt", "l") %"v469", %"v470"
          => br %"v471" ? "L455" : "L456" };
        cap_blk{ @"L455":
          %"v476" = %"pr.30" +p %"v164";
          %"v477" : "l" = "ptoi" %"pr.35";
          %"v478" : "l" = "ptoi" %"v476";
          %"v479" : "l" = "sub" %"v477", %"v478";
          call %"iw_3.v3" : "w" = $"__GI___libc_scratch_buffer_grow_preserve"("p" %"v31");
          %"iw_3.v4" : "w" = op "ext"("ub") %"iw_3.v3";
          %"iw_3.v5" : "l" = op "ext"("uw") %"iw_3.v4";
          %"v485" : "w" = op "cmp"("eq", "l") %"iw_3.v5", #0
          => br %"v485" ? "L480" : "L482" };
        cap_blk{ @"L480":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L482":
          %"chk58" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk18", %"v31";
          %"v488" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk58";
          %"v492" = %"v488" +p %"v160";
          %"v496" = %"v492" +p %"v164";
          %"v500" = %"v496" +p %"v164";
          %"v502" = %"v500" +p %"v479"
          => goto poll "L454" };
        cap_blk{ @"L456":
          %"v505" : "l" = "shl" %"pr.14", #4;
          %"v506" = %"pr.20" +p %"v505";
          %"chk59" : "a" = op "check"(int 0, int 8, "write", int 8) %"v506";
          store.ptr [%"chk59" + 0] <- %"pr.35";
          %"chk60" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk55", %"v461";
          %"v513" : "w" = op "raw_load"("sw", int 0) %"chk60";
          %"v514" : "l" = op "ext"("sw") %"v513";
          %"v515" = %"pr.35" +p %"v514";
          %"v516" : "p" = "copy" $"__printf_va_arg_table";
          %"chk61" : "a" = op "check"(int 0, int 8, "read", int 8) %"v516";
          %"v517" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk61";
          %"v521" = %"pr.30" +p %"v332";
          %"chk62" : "a" = op "check"(int 0, int 4, "read", int 1) %"v521";
          %"v522" : "w" = op "raw_load"("sw", int 0) %"chk62";
          %"v523" : "w" = "sub" %"v522", #8;
          %"v524" : "l" = op "ext"("sw") %"v523";
          %"v525" : "l" = "shl" %"v524", #3;
          %"v526" = %"v517" +p %"v525";
          %"chk63" : "a" = op "check"(int 0, int 8, "read", int 8) %"v526";
          %"v527" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk63";
          %"chk64" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk59", %"v506";
          %"v532" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk64";
          %"chk65" : "f" = "check_function" %"v527";
          rawcall void %"chk65"("p" %"v532", "p" %"v8")
          => goto "L336" };
        cap_blk{ @"L426":
          %"v536" : "l" = "shl" %"pr.14", #4;
          %"v537" = %"pr.16" +p %"v536";
          call %"v538" : "p" = $"__GI_memset"("p" %"v537", "w" #0, "l" #16)
          => goto "L336" };
        cap_blk{ @"L539":
          => br %"v176" ? "L542" : "L541" };
        cap_blk{ @"L541":
          %"v546" : "p" = "copy" $"glibc_vfprintf_internal#str.290";
          %"v547" : "p" = "copy" $"glibc_vfprintf_internal#str.291";
          %"v548" : "p" = "copy" $"glibc_vfprintf_internal#str.292";
          call void $"__libc_assert_fail"("p" %"v546", "p" %"v547", "w" #1270, "p" %"v548")
          => goto "L542" };
        cap_blk{ @"L542":
          %"v549" : "p" = "copy" $"glibc_vfprintf_internal#str.293";
          call void $"__GI___libc_fatal"("p" %"v549")
          => goto "L336" };
        cap_blk{ @"L551":
          %"v553" : "w" = op "cmp"("slt", "w") %"v334", #2
          => br %"v553" ? "L554" : "L555" };
        cap_blk{ @"L554":
          %"v556" : "w" = op "cmp"("eq", "w") %"v334", #(-1)
          => br %"v556" ? poll "L539" : "L557" };
        cap_blk{ @"L557":
          %"v558" : "w" = op "cmp"("eq", "w") %"v334", #0
          => br %"v558" ? poll "L346" : "L559" };
        cap_blk{ @"L559":
          %"v560" : "w" = op "cmp"("eq", "w") %"v334", #1
          => br %"v560" ? poll "L346" : poll "L407" };
        cap_blk{ @"L555":
          %"v562" : "w" = op "cmp"("eq", "w") %"v334", #2
          => br %"v562" ? poll "L337" : "L563" };
        cap_blk{ @"L563":
          %"v564" : "w" = op "cmp"("eq", "w") %"v334", #3
          => br %"v564" ? poll "L400" : "L565" };
        cap_blk{ @"L565":
          %"v566" : "w" = op "cmp"("eq", "w") %"v334", #4
          => br %"v566" ? poll "L400" : poll "L407" };
        cap_blk{ @"L552":
          %"v568" : "w" = op "cmp"("slt", "w") %"v334", #256
          => br %"v568" ? "L569" : "L570" };
        cap_blk{ @"L569":
          %"v571" : "w" = op "cmp"("eq", "w") %"v334", #5
          => br %"v571" ? poll "L400" : "L572" };
        cap_blk{ @"L572":
          %"v573" : "w" = op "cmp"("eq", "w") %"v334", #6
          => br %"v573" ? poll "L362" : "L574" };
        cap_blk{ @"L574":
          %"v575" : "w" = op "cmp"("eq", "w") %"v334", #7
          => br %"v575" ? poll "L362" : poll "L407" };
        cap_blk{ @"L570":
          %"v577" : "w" = op "cmp"("eq", "w") %"v334", #256
          => br %"v577" ? poll "L354" : "L578" };
        cap_blk{ @"L578":
          %"v579" : "w" = op "cmp"("eq", "w") %"v334", #263
          => br %"v579" ? poll "L369" : "L580" };
        cap_blk{ @"L580":
          %"v581" : "w" = op "cmp"("eq", "w") %"v334", #512
          => br %"v581" ? poll "L354" : "L582" };
        cap_blk{ @"L582":
          %"v583" : "w" = op "cmp"("eq", "w") %"v334", #1024
          => br %"v583" ? poll "L346" : poll "L407" };
        cap_blk{ @"L336" [phi %"pr.32" : "p" = ("L337" => %"pr.31", "L346" => %"pr.31", "L354" => %"pr.31", "L362" => %"pr.31", "L400" => %"pr.31", "L542" => %"pr.31", "L370" => %"pr.31", "L371" => %"pr.31", "L408" => %"pr.31", "L456" => %"v515", "L426" => %"pr.31"); phi %"pr.27" : "p" = ("L337" => %"pr.26", "L346" => %"pr.26", "L354" => %"pr.26", "L362" => %"pr.26", "L400" => %"pr.26", "L542" => %"pr.26", "L370" => %"pr.26", "L371" => %"pr.26", "L408" => %"pr.26", "L456" => %"pr.30", "L426" => %"pr.26"); phi %"pr.22" : "p" = ("L337" => %"pr.21", "L346" => %"pr.21", "L354" => %"pr.21", "L362" => %"pr.21", "L400" => %"pr.21", "L542" => %"pr.21", "L370" => %"pr.21", "L371" => %"pr.21", "L408" => %"pr.21", "L456" => %"pr.25", "L426" => %"pr.21"); phi %"pr.17" : "p" = ("L337" => %"pr.16", "L346" => %"pr.16", "L354" => %"pr.16", "L362" => %"pr.16", "L400" => %"pr.16", "L542" => %"pr.16", "L370" => %"pr.16", "L371" => %"pr.16", "L408" => %"pr.16", "L456" => %"pr.20", "L426" => %"pr.16")]:
          %"v586" : "l" = "add" %"pr.14", #1
          => goto poll "L323" };
        cap_blk{ @"L587" [phi %"pr.5" : "w" = ("L866" => %"v2032", "L323" => %"v10"); phi %"pr.3" : "w" = ("L866" => %"pr.4", "L323" => %"v4")]:
          %"v592" : "l" = op "ext"("sw") %"pr.5";
          %"v594" : "w" = op "cmp"("ult", "l") %"v592", %"pr.11"
          => br %"v594" ? "L595" : "L596" };
        cap_blk{ @"L595":
          call %"v598" : "w" = $"glibc_vfprintf_internal#__printf_buffer_has_failed"("p" %"v0");
          %"v599" : "w" = op "ext"("ub") %"v598";
          %"v600" : "w" = op "cmp"("eq", "w") %"v599", #0
          => goto "L596" };
        cap_blk{ @"L596" [phi %"v602" : "w" = ("L587" => #0, "L595" => %"v600")]:
          => br %"v602" ? "L588" : "L101" }
  ].
