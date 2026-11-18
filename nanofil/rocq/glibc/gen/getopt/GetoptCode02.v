(** This file contains part of glibc's checked option-parser module.
    getopt/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition getopt_blocks_02 : list term :=
  [
        cap_blk{ @"start":
          %"v18" = %"v12" +p #4;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v18";
          %"v19" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v24" : "w" = op "cmp"("slt", "w") %"v0", #1
          => br %"v24" ? "L20" : "L22" };
        cap_blk{ @"L20":
          => ret #4294967295 };
        cap_blk{ @"L22":
          %"v28" = %"v12" +p #16;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "write", int 8) %"chk0", %"v28";
          store.ptr [%"chk1" + 0] <- #0;
          %"chk2" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v12";
          %"v33" : "w" = op "raw_load"("sw", int 0) %"chk2";
          %"v34" : "w" = op "cmp"("eq", "w") %"v33", #0
          => br %"v34" ? "L36" : "L35" };
        cap_blk{ @"L35":
          %"v38" = %"v12" +p #24;
          %"chk3" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"v38";
          %"v39" : "w" = op "raw_load"("sw", int 0) %"chk3";
          %"v40" : "w" = op "cmp"("eq", "w") %"v39", #0
          => goto "L36" };
        cap_blk{ @"L36" [phi %"v42" : "w" = ("L22" => #1, "L35" => %"v40")]:
          => br %"v42" ? "iw_1.start" : "L30" };
        cap_blk{ @"iw_1.start":
          %"iw_1.v14" : "w" = op "raw_load"("sw", int 0) %"chk2";
          %"iw_1.v15" : "w" = op "cmp"("eq", "w") %"iw_1.v14", #0
          => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.L12" };
        cap_blk{ @"iw_1.L10":
          %"chk5" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk5" + 0] <- #1
          => goto "iw_1.L12" };
        cap_blk{ @"iw_1.L12":
          %"iw_1.v18" = %"v12" +p #44;
          %"iw_1.v20" = %"v12" +p #48;
          %"iw_1.v22" : "w" = op "raw_load"("sw", int 0) %"chk2";
          %"chk7" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v20";
          store "w" [%"chk7" + 0] <- %"iw_1.v22";
          store "w" [%"chk7" + (-4)] <- %"iw_1.v22";
          %"iw_1.v24" = %"v12" +p #32;
          %"chk9" : "a" = op "half_check"("upper", int 0, int 8, "write", int 8) %"chk0", %"iw_1.v24";
          store.ptr [%"chk9" + 0] <- #0;
          %"chk10" : "a" = op "check"(int 0, int 1, "read", int 1) %"v4";
          %"iw_1.v30" : "w" = op "raw_load"("sb", int 0) %"chk10";
          %"iw_1.v31" : "w" = op "cmp"("eq", "w") %"iw_1.v30", #45
          => br %"iw_1.v31" ? "iw_1.L25" : "iw_1.L26" };
        cap_blk{ @"iw_1.L25":
          %"iw_1.v33" = %"v12" +p #40;
          %"chk11" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v33";
          store "w" [%"chk11" + 0] <- #2;
          %"iw_1.v35" = %"v4" +p #1
          => goto "iw_1.L27" };
        cap_blk{ @"iw_1.L26":
          %"iw_1.v41" : "w" = op "raw_load"("sb", int 0) %"chk10";
          %"iw_1.v42" : "w" = op "cmp"("eq", "w") %"iw_1.v41", #43
          => br %"iw_1.v42" ? "iw_1.L36" : "iw_1.L37" };
        cap_blk{ @"iw_1.L36":
          %"iw_1.v44" = %"v12" +p #40;
          %"chk13" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v44";
          store "w" [%"chk13" + 0] <- #0;
          %"iw_1.v46" = %"v4" +p #1
          => goto "iw_1.L27" };
        cap_blk{ @"iw_1.L37":
          => br %"v14" ? "iw_1.L52" : "iw_1.L51" };
        cap_blk{ @"iw_1.L51":
          %"iw_1.v53" : "p" = "copy" $"glibc_getopt#str.145";
          call %"iw_1.v54" : "p" = $"__GI_getenv"("p" %"iw_1.v53");
          %"iw_1.v55" : "l" = "ptoi" %"iw_1.v54";
          %"iw_1.v56" : "w" = op "cmp"("ne", "l") %"iw_1.v55", #0
          => goto "iw_1.L52" };
        cap_blk{ @"iw_1.L52" [phi %"iw_1.v60" : "w" = ("iw_1.L37" => #1, "iw_1.L51" => %"iw_1.v56")]:
          => br %"iw_1.v60" ? "iw_1.L47" : "iw_1.L48" };
        cap_blk{ @"iw_1.L47":
          %"iw_1.v62" = %"v12" +p #40;
          %"chk14" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v62";
          store "w" [%"chk14" + 0] <- #0
          => goto "iw_1.L27" };
        cap_blk{ @"iw_1.L48":
          %"iw_1.v64" = %"v12" +p #40;
          %"chk15" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v64";
          store "w" [%"chk15" + 0] <- #1
          => goto "iw_1.L27" };
        cap_blk{ @"iw_1.L27" [phi %"iw_1.pr.1" : "p" = ("iw_1.L25" => %"iw_1.v35", "iw_1.L36" => %"iw_1.v46", "iw_1.L47" => %"v4", "iw_1.L48" => %"v4")]:
          %"iw_1.v66" = %"v12" +p #24;
          %"chk16" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"iw_1.v66";
          store "w" [%"chk16" + 0] <- #1
          => goto "L31" };
        cap_blk{ @"L30":
          %"chk17" : "a" = op "check"(int 0, int 1, "read", int 1) %"v4";
          %"v54" : "w" = op "raw_load"("sb", int 0) %"chk17";
          %"v55" : "w" = op "cmp"("eq", "w") %"v54", #45
          => br %"v55" ? "L57" : "L56" };
        cap_blk{ @"L56":
          %"v60" : "w" = op "raw_load"("sb", int 0) %"chk17";
          %"v61" : "w" = op "cmp"("eq", "w") %"v60", #43
          => goto "L57" };
        cap_blk{ @"L57" [phi %"v63" : "w" = ("L30" => #1, "L56" => %"v61")]:
          => br %"v63" ? "L49" : "L31" };
        cap_blk{ @"L49":
          %"v65" = %"v4" +p #1
          => goto "L31" };
        cap_blk{ @"L31" [phi %"pr.1" : "p" = ("iw_1.L27" => %"iw_1.pr.1", "L49" => %"v65", "L57" => %"v4")]:
          %"chk19" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.1";
          %"v71" : "w" = op "raw_load"("sb", int 0) %"chk19";
          %"v72" : "w" = op "cmp"("eq", "w") %"v71", #58
          => br %"v72" ? "L68" : "L67" };
        cap_blk{ @"L67":
          => goto "L68" };
        cap_blk{ @"L68" [phi %"pr.3" : "w" = ("L67" => %"v19", "L31" => #0)]:
          %"v77" = %"v12" +p #32;
          %"chk20" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"v77";
          %"v78" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk20";
          %"v79" : "l" = "ptoi" %"v78";
          %"v80" : "l" = "ptoi" #0;
          %"v81" : "w" = op "cmp"("eq", "l") %"v79", %"v80"
          => br %"v81" ? "L83" : "L82" };
        cap_blk{ @"L82":
          %"v85" = %"v12" +p #32;
          %"v86" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk20";
          %"chk22" : "a" = op "check"(int 0, int 1, "read", int 1) %"v86";
          %"v87" : "w" = op "raw_load"("sb", int 0) %"chk22";
          %"v88" : "w" = op "cmp"("eq", "w") %"v87", #0
          => goto "L83" };
        cap_blk{ @"L83" [phi %"v90" : "w" = ("L68" => #1, "L82" => %"v88")]:
          => br %"v90" ? "L73" : "L75" };
        cap_blk{ @"L73":
          %"v95" = %"v12" +p #48;
          %"chk23" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"v95";
          %"v96" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"chk24" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v98" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"v99" : "w" = op "cmp"("sgt", "w") %"v96", %"v98"
          => br %"v99" ? "L91" : "L93" };
        cap_blk{ @"L91":
          %"v101" = %"v12" +p #48;
          %"v103" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"chk26" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk23", %"v101";
          store "w" [%"chk26" + 0] <- %"v103"
          => goto "L93" };
        cap_blk{ @"L93":
          %"v108" = %"v12" +p #44;
          %"v109" : "w" = op "raw_load"("sw", int (-4)) %"chk23";
          %"v111" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"v112" : "w" = op "cmp"("sgt", "w") %"v109", %"v111"
          => br %"v112" ? "L104" : "L106" };
        cap_blk{ @"L104":
          %"v114" = %"v12" +p #44;
          %"v116" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"chk30" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"v114";
          store "w" [%"chk30" + 0] <- %"v116"
          => goto "L106" };
        cap_blk{ @"L106":
          %"v121" = %"v12" +p #40;
          %"v122" : "w" = op "raw_load"("uw", int (-8)) %"chk23";
          %"v123" : "w" = op "cmp"("eq", "w") %"v122", #1
          => br %"v123" ? "L117" : "L119" };
        cap_blk{ @"L117":
          %"v128" = %"v12" +p #44;
          %"v129" : "w" = op "raw_load"("sw", int (-4)) %"chk23";
          %"v131" = %"v12" +p #48;
          %"v132" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"v133" : "w" = op "cmp"("ne", "w") %"v129", %"v132"
          => br %"v133" ? "L134" : "L135" };
        cap_blk{ @"L134":
          %"v137" = %"v12" +p #48;
          %"v138" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"v140" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"v141" : "w" = op "cmp"("ne", "w") %"v138", %"v140"
          => goto "L135" };
        cap_blk{ @"L135" [phi %"v143" : "w" = ("L117" => #0, "L134" => %"v141")]:
          => br %"v143" ? "iw_2.start" : "L125" };
        cap_blk{ @"iw_2.start":
          %"iw_2.v6" = %"v12" +p #44;
          %"iw_2.v7" : "w" = op "raw_load"("sw", int (-4)) %"chk23";
          %"iw_2.v10" = %"v12" +p #48;
          %"iw_2.v11" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"iw_2.v14" : "w" = op "raw_load"("sw", int 0) %"chk24"
          => goto "iw_2.L16" };
        cap_blk{ @"iw_2.L16" [phi %"iw_2.pr.3" : "w" = ("iw_2.start" => %"iw_2.v14", "iw_2.L47" => %"iw_2.v94", "iw_2.L103" => %"iw_2.pr.3"); phi %"iw_2.pr.1" : "w" = ("iw_2.start" => %"iw_2.v7", "iw_2.L47" => %"iw_2.pr.1", "iw_2.L103" => %"iw_2.v142")]:
          %"iw_2.v21" : "w" = op "cmp"("sgt", "w") %"iw_2.pr.3", %"iw_2.v11"
          => br %"iw_2.v21" ? "iw_2.L22" : "iw_2.L23" };
        cap_blk{ @"iw_2.L22":
          %"iw_2.v26" : "w" = op "cmp"("sgt", "w") %"iw_2.v11", %"iw_2.pr.1"
          => goto "iw_2.L23" };
        cap_blk{ @"iw_2.L23" [phi %"iw_2.v28" : "w" = ("iw_2.L16" => #0, "iw_2.L22" => %"iw_2.v26")]:
          => br %"iw_2.v28" ? "iw_2.L17" : "iw_2.L18" };
        cap_blk{ @"iw_2.L17":
          %"iw_2.v34" : "w" = "sub" %"iw_2.pr.3", %"iw_2.v11";
          %"iw_2.v37" : "w" = "sub" %"iw_2.v11", %"iw_2.pr.1";
          %"iw_2.v38" : "w" = op "cmp"("sgt", "w") %"iw_2.v34", %"iw_2.v37"
          => br %"iw_2.v38" ? "iw_2.L44" : "iw_2.L100" };
        cap_blk{ @"iw_2.L44" [phi %"iw_2.pr.5" : "w" = ("iw_2.L45" => %"iw_2.v91", "iw_2.L17" => #0)]:
          %"iw_2.v50" : "w" = op "cmp"("slt", "w") %"iw_2.pr.5", %"iw_2.v37"
          => br %"iw_2.v50" ? "iw_2.L45" : "iw_2.L47" };
        cap_blk{ @"iw_2.L45":
          %"iw_2.v54" : "w" = "add" %"iw_2.pr.1", %"iw_2.pr.5";
          %"iw_2.v55" : "l" = op "ext"("sw") %"iw_2.v54";
          %"iw_2.v56" : "l" = "shl" %"iw_2.v55", #3;
          %"iw_2.v57" = %"v2" +p %"iw_2.v56";
          %"chk39" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_2.v57";
          %"iw_2.v58" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk39";
          %"iw_2.v71" : "w" = "sub" %"iw_2.pr.3", %"iw_2.v37";
          %"iw_2.v73" : "w" = "add" %"iw_2.v71", %"iw_2.pr.5";
          %"iw_2.v74" : "l" = op "ext"("sw") %"iw_2.v73";
          %"iw_2.v75" : "l" = "shl" %"iw_2.v74", #3;
          %"iw_2.v76" = %"v2" +p %"iw_2.v75";
          %"chk40" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_2.v76";
          %"iw_2.v77" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"chk41" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk39", %"iw_2.v57";
          store.ptr [%"chk41" + 0] <- %"iw_2.v77";
          %"chk42" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk40", %"iw_2.v76";
          store.ptr [%"chk42" + 0] <- %"iw_2.v58";
          %"iw_2.v91" : "w" = "add" %"iw_2.pr.5", #1
          => goto poll "iw_2.L44" };
        cap_blk{ @"iw_2.L47":
          %"iw_2.v94" : "w" = "sub" %"iw_2.pr.3", %"iw_2.v37"
          => goto poll "iw_2.L16" };
        cap_blk{ @"iw_2.L100" [phi %"iw_2.pr.6" : "w" = ("iw_2.L101" => %"iw_2.v139", "iw_2.L17" => #0)]:
          %"iw_2.v106" : "w" = op "cmp"("slt", "w") %"iw_2.pr.6", %"iw_2.v34"
          => br %"iw_2.v106" ? "iw_2.L101" : "iw_2.L103" };
        cap_blk{ @"iw_2.L101":
          %"iw_2.v110" : "w" = "add" %"iw_2.pr.1", %"iw_2.pr.6";
          %"iw_2.v111" : "l" = op "ext"("sw") %"iw_2.v110";
          %"iw_2.v112" : "l" = "shl" %"iw_2.v111", #3;
          %"iw_2.v113" = %"v2" +p %"iw_2.v112";
          %"chk43" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_2.v113";
          %"iw_2.v114" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk43";
          %"iw_2.v125" : "w" = "add" %"iw_2.v11", %"iw_2.pr.6";
          %"iw_2.v126" : "l" = op "ext"("sw") %"iw_2.v125";
          %"iw_2.v127" : "l" = "shl" %"iw_2.v126", #3;
          %"iw_2.v128" = %"v2" +p %"iw_2.v127";
          %"chk44" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_2.v128";
          %"iw_2.v129" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk44";
          %"chk45" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk43", %"iw_2.v113";
          store.ptr [%"chk45" + 0] <- %"iw_2.v129";
          %"chk46" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk44", %"iw_2.v128";
          store.ptr [%"chk46" + 0] <- %"iw_2.v114";
          %"iw_2.v139" : "w" = "add" %"iw_2.pr.6", #1
          => goto poll "iw_2.L100" };
        cap_blk{ @"iw_2.L103":
          %"iw_2.v142" : "w" = "add" %"iw_2.pr.1", %"iw_2.v34"
          => goto poll "iw_2.L16" };
        cap_blk{ @"iw_2.L18":
          %"iw_2.v144" = %"v12" +p #44;
          %"chk47" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"iw_2.v144";
          %"iw_2.v145" : "w" = op "raw_load"("sw", int 0) %"chk47";
          %"chk48" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"iw_2.v147" : "w" = op "raw_load"("sw", int 0) %"chk48";
          %"iw_2.v149" = %"v12" +p #48;
          %"chk49" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk23", %"iw_2.v149";
          %"iw_2.v150" : "w" = op "raw_load"("sw", int 0) %"chk49";
          %"iw_2.v151" : "w" = "sub" %"iw_2.v147", %"iw_2.v150";
          %"iw_2.v152" : "w" = "add" %"iw_2.v145", %"iw_2.v151";
          %"chk50" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk47", %"iw_2.v144";
          store "w" [%"chk50" + 0] <- %"iw_2.v152";
          %"iw_2.v156" : "w" = op "raw_load"("sw", int 0) %"chk48";
          store "w" [%"chk49" + 0] <- %"iw_2.v156"
          => goto "L159" };
        cap_blk{ @"L125":
          %"v150" = %"v12" +p #48;
          %"v151" : "w" = op "raw_load"("sw", int 0) %"chk23";
          %"v153" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"v154" : "w" = op "cmp"("ne", "w") %"v151", %"v153"
          => br %"v154" ? "L146" : "L159" };
        cap_blk{ @"L146":
          %"v156" = %"v12" +p #44;
          %"v158" : "w" = op "raw_load"("sw", int 0) %"chk24";
          %"chk56" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk0", %"v156";
          store "w" [%"chk56" + 0] <- %"v158"
          => goto "L159" };
        cap_blk{ @"L159":
          %"chk57" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v163" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"v165" : "w" = op "cmp"("slt", "w") %"v163", %"v0"
          => br %"v165" ? "L166" : "L167" };
        cap_blk{ @"L166":
          %"v170" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"v171" : "l" = op "ext"("sw") %"v170";
          %"v172" : "l" = "shl" %"v171", #3;
          %"v173" = %"v2" +p %"v172";
          %"chk59" : "a" = op "check"(int 0, int 8, "read", int 8) %"v173";
          %"v174" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk59";
          %"chk60" : "a" = op "check"(int 0, int 1, "read", int 1) %"v174";
          %"v176" : "w" = op "raw_load"("sb", int 0) %"chk60";
          %"v177" : "w" = op "cmp"("ne", "w") %"v176", #45
          => br %"v177" ? "L167" : "L178" };
        cap_blk{ @"L178":
          %"v182" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"v183" : "l" = op "ext"("sw") %"v182";
          %"v184" : "l" = "shl" %"v183", #3;
          %"v185" = %"v2" +p %"v184";
          %"chk62" : "a" = op "check"(int 0, int 8, "read", int 8) %"v185";
          %"v186" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk62";
          %"v187" = %"v186" +p #1;
          %"chk63" : "a" = op "check"(int 0, int 1, "read", int 1) %"v187";
          %"v188" : "w" = op "raw_load"("sb", int 0) %"chk63";
          %"v189" : "w" = op "cmp"("eq", "w") %"v188", #0
          => goto "L167" };
        cap_blk{ @"L167" [phi %"v193" : "w" = ("L159" => #0, "L166" => #1, "L178" => %"v189")]:
          => br %"v193" ? "L160" : "L161" };
        cap_blk{ @"L160":
          %"v195" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"v196" : "w" = "add" %"v195", #1;
          %"chk65" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk65" + 0] <- %"v196"
          => goto poll "L159" };
        cap_blk{ @"L161":
          %"v198" = %"v12" +p #48;
          %"v200" : "w" = op "raw_load"("sw", int 0) %"chk57";
          %"chk67" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk23", %"v198";
          store "w" [%"chk67" + 0] <- %"v200"
          => goto "L119" };
        cap_blk{ @"L119":
          %"chk68" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v205" : "w" = op "raw_load"("sw", int 0) %"chk68";
          %"v207" : "w" = op "cmp"("ne", "w") %"v205", %"v0"
          => br %"v207" ? "L208" : "L209" };
        cap_blk{ @"L208":
          %"v212" : "w" = op "raw_load"("sw", int 0) %"chk68";
          %"v213" : "l" = op "ext"("sw") %"v212";
          %"v214" : "l" = "shl" %"v213", #3;
          %"v215" = %"v2" +p %"v214";
          %"chk70" : "a" = op "check"(int 0, int 8, "read", int 8) %"v215";
          %"v216" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk70";
          %"v217" : "p" = "copy" $"glibc_getopt#str.146";
          call %"v218" : "w" = $"__GI_strcmp"("p" %"v216", "p" %"v217");
          %"v219" : "w" = op "cmp"("eq", "w") %"v218", #0
          => goto "L209" };
        cap_blk{ @"L209" [phi %"v221" : "w" = ("L119" => #0, "L208" => %"v219")]:
          => br %"v221" ? "L201" : "L203" };
        cap_blk{ @"L201":
          %"chk71" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v223" : "w" = op "raw_load"("sw", int 0) %"chk71";
          %"v224" : "w" = "add" %"v223", #1;
          %"chk72" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk72" + 0] <- %"v224";
          %"v229" = %"v12" +p #44;
          %"chk73" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"v229";
          %"v230" : "w" = op "raw_load"("sw", int 0) %"chk73";
          %"v232" = %"v12" +p #48;
          %"chk74" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk23", %"v232";
          %"v233" : "w" = op "raw_load"("sw", int 0) %"chk74";
          %"v234" : "w" = op "cmp"("ne", "w") %"v230", %"v233"
          => br %"v234" ? "L235" : "L236" };
        cap_blk{ @"L235":
          %"v238" = %"v12" +p #48;
          %"v239" : "w" = op "raw_load"("sw", int 0) %"chk74";
          %"v241" : "w" = op "raw_load"("sw", int 0) %"chk72";
          %"v242" : "w" = op "cmp"("ne", "w") %"v239", %"v241"
          => goto "L236" };
        cap_blk{ @"L236" [phi %"v244" : "w" = ("L201" => #0, "L235" => %"v242")]:
          => br %"v244" ? "iw_3.start" : "L226" };
        cap_blk{ @"iw_3.start":
          %"iw_3.v6" = %"v12" +p #44;
          %"iw_3.v7" : "w" = op "raw_load"("sw", int 0) %"chk73";
          %"iw_3.v10" = %"v12" +p #48;
          %"iw_3.v11" : "w" = op "raw_load"("sw", int 0) %"chk74";
          %"iw_3.v14" : "w" = op "raw_load"("sw", int 0) %"chk72"
          => goto "iw_3.L16" };
        cap_blk{ @"iw_3.L16" [phi %"iw_3.pr.3" : "w" = ("iw_3.start" => %"iw_3.v14", "iw_3.L47" => %"iw_3.v94", "iw_3.L103" => %"iw_3.pr.3"); phi %"iw_3.pr.1" : "w" = ("iw_3.start" => %"iw_3.v7", "iw_3.L47" => %"iw_3.pr.1", "iw_3.L103" => %"iw_3.v142")]:
          %"iw_3.v21" : "w" = op "cmp"("sgt", "w") %"iw_3.pr.3", %"iw_3.v11"
          => br %"iw_3.v21" ? "iw_3.L22" : "iw_3.L23" };
        cap_blk{ @"iw_3.L22":
          %"iw_3.v26" : "w" = op "cmp"("sgt", "w") %"iw_3.v11", %"iw_3.pr.1"
          => goto "iw_3.L23" };
        cap_blk{ @"iw_3.L23" [phi %"iw_3.v28" : "w" = ("iw_3.L16" => #0, "iw_3.L22" => %"iw_3.v26")]:
          => br %"iw_3.v28" ? "iw_3.L17" : "iw_3.L18" };
        cap_blk{ @"iw_3.L17":
          %"iw_3.v34" : "w" = "sub" %"iw_3.pr.3", %"iw_3.v11";
          %"iw_3.v37" : "w" = "sub" %"iw_3.v11", %"iw_3.pr.1";
          %"iw_3.v38" : "w" = op "cmp"("sgt", "w") %"iw_3.v34", %"iw_3.v37"
          => br %"iw_3.v38" ? "iw_3.L44" : "iw_3.L100" };
        cap_blk{ @"iw_3.L44" [phi %"iw_3.pr.5" : "w" = ("iw_3.L45" => %"iw_3.v91", "iw_3.L17" => #0)]:
          %"iw_3.v50" : "w" = op "cmp"("slt", "w") %"iw_3.pr.5", %"iw_3.v37"
          => br %"iw_3.v50" ? "iw_3.L45" : "iw_3.L47" };
        cap_blk{ @"iw_3.L45":
          %"iw_3.v54" : "w" = "add" %"iw_3.pr.1", %"iw_3.pr.5";
          %"iw_3.v55" : "l" = op "ext"("sw") %"iw_3.v54";
          %"iw_3.v56" : "l" = "shl" %"iw_3.v55", #3;
          %"iw_3.v57" = %"v2" +p %"iw_3.v56";
          %"chk80" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_3.v57";
          %"iw_3.v58" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk80";
          %"iw_3.v71" : "w" = "sub" %"iw_3.pr.3", %"iw_3.v37";
          %"iw_3.v73" : "w" = "add" %"iw_3.v71", %"iw_3.pr.5";
          %"iw_3.v74" : "l" = op "ext"("sw") %"iw_3.v73";
          %"iw_3.v75" : "l" = "shl" %"iw_3.v74", #3;
          %"iw_3.v76" = %"v2" +p %"iw_3.v75";
          %"chk81" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_3.v76";
          %"iw_3.v77" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk81";
          %"chk82" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk80", %"iw_3.v57";
          store.ptr [%"chk82" + 0] <- %"iw_3.v77";
          %"chk83" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk81", %"iw_3.v76";
          store.ptr [%"chk83" + 0] <- %"iw_3.v58";
          %"iw_3.v91" : "w" = "add" %"iw_3.pr.5", #1
          => goto poll "iw_3.L44" };
        cap_blk{ @"iw_3.L47":
          %"iw_3.v94" : "w" = "sub" %"iw_3.pr.3", %"iw_3.v37"
          => goto poll "iw_3.L16" };
        cap_blk{ @"iw_3.L100" [phi %"iw_3.pr.6" : "w" = ("iw_3.L101" => %"iw_3.v139", "iw_3.L17" => #0)]:
          %"iw_3.v106" : "w" = op "cmp"("slt", "w") %"iw_3.pr.6", %"iw_3.v34"
          => br %"iw_3.v106" ? "iw_3.L101" : "iw_3.L103" };
        cap_blk{ @"iw_3.L101":
          %"iw_3.v110" : "w" = "add" %"iw_3.pr.1", %"iw_3.pr.6";
          %"iw_3.v111" : "l" = op "ext"("sw") %"iw_3.v110";
          %"iw_3.v112" : "l" = "shl" %"iw_3.v111", #3;
          %"iw_3.v113" = %"v2" +p %"iw_3.v112";
          %"chk84" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_3.v113";
          %"iw_3.v114" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk84";
          %"iw_3.v125" : "w" = "add" %"iw_3.v11", %"iw_3.pr.6";
          %"iw_3.v126" : "l" = op "ext"("sw") %"iw_3.v125";
          %"iw_3.v127" : "l" = "shl" %"iw_3.v126", #3;
          %"iw_3.v128" = %"v2" +p %"iw_3.v127";
          %"chk85" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_3.v128";
          %"iw_3.v129" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk85";
          %"chk86" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk84", %"iw_3.v113";
          store.ptr [%"chk86" + 0] <- %"iw_3.v129";
          %"chk87" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk85", %"iw_3.v128";
          store.ptr [%"chk87" + 0] <- %"iw_3.v114";
          %"iw_3.v139" : "w" = "add" %"iw_3.pr.6", #1
          => goto poll "iw_3.L100" };
        cap_blk{ @"iw_3.L103":
          %"iw_3.v142" : "w" = "add" %"iw_3.pr.1", %"iw_3.v34"
          => goto poll "iw_3.L16" };
        cap_blk{ @"iw_3.L18":
          %"iw_3.v144" = %"v12" +p #44;
          %"chk88" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk73", %"iw_3.v144";
          %"iw_3.v145" : "w" = op "raw_load"("sw", int 0) %"chk88";
          %"chk89" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"iw_3.v147" : "w" = op "raw_load"("sw", int 0) %"chk89";
          %"iw_3.v149" = %"v12" +p #48;
          %"chk90" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk23", %"iw_3.v149";
          %"iw_3.v150" : "w" = op "raw_load"("sw", int 0) %"chk90";
          %"iw_3.v151" : "w" = "sub" %"iw_3.v147", %"iw_3.v150";
          %"iw_3.v152" : "w" = "add" %"iw_3.v145", %"iw_3.v151";
          %"chk91" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk73", %"iw_3.v144";
          store "w" [%"chk91" + 0] <- %"iw_3.v152";
          %"iw_3.v156" : "w" = op "raw_load"("sw", int 0) %"chk89";
          store "w" [%"chk90" + 0] <- %"iw_3.v156"
          => goto "L227" };
        cap_blk{ @"L226":
          %"v251" = %"v12" +p #44;
          %"v252" : "w" = op "raw_load"("sw", int 0) %"chk73";
          %"v254" = %"v12" +p #48;
          %"v255" : "w" = op "raw_load"("sw", int 0) %"chk74";
          %"v256" : "w" = op "cmp"("eq", "w") %"v252", %"v255"
          => br %"v256" ? "L247" : "L227" };
        cap_blk{ @"L247":
          %"v258" = %"v12" +p #44;
          %"v260" : "w" = op "raw_load"("sw", int 0) %"chk72";
          store "w" [%"chk73" + 0] <- %"v260"
          => goto "L227" };
        cap_blk{ @"L227":
          %"v262" = %"v12" +p #48;
          %"chk98" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk23", %"v262";
          store "w" [%"chk98" + 0] <- %"v0";
          %"chk99" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk99" + 0] <- %"v0"
          => goto "L203" };
        cap_blk{ @"L203":
          %"chk100" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk2", %"v12";
          %"v270" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v272" : "w" = op "cmp"("eq", "w") %"v270", %"v0"
          => br %"v272" ? "L266" : "L268" };
        cap_blk{ @"L266":
          %"v277" = %"v12" +p #44;
          %"chk101" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk0", %"v277";
          %"v278" : "w" = op "raw_load"("sw", int 0) %"chk101";
          %"v280" = %"v12" +p #48;
          %"chk102" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk23", %"v280";
          %"v281" : "w" = op "raw_load"("sw", int 0) %"chk102";
          %"v282" : "w" = op "cmp"("ne", "w") %"v278", %"v281"
          => br %"v282" ? "L273" : "L275" };
        cap_blk{ @"L273":
          %"v285" = %"v12" +p #44;
          %"v286" : "w" = op "raw_load"("sw", int 0) %"chk101";
          %"chk104" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk2", %"v12";
          store "w" [%"chk104" + 0] <- %"v286"
          => goto "L275" };
        cap_blk{ @"L275":
          => ret #4294967295 };
        cap_blk{ @"L268":
          %"v294" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v295" : "l" = op "ext"("sw") %"v294";
          %"v296" : "l" = "shl" %"v295", #3;
          %"v297" = %"v2" +p %"v296";
          %"chk106" : "a" = op "check"(int 0, int 8, "read", int 8) %"v297";
          %"v298" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk106";
          %"chk107" : "a" = op "check"(int 0, int 1, "read", int 1) %"v298";
          %"v300" : "w" = op "raw_load"("sb", int 0) %"chk107";
          %"v301" : "w" = op "cmp"("ne", "w") %"v300", #45
          => br %"v301" ? "L303" : "L302" }
  ].
