(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_08 : list term :=
  [
        cap_blk{ @"L588":
          %"v611" : "l" = "mul" %"v592", #72;
          %"v612" = %"pr.7" +p %"v611";
          %"v613" = %"v612" +p #12;
          %"chk66" : "a" = op "check"(int 0, int 4, "read", int 1) %"v613";
          %"v614" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v615" : "w" = "shl" %"v614", #28;
          %"v616" : "w" = "shr" %"v615", #31;
          %"v624" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v625" : "w" = "shl" %"v624", #27;
          %"v626" : "w" = "shr" %"v625", #31;
          %"v634" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v635" : "w" = "shl" %"v634", #26;
          %"v636" : "w" = "shr" %"v635", #31;
          %"v644" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v645" : "w" = "shl" %"v644", #25;
          %"v646" : "w" = "shr" %"v645", #31;
          %"v654" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v655" : "w" = "shl" %"v654", #24;
          %"v656" : "w" = "shr" %"v655", #31;
          %"v664" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v674" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v675" : "w" = "shl" %"v674", #30;
          %"v676" : "w" = "shr" %"v675", #31;
          %"v684" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v685" : "w" = "shl" %"v684", #22;
          %"v686" : "w" = "shr" %"v685", #31;
          %"v694" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v695" : "w" = "shl" %"v694", #29;
          %"v696" : "w" = "shr" %"v695", #31;
          %"v703" = %"v612" +p #4;
          %"chk75" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk66", %"v703";
          %"v704" : "w" = op "raw_load"("sw", int 0) %"chk75";
          %"chk76" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk66", %"v612";
          %"v711" : "w" = op "raw_load"("sw", int 0) %"chk76";
          %"v719" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v720" : "w" = "shl" %"v719", #20;
          %"v721" : "w" = "shr" %"v720", #31;
          %"v728" = %"v612" +p #16;
          %"chk78" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v728";
          %"v729" : "w" = op "raw_load"("sw", int 0) %"chk78";
          %"v730" : "w" = op "ext"("sb") %"v729";
          %"v737" = %"v612" +p #8;
          %"v738" : "w" = op "raw_load"("sw", int 4) %"chk75";
          %"v739" : "w" = op "ext"("sb") %"v738";
          %"v742" = %"v14" +p #1000;
          %"v751" = %"v612" +p #44;
          %"chk80" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v751";
          %"v752" : "w" = op "raw_load"("sw", int 0) %"chk80";
          %"v754" : "w" = op "cmp"("ne", "w") %"v752", #4294967295
          => br %"v754" ? "L743" : "L745" };
        cap_blk{ @"L743":
          %"v760" = %"v612" +p #4;
          %"v767" = %"v612" +p #44;
          %"v768" : "w" = op "raw_load"("sw", int 0) %"chk80";
          %"v769" : "l" = op "ext"("sw") %"v768";
          %"v770" : "l" = "shl" %"v769", #4;
          %"v771" = %"pr.16" +p %"v770";
          %"chk82" : "a" = op "check"(int 0, int 4, "read", int 1) %"v771";
          %"v772" : "w" = op "raw_load"("sw", int 0) %"chk82";
          %"chk83" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk75", %"v760";
          store "w" [%"chk83" + 0] <- %"v772";
          %"v782" : "w" = op "raw_load"("sw", int 0) %"chk83";
          %"v783" : "w" = op "cmp"("slt", "w") %"v782", #0
          => br %"v783" ? "L773" : "L775" };
        cap_blk{ @"L773":
          %"v789" = %"v612" +p #4;
          %"v790" : "w" = op "raw_load"("sw", int 0) %"chk83";
          %"v792" : "w" = "mul" %"v790", #4294967295;
          store "w" [%"chk83" + 0] <- %"v792";
          %"v798" = %"v612" +p #12;
          %"v799" : "w" = op "raw_load"("uw", int 0) %"chk66";
          %"v800" : "w" = "and" %"v799", #4294967263;
          %"v803" : "w" = "or" %"v800", #32;
          store "w" [%"chk66" + 0] <- %"v803"
          => goto "L775" };
        cap_blk{ @"L775" [phi %"pr.65" : "w" = ("L773" => #1, "L743" => %"v636")]:
          %"v811" = %"v612" +p #4;
          %"v812" : "w" = op "raw_load"("sw", int 0) %"chk83"
          => goto "L745" };
        cap_blk{ @"L745" [phi %"pr.81" : "w" = ("L775" => %"v812", "L588" => %"v704"); phi %"pr.64" : "w" = ("L775" => %"pr.65", "L588" => %"v636")]:
          %"v821" = %"v612" +p #40;
          %"v822" : "w" = op "raw_load"("sw", int (-4)) %"chk80";
          %"v824" : "w" = op "cmp"("ne", "w") %"v822", #4294967295
          => br %"v824" ? "L813" : "L815" };
        cap_blk{ @"L813":
          %"v836" = %"v612" +p #40;
          %"v837" : "w" = op "raw_load"("sw", int (-4)) %"chk80";
          %"v838" : "l" = op "ext"("sw") %"v837";
          %"v839" : "l" = "shl" %"v838", #4;
          %"v840" = %"pr.16" +p %"v839";
          %"chk92" : "a" = op "check"(int 0, int 4, "read", int 1) %"v840";
          %"v841" : "w" = op "raw_load"("sw", int 0) %"chk92";
          %"chk93" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk76", %"v612";
          store "w" [%"chk93" + 0] <- %"v841";
          %"v850" : "w" = op "raw_load"("sw", int 0) %"chk93";
          %"v851" : "w" = op "cmp"("slt", "w") %"v850", #0
          => br %"v851" ? "L842" : "L844" };
        cap_blk{ @"L842":
          store "w" [%"chk93" + 0] <- #4294967295
          => goto "L844" };
        cap_blk{ @"L844":
          %"v863" : "w" = op "raw_load"("sw", int 0) %"chk93"
          => goto "L815" };
        cap_blk{ @"L815" [phi %"pr.89" : "w" = ("L844" => %"v863", "L745" => %"v711")]:
          %"v872" : "p" = "copy" $"__printf_function_table";
          %"chk97" : "a" = op "check"(int 0, int 8, "read", int 8) %"v872";
          %"v873" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk97";
          %"v874" : "l" = "ptoi" %"v873";
          %"v875" : "l" = "ptoi" #0;
          %"v876" : "w" = op "cmp"("ne", "l") %"v874", %"v875"
          => br %"v876" ? "L879" : "L880" };
        cap_blk{ @"L879":
          %"v881" : "p" = "copy" $"__printf_function_table";
          %"chk98" : "a" = op "check"(int 0, int 8, "read", int 8) %"v881";
          %"v882" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk98";
          %"v884" : "l" = op "ext"("sw") %"v739";
          %"v885" : "l" = "shl" %"v884", #3;
          %"v886" = %"v882" +p %"v885";
          %"chk99" : "a" = op "check"(int 0, int 8, "read", int 8) %"v886";
          %"v887" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk99";
          %"v888" : "l" = "ptoi" %"v887";
          %"v890" : "w" = op "cmp"("ne", "l") %"v888", %"v875"
          => goto "L880" };
        cap_blk{ @"L880" [phi %"v892" : "w" = ("L815" => #0, "L879" => %"v890")]:
          => br %"v892" ? "L867" : "L940" };
        cap_blk{ @"L867":
          %"v895" : "p" = "copy" $"__printf_function_table";
          %"chk100" : "a" = op "check"(int 0, int 8, "read", int 8) %"v895";
          %"v896" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk100";
          %"v898" : "l" = op "ext"("sw") %"v739";
          %"v899" : "l" = "shl" %"v898", #3;
          %"v900" = %"v896" +p %"v899";
          %"chk101" : "a" = op "check"(int 0, int 8, "read", int 8) %"v900";
          %"v901" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk101";
          %"v908" = %"v612" +p #48;
          %"chk102" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v908";
          %"v909" : "w" = op "raw_load"("sw", int 0) %"chk102";
          %"v910" : "l" = op "ext"("sw") %"v909";
          %"v911" : "l" = "shl" %"v910", #4;
          %"v912" = %"pr.16" +p %"v911";
          %"v918" = %"v612" +p #56;
          %"chk103" : "a" = op "half_check"("upper", int 0, int 8, "read", int 1) %"chk66", %"v918";
          %"v919" : "l" = op "raw_load"("l", int 0) %"chk103";
          call %"v925" : "w" = $"__printf_function_invoke"("p" %"v0", "p" %"v901", "p" %"v912", "l" %"v919", "p" %"v612");
          %"v931" : "w" = op "cmp"("ne", "w") %"v925", #4294967294
          => br %"v931" ? "L926" : "L940" };
        cap_blk{ @"L926":
          %"v936" : "w" = op "cmp"("slt", "w") %"v925", #0
          => br %"v936" ? "L932" : "L866" };
        cap_blk{ @"L932":
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L101" };
        cap_blk{ @"L940":
          %"v950" : "w" = op "cmp"("slt", "w") %"v739", #32
          => br %"v950" ? "L952" : "L951" };
        cap_blk{ @"L951":
          %"v954" : "w" = op "cmp"("sgt", "w") %"v739", #122
          => goto "L952" };
        cap_blk{ @"L952" [phi %"v956" : "w" = ("L940" => #1, "L951" => %"v954")]:
          => br %"v956" ? "L948" : "L947" };
        cap_blk{ @"L947":
          %"v960" : "p" = "copy" $"glibc_vfprintf_internal#printf_positional.step4_jumps.294";
          %"v961" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v963" : "w" = "sub" %"v739", #32;
          %"v964" : "l" = op "ext"("sw") %"v963";
          %"v965" = %"v961" +p %"v964";
          %"chk104" : "a" = op "check"(int 0, int 1, "read", int 1) %"v965";
          %"v966" : "w" = op "raw_load"("ub", int 0) %"chk104";
          %"v967" : "l" = op "ext"("uw") %"v966";
          %"v968" : "l" = "shl" %"v967", #2;
          %"v969" = %"v960" +p %"v968";
          %"chk105" : "a" = op "check"(int 0, int 4, "read", int 1) %"v969";
          %"v970" : "w" = op "raw_load"("sw", int 0) %"chk105";
          %"v971" : "l" = op "ext"("sw") %"v970"
          => goto "L948" };
        cap_blk{ @"L948" [phi %"v972" : "l" = ("L947" => %"v971", "L952" => #0)]:
          %"v973" : "w" = "copy" %"v972";
          %"v974" : "l" = op "ext"("sw") %"v973";
          %"v975" = #1 +p %"v974";
          %"v977" : "l" = "ptoi" %"v975";
          %"v2035" : "w" = op "cmp"("ult", "l") %"v977", #8
          => br %"v2035" ? "L2036" : "L2037" };
        cap_blk{ @"L980":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #37)
          => goto "L866" };
        cap_blk{ @"L984":
          => br %"v696" ? "L1012" : "L1013" };
        cap_blk{ @"L1012":
          %"v1022" = %"v612" +p #48;
          %"chk106" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1022";
          %"v1023" : "w" = op "raw_load"("sw", int 0) %"chk106";
          %"v1024" : "l" = op "ext"("sw") %"v1023";
          %"v1025" : "l" = "shl" %"v1024", #4;
          %"v1026" = %"pr.16" +p %"v1025";
          %"chk107" : "a" = op "check"(int 0, int 8, "read", int 1) %"v1026";
          %"v1027" : "l" = op "raw_load"("l", int 0) %"chk107"
          => goto "L1014" };
        cap_blk{ @"L1013":
          => br %"v686" ? "L1028" : "L1029" };
        cap_blk{ @"L1028":
          %"v1038" = %"v612" +p #48;
          %"chk108" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1038";
          %"v1039" : "w" = op "raw_load"("sw", int 0) %"chk108";
          %"v1040" : "l" = op "ext"("sw") %"v1039";
          %"v1041" : "l" = "shl" %"v1040", #4;
          %"v1042" = %"pr.16" +p %"v1041";
          %"chk109" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1042";
          %"v1043" : "w" = op "raw_load"("uw", int 0) %"chk109";
          %"v1044" : "w" = op "ext"("sb") %"v1043";
          %"v1045" : "l" = op "ext"("sw") %"v1044"
          => goto "L1014" };
        cap_blk{ @"L1029":
          %"v1050" : "w" = op "cmp"("eq", "w") %"v676", #0
          => br %"v1050" ? "L1046" : "L1047" };
        cap_blk{ @"L1046":
          %"v1057" = %"v612" +p #48;
          %"chk110" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1057";
          %"v1058" : "w" = op "raw_load"("sw", int 0) %"chk110";
          %"v1059" : "l" = op "ext"("sw") %"v1058";
          %"v1060" : "l" = "shl" %"v1059", #4;
          %"v1061" = %"pr.16" +p %"v1060";
          %"chk111" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1061";
          %"v1062" : "w" = op "raw_load"("sw", int 0) %"chk111";
          %"v1063" : "l" = op "ext"("sw") %"v1062"
          => goto "L1014" };
        cap_blk{ @"L1047":
          %"v1070" = %"v612" +p #48;
          %"chk112" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1070";
          %"v1071" : "w" = op "raw_load"("sw", int 0) %"chk112";
          %"v1072" : "l" = op "ext"("sw") %"v1071";
          %"v1073" : "l" = "shl" %"v1072", #4;
          %"v1074" = %"pr.16" +p %"v1073";
          %"chk113" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1074";
          %"v1075" : "w" = op "raw_load"("uw", int 0) %"chk113";
          %"v1076" : "w" = op "ext"("sh") %"v1075";
          %"v1077" : "l" = op "ext"("sw") %"v1076"
          => goto "L1014" };
        cap_blk{ @"L1014" [phi %"pr.95" : "l" = ("L1012" => %"v1027", "L1028" => %"v1045", "L1046" => %"v1063", "L1047" => %"v1077")]:
          %"v1079" : "w" = op "cmp"("slt", "l") %"pr.95", #0
          => br %"v1079" ? "L1080" : "L1088" };
        cap_blk{ @"L1080":
          %"v1085" : "l" = "neg" %"pr.95"
          => goto "L1088" };
        cap_blk{ @"L1090" [phi %"pr.48" : "w" = ("L2040" => #10, "L2048" => #8, "L2050" => #16, "L2071" => #2)]:
          => br %"v696" ? "L1147" : "L1148" };
        cap_blk{ @"L1147":
          %"v1157" = %"v612" +p #48;
          %"chk114" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1157";
          %"v1158" : "w" = op "raw_load"("sw", int 0) %"chk114";
          %"v1159" : "l" = op "ext"("sw") %"v1158";
          %"v1160" : "l" = "shl" %"v1159", #4;
          %"v1161" = %"pr.16" +p %"v1160";
          %"chk115" : "a" = op "check"(int 0, int 8, "read", int 1) %"v1161";
          %"v1162" : "l" = op "raw_load"("l", int 0) %"chk115"
          => goto "L1088" };
        cap_blk{ @"L1148":
          => br %"v686" ? "L1163" : "L1164" };
        cap_blk{ @"L1163":
          %"v1173" = %"v612" +p #48;
          %"chk116" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1173";
          %"v1174" : "w" = op "raw_load"("sw", int 0) %"chk116";
          %"v1175" : "l" = op "ext"("sw") %"v1174";
          %"v1176" : "l" = "shl" %"v1175", #4;
          %"v1177" = %"pr.16" +p %"v1176";
          %"chk117" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1177";
          %"v1178" : "w" = op "raw_load"("uw", int 0) %"chk117";
          %"v1179" : "w" = op "ext"("ub") %"v1178";
          %"v1180" : "l" = op "ext"("uw") %"v1179"
          => goto "L1088" };
        cap_blk{ @"L1164":
          %"v1185" : "w" = op "cmp"("eq", "w") %"v676", #0
          => br %"v1185" ? "L1181" : "L1182" };
        cap_blk{ @"L1181":
          %"v1192" = %"v612" +p #48;
          %"chk118" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1192";
          %"v1193" : "w" = op "raw_load"("sw", int 0) %"chk118";
          %"v1194" : "l" = op "ext"("sw") %"v1193";
          %"v1195" : "l" = "shl" %"v1194", #4;
          %"v1196" = %"pr.16" +p %"v1195";
          %"chk119" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1196";
          %"v1197" : "w" = op "raw_load"("uw", int 0) %"chk119";
          %"v1198" : "l" = op "ext"("uw") %"v1197"
          => goto "L1088" };
        cap_blk{ @"L1182":
          %"v1205" = %"v612" +p #48;
          %"chk120" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk66", %"v1205";
          %"v1206" : "w" = op "raw_load"("sw", int 0) %"chk120";
          %"v1207" : "l" = op "ext"("sw") %"v1206";
          %"v1208" : "l" = "shl" %"v1207", #4;
          %"v1209" = %"pr.16" +p %"v1208";
          %"chk121" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1209";
          %"v1210" : "w" = op "raw_load"("uw", int 0) %"chk121";
          %"v1211" : "w" = op "ext"("uh") %"v1210";
          %"v1212" : "l" = op "ext"("uw") %"v1211"
          => goto "L1088" };
        cap_blk{ @"L1088" [phi %"pr.93" : "w" = ("L1080" => %"v739", "L1014" => %"v739", "L1147" => %"v739", "L1163" => %"v739", "L1181" => %"v739", "L1182" => %"v739", "L1603" => #120, "L1739" => %"v739", "L1728" => %"v739"); phi %"pr.69" : "w" = ("L1080" => %"v656", "L1014" => %"v656", "L1147" => %"v656", "L1163" => %"v656", "L1181" => %"v656", "L1182" => %"v656", "L1603" => #0, "L1739" => %"v656", "L1728" => %"v656"); phi %"pr.67" : "w" = ("L1080" => %"v646", "L1014" => %"v646", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => %"v646", "L1739" => %"v646", "L1728" => %"v646"); phi %"pr.62" : "w" = ("L1080" => %"v626", "L1014" => %"v626", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => %"v626", "L1739" => %"v626", "L1728" => %"v626"); phi %"pr.59" : "w" = ("L1080" => %"v616", "L1014" => %"v616", "L1147" => %"v616", "L1163" => %"v616", "L1181" => %"v616", "L1182" => %"v616", "L1603" => #1, "L1739" => %"v616", "L1728" => %"v616"); phi %"pr.47" : "w" = ("L1080" => #10, "L1014" => #10, "L1147" => %"pr.48", "L1163" => %"pr.48", "L1181" => %"pr.48", "L1182" => %"pr.48", "L1603" => #16, "L1739" => #10, "L1728" => #10); phi %"pr.40" : "l" = ("L1080" => %"v1085", "L1014" => %"pr.95", "L1147" => %"v1162", "L1163" => %"v1180", "L1181" => %"v1198", "L1182" => %"v1212", "L1603" => %"v1621", "L1739" => %"v1744", "L1728" => %"v1738"); phi %"pr.37" : "w" = ("L1080" => %"v1079", "L1014" => %"v1079", "L1147" => #0, "L1163" => #0, "L1181" => #0, "L1182" => #0, "L1603" => #0, "L1739" => %"v1736", "L1728" => %"v1736")]:
          %"v1217" : "w" = op "cmp"("slt", "w") %"pr.89", #0
          => br %"v1217" ? "L1215" : "L1214" };
        cap_blk{ @"L1214":
          => goto "L1215" };
        cap_blk{ @"L1215" [phi %"pr.92" : "w" = ("L1214" => #32, "L1088" => %"v730"); phi %"pr.86" : "w" = ("L1214" => %"pr.89", "L1088" => #1)]:
          %"v1222" : "w" = op "cmp"("eq", "w") %"pr.86", #0
          => br %"v1222" ? "L1223" : "L1224" };
        cap_blk{ @"L1223":
          %"v1226" : "w" = op "cmp"("eq", "l") %"pr.40", #0
          => goto "L1224" };
        cap_blk{ @"L1224" [phi %"v1228" : "w" = ("L1215" => #0, "L1223" => %"v1226")]:
          => br %"v1228" ? "L1218" : "L1219" };
        cap_blk{ @"L1218":
          %"v1234" : "w" = op "cmp"("eq", "w") %"pr.47", #8
          => br %"v1234" ? "L1235" : "L1236" };
        cap_blk{ @"L1235":
          %"v1238" : "w" = op "cmp"("ne", "w") %"pr.59", #0
          => goto "L1236" };
        cap_blk{ @"L1236" [phi %"v1239" : "w" = ("L1218" => #0, "L1235" => %"v1238")]:
          => br %"v1239" ? "L1230" : "L1220" };
        cap_blk{ @"L1230":
          (op "flight"(%"v1241", "sub", [op "address"(%"v742"); #1], op "lower"(%"v742")));
          %"chk122" : "a" = op "check"(int 0, int 1, "write", int 1) %"v1241";
          store "b" [%"chk122" + 0] <- #48
          => goto "L1220" };
        cap_blk{ @"L1219":
          %"v1245" : "w" = op "ext"("sb") %"pr.93";
          %"v1246" : "w" = op "cmp"("eq", "w") %"v1245", #88;
          call %"v1247" : "p" = $"_itoa_word"("l" %"pr.40", "p" %"v742", "w" %"pr.47", "w" %"v1246")
          => goto "L1220" };
        cap_blk{ @"L1220" [phi %"pr.53" : "p" = ("L1219" => %"v1247", "L1230" => %"v1241", "L1236" => %"v742")]:
          => br %"pr.69" ? "L1252" : "L1251" };
        cap_blk{ @"L1251":
          => br %"v721" ? "L1254" : "L1252" };
        cap_blk{ @"L1254":
          %"v1257" : "w" = op "cmp"("eq", "w") %"pr.47", #10
          => goto "L1252" };
        cap_blk{ @"L1252" [phi %"v1261" : "w" = ("L1220" => #1, "L1251" => #0, "L1254" => %"v1257")]:
          => br %"pr.69" ? "L1263" : "L1264" };
        cap_blk{ @"L1263":
          %"v1267" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk123" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1267";
          %"v1268" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk123";
          %"v1271" : "l" = "ptoi" %"v742";
          %"v1272" : "l" = "ptoi" %"pr.53";
          %"v1273" : "l" = "sub" %"v1271", %"v1272";
          call %"v1274" : "w" = $"__grouping_iterator_init"("p" %"v1248", "w" #1, "p" %"v1268", "w" %"v1273")
          => goto "L1265" };
        cap_blk{ @"L1264":
          => br %"v721" ? "L1280" : "L1281" };
        cap_blk{ @"L1280":
          %"v1283" : "w" = op "cmp"("eq", "w") %"pr.47", #10
          => goto "L1281" };
        cap_blk{ @"L1281" [phi %"v1285" : "w" = ("L1264" => #0, "L1280" => %"v1283")]:
          => br %"v1285" ? "L1276" : "L1265" };
        cap_blk{ @"L1276":
          %"v1288" : "l" = "ptoi" %"v742";
          %"v1289" : "l" = "ptoi" %"pr.53";
          %"v1290" : "l" = "sub" %"v1288", %"v1289";
          call %"v1291" : "w" = $"__grouping_iterator_init_none"("p" %"v1248", "w" %"v1290")
          => goto "L1265" };
        cap_blk{ @"L1265":
          => br %"v721" ? "L1298" : "L1299" };
        cap_blk{ @"L1298":
          %"v1301" : "w" = op "cmp"("eq", "w") %"pr.47", #10
          => goto "L1299" };
        cap_blk{ @"L1299" [phi %"v1303" : "w" = ("L1265" => #0, "L1298" => %"v1301")]:
          => br %"v1303" ? "L1294" : "L1295" };
        cap_blk{ @"L1294":
          %"v1304" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk124" : "a" = op "check"(int 0, int 8, "read", int 8) %"v1304";
          %"v1305" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk124";
          call %"v1308" : "w" = $"__translated_number_width"("p" %"v1305", "p" %"pr.53", "p" %"v742")
          => goto "L1296" };
        cap_blk{ @"L1295":
          %"v1311" : "l" = "ptoi" %"v742";
          %"v1312" : "l" = "ptoi" %"pr.53";
          %"v1313" : "l" = "sub" %"v1311", %"v1312"
          => goto "L1296" };
        cap_blk{ @"L1296" [phi %"pr.98" : "w" = ("L1294" => %"v1308", "L1295" => %"v1313")]:
          => br %"pr.69" ? "L1314" : "L1316" };
        cap_blk{ @"L1314":
          %"v1319" = %"v1248" +p #20;
          %"chk125" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1319";
          %"v1320" : "w" = op "raw_load"("uw", int 0) %"chk125";
          call %"v1322" : "l" = $"__GI_strlen"("p" %"pr.6");
          %"v1323" : "l" = op "ext"("uw") %"v1320";
          %"v1324" : "l" = "mul" %"v1323", %"v1322";
          %"v1325" : "l" = op "ext"("sw") %"pr.98";
          %"v1326" : "l" = "add" %"v1325", %"v1324"
          => goto "L1316" };
        cap_blk{ @"L1316" [phi %"pr.99" : "w" = ("L1314" => %"v1326", "L1296" => %"pr.98")]:
          %"v1330" : "w" = op "cmp"("sle", "w") %"pr.86", %"pr.99"
          => br %"v1330" ? "L1331" : "L1332" };
        cap_blk{ @"L1331":
          %"v1334" : "w" = op "cmp"("ne", "l") %"pr.40", #0
          => goto "L1332" };
        cap_blk{ @"L1332" [phi %"v1336" : "w" = ("L1316" => #0, "L1331" => %"v1334")]:
          => br %"v1336" ? "L1337" : "L1338" };
        cap_blk{ @"L1337":
          %"v1340" : "w" = op "cmp"("ne", "w") %"pr.59", #0
          => goto "L1338" };
        cap_blk{ @"L1338" [phi %"v1341" : "w" = ("L1332" => #0, "L1337" => %"v1340")]:
          => br %"v1341" ? "L1342" : "L1343" };
        cap_blk{ @"L1342":
          %"v1345" : "w" = op "cmp"("eq", "w") %"pr.47", #8
          => goto "L1343" };
        cap_blk{ @"L1343" [phi %"v1347" : "w" = ("L1338" => #0, "L1342" => %"v1345")]:
          %"v1356" : "l" = "ptoi" %"v742";
          %"v1357" : "l" = "ptoi" %"pr.53";
          %"v1358" : "l" = "sub" %"v1356", %"v1357";
          %"v1359" : "l" = op "ext"("sw") %"pr.86";
          %"v1360" : "l" = "sub" %"v1359", %"v1358";
          %"v1361" : "w" = op "cmp"("slt", "l") %"v1360", #0
          => br %"v1361" ? "L1352" : "L1351" };
        cap_blk{ @"L1351":
          => goto "L1352" };
        cap_blk{ @"L1352" [phi %"v1370" : "l" = ("L1351" => %"v1360", "L1343" => #0)]:
          %"v1375" : "w" = op "cmp"("eq", "w") %"pr.64", #0
          => br %"v1375" ? "L1371" : "L1372" };
        cap_blk{ @"L1371":
          %"v1378" : "w" = "copy" %"v1370";
          %"v1379" : "w" = "add" %"pr.99", %"v1378";
          %"v1380" : "w" = "sub" %"pr.81", %"v1379";
          %"v1385" : "w" = op "cmp"("ne", "l") %"pr.40", #0
          => br %"v1385" ? "L1386" : "L1387" };
        cap_blk{ @"L1386":
          %"v1389" : "w" = op "cmp"("ne", "w") %"pr.59", #0
          => goto "L1387" };
        cap_blk{ @"L1387" [phi %"v1390" : "w" = ("L1371" => #0, "L1386" => %"v1389")]:
          => br %"v1390" ? "L1391" : "L1392" };
        cap_blk{ @"L1391":
          %"v1394" : "w" = op "cmp"("eq", "w") %"pr.47", #16
          => br %"v1394" ? "L1392" : "L1395" };
        cap_blk{ @"L1395":
          %"v1398" : "w" = op "cmp"("eq", "w") %"pr.47", #2
          => goto "L1392" };
        cap_blk{ @"L1392" [phi %"v1402" : "w" = ("L1387" => #0, "L1391" => #1, "L1395" => %"v1398")]:
          => br %"v1402" ? "L1381" : "L1383" };
        cap_blk{ @"L1381":
          %"v1404" : "w" = "sub" %"v1380", #2
          => goto "L1383" };
        cap_blk{ @"L1383" [phi %"pr.72" : "w" = ("L1381" => %"v1404", "L1392" => %"v1380")]:
          => br %"v1347" ? "L1405" : "L1407" };
        cap_blk{ @"L1405":
          %"v1410" : "w" = "sub" %"pr.72", #1
          => goto "L1407" };
        cap_blk{ @"L1407" [phi %"pr.73" : "w" = ("L1405" => %"v1410", "L1383" => %"pr.72")]:
          => br %"pr.37" ? "L1416" : "L1415" };
        cap_blk{ @"L1415":
          %"v1418" : "w" = op "cmp"("ne", "w") %"pr.67", #0
          => goto "L1416" };
        cap_blk{ @"L1416" [phi %"v1419" : "w" = ("L1407" => #1, "L1415" => %"v1418")]:
          => br %"v1419" ? "L1421" : "L1420" };
        cap_blk{ @"L1420":
          %"v1423" : "w" = op "cmp"("ne", "w") %"pr.62", #0
          => goto "L1421" };
        cap_blk{ @"L1421" [phi %"v1424" : "w" = ("L1416" => #1, "L1420" => %"v1423")]:
          => br %"v1424" ? "L1411" : "L1413" };
        cap_blk{ @"L1411":
          %"v1426" : "w" = "sub" %"pr.73", #1
          => goto "L1413" };
        cap_blk{ @"L1413" [phi %"pr.74" : "w" = ("L1411" => %"v1426", "L1421" => %"pr.73")]:
          %"v1430" : "w" = op "ext"("sb") %"pr.92";
          %"v1431" : "w" = op "cmp"("eq", "w") %"v1430", #32
          => br %"v1431" ? "L1427" : "L1429" };
        cap_blk{ @"L1427":
          %"v1434" : "l" = op "ext"("sw") %"pr.74";
          call void $"glibc_vfprintf_internal#__printf_buffer_pad"("p" %"v0", "w" #32, "l" %"v1434")
          => goto "L1429" };
        cap_blk{ @"L1429" [phi %"pr.75" : "w" = ("L1427" => #0, "L1413" => %"pr.74")]:
          => br %"pr.37" ? "L1435" : "L1436" };
        cap_blk{ @"L1435":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #45)
          => goto "L1437" };
        cap_blk{ @"L1436":
          => br %"pr.67" ? "L1440" : "L1441" };
        cap_blk{ @"L1440":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #43)
          => goto "L1437" };
        cap_blk{ @"L1441":
          => br %"pr.62" ? "L1445" : "L1437" };
        cap_blk{ @"L1445":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #32)
          => goto "L1437" };
        cap_blk{ @"L1437":
          => br %"v1385" ? "L1455" : "L1456" };
        cap_blk{ @"L1455":
          %"v1458" : "w" = op "cmp"("ne", "w") %"pr.59", #0
          => goto "L1456" };
        cap_blk{ @"L1456" [phi %"v1459" : "w" = ("L1437" => #0, "L1455" => %"v1458")]:
          => br %"v1459" ? "L1460" : "L1461" };
        cap_blk{ @"L1460":
          %"v1463" : "w" = op "cmp"("eq", "w") %"pr.47", #16
          => br %"v1463" ? "L1461" : "L1464" };
        cap_blk{ @"L1464":
          %"v1467" : "w" = op "cmp"("eq", "w") %"pr.47", #2
          => goto "L1461" };
        cap_blk{ @"L1461" [phi %"v1471" : "w" = ("L1456" => #0, "L1460" => #1, "L1464" => %"v1467")]:
          => br %"v1471" ? "L1450" : "L1452" }
  ].
