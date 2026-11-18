(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
From Glibc Require Import FormatterCode07 FormatterCode08 FormatterCode09.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_10 : list term :=
  [
    cap_fn{ "local" "glibc_vfprintf_internal#printf_positional" [param "p" %"v0"; param "p" %"v2"; param "w" %"v4"; param "p" %"v6"; param "p" %"v8"; param "w" %"v10"; param "p" %"v12"; param "p" %"v14"; param "w" %"v16"; param "p" %"v18"; param "p" %"v20"; param "w" %"v22"] -> "void"
      blocks (formatter_blocks_07 ++ formatter_blocks_08 ++ formatter_blocks_09) };
    cap_fn{ "local" "glibc_vfprintf_internal#printf_unknown" [param "p" %"v0"; param "p" %"v2"] -> "void"
      {
        @"start":
          %"v4" : "p" = op "alloc"(int 4) #12;
          %"v7" = %"v4" +p #12;
          %"iw_1.v8" = %"v0" +p #8;
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_1.v8";
          %"iw_1.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"iw_1.v11" = %"v0" +p #16;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"iw_1.v11";
          %"iw_1.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"iw_1.v13" : "l" = "ptoi" %"iw_1.v9";
          %"iw_1.v14" : "l" = "ptoi" %"iw_1.v12";
          %"iw_1.v15" : "w" = op "cmp"("ne", "l") %"iw_1.v13", %"iw_1.v14"
          => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
        @"iw_1.L4":
          %"iw_1.v17" = %"v0" +p #8;
          %"iw_1.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"iw_1.v19" = %"iw_1.v18" +p #1;
          %"chk3" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_1.v17";
          store.ptr [%"chk3" + 0] <- %"iw_1.v19";
          %"chk4" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_1.v18";
          store "b" [%"chk4" + 0] <- #37
          => goto "iw_1.join";
        @"iw_1.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #37)
          => goto "iw_1.join";
        @"iw_1.join":
          %"v14" = %"v2" +p #12;
          %"chk5" : "a" = op "check"(int 0, int 4, "read", int 1) %"v14";
          %"v15" : "w" = op "raw_load"("uw", int 0) %"chk5";
          %"v16" : "w" = "shl" %"v15", #28;
          %"v17" : "w" = "shr" %"v16", #31
          => br %"v17" ? "iw_2.start" : "L12";
        @"iw_2.start":
          %"iw_2.v8" = %"v0" +p #8;
          %"chk6" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"iw_2.v8";
          %"iw_2.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"iw_2.v11" = %"v0" +p #16;
          %"chk7" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"iw_2.v11";
          %"iw_2.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"iw_2.v13" : "l" = "ptoi" %"iw_2.v9";
          %"iw_2.v14" : "l" = "ptoi" %"iw_2.v12";
          %"iw_2.v15" : "w" = op "cmp"("ne", "l") %"iw_2.v13", %"iw_2.v14"
          => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
        @"iw_2.L4":
          %"iw_2.v17" = %"v0" +p #8;
          %"iw_2.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"iw_2.v19" = %"iw_2.v18" +p #1;
          %"chk9" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_2.v17";
          store.ptr [%"chk9" + 0] <- %"iw_2.v19";
          %"chk10" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_2.v18";
          store "b" [%"chk10" + 0] <- #35
          => goto "L12";
        @"iw_2.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #35)
          => goto "L12";
        @"L12":
          %"v23" = %"v2" +p #12;
          %"chk11" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk5", %"v23";
          %"v24" : "w" = op "raw_load"("uw", int 0) %"chk11";
          %"v25" : "w" = "shl" %"v24", #24;
          %"v26" : "w" = "shr" %"v25", #31
          => br %"v26" ? "iw_3.start" : "L21";
        @"iw_3.start":
          %"iw_3.v8" = %"v0" +p #8;
          %"chk12" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"iw_3.v8";
          %"iw_3.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk12";
          %"iw_3.v11" = %"v0" +p #16;
          %"chk13" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"iw_3.v11";
          %"iw_3.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk13";
          %"iw_3.v13" : "l" = "ptoi" %"iw_3.v9";
          %"iw_3.v14" : "l" = "ptoi" %"iw_3.v12";
          %"iw_3.v15" : "w" = op "cmp"("ne", "l") %"iw_3.v13", %"iw_3.v14"
          => br %"iw_3.v15" ? "iw_3.L4" : "iw_3.L5";
        @"iw_3.L4":
          %"iw_3.v17" = %"v0" +p #8;
          %"iw_3.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk12";
          %"iw_3.v19" = %"iw_3.v18" +p #1;
          %"chk15" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_3.v17";
          store.ptr [%"chk15" + 0] <- %"iw_3.v19";
          %"chk16" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_3.v18";
          store "b" [%"chk16" + 0] <- #39
          => goto "L21";
        @"iw_3.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #39)
          => goto "L21";
        @"L21":
          %"v32" = %"v2" +p #12;
          %"chk17" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk5", %"v32";
          %"v33" : "w" = op "raw_load"("uw", int 0) %"chk17";
          %"v34" : "w" = "shl" %"v33", #25;
          %"v35" : "w" = "shr" %"v34", #31
          => br %"v35" ? "iw_4.start" : "L29";
        @"iw_4.start":
          %"iw_4.v8" = %"v0" +p #8;
          %"chk18" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"iw_4.v8";
          %"iw_4.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk18";
          %"iw_4.v11" = %"v0" +p #16;
          %"chk19" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"iw_4.v11";
          %"iw_4.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"iw_4.v13" : "l" = "ptoi" %"iw_4.v9";
          %"iw_4.v14" : "l" = "ptoi" %"iw_4.v12";
          %"iw_4.v15" : "w" = op "cmp"("ne", "l") %"iw_4.v13", %"iw_4.v14"
          => br %"iw_4.v15" ? "iw_4.L4" : "iw_4.L5";
        @"iw_4.L4":
          %"iw_4.v17" = %"v0" +p #8;
          %"iw_4.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk18";
          %"iw_4.v19" = %"iw_4.v18" +p #1;
          %"chk21" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_4.v17";
          store.ptr [%"chk21" + 0] <- %"iw_4.v19";
          %"chk22" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_4.v18";
          store "b" [%"chk22" + 0] <- #43
          => goto "L30";
        @"iw_4.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #43)
          => goto "L30";
        @"L29":
          %"v41" = %"v2" +p #12;
          %"v42" : "w" = op "raw_load"("uw", int 0) %"chk17";
          %"v43" : "w" = "shl" %"v42", #27;
          %"v44" : "w" = "shr" %"v43", #31
          => br %"v44" ? "iw_5.start" : "L30";
        @"iw_5.start":
          %"iw_5.v8" = %"v0" +p #8;
          %"chk24" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"iw_5.v8";
          %"iw_5.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          %"iw_5.v11" = %"v0" +p #16;
          %"chk25" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"iw_5.v11";
          %"iw_5.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk25";
          %"iw_5.v13" : "l" = "ptoi" %"iw_5.v9";
          %"iw_5.v14" : "l" = "ptoi" %"iw_5.v12";
          %"iw_5.v15" : "w" = op "cmp"("ne", "l") %"iw_5.v13", %"iw_5.v14"
          => br %"iw_5.v15" ? "iw_5.L4" : "iw_5.L5";
        @"iw_5.L4":
          %"iw_5.v17" = %"v0" +p #8;
          %"iw_5.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          %"iw_5.v19" = %"iw_5.v18" +p #1;
          %"chk27" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_5.v17";
          store.ptr [%"chk27" + 0] <- %"iw_5.v19";
          %"chk28" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_5.v18";
          store "b" [%"chk28" + 0] <- #32
          => goto "L30";
        @"iw_5.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #32)
          => goto "L30";
        @"L30":
          %"v50" = %"v2" +p #12;
          %"chk29" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk5", %"v50";
          %"v51" : "w" = op "raw_load"("uw", int 0) %"chk29";
          %"v52" : "w" = "shl" %"v51", #26;
          %"v53" : "w" = "shr" %"v52", #31
          => br %"v53" ? "iw_6.start" : "L48";
        @"iw_6.start":
          %"iw_6.v8" = %"v0" +p #8;
          %"chk30" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"iw_6.v8";
          %"iw_6.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk30";
          %"iw_6.v11" = %"v0" +p #16;
          %"chk31" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk1", %"iw_6.v11";
          %"iw_6.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk31";
          %"iw_6.v13" : "l" = "ptoi" %"iw_6.v9";
          %"iw_6.v14" : "l" = "ptoi" %"iw_6.v12";
          %"iw_6.v15" : "w" = op "cmp"("ne", "l") %"iw_6.v13", %"iw_6.v14"
          => br %"iw_6.v15" ? "iw_6.L4" : "iw_6.L5";
        @"iw_6.L4":
          %"iw_6.v17" = %"v0" +p #8;
          %"iw_6.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk30";
          %"iw_6.v19" = %"iw_6.v18" +p #1;
          %"chk33" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"iw_6.v17";
          store.ptr [%"chk33" + 0] <- %"iw_6.v19";
          %"chk34" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_6.v18";
          store "b" [%"chk34" + 0] <- #45
          => goto "L48";
        @"iw_6.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" #45)
          => goto "L48";
        @"L48":
          %"v59" = %"v2" +p #16;
          %"chk35" : "a" = op "half_check"("upper", int 0, int 4, "read", int 1) %"chk5", %"v59";
          %"v60" : "w" = op "raw_load"("sw", int 0) %"chk35";
          %"v61" : "w" = op "cmp"("eq", "w") %"v60", #48
          => br %"v61" ? "L55" : "L57";
        @"L55":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #48)
          => goto "L57";
        @"L57":
          %"v67" = %"v2" +p #12;
          %"chk36" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk5", %"v67";
          %"v68" : "w" = op "raw_load"("uw", int 0) %"chk36";
          %"v69" : "w" = "shl" %"v68", #20;
          %"v70" : "w" = "shr" %"v69", #31
          => br %"v70" ? "L63" : "L65";
        @"L63":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #73)
          => goto "L65";
        @"L65":
          %"v76" = %"v2" +p #4;
          %"chk37" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk5", %"v76";
          %"v77" : "w" = op "raw_load"("sw", int 0) %"chk37";
          %"v78" : "w" = op "cmp"("ne", "w") %"v77", #0
          => br %"v78" ? "L72" : "L74";
        @"L72":
          %"v80" = %"v2" +p #4;
          %"v81" : "w" = op "raw_load"("sw", int 0) %"chk37";
          %"v82" : "l" = op "ext"("sw") %"v81";
          call %"v84" : "p" = $"_itoa_word"("l" %"v82", "p" %"v7", "w" #10, "w" #0)
          => goto "L85";
        @"L85" [phi %"pr.2" : "p" = ("L72" => %"v84", "L86" => %"v95")]:
          %"v90" : "l" = "ptoi" %"pr.2";
          %"v91" : "l" = "ptoi" %"v7";
          %"v92" : "w" = op "cmp"("ult", "l") %"v90", %"v91"
          => br %"v92" ? "L86" : "L74";
        @"L86":
          %"v95" = %"pr.2" +p #1;
          %"chk39" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.2";
          %"v96" : "w" = op "raw_load"("sb", int 0) %"chk39";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v96")
          => goto poll "L85";
        @"L74":
          %"chk40" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk5", %"v2";
          %"v101" : "w" = op "raw_load"("sw", int 0) %"chk40";
          %"v103" : "w" = op "cmp"("ne", "w") %"v101", #4294967295
          => br %"v103" ? "L97" : "L99";
        @"L97":
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" #46);
          %"chk41" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk40", %"v2";
          %"v106" : "w" = op "raw_load"("sw", int 0) %"chk41";
          %"v107" : "l" = op "ext"("sw") %"v106";
          call %"v109" : "p" = $"_itoa_word"("l" %"v107", "p" %"v7", "w" #10, "w" #0)
          => goto "L110";
        @"L110" [phi %"pr.1" : "p" = ("L111" => %"v120", "L97" => %"v109")]:
          %"v115" : "l" = "ptoi" %"pr.1";
          %"v116" : "l" = "ptoi" %"v7";
          %"v117" : "w" = op "cmp"("ult", "l") %"v115", %"v116"
          => br %"v117" ? "L111" : "L99";
        @"L111":
          %"v120" = %"pr.1" +p #1;
          %"chk42" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.1";
          %"v121" : "w" = op "raw_load"("sb", int 0) %"chk42";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v121")
          => goto poll "L110";
        @"L99":
          %"v126" = %"v2" +p #8;
          %"chk43" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk5", %"v126";
          %"v127" : "w" = op "raw_load"("sw", int 0) %"chk43";
          %"v128" : "w" = op "cmp"("ne", "w") %"v127", #0
          => br %"v128" ? "L122" : "L124";
        @"L122":
          %"v131" = %"v2" +p #8;
          %"v132" : "w" = op "raw_load"("sw", int 0) %"chk43";
          %"v133" : "w" = op "ext"("sb") %"v132";
          call void $"glibc_vfprintf_internal#__printf_buffer_putc"("p" %"v0", "w" %"v133")
          => goto "L124";
        @"L124":
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#group_number" [param "p" %"v0"; param "p" %"v2"; param "p" %"v4"; param "p" %"v6"; param "p" %"v8"; param "w" %"v10"] -> "void"
      {
        @"start":
          %"v15" : "w" = op "ext"("ub") %"v10";
          %"v16" : "w" = op "cmp"("eq", "w") %"v15", #0
          => br %"v16" ? "L19" : "L43";
        @"L19" [phi %"pr.1" : "p" = ("L21" => %"v40", "start" => %"v4")]:
          %"v25" : "l" = "ptoi" %"pr.1";
          %"v26" : "l" = "ptoi" %"v6";
          %"v27" : "w" = op "cmp"("ne", "l") %"v25", %"v26"
          => br %"v27" ? "L20" : "L14";
        @"L20":
          call %"v32" : "w" = $"__grouping_iterator_next"("p" %"v2");
          %"v33" : "w" = op "ext"("ub") %"v32"
          => br %"v33" ? "iw_1.start" : "L30";
        @"iw_1.start":
          call void $"__printf_buffer_puts_1"("p" %"v0", "p" %"v8")
          => goto "L30";
        @"L30":
          %"chk0" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.1";
          %"v38" : "w" = op "raw_load"("sb", int 0) %"chk0";
          %"iw_2.v8" = %"v0" +p #8;
          %"chk1" : "a" = op "check"(int 0, int 8, "read", int 8) %"iw_2.v8";
          %"iw_2.v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"iw_2.v11" = %"v0" +p #16;
          %"chk2" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk1", %"iw_2.v11";
          %"iw_2.v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          %"iw_2.v13" : "l" = "ptoi" %"iw_2.v9";
          %"iw_2.v14" : "l" = "ptoi" %"iw_2.v12";
          %"iw_2.v15" : "w" = op "cmp"("ne", "l") %"iw_2.v13", %"iw_2.v14"
          => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
        @"iw_2.L4":
          %"iw_2.v17" = %"v0" +p #8;
          %"iw_2.v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"iw_2.v19" = %"iw_2.v18" +p #1;
          %"chk4" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk1", %"iw_2.v17";
          store.ptr [%"chk4" + 0] <- %"iw_2.v19";
          %"chk5" : "a" = op "check"(int 0, int 1, "write", int 1) %"iw_2.v18";
          store "b" [%"chk5" + 0] <- %"v38"
          => goto "L21";
        @"iw_2.L5":
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" %"v38")
          => goto "L21";
        @"L21":
          %"v40" = %"pr.1" +p #1
          => goto poll "L19";
        @"L43" [phi %"pr.2" : "p" = ("L54" => %"v78", "start" => %"v4")]:
          %"v49" : "l" = "ptoi" %"pr.2";
          %"v50" : "l" = "ptoi" %"v6";
          %"v51" : "w" = op "cmp"("ne", "l") %"v49", %"v50"
          => br %"v51" ? "L44" : "L14";
        @"L44":
          call %"v56" : "w" = $"__grouping_iterator_next"("p" %"v2");
          %"v57" : "w" = op "ext"("ub") %"v56"
          => br %"v57" ? "iw_3.start" : "L54";
        @"iw_3.start":
          call void $"__printf_buffer_puts_1"("p" %"v0", "p" %"v8")
          => goto "L54";
        @"L54":
          %"chk6" : "a" = op "check"(int 0, int 1, "read", int 1) %"pr.2";
          %"v62" : "w" = op "raw_load"("sb", int 0) %"chk6";
          %"v63" : "w" = "sub" %"v62", #48;
          %"v65" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk7" : "a" = op "check"(int 0, int 8, "read", int 8) %"v65";
          %"v66" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk7";
          %"chk8" : "a" = op "check"(int 0, int 8, "read", int 8) %"v66";
          %"v68" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk8";
          %"v69" = %"v68" +p #56;
          %"v71" : "w" = "add" %"v63", #41;
          %"v72" : "w" = "and" %"v71", #65535;
          %"v73" : "l" = op "ext"("sw") %"v72";
          %"v74" : "l" = "shl" %"v73", #3;
          %"v75" = %"v69" +p %"v74";
          %"chk9" : "a" = op "check"(int 0, int 8, "read", int 8) %"v75";
          %"v76" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk9";
          call void $"__printf_buffer_puts_1"("p" %"v0", "p" %"v76");
          %"v78" = %"pr.2" +p #1
          => goto poll "L43";
        @"L14":
          => ret void
      } }
  ].
