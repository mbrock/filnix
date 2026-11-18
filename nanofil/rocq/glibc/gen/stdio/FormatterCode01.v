(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_01 : list term :=
  [
    cap{ op "data"("formatter_roots", op "ro"("export"), int 8, [op "item"("p", op "sym"("__vfprintf_internal", int 0))]) };
    cap_fn{ "local" "glibc_vfprintf_internal#read_int" [param "p" %"v0"] -> "w"
      {
        @"start":
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v0";
          %"v4" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"chk1" : "a" = op "check"(int 0, int 1, "read", int 1) %"v4";
          %"v5" : "w" = op "raw_load"("ub", int 0) %"chk1";
          %"v6" : "w" = "sub" %"v5", #48
          => goto "L7";
        @"L7" [phi %"pr.4" : "w" = ("start" => %"v6", "L16" => #4294967295, "L36" => %"v45", "L22" => #4294967295, "L8" => %"pr.4")]:
          %"chk2" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v0";
          %"v11" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          %"v12" = %"v11" +p #1;
          %"chk3" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"v0";
          store.ptr [%"chk3" + 0] <- %"v12";
          %"chk4" : "a" = op "check"(int 0, int 1, "read", int 1) %"v12";
          %"v13" : "w" = op "raw_load"("ub", int 0) %"chk4";
          %"v14" : "w" = "sub" %"v13", #48;
          %"v15" : "w" = op "cmp"("ult", "w") %"v14", #10
          => br %"v15" ? "L8" : "L9";
        @"L8":
          %"v20" : "w" = op "cmp"("sge", "w") %"pr.4", #0
          => br %"v20" ? "L16" : poll "L7";
        @"L16":
          %"v26" : "w" = op "cmp"("sgt", "w") %"pr.4", #214748364
          => br %"v26" ? poll "L7" : "L22";
        @"L22":
          %"chk5" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v0";
          %"v30" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk5";
          %"chk6" : "a" = op "check"(int 0, int 1, "read", int 1) %"v30";
          %"v31" : "w" = op "raw_load"("ub", int 0) %"chk6";
          %"v32" : "w" = "sub" %"v31", #48;
          %"v34" : "w" = "mul" %"pr.4", #10;
          %"v39" : "w" = "sub" #2147483647, %"v32";
          %"v41" : "w" = op "cmp"("slt", "w") %"v39", %"v34"
          => br %"v41" ? poll "L7" : "L36";
        @"L36":
          %"v45" : "w" = "add" %"v34", %"v32"
          => goto poll "L7";
        @"L9":
          => ret %"pr.4"
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#outstring_converted_wide_string" [param "p" %"v0"; param "p" %"v2"; param "w" %"v4"; param "w" %"v6"; param "w" %"v8"] -> "void"
      {
        @"start":
          %"v3" : "p" = op "alloc"(int 8) #8;
          %"v10" : "p" = op "alloc"(int 4) #256;
          %"v22" : "p" = op "alloc"(int 4) #8;
          %"v24" : "p" = op "alloc"(int 8) #8;
          %"v94" : "p" = op "alloc"(int 4) #8;
          %"chk0" : "a" = op "check"(int 0, int 8, "write", int 8) %"v3";
          store.ptr [%"chk0" + 0] <- %"v2";
          %"v15" : "w" = op "cmp"("sgt", "w") %"v6", #0
          => br %"v15" ? "L16" : "L17";
        @"L16":
          %"v18" : "w" = op "ext"("ub") %"v8";
          %"v19" : "w" = op "cmp"("eq", "w") %"v18", #0
          => goto "L17";
        @"L17" [phi %"v21" : "w" = ("start" => #0, "L16" => %"v19")]:
          => br %"v21" ? "L11" : "L13";
        @"L11":
          %"chk1" : "a" = op "check"(int 0, int 4, "write", int 1) %"v22";
          store "w" [%"chk1" + 0] <- #0;
          %"v23" = %"v22" +p #4;
          %"chk2" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk1", %"v23";
          store "w" [%"chk2" + 0] <- #0;
          store "w" [%"chk1" + 0] <- #0;
          %"chk4" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v3";
          %"v25" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk4";
          %"chk5" : "a" = op "check"(int 0, int 8, "write", int 8) %"v24";
          store.ptr [%"chk5" + 0] <- %"v25";
          %"v31" : "w" = op "cmp"("slt", "w") %"v4", #0
          => br %"v31" ? "L27" : "L28";
        @"L27":
          call %"v32" : "l" = $"__wcsrtombs"("p" #0, "p" %"v24", "l" #0, "p" %"v22")
          => goto "L29";
        @"L28":
          %"v35" : "l" = op "ext"("sw") %"v4"
          => goto "L36";
        @"L36" [phi %"pr.3" : "l" = ("L28" => %"v35", "L71" => %"v80"); phi %"pr.2" : "l" = ("L28" => #0, "L71" => %"v77")]:
          %"v40" : "w" = op "cmp"("ugt", "l") %"pr.3", #0
          => br %"v40" ? "L41" : "L42";
        @"L41":
          %"chk6" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk5", %"v24";
          %"v43" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk6";
          %"v44" : "l" = "ptoi" %"v43";
          %"v45" : "l" = "ptoi" #0;
          %"v46" : "w" = op "cmp"("ne", "l") %"v44", %"v45"
          => goto "L42";
        @"L42" [phi %"v48" : "w" = ("L36" => #0, "L41" => %"v46")]:
          => br %"v48" ? "L37" : "L29";
        @"L37":
          %"v55" : "w" = op "cmp"("ult", "l") %"pr.3", #256
          => br %"v55" ? "L52" : "L51";
        @"L51":
          => goto "L52";
        @"L52" [phi %"pr.4" : "l" = ("L51" => #256, "L37" => %"pr.3")]:
          call %"v59" : "l" = $"__wcsrtombs"("p" %"v10", "p" %"v24", "l" %"pr.4", "p" %"v22");
          %"v66" : "w" = op "cmp"("eq", "l") %"v59", #18446744073709551615
          => br %"v66" ? "iw_1.start" : "L62";
        @"iw_1.start":
          %"iw_1.v3" = %"v0" +p #32;
          %"chk7" : "a" = op "check"(int 0, int 4, "write", int 1) %"iw_1.v3";
          store "w" [%"chk7" + 0] <- #0
          => ret void;
        @"L62":
          %"v73" : "w" = op "cmp"("eq", "l") %"v59", #0
          => br %"v73" ? "L29" : "L71";
        @"L71":
          %"v77" : "l" = "add" %"pr.2", %"v59";
          %"v80" : "l" = "sub" %"pr.3", %"v59"
          => goto poll "L36";
        @"L29" [phi %"pr.1" : "l" = ("L27" => %"v32", "L42" => %"pr.2", "L62" => %"pr.2")]:
          %"v84" : "l" = op "ext"("sw") %"v6";
          %"v85" : "l" = "sub" %"v84", %"pr.1";
          %"iw_2.v10" : "w" = op "cmp"("sgt", "l") %"v85", #0
          => br %"iw_2.v10" ? "iw_2.L6" : "iw_3.start";
        @"iw_2.L6":
          call void $"__printf_buffer_pad_1"("p" %"v0", "w" #32, "l" %"v85")
          => goto "iw_3.start";
        @"iw_3.start":
          %"iw_3.v3" = %"v0" +p #32;
          %"chk8" : "a" = op "check"(int 0, int 4, "read", int 1) %"iw_3.v3";
          %"iw_3.v4" : "w" = op "raw_load"("uw", int 0) %"chk8";
          %"iw_3.v5" : "w" = op "cmp"("eq", "w") %"iw_3.v4", #0
          => br %"iw_3.v5" ? "L86" : "L13";
        @"L86":
          => ret void;
        @"L13":
          %"chk9" : "a" = op "check"(int 0, int 4, "write", int 1) %"v94";
          store "w" [%"chk9" + 0] <- #0;
          %"v95" = %"v94" +p #4;
          %"chk10" : "a" = op "half_check"("upper", int 0, int 4, "write", int 1) %"chk9", %"v95";
          store "w" [%"chk10" + 0] <- #0;
          store "w" [%"chk9" + 0] <- #0;
          %"v103" : "w" = op "cmp"("sge", "w") %"v4", #0
          => br %"v103" ? "L99" : "L106";
        @"L99":
          %"v105" : "l" = op "ext"("sw") %"v4"
          => goto "L106";
        @"L106" [phi %"pr.7" : "l" = ("L99" => %"v105", "L13" => #18446744073709551615, "L150" => %"v157", "L141" => %"pr.7"); phi %"pr.5" : "l" = ("L99" => #0, "L13" => #0, "L150" => %"v149", "L141" => %"v149")]:
          %"v110" : "w" = op "cmp"("ugt", "l") %"pr.7", #0
          => br %"v110" ? "L111" : "L112";
        @"L111":
          %"chk12" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk0", %"v3";
          %"v113" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk12";
          %"v114" : "l" = "ptoi" %"v113";
          %"v115" : "l" = "ptoi" #0;
          %"v116" : "w" = op "cmp"("ne", "l") %"v114", %"v115"
          => goto "L112";
        @"L112" [phi %"v118" : "w" = ("L106" => #0, "L111" => %"v116")]:
          => br %"v118" ? "L107" : "L108";
        @"L107":
          %"v125" : "w" = op "cmp"("ult", "l") %"pr.7", #256
          => br %"v125" ? "L122" : "L121";
        @"L121":
          => goto "L122";
        @"L122" [phi %"pr.9" : "l" = ("L121" => #256, "L107" => %"pr.7")]:
          call %"v129" : "l" = $"__wcsrtombs"("p" %"v10", "p" %"v3", "l" %"pr.9", "p" %"v94");
          %"v136" : "w" = op "cmp"("eq", "l") %"v129", #18446744073709551615
          => br %"v136" ? "iw_4.start" : "L132";
        @"iw_4.start":
          %"iw_4.v3" = %"v0" +p #32;
          %"chk13" : "a" = op "check"(int 0, int 4, "write", int 1) %"iw_4.v3";
          store "w" [%"chk13" + 0] <- #0
          => ret void;
        @"L132":
          %"v143" : "w" = op "cmp"("eq", "l") %"v129", #0
          => br %"v143" ? "L108" : "L141";
        @"L141":
          call void $"__printf_buffer_write"("p" %"v0", "p" %"v10", "l" %"v129");
          %"v149" : "l" = "add" %"pr.5", %"v129"
          => br %"v103" ? "L150" : poll "L106";
        @"L150":
          %"v157" : "l" = "sub" %"pr.7", %"v129"
          => goto poll "L106";
        @"L108":
          => br %"v15" ? "L163" : "L164";
        @"L163":
          %"v165" : "w" = op "ext"("ub") %"v8";
          %"v166" : "w" = op "cmp"("ne", "w") %"v165", #0
          => goto "L164";
        @"L164" [phi %"v167" : "w" = ("L108" => #0, "L163" => %"v166")]:
          => br %"v167" ? "L158" : "L160";
        @"L158":
          %"v171" : "l" = op "ext"("sw") %"v6";
          %"v172" : "l" = "sub" %"v171", %"pr.5";
          %"iw_5.v10" : "w" = op "cmp"("sgt", "l") %"v172", #0
          => br %"iw_5.v10" ? "iw_5.L6" : "L160";
        @"iw_5.L6":
          call void $"__printf_buffer_pad_1"("p" %"v0", "w" #32, "l" %"v172")
          => goto "L160";
        @"L160":
          => ret void
      } }
  ].
