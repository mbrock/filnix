(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These items retain their order in the linked module. *)
Definition formatter_items_11 : list term :=
  [
    cap_fn{ "export" "__vfprintf_internal" [param "p" %"v0"; param "p" %"v2"; param "p" %"v4"; param "w" %"v6"] -> "w"
      {
        @"start":
          %"v178" : "p" = op "alloc"(int 8) #176;
          %"v187" : "p" = op "alloc"(int 8) #32;
          %"v290" : "p" = op "alloc"(int 8) #176;
          %"v30" = %"v0" +p #192;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v30";
          %"v31" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v32" : "w" = op "cmp"("eq", "w") %"v31", #0
          => br %"v32" ? "L26" : "L28";
        @"L26":
          %"v34" = %"v0" +p #192;
          %"chk1" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk0", %"v34";
          store "w" [%"chk1" + 0] <- #4294967295
          => goto "L28";
        @"L28":
          %"v37" = %"v0" +p #192;
          %"v38" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v61" : "w" = op "cmp"("ne", "w") %"v38", #4294967295
          => br %"v61" ? "L8" : "L71";
        @"L8":
          => ret #4294967295;
        @"L71":
          %"chk3" : "a" = op "half_check"("lower", int 0, int 4, "read", int 1) %"chk0", %"v0";
          %"v76" : "w" = op "raw_load"("sw", int 0) %"chk3";
          %"v77" : "w" = "and" %"v76", #8
          => br %"v77" ? "L72" : "L74";
        @"L72":
          %"v79" : "w" = op "raw_load"("sw", int 0) %"chk3";
          %"v80" : "w" = "or" %"v79", #32;
          %"chk5" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk3", %"v0";
          store "w" [%"chk5" + 0] <- %"v80";
          %"v81" : "p" = "copy" $"__libc_errno";
          %"chk6" : "a" = op "check"(int 0, int 4, "write", int 1) %"v81";
          store "w" [%"chk6" + 0] <- #9
          => ret #4294967295;
        @"L74":
          %"v88" : "l" = "ptoi" %"v2";
          %"v89" : "l" = "ptoi" #0;
          %"v90" : "w" = op "cmp"("eq", "l") %"v88", %"v89"
          => br %"v90" ? "L84" : "L107";
        @"L84":
          %"v91" : "p" = "copy" $"__libc_errno";
          %"chk7" : "a" = op "check"(int 0, int 4, "write", int 1) %"v91";
          store "w" [%"chk7" + 0] <- #22
          => ret #4294967295;
        @"L107":
          %"v121" = %"v0" +p #192;
          %"v122" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v123" : "w" = op "cmp"("eq", "w") %"v122", #0
          => br %"v123" ? "L117" : "L119";
        @"L117":
          %"v125" = %"v0" +p #192;
          %"chk9" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk0", %"v125";
          store "w" [%"chk9" + 0] <- #4294967295
          => goto "L119";
        @"L119":
          %"v128" = %"v0" +p #192;
          %"v129" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v162" : "w" = op "cmp"("ne", "w") %"v129", #4294967295
          => br %"v162" ? "L94" : "L96";
        @"L94":
          => ret #4294967295;
        @"L96":
          %"v171" = %"v0" +p #116;
          %"v172" : "w" = op "raw_load"("sw", int (-76)) %"chk0";
          %"v173" : "w" = "shl" %"v172", #8;
          %"v174" : "w" = "sar" %"v173", #8;
          %"v175" : "w" = "and" %"v174", #128;
          %"v177" : "w" = op "cmp"("eq", "w") %"v175", #0
          => br %"v177" ? "L167" : "L169";
        @"L167":
          call void $"__printf_buffer_to_file_init"("p" %"v178", "p" %"v0");
          call void $"__printf_buffer"("p" %"v178", "p" %"v2", "p" %"v4", "w" %"v6");
          call %"v183" : "w" = $"__printf_buffer_to_file_done"("p" %"v178")
          => ret %"v183";
        @"L169":
          %"v189" : "p" = "copy" $"_IO_funlockfile";
          %"v190" = %"v187" +p #8;
          %"chk12" : "a" = op "check"(int 0, int 8, "write", int 8) %"v190";
          store.ptr [%"chk12" + 0] <- %"v0";
          %"chk13" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk3", %"v0";
          %"v196" : "w" = op "raw_load"("sw", int 0) %"chk13";
          %"v197" : "w" = "and" %"v196", #32768;
          %"v198" : "w" = op "cmp"("eq", "w") %"v197", #0
          => br %"v198" ? "L192" : "L194";
        @"L192":
          %"chk14" : "a" = op "half_check"("lower", int 0, int 8, "write", int 8) %"chk12", %"v187";
          store.ptr [%"chk14" + 0] <- %"v189";
          call void $"__GI___libc_cleanup_push_defer"("p" %"v187")
          => goto "L194";
        @"L194" [phi %"pr.5" : "w" = ("L192" => #1, "L169" => #0)]:
          %"chk15" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk3", %"v0";
          %"v206" : "w" = op "raw_load"("sw", int 0) %"chk15";
          %"v207" : "w" = "and" %"v206", #32768;
          %"v208" : "w" = op "cmp"("eq", "w") %"v207", #0
          => br %"v208" ? "L209" : "L204";
        @"L209":
          call %"v213" : "p" = $"zthread_self_cookie"();
          %"v217" : "p" = "copy" $"__libc_single_threaded_internal";
          %"chk16" : "a" = op "check"(int 0, int 1, "read", int 1) %"v217";
          %"v218" : "w" = op "raw_load"("sb", int 0) %"chk16";
          %"v219" : "w" = op "cmp"("ne", "w") %"v218", #0
          => br %"v219" ? "L220" : "L221";
        @"L220":
          %"v223" = %"v0" +p #136;
          %"chk17" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v223";
          %"v224" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk17";
          %"v225" = %"v224" +p #8;
          %"chk18" : "a" = op "check"(int 0, int 8, "read", int 8) %"v225";
          %"v226" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk18";
          %"v227" : "l" = "ptoi" %"v226";
          %"v229" : "w" = op "cmp"("eq", "l") %"v227", %"v89"
          => goto "L221";
        @"L221" [phi %"v231" : "w" = ("L209" => #0, "L220" => %"v229")]:
          => br %"v231" ? "L214" : "L215";
        @"L214":
          %"v233" = %"v0" +p #136;
          %"chk19" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v233";
          %"v234" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"chk20" : "a" = op "check"(int 0, int 4, "write", int 1) %"v234";
          store "w" [%"chk20" + 0] <- #1;
          %"v237" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk19";
          %"v238" = %"v237" +p #8;
          %"chk22" : "a" = op "check"(int 0, int 8, "write", int 8) %"v238";
          store.ptr [%"chk22" + 0] <- %"v213"
          => goto "L204";
        @"L215":
          %"v244" = %"v0" +p #136;
          %"chk23" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v244";
          %"v245" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk23";
          %"v246" = %"v245" +p #8;
          %"chk24" : "a" = op "check"(int 0, int 8, "read", int 8) %"v246";
          %"v247" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk24";
          %"v249" : "l" = "ptoi" %"v247";
          %"v250" : "l" = "ptoi" %"v213";
          %"v251" : "w" = op "cmp"("ne", "l") %"v249", %"v250"
          => br %"v251" ? "L240" : "L241";
        @"L240":
          %"v254" = %"v0" +p #136;
          %"v255" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk23";
          %"chk26" : "a" = op "check"(int 0, int 4, "write", int 4) %"v255";
          %"v262" : "w" = op "raw_cas"("sw", int 0) %"chk26", #0, #1;
          %"v263" : "w" = op "cmp"("eq", "w") %"v262", #0
          => br %"v263" ? "L265" : "L264";
        @"L264":
          => goto "L265";
        @"L265":
          %"v266" : "w" = op "cmp"("ne", "w") %"v262", #0
          => br %"v266" ? "L269" : "L258";
        @"L269":
          call void $"__GI___lll_lock_wait_private"("p" %"v255")
          => goto "L258";
        @"L258":
          %"v280" = %"v0" +p #136;
          %"chk27" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk23", %"v280";
          %"v281" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk27";
          %"v282" = %"v281" +p #8;
          %"chk28" : "a" = op "check"(int 0, int 8, "write", int 8) %"v282";
          store.ptr [%"chk28" + 0] <- %"v213"
          => goto "L204";
        @"L241":
          %"v285" = %"v0" +p #136;
          %"v286" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk23";
          %"v287" = %"v286" +p #4;
          %"chk30" : "a" = op "check"(int 0, int 4, "read", int 1) %"v287";
          %"v288" : "w" = op "raw_load"("sw", int 0) %"chk30";
          %"v289" : "w" = "add" %"v288", #1;
          %"chk31" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk30", %"v287";
          store "w" [%"chk31" + 0] <- %"v289"
          => goto "L204";
        @"L204":
          call void $"__printf_buffer_to_file_init"("p" %"v290", "p" %"v0");
          call void $"__printf_buffer"("p" %"v290", "p" %"v2", "p" %"v4", "w" %"v6");
          call %"v295" : "w" = $"__printf_buffer_to_file_done"("p" %"v290");
          %"chk32" : "a" = op "renew"(int 0, int 4, "read", int 1) %"chk3", %"v0";
          %"v300" : "w" = op "raw_load"("sw", int 0) %"chk32";
          %"v301" : "w" = "and" %"v300", #32768;
          %"v302" : "w" = op "cmp"("eq", "w") %"v301", #0
          => br %"v302" ? "L303" : "L298";
        @"L303":
          %"v309" : "p" = "copy" $"__libc_single_threaded_internal";
          %"chk33" : "a" = op "check"(int 0, int 1, "read", int 1) %"v309";
          %"v310" : "w" = op "raw_load"("sb", int 0) %"chk33";
          %"v311" : "w" = op "cmp"("ne", "w") %"v310", #0
          => br %"v311" ? "L312" : "L313";
        @"L312":
          %"v315" = %"v0" +p #136;
          %"chk34" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v315";
          %"v316" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk34";
          %"v317" = %"v316" +p #4;
          %"chk35" : "a" = op "check"(int 0, int 4, "read", int 1) %"v317";
          %"v318" : "w" = op "raw_load"("sw", int 0) %"chk35";
          %"v319" : "w" = op "cmp"("eq", "w") %"v318", #0
          => goto "L313";
        @"L313" [phi %"v321" : "w" = ("L303" => #0, "L312" => %"v319")]:
          => br %"v321" ? "L306" : "L307";
        @"L306":
          %"v323" = %"v0" +p #136;
          %"chk36" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v323";
          %"v324" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk36";
          %"v325" = %"v324" +p #8;
          %"chk37" : "a" = op "check"(int 0, int 8, "write", int 8) %"v325";
          store.ptr [%"chk37" + 0] <- #0;
          %"chk38" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk36", %"v323";
          %"v328" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk38";
          %"chk39" : "a" = op "check"(int 0, int 4, "write", int 1) %"v328";
          store "w" [%"chk39" + 0] <- #0
          => goto "L298";
        @"L307":
          %"v333" = %"v0" +p #136;
          %"chk40" : "a" = op "half_check"("lower", int 0, int 8, "read", int 8) %"chk0", %"v333";
          %"v334" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"v335" = %"v334" +p #4;
          %"chk41" : "a" = op "check"(int 0, int 4, "read", int 1) %"v335";
          %"v336" : "w" = op "raw_load"("sw", int 0) %"chk41";
          %"v337" : "w" = op "cmp"("eq", "w") %"v336", #0
          => br %"v337" ? "L329" : "L330";
        @"L329":
          %"v339" = %"v0" +p #136;
          %"v340" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"v341" = %"v340" +p #8;
          %"chk43" : "a" = op "check"(int 0, int 8, "write", int 8) %"v341";
          store.ptr [%"chk43" + 0] <- #0;
          %"chk44" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk40", %"v339";
          %"v345" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk44";
          %"chk45" : "a" = op "check"(int 0, int 4, "read", int 1) %"v345";
          %"v349" : "w" = op "raw_load"("sw", int 0) %"chk45"
          => goto "L350";
        @"L350" [phi %"v352" : "w" = ("L329" => %"v349", "L350" => %"v353")]:
          %"chk46" : "a" = op "half_check"("lower", int 0, int 4, "write", int 4) %"chk45", %"v345";
          %"v353" : "w" = op "raw_cas"("sw", int 0) %"chk46", %"v352", #0;
          %"v354" : "w" = op "cmp"("eq", "w") %"v353", %"v352"
          => br %"v354" ? "L351" : poll "L350";
        @"L351":
          %"v359" : "w" = op "cmp"("sgt", "w") %"v352", #1
          => br %"v359" ? "L362" : "L298";
        @"L362":
          call void $"__GI___lll_lock_wake_private"("p" %"v345")
          => goto "L298";
        @"L330":
          %"v374" = %"v0" +p #136;
          %"v375" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk40";
          %"v376" = %"v375" +p #4;
          %"chk48" : "a" = op "check"(int 0, int 4, "read", int 1) %"v376";
          %"v377" : "w" = op "raw_load"("sw", int 0) %"chk48";
          %"v378" : "w" = "sub" %"v377", #1;
          %"chk49" : "a" = op "renew"(int 0, int 4, "write", int 1) %"chk48", %"v376";
          store "w" [%"chk49" + 0] <- %"v378"
          => goto "L298";
        @"L298":
          => br %"pr.5" ? "L379" : "L385";
        @"L379":
          call void $"__GI___libc_cleanup_pop_restore"("p" %"v187")
          => goto "L385";
        @"L385":
          => ret %"v295"
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__find_specmb.gnu_inline" [param "p" %"v0"] -> "p"
      {
        @"start":
          call %"v3" : "p" = $"__GI___strchrnul"("p" %"v0", "w" #37)
          => ret %"v3"
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_has_failed" [param "p" %"v0"] -> "w"
      {
        @"start":
          %"v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v3";
          %"v4" : "w" = op "raw_load"("uw", int 0) %"chk0";
          %"v5" : "w" = op "cmp"("eq", "w") %"v4", #0
          => ret %"v5"
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_mark_failed" [param "p" %"v0"] -> "void"
      {
        @"start":
          %"v3" = %"v0" +p #32;
          %"chk0" : "a" = op "check"(int 0, int 4, "write", int 1) %"v3";
          store "w" [%"chk0" + 0] <- #0
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_pad" [param "p" %"v0"; param "w" %"v2"; param "l" %"v4"] -> "void"
      {
        @"start":
          %"v10" : "w" = op "cmp"("sgt", "l") %"v4", #0
          => br %"v10" ? "L6" : "L8";
        @"L6":
          %"v12" : "w" = op "ext"("sb") %"v2";
          call void $"__printf_buffer_pad_1"("p" %"v0", "w" %"v12", "l" %"v4")
          => goto "L8";
        @"L8":
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__printf_buffer_putc" [param "p" %"v0"; param "w" %"v2"] -> "void"
      {
        @"start":
          %"v8" = %"v0" +p #8;
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v8";
          %"v9" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v11" = %"v0" +p #16;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "read", int 8) %"chk0", %"v11";
          %"v12" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk1";
          %"v13" : "l" = "ptoi" %"v9";
          %"v14" : "l" = "ptoi" %"v12";
          %"v15" : "w" = op "cmp"("ne", "l") %"v13", %"v14"
          => br %"v15" ? "L4" : "L5";
        @"L4":
          %"v17" = %"v0" +p #8;
          %"v18" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v19" = %"v18" +p #1;
          %"chk3" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk0", %"v17";
          store.ptr [%"chk3" + 0] <- %"v19";
          %"v20" : "w" = op "ext"("sb") %"v2";
          %"chk4" : "a" = op "check"(int 0, int 1, "write", int 1) %"v18";
          store "b" [%"chk4" + 0] <- %"v20"
          => goto "L6";
        @"L5":
          %"v22" : "w" = op "ext"("sb") %"v2";
          call void $"__printf_buffer_putc_1"("p" %"v0", "w" %"v22")
          => goto "L6";
        @"L6":
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#__printf_fp_spec" [param "p" %"v0"; param "p" %"v2"; param "p" %"v4"] -> "void"
      {
        @"start":
          %"v10" = %"v2" +p #8;
          %"chk0" : "a" = op "check"(int 0, int 4, "read", int 1) %"v10";
          %"v11" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v12" : "w" = op "cmp"("eq", "w") %"v11", #97
          => br %"v12" ? "L14" : "L13";
        @"L13":
          %"v16" = %"v2" +p #8;
          %"v17" : "w" = op "raw_load"("sw", int 0) %"chk0";
          %"v18" : "w" = op "cmp"("eq", "w") %"v17", #65
          => goto "L14";
        @"L14" [phi %"v20" : "w" = ("start" => #1, "L13" => %"v18")]:
          => br %"v20" ? "L6" : "L7";
        @"L6":
          %"v22" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk2" : "a" = op "check"(int 0, int 8, "read", int 8) %"v22";
          %"v23" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk2";
          call void $"__printf_fphex_l_buffer"("p" %"v0", "p" %"v23", "p" %"v2", "p" %"v4")
          => goto "L8";
        @"L7":
          %"v27" : "p" = "copy" $"__libc_tsd_LOCALE";
          %"chk3" : "a" = op "check"(int 0, int 8, "read", int 8) %"v27";
          %"v28" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk3";
          call void $"__printf_fp_l_buffer"("p" %"v0", "p" %"v28", "p" %"v2", "p" %"v4")
          => goto "L8";
        @"L8":
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#scratch_buffer_free" [param "p" %"v0"] -> "void"
      {
        @"start":
          %"chk0" : "a" = op "check"(int 0, int 8, "read", int 8) %"v0";
          %"v6" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          %"v8" = %"v0" +p #16;
          %"v9" : "l" = "ptoi" %"v6";
          %"v10" : "l" = "ptoi" %"v8";
          %"v11" : "w" = op "cmp"("ne", "l") %"v9", %"v10"
          => br %"v11" ? "L2" : "L4";
        @"L2":
          %"v13" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk0";
          call void $"free"("p" %"v13")
          => goto "L4";
        @"L4":
          => ret void
      } };
    cap_fn{ "local" "glibc_vfprintf_internal#scratch_buffer_init" [param "p" %"v0"] -> "void"
      {
        @"start":
          %"v4" = %"v0" +p #16;
          %"chk0" : "a" = op "check"(int 0, int 8, "write", int 8) %"v0";
          store.ptr [%"chk0" + 0] <- %"v4";
          %"v6" = %"v0" +p #8;
          %"chk1" : "a" = op "half_check"("upper", int 0, int 8, "write", int 1) %"chk0", %"v6";
          store "l" [%"chk1" + 0] <- #1024
          => ret void
      } };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step0_jumps.277", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #1); op "item"("w", #2); op "item"("w", #3); op "item"("w", #4); op "item"("w", #5); op "item"("w", #6); op "item"("w", #7); op "item"("w", #8); op "item"("w", #9); op "item"("w", #10); op "item"("w", #11); op "item"("w", #12); op "item"("w", #13); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #19); op "item"("w", #20); op "item"("w", #21); op "item"("w", #22); op "item"("w", #23); op "item"("w", #24); op "item"("w", #25); op "item"("w", #26); op "item"("w", #27); op "item"("w", #28); op "item"("w", #29); op "item"("w", #30); op "item"("w", #31)]) };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step1_jumps.278", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #9); op "item"("w", #10); op "item"("w", #11); op "item"("w", #12); op "item"("w", #13); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #19); op "item"("w", #20); op "item"("w", #21); op "item"("w", #22); op "item"("w", #23); op "item"("w", #24); op "item"("w", #25); op "item"("w", #26); op "item"("w", #27); op "item"("w", #28); op "item"("w", #0); op "item"("w", #30); op "item"("w", #31)]) };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step2_jumps.279", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #10); op "item"("w", #11); op "item"("w", #12); op "item"("w", #13); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #19); op "item"("w", #20); op "item"("w", #21); op "item"("w", #22); op "item"("w", #23); op "item"("w", #24); op "item"("w", #25); op "item"("w", #26); op "item"("w", #27); op "item"("w", #28); op "item"("w", #0); op "item"("w", #30); op "item"("w", #31)]) };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step3a_jumps.280", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #32); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #23); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #30); op "item"("w", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step3b_jumps.281", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #12); op "item"("w", #0); op "item"("w", #0); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #19); op "item"("w", #20); op "item"("w", #21); op "item"("w", #22); op "item"("w", #23); op "item"("w", #24); op "item"("w", #25); op "item"("w", #26); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #30); op "item"("w", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#__printf_buffer.step4_jumps.282", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #14); op "item"("w", #15); op "item"("w", #16); op "item"("w", #17); op "item"("w", #18); op "item"("w", #19); op "item"("w", #20); op "item"("w", #21); op "item"("w", #22); op "item"("w", #23); op "item"("w", #24); op "item"("w", #25); op "item"("w", #26); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #30); op "item"("w", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#jump_table", op "ro"("local"), int 1, [op "item"("b", op "str"(term(TList (app [(chr 1); (chr 0); (chr 0); (chr 4); (chr 0); (chr 14); (chr 0); (chr 6); (chr 0); (chr 0); (chr 7); (chr 2); (chr 0); (chr 3); (chr 9); (chr 0); (chr 5); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 8); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 26); (chr 30); (chr 25); (chr 0); (chr 19); (chr 19); (chr 19); (chr 0); (chr 29); (chr 0); (chr 0); (chr 12)] [(chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 21); (chr 0); (chr 0); (chr 0); (chr 0); (chr 18); (chr 0); (chr 13); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 0); (chr 26); (chr 30); (chr 20); (chr 15); (chr 19); (chr 19); (chr 19); (chr 10); (chr 15); (chr 28); (chr 0); (chr 11); (chr 24); (chr 23); (chr 17); (chr 22); (chr 12); (chr 0); (chr 21); (chr 27); (chr 16); (chr 0); (chr 31); (chr 18); (chr 0); (chr 13)]))))]) };
    cap{ op "data"("glibc_vfprintf_internal#null", op "ro"("local"), int 1, [op "item"("b", op "str"(["("; "n"; "u"; "l"; "l"; ")"])); op "zero"(int 1)]) };
    cap{ op "data"("glibc_vfprintf_internal#printf_positional.step4_jumps.294", op "ro"("local"), int 4, [op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #1); op "item"("w", #2); op "item"("w", #3); op "item"("w", #4); op "item"("w", #5); op "item"("w", #6); op "item"("w", #7); op "item"("w", #8); op "item"("w", #9); op "item"("w", #10); op "item"("w", #11); op "item"("w", #12); op "item"("w", #13); op "item"("w", #0); op "item"("w", #0); op "item"("w", #0); op "item"("w", #14); op "item"("w", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.284", op "ro"("local"), int 1, [op "item"("b", #40); op "item"("b", #110); op "item"("b", #105); op "item"("b", #108); op "item"("b", #41); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.285", op "ro"("local"), int 1, [op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #32); op "item"("b", #37); op "item"("b", #110); op "item"("b", #32); op "item"("b", #105); op "item"("b", #110); op "item"("b", #32); op "item"("b", #119); op "item"("b", #114); op "item"("b", #105); op "item"("b", #116); op "item"("b", #97); op "item"("b", #98); op "item"("b", #108); op "item"("b", #101); op "item"("b", #32); op "item"("b", #115); op "item"("b", #101); op "item"("b", #103); op "item"("b", #109); op "item"("b", #101); op "item"("b", #110); op "item"("b", #116); op "item"("b", #115); op "item"("b", #32); op "item"("b", #100); op "item"("b", #101); op "item"("b", #116); op "item"("b", #101); op "item"("b", #99); op "item"("b", #116); op "item"("b", #101); op "item"("b", #100); op "item"("b", #32); op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.286", op "ro"("local"), int 1, [op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #32); op "item"("b", #112); op "item"("b", #114); op "item"("b", #111); op "item"("b", #99); op "item"("b", #102); op "item"("b", #115); op "item"("b", #32); op "item"("b", #99); op "item"("b", #111); op "item"("b", #117); op "item"("b", #108); op "item"("b", #100); op "item"("b", #32); op "item"("b", #110); op "item"("b", #111); op "item"("b", #116); op "item"("b", #32); op "item"("b", #111); op "item"("b", #112); op "item"("b", #101); op "item"("b", #110); op "item"("b", #32); op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #10); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.289", op "ro"("local"), int 4, [op "item"("w", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.290", op "ro"("local"), int 1, [op "item"("b", #40); op "item"("b", #109); op "item"("b", #111); op "item"("b", #100); op "item"("b", #101); op "item"("b", #95); op "item"("b", #102); op "item"("b", #108); op "item"("b", #97); op "item"("b", #103); op "item"("b", #115); op "item"("b", #32); op "item"("b", #38); op "item"("b", #32); op "item"("b", #80); op "item"("b", #82); op "item"("b", #73); op "item"("b", #78); op "item"("b", #84); op "item"("b", #70); op "item"("b", #95); op "item"("b", #70); op "item"("b", #79); op "item"("b", #82); op "item"("b", #84); op "item"("b", #73); op "item"("b", #70); op "item"("b", #89); op "item"("b", #41); op "item"("b", #32); op "item"("b", #33); op "item"("b", #61); op "item"("b", #32); op "item"("b", #48); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.291", op "ro"("local"), int 1, [op "item"("b", #118); op "item"("b", #102); op "item"("b", #112); op "item"("b", #114); op "item"("b", #105); op "item"("b", #110); op "item"("b", #116); op "item"("b", #102); op "item"("b", #45); op "item"("b", #105); op "item"("b", #110); op "item"("b", #116); op "item"("b", #101); op "item"("b", #114); op "item"("b", #110); op "item"("b", #97); op "item"("b", #108); op "item"("b", #46); op "item"("b", #99); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.292", op "ro"("local"), int 1, [op "item"("b", #112); op "item"("b", #114); op "item"("b", #105); op "item"("b", #110); op "item"("b", #116); op "item"("b", #102); op "item"("b", #95); op "item"("b", #112); op "item"("b", #111); op "item"("b", #115); op "item"("b", #105); op "item"("b", #116); op "item"("b", #105); op "item"("b", #111); op "item"("b", #110); op "item"("b", #97); op "item"("b", #108); op "item"("b", #0)]) };
    cap{ op "data"("glibc_vfprintf_internal#str.293", op "ro"("local"), int 1, [op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #32); op "item"("b", #105); op "item"("b", #110); op "item"("b", #118); op "item"("b", #97); op "item"("b", #108); op "item"("b", #105); op "item"("b", #100); op "item"("b", #32); op "item"("b", #37); op "item"("b", #78); op "item"("b", #36); op "item"("b", #32); op "item"("b", #117); op "item"("b", #115); op "item"("b", #101); op "item"("b", #32); op "item"("b", #100); op "item"("b", #101); op "item"("b", #116); op "item"("b", #101); op "item"("b", #99); op "item"("b", #116); op "item"("b", #101); op "item"("b", #100); op "item"("b", #32); op "item"("b", #42); op "item"("b", #42); op "item"("b", #42); op "item"("b", #10); op "item"("b", #0)]) }
  ].
