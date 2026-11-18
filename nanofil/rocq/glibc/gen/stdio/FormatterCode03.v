(** This file retains complete items or blocks of glibc's checked formatter.
    stdio/code.sh regenerates it from the pinned capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Glibc Require Import CodePrelude.
From Nanofil Require Import CaptureNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.

(** These blocks retain their order in the linked module. *)
Definition formatter_blocks_03 : list term :=
  [
        cap_blk{ @"L581":
          %"v589" : "p" = "copy" $"__libc_errno";
          %"chk70" : "a" = op "check"(int 0, int 4, "write", int 1) %"v589";
          store "w" [%"chk70" + 0] <- #75;
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L516" };
        cap_blk{ @"L583":
          %"chk71" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v595" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk71";
          %"chk72" : "a" = op "check"(int 0, int 1, "read", int 1) %"v595";
          %"v596" : "w" = op "raw_load"("ub", int 0) %"chk72";
          %"v597" : "w" = op "cmp"("eq", "w") %"v596", #36
          => br %"v597" ? "L77" : "L599" };
        cap_blk{ @"L599":
          %"v604" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk71";
          %"chk74" : "a" = op "check"(int 0, int 1, "read", int 1) %"v604";
          %"v605" : "w" = op "raw_load"("ub", int 0) %"chk74";
          %"v606" : "w" = op "ext"("sb") %"v605";
          %"v611" : "w" = op "cmp"("slt", "w") %"v606", #32
          => br %"v611" ? "L613" : "L612" };
        cap_blk{ @"L612":
          %"v615" : "w" = op "cmp"("sgt", "w") %"v606", #122
          => goto "L613" };
        cap_blk{ @"L613" [phi %"v617" : "w" = ("L599" => #1, "L612" => %"v615")]:
          => br %"v617" ? "L609" : "L608" };
        cap_blk{ @"L608":
          %"v621" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step1_jumps.278";
          %"v622" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v624" : "w" = "sub" %"v606", #32;
          %"v625" : "l" = op "ext"("sw") %"v624";
          %"v626" = %"v622" +p %"v625";
          %"chk75" : "a" = op "check"(int 0, int 1, "read", int 1) %"v626";
          %"v627" : "w" = op "raw_load"("ub", int 0) %"chk75";
          %"v628" : "l" = op "ext"("uw") %"v627";
          %"v629" : "l" = "shl" %"v628", #2;
          %"v630" = %"v621" +p %"v629";
          %"chk76" : "a" = op "check"(int 0, int 4, "read", int 1) %"v630";
          %"v631" : "w" = op "raw_load"("sw", int 0) %"chk76";
          %"v632" : "l" = op "ext"("sw") %"v631"
          => goto "L609" };
        cap_blk{ @"L609" [phi %"v633" : "l" = ("L608" => %"v632", "L613" => #0)]:
          %"v634" : "w" = "copy" %"v633";
          %"v635" : "l" = op "ext"("sw") %"v634";
          %"v636" = #1 +p %"v635";
          %"v638" : "l" = "ptoi" %"v636"
          => goto "L144" };
        cap_blk{ @"L639":
          %"chk77" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v640" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk77";
          %"v641" = %"v640" +p #1;
          %"chk78" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk78" + 0] <- %"v641";
          %"chk79" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v645" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk79";
          %"chk80" : "a" = op "check"(int 0, int 1, "read", int 1) %"v645";
          %"v646" : "w" = op "raw_load"("ub", int 0) %"chk80";
          %"v647" : "w" = op "cmp"("eq", "w") %"v646", #42
          => br %"v647" ? "L642" : "L643" };
        cap_blk{ @"L642":
          %"v649" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk79";
          %"v650" = %"v649" +p #1;
          %"chk82" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk82" + 0] <- %"v650";
          %"chk83" : "a" = op "check"(int 0, int 8, "write", int 8) %"v648";
          store.ptr [%"chk83" + 0] <- %"v650";
          %"chk84" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk83", %"v648";
          %"v654" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk84";
          %"chk85" : "a" = op "check"(int 0, int 1, "read", int 1) %"v654";
          %"v655" : "w" = op "raw_load"("ub", int 0) %"chk85";
          %"v656" : "w" = "sub" %"v655", #48;
          %"v657" : "w" = op "cmp"("ult", "w") %"v656", #10
          => br %"v657" ? "L651" : "L653" };
        cap_blk{ @"L651":
          call %"v659" : "w" = $"glibc_vfprintf_internal#read_int"("p" %"v648");
          %"v665" : "w" = op "cmp"("eq", "w") %"v659", #4294967295
          => br %"v665" ? "L660" : "L662" };
        cap_blk{ @"L660":
          %"v666" : "p" = "copy" $"__libc_errno";
          %"chk86" : "a" = op "check"(int 0, int 4, "write", int 1) %"v666";
          store "w" [%"chk86" + 0] <- #75;
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L516" };
        cap_blk{ @"L662":
          => br %"v659" ? "L673" : "L674" };
        cap_blk{ @"L673":
          %"chk87" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk83", %"v648";
          %"v675" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk87";
          %"chk88" : "a" = op "check"(int 0, int 1, "read", int 1) %"v675";
          %"v676" : "w" = op "raw_load"("ub", int 0) %"chk88";
          %"v677" : "w" = op "cmp"("eq", "w") %"v676", #36
          => goto "L674" };
        cap_blk{ @"L674" [phi %"v679" : "w" = ("L662" => #0, "L673" => %"v677")]:
          => br %"v679" ? "L77" : "L653" };
        cap_blk{ @"L653":
          %"v682" : "w" = "va_arg" %"v4";
          %"v687" : "w" = op "cmp"("slt", "w") %"v682", #0
          => br %"v687" ? "L644" : "L684" };
        cap_blk{ @"L684":
          => goto "L644" };
        cap_blk{ @"L643":
          %"v692" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk79";
          %"chk90" : "a" = op "check"(int 0, int 1, "read", int 1) %"v692";
          %"v693" : "w" = op "raw_load"("ub", int 0) %"chk90";
          %"v694" : "w" = "sub" %"v693", #48;
          %"v695" : "w" = op "cmp"("ult", "w") %"v694", #10
          => br %"v695" ? "L689" : "L644" };
        cap_blk{ @"L689":
          call %"v696" : "w" = $"glibc_vfprintf_internal#read_int"("p" %"v10");
          %"v702" : "w" = op "cmp"("eq", "w") %"v696", #4294967295
          => br %"v702" ? "L697" : "L644" };
        cap_blk{ @"L697":
          %"v703" : "p" = "copy" $"__libc_errno";
          %"chk91" : "a" = op "check"(int 0, int 4, "write", int 1) %"v703";
          store "w" [%"chk91" + 0] <- #75;
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L516" };
        cap_blk{ @"L644" [phi %"pr.85" : "w" = ("L684" => %"v682", "L653" => #4294967295, "L689" => %"v696", "L643" => #0)]:
          %"chk92" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v711" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk92";
          %"chk93" : "a" = op "check"(int 0, int 1, "read", int 1) %"v711";
          %"v712" : "w" = op "raw_load"("ub", int 0) %"chk93";
          %"v713" : "w" = op "ext"("sb") %"v712";
          %"v718" : "w" = op "cmp"("slt", "w") %"v713", #32
          => br %"v718" ? "L720" : "L719" };
        cap_blk{ @"L719":
          %"v722" : "w" = op "cmp"("sgt", "w") %"v713", #122
          => goto "L720" };
        cap_blk{ @"L720" [phi %"v724" : "w" = ("L644" => #1, "L719" => %"v722")]:
          => br %"v724" ? "L716" : "L715" };
        cap_blk{ @"L715":
          %"v728" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step2_jumps.279";
          %"v729" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v731" : "w" = "sub" %"v713", #32;
          %"v732" : "l" = op "ext"("sw") %"v731";
          %"v733" = %"v729" +p %"v732";
          %"chk94" : "a" = op "check"(int 0, int 1, "read", int 1) %"v733";
          %"v734" : "w" = op "raw_load"("ub", int 0) %"chk94";
          %"v735" : "l" = op "ext"("uw") %"v734";
          %"v736" : "l" = "shl" %"v735", #2;
          %"v737" = %"v728" +p %"v736";
          %"chk95" : "a" = op "check"(int 0, int 4, "read", int 1) %"v737";
          %"v738" : "w" = op "raw_load"("sw", int 0) %"chk95";
          %"v739" : "l" = op "ext"("sw") %"v738"
          => goto "L716" };
        cap_blk{ @"L716" [phi %"v740" : "l" = ("L715" => %"v739", "L720" => #0)]:
          %"v741" : "w" = "copy" %"v740";
          %"v742" : "l" = op "ext"("sw") %"v741";
          %"v743" = #1 +p %"v742";
          %"v745" : "l" = "ptoi" %"v743"
          => goto "L144" };
        cap_blk{ @"L747":
          %"chk96" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v752" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk96";
          %"v753" = %"v752" +p #1;
          %"chk97" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk97" + 0] <- %"v753";
          %"chk98" : "a" = op "check"(int 0, int 1, "read", int 1) %"v753";
          %"v754" : "w" = op "raw_load"("ub", int 0) %"chk98";
          %"v755" : "w" = op "ext"("sb") %"v754";
          %"v760" : "w" = op "cmp"("slt", "w") %"v755", #32
          => br %"v760" ? "L762" : "L761" };
        cap_blk{ @"L761":
          %"v764" : "w" = op "cmp"("sgt", "w") %"v755", #122
          => goto "L762" };
        cap_blk{ @"L762" [phi %"v766" : "w" = ("L747" => #1, "L761" => %"v764")]:
          => br %"v766" ? "L758" : "L757" };
        cap_blk{ @"L757":
          %"v770" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step3a_jumps.280";
          %"v771" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v773" : "w" = "sub" %"v755", #32;
          %"v774" : "l" = op "ext"("sw") %"v773";
          %"v775" = %"v771" +p %"v774";
          %"chk99" : "a" = op "check"(int 0, int 1, "read", int 1) %"v775";
          %"v776" : "w" = op "raw_load"("ub", int 0) %"chk99";
          %"v777" : "l" = op "ext"("uw") %"v776";
          %"v778" : "l" = "shl" %"v777", #2;
          %"v779" = %"v770" +p %"v778";
          %"chk100" : "a" = op "check"(int 0, int 4, "read", int 1) %"v779";
          %"v780" : "w" = op "raw_load"("sw", int 0) %"chk100";
          %"v781" : "l" = op "ext"("sw") %"v780"
          => goto "L758" };
        cap_blk{ @"L758" [phi %"v782" : "l" = ("L757" => %"v781", "L762" => #0)]:
          %"v783" : "w" = "copy" %"v782";
          %"v784" : "l" = op "ext"("sw") %"v783";
          %"v785" = #1 +p %"v784";
          %"v787" : "l" = "ptoi" %"v785"
          => goto "L144" };
        cap_blk{ @"L789":
          %"chk101" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v794" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk101";
          %"v795" = %"v794" +p #1;
          %"chk102" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk102" + 0] <- %"v795";
          %"chk103" : "a" = op "check"(int 0, int 1, "read", int 1) %"v795";
          %"v796" : "w" = op "raw_load"("ub", int 0) %"chk103";
          %"v797" : "w" = op "ext"("sb") %"v796";
          %"v802" : "w" = op "cmp"("slt", "w") %"v797", #32
          => br %"v802" ? "L804" : "L803" };
        cap_blk{ @"L803":
          %"v806" : "w" = op "cmp"("sgt", "w") %"v797", #122
          => goto "L804" };
        cap_blk{ @"L804" [phi %"v808" : "w" = ("L789" => #1, "L803" => %"v806")]:
          => br %"v808" ? "L800" : "L799" };
        cap_blk{ @"L799":
          %"v812" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v813" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v815" : "w" = "sub" %"v797", #32;
          %"v816" : "l" = op "ext"("sw") %"v815";
          %"v817" = %"v813" +p %"v816";
          %"chk104" : "a" = op "check"(int 0, int 1, "read", int 1) %"v817";
          %"v818" : "w" = op "raw_load"("ub", int 0) %"chk104";
          %"v819" : "l" = op "ext"("uw") %"v818";
          %"v820" : "l" = "shl" %"v819", #2;
          %"v821" = %"v812" +p %"v820";
          %"chk105" : "a" = op "check"(int 0, int 4, "read", int 1) %"v821";
          %"v822" : "w" = op "raw_load"("sw", int 0) %"chk105";
          %"v823" : "l" = op "ext"("sw") %"v822"
          => goto "L800" };
        cap_blk{ @"L800" [phi %"v824" : "l" = ("L799" => %"v823", "L804" => #0)]:
          %"v825" : "w" = "copy" %"v824";
          %"v826" : "l" = op "ext"("sw") %"v825";
          %"v827" = #1 +p %"v826";
          %"v829" : "l" = "ptoi" %"v827"
          => goto "L144" };
        cap_blk{ @"L831":
          %"chk106" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v836" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk106";
          %"v837" = %"v836" +p #1;
          %"chk107" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk107" + 0] <- %"v837";
          %"chk108" : "a" = op "check"(int 0, int 1, "read", int 1) %"v837";
          %"v838" : "w" = op "raw_load"("ub", int 0) %"chk108";
          %"v839" : "w" = op "ext"("sb") %"v838";
          %"v844" : "w" = op "cmp"("slt", "w") %"v839", #32
          => br %"v844" ? "L846" : "L845" };
        cap_blk{ @"L845":
          %"v848" : "w" = op "cmp"("sgt", "w") %"v839", #122
          => goto "L846" };
        cap_blk{ @"L846" [phi %"v850" : "w" = ("L831" => #1, "L845" => %"v848")]:
          => br %"v850" ? "L842" : "L841" };
        cap_blk{ @"L841":
          %"v854" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step3b_jumps.281";
          %"v855" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v857" : "w" = "sub" %"v839", #32;
          %"v858" : "l" = op "ext"("sw") %"v857";
          %"v859" = %"v855" +p %"v858";
          %"chk109" : "a" = op "check"(int 0, int 1, "read", int 1) %"v859";
          %"v860" : "w" = op "raw_load"("ub", int 0) %"chk109";
          %"v861" : "l" = op "ext"("uw") %"v860";
          %"v862" : "l" = "shl" %"v861", #2;
          %"v863" = %"v854" +p %"v862";
          %"chk110" : "a" = op "check"(int 0, int 4, "read", int 1) %"v863";
          %"v864" : "w" = op "raw_load"("sw", int 0) %"chk110";
          %"v865" : "l" = op "ext"("sw") %"v864"
          => goto "L842" };
        cap_blk{ @"L842" [phi %"v866" : "l" = ("L841" => %"v865", "L846" => #0)]:
          %"v867" : "w" = "copy" %"v866";
          %"v868" : "l" = op "ext"("sw") %"v867";
          %"v869" = #1 +p %"v868";
          %"v871" : "l" = "ptoi" %"v869"
          => goto "L144" };
        cap_blk{ @"L873":
          %"chk111" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v878" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk111";
          %"v879" = %"v878" +p #1;
          %"chk112" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk112" + 0] <- %"v879";
          %"chk113" : "a" = op "check"(int 0, int 1, "read", int 1) %"v879";
          %"v880" : "w" = op "raw_load"("ub", int 0) %"chk113";
          %"v881" : "w" = op "ext"("sb") %"v880";
          %"v886" : "w" = op "cmp"("slt", "w") %"v881", #32
          => br %"v886" ? "L888" : "L887" };
        cap_blk{ @"L887":
          %"v890" : "w" = op "cmp"("sgt", "w") %"v881", #122
          => goto "L888" };
        cap_blk{ @"L888" [phi %"v892" : "w" = ("L873" => #1, "L887" => %"v890")]:
          => br %"v892" ? "L884" : "L883" };
        cap_blk{ @"L883":
          %"v896" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v897" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v899" : "w" = "sub" %"v881", #32;
          %"v900" : "l" = op "ext"("sw") %"v899";
          %"v901" = %"v897" +p %"v900";
          %"chk114" : "a" = op "check"(int 0, int 1, "read", int 1) %"v901";
          %"v902" : "w" = op "raw_load"("ub", int 0) %"chk114";
          %"v903" : "l" = op "ext"("uw") %"v902";
          %"v904" : "l" = "shl" %"v903", #2;
          %"v905" = %"v896" +p %"v904";
          %"chk115" : "a" = op "check"(int 0, int 4, "read", int 1) %"v905";
          %"v906" : "w" = op "raw_load"("sw", int 0) %"chk115";
          %"v907" : "l" = op "ext"("sw") %"v906"
          => goto "L884" };
        cap_blk{ @"L884" [phi %"v908" : "l" = ("L883" => %"v907", "L888" => #0)]:
          %"v909" : "w" = "copy" %"v908";
          %"v910" : "l" = op "ext"("sw") %"v909";
          %"v911" = #1 +p %"v910";
          %"v913" : "l" = "ptoi" %"v911"
          => goto "L144" };
        cap_blk{ @"L917":
          %"chk116" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v922" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk116";
          %"v923" = %"v922" +p #1;
          %"chk117" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk117" + 0] <- %"v923";
          %"chk118" : "a" = op "check"(int 0, int 1, "read", int 1) %"v923";
          %"v924" : "w" = op "raw_load"("ub", int 0) %"chk118";
          %"v925" : "w" = op "ext"("sb") %"v924";
          %"v930" : "w" = op "cmp"("slt", "w") %"v925", #32
          => br %"v930" ? "L932" : "L931" };
        cap_blk{ @"L931":
          %"v934" : "w" = op "cmp"("sgt", "w") %"v925", #122
          => goto "L932" };
        cap_blk{ @"L932" [phi %"v936" : "w" = ("L917" => #1, "L931" => %"v934")]:
          => br %"v936" ? "L928" : "L927" };
        cap_blk{ @"L927":
          %"v940" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v941" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v943" : "w" = "sub" %"v925", #32;
          %"v944" : "l" = op "ext"("sw") %"v943";
          %"v945" = %"v941" +p %"v944";
          %"chk119" : "a" = op "check"(int 0, int 1, "read", int 1) %"v945";
          %"v946" : "w" = op "raw_load"("ub", int 0) %"chk119";
          %"v947" : "l" = op "ext"("uw") %"v946";
          %"v948" : "l" = "shl" %"v947", #2;
          %"v949" = %"v940" +p %"v948";
          %"chk120" : "a" = op "check"(int 0, int 4, "read", int 1) %"v949";
          %"v950" : "w" = op "raw_load"("sw", int 0) %"chk120";
          %"v951" : "l" = op "ext"("sw") %"v950"
          => goto "L928" };
        cap_blk{ @"L928" [phi %"v952" : "l" = ("L927" => %"v951", "L932" => #0)]:
          %"v953" : "w" = "copy" %"v952";
          %"v954" : "l" = op "ext"("sw") %"v953";
          %"v955" = #1 +p %"v954";
          %"v957" : "l" = "ptoi" %"v955"
          => goto "L144" };
        cap_blk{ @"L961":
          %"chk121" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v966" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk121";
          %"v967" = %"v966" +p #1;
          %"chk122" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk122" + 0] <- %"v967";
          %"chk123" : "a" = op "check"(int 0, int 1, "read", int 1) %"v967";
          %"v968" : "w" = op "raw_load"("ub", int 0) %"chk123";
          %"v969" : "w" = op "ext"("sb") %"v968";
          %"v974" : "w" = op "cmp"("slt", "w") %"v969", #32
          => br %"v974" ? "L976" : "L975" };
        cap_blk{ @"L975":
          %"v978" : "w" = op "cmp"("sgt", "w") %"v969", #122
          => goto "L976" };
        cap_blk{ @"L976" [phi %"v980" : "w" = ("L961" => #1, "L975" => %"v978")]:
          => br %"v980" ? "L972" : "L971" };
        cap_blk{ @"L971":
          %"v984" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v985" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v987" : "w" = "sub" %"v969", #32;
          %"v988" : "l" = op "ext"("sw") %"v987";
          %"v989" = %"v985" +p %"v988";
          %"chk124" : "a" = op "check"(int 0, int 1, "read", int 1) %"v989";
          %"v990" : "w" = op "raw_load"("ub", int 0) %"chk124";
          %"v991" : "l" = op "ext"("uw") %"v990";
          %"v992" : "l" = "shl" %"v991", #2;
          %"v993" = %"v984" +p %"v992";
          %"chk125" : "a" = op "check"(int 0, int 4, "read", int 1) %"v993";
          %"v994" : "w" = op "raw_load"("sw", int 0) %"chk125";
          %"v995" : "l" = op "ext"("sw") %"v994"
          => goto "L972" };
        cap_blk{ @"L972" [phi %"v996" : "l" = ("L971" => %"v995", "L976" => #0)]:
          %"v997" : "w" = "copy" %"v996";
          %"v998" : "l" = op "ext"("sw") %"v997";
          %"v999" = #1 +p %"v998";
          %"v1001" : "l" = "ptoi" %"v999"
          => goto "L144" };
        cap_blk{ @"L1005":
          %"chk126" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v1010" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk126";
          %"v1011" = %"v1010" +p #1;
          %"chk127" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk127" + 0] <- %"v1011";
          %"chk128" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1011";
          %"v1012" : "w" = op "raw_load"("ub", int 0) %"chk128";
          %"v1013" : "w" = op "ext"("sb") %"v1012";
          %"v1018" : "w" = op "cmp"("slt", "w") %"v1013", #32
          => br %"v1018" ? "L1020" : "L1019" };
        cap_blk{ @"L1019":
          %"v1022" : "w" = op "cmp"("sgt", "w") %"v1013", #122
          => goto "L1020" };
        cap_blk{ @"L1020" [phi %"v1024" : "w" = ("L1005" => #1, "L1019" => %"v1022")]:
          => br %"v1024" ? "L1016" : "L1015" };
        cap_blk{ @"L1015":
          %"v1028" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v1029" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v1031" : "w" = "sub" %"v1013", #32;
          %"v1032" : "l" = op "ext"("sw") %"v1031";
          %"v1033" = %"v1029" +p %"v1032";
          %"chk129" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1033";
          %"v1034" : "w" = op "raw_load"("ub", int 0) %"chk129";
          %"v1035" : "l" = op "ext"("uw") %"v1034";
          %"v1036" : "l" = "shl" %"v1035", #2;
          %"v1037" = %"v1028" +p %"v1036";
          %"chk130" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1037";
          %"v1038" : "w" = op "raw_load"("sw", int 0) %"chk130";
          %"v1039" : "l" = op "ext"("sw") %"v1038"
          => goto "L1016" };
        cap_blk{ @"L1016" [phi %"v1040" : "l" = ("L1015" => %"v1039", "L1020" => #0)]:
          %"v1041" : "w" = "copy" %"v1040";
          %"v1042" : "l" = op "ext"("sw") %"v1041";
          %"v1043" = #1 +p %"v1042";
          %"v1045" : "l" = "ptoi" %"v1043"
          => goto "L144" };
        cap_blk{ @"L1046":
          %"chk131" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v1047" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk131";
          %"v1048" = %"v1047" +p #1;
          %"chk132" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk132" + 0] <- %"v1048";
          %"chk133" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v1054" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk133";
          %"chk134" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1054";
          %"v1055" : "w" = op "raw_load"("ub", int 0) %"chk134";
          %"v1056" : "w" = op "cmp"("eq", "w") %"v1055", #102
          => br %"v1056" ? "L1051" : "L1053" };
        cap_blk{ @"L1051":
          %"v1057" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk133";
          %"v1058" = %"v1057" +p #1;
          %"chk136" : "a" = op "renew"(int 0, int 8, "write", int 8) %"chk3", %"v10";
          store.ptr [%"chk136" + 0] <- %"v1058"
          => goto "L1053" };
        cap_blk{ @"L1053" [phi %"pr.99" : "w" = ("L1051" => #1, "L1046" => #0)]:
          %"chk137" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v1064" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk137";
          %"chk138" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1064";
          %"v1065" : "w" = op "raw_load"("ub", int 0) %"chk138";
          %"v1066" : "w" = "sub" %"v1065", #48;
          %"v1067" : "w" = op "cmp"("ult", "w") %"v1066", #10
          => br %"v1067" ? "L1061" : "L1063" };
        cap_blk{ @"L1061":
          call %"v1068" : "w" = $"glibc_vfprintf_internal#read_int"("p" %"v10")
          => goto "L1063" };
        cap_blk{ @"L1063" [phi %"pr.100" : "w" = ("L1061" => %"v1068", "L1053" => #0)]:
          => br %"pr.99" ? "L1074" : "L1071" };
        cap_blk{ @"L1074":
          %"v1081" : "w" = op "cmp"("eq", "w") %"pr.100", #8
          => br %"v1081" ? "L1071" : "L1082" };
        cap_blk{ @"L1082":
          %"v1083" : "w" = op "cmp"("eq", "w") %"pr.100", #16
          => br %"v1083" ? "L1071" : "L1084" };
        cap_blk{ @"L1084":
          %"v1085" : "w" = op "cmp"("eq", "w") %"pr.100", #32
          => br %"v1085" ? "L1071" : "L1086" };
        cap_blk{ @"L1086":
          %"v1087" : "w" = op "cmp"("eq", "w") %"pr.100", #64
          => br %"v1087" ? "L1071" : "L1088" };
        cap_blk{ @"L1088":
          => goto "L1071" };
        cap_blk{ @"L1071" [phi %"pr.101" : "w" = ("L1088" => %"pr.100", "L1074" => #8, "L1082" => #64, "L1084" => #64, "L1086" => #64, "L1063" => %"pr.100")]:
          %"v1100" : "w" = op "cmp"("eq", "w") %"pr.101", #8
          => br %"v1100" ? "L1091" : "L1101" };
        cap_blk{ @"L1096":
          %"v1097" : "p" = "copy" $"__libc_errno";
          %"chk139" : "a" = op "check"(int 0, int 4, "write", int 1) %"v1097";
          store "w" [%"chk139" + 0] <- #22;
          call void $"glibc_vfprintf_internal#__printf_buffer_mark_failed"("p" %"v0")
          => goto "L516" };
        cap_blk{ @"L1101":
          %"v1102" : "w" = op "cmp"("eq", "w") %"pr.101", #16
          => br %"v1102" ? "L1091" : "L1103" };
        cap_blk{ @"L1103":
          %"v1104" : "w" = op "cmp"("eq", "w") %"pr.101", #32
          => br %"v1104" ? "L1091" : "L1105" };
        cap_blk{ @"L1105":
          %"v1106" : "w" = op "cmp"("eq", "w") %"pr.101", #64
          => br %"v1106" ? "L1091" : poll "L1096" };
        cap_blk{ @"L1091" [phi %"pr.64" : "w" = ("L1071" => #1, "L1101" => %"pr.65", "L1103" => %"pr.65", "L1105" => %"pr.65"); phi %"pr.61" : "w" = ("L1071" => %"pr.62", "L1101" => %"pr.62", "L1103" => %"pr.62", "L1105" => #1); phi %"pr.59" : "w" = ("L1071" => %"pr.60", "L1101" => #1, "L1103" => %"pr.60", "L1105" => %"pr.60"); phi %"pr.56" : "w" = ("L1071" => %"pr.57", "L1101" => %"pr.57", "L1103" => %"pr.57", "L1105" => #1)]:
          %"chk140" : "a" = op "renew"(int 0, int 8, "read", int 8) %"chk3", %"v10";
          %"v1113" : "p" = op "raw_load_pointer"(int 0, ["aux_read"; "lower_resolve"; "address_read"]) %"chk140";
          %"chk141" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1113";
          %"v1114" : "w" = op "raw_load"("ub", int 0) %"chk141";
          %"v1115" : "w" = op "ext"("sb") %"v1114";
          %"v1120" : "w" = op "cmp"("slt", "w") %"v1115", #32
          => br %"v1120" ? "L1122" : "L1121" };
        cap_blk{ @"L1121":
          %"v1124" : "w" = op "cmp"("sgt", "w") %"v1115", #122
          => goto "L1122" };
        cap_blk{ @"L1122" [phi %"v1126" : "w" = ("L1091" => #1, "L1121" => %"v1124")]:
          => br %"v1126" ? "L1118" : "L1117" };
        cap_blk{ @"L1117":
          %"v1130" : "p" = "copy" $"glibc_vfprintf_internal#__printf_buffer.step4_jumps.282";
          %"v1131" : "p" = "copy" $"glibc_vfprintf_internal#jump_table";
          %"v1133" : "w" = "sub" %"v1115", #32;
          %"v1134" : "l" = op "ext"("sw") %"v1133";
          %"v1135" = %"v1131" +p %"v1134";
          %"chk142" : "a" = op "check"(int 0, int 1, "read", int 1) %"v1135";
          %"v1136" : "w" = op "raw_load"("ub", int 0) %"chk142";
          %"v1137" : "l" = op "ext"("uw") %"v1136";
          %"v1138" : "l" = "shl" %"v1137", #2;
          %"v1139" = %"v1130" +p %"v1138";
          %"chk143" : "a" = op "check"(int 0, int 4, "read", int 1) %"v1139";
          %"v1140" : "w" = op "raw_load"("sw", int 0) %"chk143";
          %"v1141" : "l" = op "ext"("sw") %"v1140"
          => goto "L1118" }
  ].
