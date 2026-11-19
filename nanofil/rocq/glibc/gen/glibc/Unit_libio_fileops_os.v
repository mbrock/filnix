(** This file defines checked IR from glibc’s `libio/fileops.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn__IO_file_close_maybe_unlink : func :=
  ir_fn{ "export" "_IO_file_close_maybe_unlink"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v9" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v13" : W = (Cmp Eq W) %"v10", #4294967295
    => br %"v13" ? "L5" : "L7";
  @"L5":
    => ret #4294967295;
  @"L7":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v21" : W = And %"v20", #8;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L23" : "L24";
  @"L23":
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v27" : W = And %"v26", #2048;
    %"v28" : W = (Cmp Ne W) %"v27", #0
    => goto "L24";
  @"L24" [%"v30" : W = phi("L7" => #0, "L23" => %"v28")]:
    => br %"v30" ? "L16" : "L17";
  @"L16":
    %"v35" = %"v0" +p #192;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v35";
    %"v36" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v37" : W = (Cmp Sle W) %"v36", #0
    => br %"v37" ? "L31" : "L32";
  @"L31":
    %"v40" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v43" = %"v0" +p #40;
    %"v44" : P = (RawLoadPointer 8 load_effects) %"chk4";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v48" : L = Ptoi %"v44";
    %"v49" : L = Ptoi %"v47";
    %"v50" : L = Sub %"v48", %"v49";
    call %"v51" : W = $"_IO_new_do_write"(P %"v0", P %"v41", L %"v50")
    => goto "L18";
  @"L32":
    %"v54" = %"v0" +p #160;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v56" = %"v55" +p #24;
    %"chk8" : A = (Check 0 8 Read 8) %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v61" = %"v60" +p #32;
    %"chk10" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v66" = %"v65" +p #24;
    %"chk12" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v68" : L = Ptoi %"v62";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Sub %"v68", %"v69";
    %"v71" : L = Div %"v70", #4;
    call %"v72" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v57", L %"v71")
    => goto "L18";
  @"L17":
    %"v78" = %"v0" +p #112;
    %"v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v80" : W = (Cmp Sge W) %"v79", #0
    => br %"v80" ? "L81" : "L82";
  @"L81":
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v85" : W = And %"v84", #256
    => br %"v85" ? "L87" : "L86";
  @"L86":
    %"v89" = %"v0" +p #192;
    %"chk15" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v89";
    %"v90" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v91" : W = (Cmp Sle W) %"v90", #0
    => br %"v91" ? "L92" : "L87";
  @"L92":
    %"v95" = %"v0" +p #8;
    %"chk16" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v95";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v98" = %"v0" +p #16;
    %"v99" : P = (RawLoadPointer 8 load_effects) %"chk16";
    %"v100" : L = Ptoi %"v96";
    %"v101" : L = Ptoi %"v99";
    %"v102" : W = (Cmp Ult L) %"v100", %"v101"
    => goto "L87";
  @"L87" [%"v106" : W = phi("L81" => #1, "L86" => #0, "L92" => %"v102")]:
    => br %"v106" ? "L82" : "L110";
  @"L110":
    %"v113" = %"v0" +p #192;
    %"chk18" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v113";
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v115" : W = (Cmp Sgt W) %"v114", #0
    => br %"v115" ? "L118" : "L82";
  @"L118":
    %"v121" = %"v0" +p #160;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 8 Read 8) %"v122";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v127" = %"v126" +p #8;
    %"chk22" : A = (Check 0 8 Read 8) %"v127";
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v129" : L = Ptoi %"v123";
    %"v130" : L = Ptoi %"v128";
    %"v131" : W = (Cmp Ult L) %"v129", %"v130"
    => goto "L82";
  @"L82" [%"v137" : W = phi("L17" => #0, "L87" => #1, "L110" => #0, "L118" => %"v131")]:
    => br %"v137" ? "L74" : "L18";
  @"L74":
    %"v140" = %"v0" +p #216;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v140";
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"iw_1.v4" : L = Ptoi %"v141";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v143" = %"v141" +p #72;
    %"chk24" : A = (Check 0 8 Read 8) %"v143";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : F = CheckFunction %"v144";
    rawcall %"v146" : L = %"chk25"(P %"v0", L #0, W #1, W #0);
    %"v153" : W = (Cmp Eq L) %"v146", #18446744073709551615
    => br %"v153" ? "L147" : "L148";
  @"L147":
    %"v157" : P = Copy $"__libc_errno";
    %"chk26" : A = (Check 0 4 Read 1) %"v157";
    %"v158" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v159" : W = (Cmp Ne W) %"v158", #29
    => br %"v159" ? "L18" : "L155";
  @"L155":
    => goto "L18";
  @"L148":
    %"chk27" : A = (Renew 0 4 Read 1) %"chk1", %"v0";
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"v166" : W = And %"v165", #256
    => br %"v166" ? "L161" : "L163";
  @"L161":
    %"v169" = %"v0" +p #88;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v169";
    %"v170" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v172" = %"v0" +p #72;
    %"v173" : P = (RawLoadPointer (-16) load_effects) %"chk28";
    %"v174" : L = Ptoi %"v170";
    %"v175" : L = Ptoi %"v173";
    %"v176" : L = Sub %"v174", %"v175";
    %"v177" : L = Sub %"v146", %"v176"
    => goto "L163";
  @"L163" [%"pr.5" : L = phi("L161" => %"v177", "L148" => %"v146")]:
    %"v182" = %"v0" +p #216;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk23", %"v182";
    %"v183" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"iw_2.v4" : L = Ptoi %"v183";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join";
  @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join";
  @"iw_2.join":
    %"v185" = %"v183" +p #128;
    %"chk31" : A = (Check 0 8 Read 8) %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : F = CheckFunction %"v186";
    rawcall %"v189" : L = %"chk32"(P %"v0", L %"pr.5", W #0);
    %"v190" : W = (Cmp Slt L) %"v189", #0
    => br %"v190" ? "L191" : "L192";
  @"L191":
    %"v193" : P = Copy $"__libc_errno";
    %"chk33" : A = (Check 0 4 Read 1) %"v193";
    %"v194" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v195" : W = (Cmp Ne W) %"v194", #29
    => goto "L192";
  @"L192" [%"v197" : W = phi("iw_2.join" => #0, "L191" => %"v195")]:
    => br %"v197" ? "L18" : "L179";
  @"L179":
    => goto "L18";
  @"L18" [%"pr.3" : W = phi("L31" => %"v51", "L32" => %"v72", "L155" => #0, "L147" => #4294967295, "L179" => #0, "L192" => #4294967295, "L82" => #0)]:
    call void $"__GI__IO_unsave_markers"(P %"v0");
    %"v206" = %"v0" +p #116;
    %"chk34" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v206";
    %"v207" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"v208" : W = Shl %"v207", #8;
    %"v209" : W = Sar %"v208", #8;
    %"v210" : W = And %"v209", #32;
    %"v211" : W = (Cmp Eq W) %"v210", #0
    => br %"v211" ? "L202" : "L204";
  @"L202":
    %"v213" = %"v0" +p #216;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v213";
    %"v214" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"iw_3.v4" : L = Ptoi %"v214";
    %"iw_3.v7" : P = Copy $"__io_vtables";
    %"iw_3.v8" : L = Ptoi %"iw_3.v7";
    %"iw_3.v9" : L = Sub %"iw_3.v4", %"iw_3.v8";
    %"iw_3.v15" : W = (Cmp Uge L) %"iw_3.v9", #2352
    => br %"iw_3.v15" ? "iw_3.L10" : "iw_3.join";
  @"iw_3.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_3.join";
  @"iw_3.join":
    %"v216" = %"v214" +p #136;
    %"chk36" : A = (Check 0 8 Read 8) %"v216";
    %"v217" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : F = CheckFunction %"v217";
    rawcall %"v219" : W = %"chk37"(P %"v0")
    => goto "L204";
  @"L204" [%"v220" : W = phi("iw_3.join" => %"v219", "L18" => #0)]:
    %"v225" = %"v0" +p #192;
    %"chk38" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v225";
    %"v226" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v227" : W = (Cmp Sgt W) %"v226", #0
    => br %"v227" ? "L221" : "L223";
  @"L221":
    %"v232" = %"v0" +p #160;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v232";
    %"v233" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v234" = %"v233" +p #72;
    %"chk40" : A = (Check 0 8 Read 8) %"v234";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v236" : L = Ptoi %"v235";
    %"v237" : L = Ptoi #0;
    %"v238" : W = (Cmp Ne L) %"v236", %"v237"
    => br %"v238" ? "L228" : "L230";
  @"L228":
    call void $"__GI__IO_free_wbackup_area"(P %"v0")
    => goto "L230";
  @"L230":
    call void $"__GI__IO_wsetb"(P %"v0", P #0, P #0, W #0);
    %"v242" = %"v0" +p #160;
    %"chk41" : A = (Renew 0 8 Read 8) %"chk39", %"v242";
    %"v243" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v244" = %"v243" +p #16;
    %"chk42" : A = (Check 0 8 Write 8) %"v244";
    store.ptr [%"chk42" + 0] <- #0;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk39", %"v242";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"chk44" : A = (Check 0 8 Write 8) %"v247";
    store.ptr [%"chk44" + 0] <- #0;
    %"chk45" : A = (Renew 0 8 Read 8) %"chk39", %"v242";
    %"v250" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v251" = %"v250" +p #8;
    %"chk46" : A = (Check 0 8 Write 8) %"v251";
    store.ptr [%"chk46" + 0] <- #0;
    %"chk47" : A = (Renew 0 8 Read 8) %"chk39", %"v242";
    %"v254" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v255" = %"v254" +p #24;
    %"v258" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v259" = %"v258" +p #32;
    %"chk49" : A = (Check 0 8 Write 8) %"v259";
    store.ptr [%"chk49" + 0] <- #0;
    %"chk50" : A = (Check 0 8 Write 8) %"v255";
    store.ptr [%"chk50" + 0] <- #0;
    %"chk51" : A = (Renew 0 8 Read 8) %"chk39", %"v242";
    %"v262" : P = (RawLoadPointer 0 load_effects) %"chk51";
    %"v263" = %"v262" +p #40;
    %"chk52" : A = (Check 0 8 Write 8) %"v263";
    store.ptr [%"chk52" + 0] <- #0
    => goto "L223";
  @"L223":
    call void $"__GI__IO_setb"(P %"v0", P #0, P #0, W #0);
    %"v266" = %"v0" +p #24;
    %"chk53" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v266";
    store.ptr [%"chk53" + 0] <- #0;
    %"v268" = %"v0" +p #8;
    %"chk54" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v268";
    store.ptr [%"chk54" + 0] <- #0;
    %"v270" = %"v0" +p #16;
    %"chk55" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v270";
    store.ptr [%"chk55" + 0] <- #0;
    %"v272" = %"v0" +p #32;
    %"v274" = %"v0" +p #40;
    %"chk56" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v274";
    store.ptr [%"chk56" + 0] <- #0;
    %"chk57" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v272";
    store.ptr [%"chk57" + 0] <- #0;
    %"v276" = %"v0" +p #48;
    %"chk58" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v276";
    store.ptr [%"chk58" + 0] <- #0;
    %"v280" : W = (Ext Ub) %"v2"
    => br %"v280" ? "L277" : "L279";
  @"L277":
    call void $"__GI__IO_un_link"(P %"v0")
    => goto "L279";
  @"L279":
    %"chk59" : A = (Renew 0 4 Read 1) %"chk1", %"v0";
    %"v288" : W = (RawLoad (LdNarrow Sw) 0) %"chk59";
    %"v289" : W = And %"v288", #128;
    %"v290" : W = Or %"v289", #4222428172;
    %"chk60" : A = (Renew 0 4 Write 1) %"chk1", %"v0";
    store Ww [%"chk60" + 0] <- %"v290";
    %"v292" = %"v0" +p #112;
    %"chk61" : A = (Renew 0 4 Write 1) %"chk0", %"v292";
    store Ww [%"chk61" + 0] <- #4294967295;
    %"v295" = %"v0" +p #144;
    %"chk62" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v295";
    store Wl [%"chk62" + 0] <- #18446744073709551615
    => br %"v220" ? "L300" : "L299";
  @"L299":
    => goto "L300";
  @"L300" [%"v304" : W = phi("L299" => %"pr.3", "L279" => %"v220")]:
    => ret %"v304"
} }.

Definition fn__IO_file_close_mmap : func :=
  ir_fn{ "export" "_IO_file_close_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v3";
    %"v4" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v6" = %"v0" +p #64;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : L = Sub %"v11", %"v12";
    call %"v14" : W = $"__GI___munmap"(P %"v4", L %"v13");
    %"chk3" : A = (Renew 0 8 Write 8) %"chk1", %"v6";
    store.ptr [%"chk3" + 0] <- #0;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk0", %"v3";
    store.ptr [%"chk4" + 0] <- #0;
    %"v20" = %"v0" +p #112;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    call %"v22" : W = $"__GI___close_nocancel"(W %"v21")
    => ret %"v22"
} }.

Definition fn__IO_file_seekoff_maybe_mmap : func :=
  ir_fn{ "export" "_IO_file_seekoff_maybe_mmap"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v11";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v13" = %"v11" +p #128;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v14";
    rawcall %"v18" : L = %"chk2"(P %"v0", L %"v2", W %"v4");
    %"v23" : W = (Cmp Slt L) %"v18", #0
    => br %"v23" ? "L19" : "L21";
  @"L19":
    => ret #18446744073709551615;
  @"L21":
    %"v28" = %"v0" +p #144;
    %"chk3" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v28";
    store Wl [%"chk3" + 0] <- %"v18"
    => ret %"v18"
} }.

Definition fn__IO_file_seekoff_mmap : func :=
  ir_fn{ "export" "_IO_file_seekoff_mmap"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v13" : W = (Cmp Eq W) %"v6", #0
    => br %"v13" ? "L9" : "L11";
  @"L9":
    %"v15" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Read 1) %"v15";
    %"v16" : L = (RawLoad LdL 0) %"chk0";
    %"v18" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v21" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v23" : L = Ptoi %"v19";
    %"v24" : L = Ptoi %"v22";
    %"v25" : L = Sub %"v23", %"v24";
    %"v26" : L = Sub %"v16", %"v25"
    => ret %"v26";
  @"L11":
    %"chk3" : A = (Check 0 4 Read 1) %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v33" : W = And %"v32", #256
    => br %"v33" ? "L28" : "L30";
  @"L28":
    %"v38" : W = (Cmp Eq W) %"v4", #1
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v0" +p #8;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v44" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v46" : L = Ptoi %"v42";
    %"v47" : L = Ptoi %"v45";
    %"v48" : L = Sub %"v46", %"v47";
    %"v49" : L = Add %"v2", %"v48"
    => goto "L36";
  @"L36" [%"pr.2" : L = phi("L34" => %"v49", "L28" => %"v2")]:
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto "L30";
  @"L30" [%"pr.1" : L = phi("L36" => %"pr.2", "L11" => %"v2")]:
    %"v84" : W = (Cmp Eq W) %"v4", #1
    => br %"v84" ? "L54" : "L85";
  @"L54":
    %"v57" = %"v0" +p #144;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 1) %"chk3", %"v57";
    %"v58" : L = (RawLoad LdL 0) %"chk6";
    %"v60" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v63" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v65" : L = Ptoi %"v61";
    %"v66" : L = Ptoi %"v64";
    %"v67" : L = Sub %"v65", %"v66";
    %"v68" : L = Sub %"v58", %"v67";
    %"v69" : L = Add %"pr.1", %"v68"
    => goto "L53";
  @"L71":
    %"v74" = %"v0" +p #64;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v77" = %"v0" +p #56;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v79" : L = Ptoi %"v75";
    %"v80" : L = Ptoi %"v78";
    %"v81" : L = Sub %"v79", %"v80";
    %"v82" : L = Add %"pr.1", %"v81"
    => goto "L53";
  @"L85":
    %"v86" : W = (Cmp Eq W) %"v4", #0
    => br %"v86" ? "L53" : "L87";
  @"L87":
    %"v88" : W = (Cmp Eq W) %"v4", #2
    => br %"v88" ? poll "L71" : "L53";
  @"L53" [%"pr.3" : L = phi("L54" => %"v69", "L71" => %"v82", "L85" => %"pr.1", "L87" => %"pr.1")]:
    %"v94" : W = (Cmp Slt L) %"pr.3", #0
    => br %"v94" ? "L90" : "L92";
  @"L90":
    %"v95" : P = Copy $"__libc_errno";
    %"chk11" : A = (Check 0 4 Write 1) %"v95";
    store Ww [%"chk11" + 0] <- #22
    => ret #18446744073709551615;
  @"L92":
    %"v100" = %"v0" +p #216;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v4" : L = Ptoi %"v101";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v103" = %"v101" +p #128;
    %"chk13" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : F = CheckFunction %"v104";
    rawcall %"v107" : L = %"chk14"(P %"v0", L %"pr.3", W #0);
    %"v112" : W = (Cmp Slt L) %"v107", #0
    => br %"v112" ? "L108" : "L110";
  @"L108":
    => ret #18446744073709551615;
  @"L110":
    %"v121" = %"v0" +p #64;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v124" = %"v0" +p #56;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk3", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v126" : L = Ptoi %"v122";
    %"v127" : L = Ptoi %"v125";
    %"v128" : L = Sub %"v126", %"v127";
    %"v129" : W = (Cmp Sgt L) %"pr.3", %"v128"
    => br %"v129" ? "L116" : "L117";
  @"L116":
    %"v131" = %"v0" +p #24;
    %"v133" = %"v0" +p #56;
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk18" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v131";
    store.ptr [%"chk18" + 0] <- %"v134";
    %"v136" = %"v0" +p #8;
    %"v138" = %"v0" +p #64;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk15", %"v138";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v136";
    store.ptr [%"chk20" + 0] <- %"v139";
    %"v141" = %"v0" +p #16;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk15", %"v138";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v141";
    store.ptr [%"chk22" + 0] <- %"v144"
    => goto "L118";
  @"L117":
    %"v146" = %"v0" +p #24;
    %"v148" = %"v0" +p #56;
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk24" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v146";
    store.ptr [%"chk24" + 0] <- %"v149";
    %"v151" = %"v0" +p #8;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk16", %"v148";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v156" = %"v154" +p %"pr.3";
    %"chk26" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v151";
    store.ptr [%"chk26" + 0] <- %"v156";
    %"v158" = %"v0" +p #16;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk16", %"v148";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v163" = %"v161" +p %"pr.3";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v158";
    store.ptr [%"chk28" + 0] <- %"v163"
    => goto "L118";
  @"L118":
    %"v165" = %"v0" +p #144;
    %"chk29" : A = (HalfCheck Upper 0 8 Write 1) %"chk3", %"v165";
    store Wl [%"chk29" + 0] <- %"v107";
    %"chk30" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v169" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v171" : W = And %"v169", #4294967279;
    store Ww [%"chk30" + 0] <- %"v171"
    => ret %"pr.3"
} }.

Definition fn__IO_file_setbuf_mmap : func :=
  ir_fn{ "export" "_IO_file_setbuf_mmap"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    %"v8" = %"v0" +p #216;
    %"v9" : P = Copy $"__io_vtables";
    %"v10" = %"v9" +p #336;
    %"chk0" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk0" + 0] <- %"v10";
    %"v12" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v14" = %"v13" +p #224;
    %"v15" : P = Copy $"__io_vtables";
    %"v16" = %"v15" +p #840;
    %"chk2" : A = (Check 0 8 Write 8) %"v14";
    store.ptr [%"chk2" + 0] <- %"v16";
    call %"v20" : P = $"_IO_new_file_setbuf"(P %"v0", P %"v2", L %"v4");
    %"v25" : L = Ptoi %"v20";
    %"v26" : L = Ptoi #0;
    %"v27" : W = (Cmp Eq L) %"v25", %"v26"
    => br %"v27" ? "L21" : "L23";
  @"L21":
    %"v29" = %"v0" +p #216;
    %"v30" : P = Copy $"__io_vtables";
    %"v31" = %"v30" +p #504;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v29";
    store.ptr [%"chk3" + 0] <- %"v31";
    %"v33" = %"v0" +p #160;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v35" = %"v34" +p #224;
    %"v36" : P = Copy $"__io_vtables";
    %"v37" = %"v36" +p #1008;
    %"chk5" : A = (Check 0 8 Write 8) %"v35";
    store.ptr [%"chk5" + 0] <- %"v37"
    => goto "L23";
  @"L23":
    => ret %"v20"
} }.

Definition fn__IO_file_sync_mmap : func :=
  ir_fn{ "export" "_IO_file_sync_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Read 1) %"v4";
    %"v5" : L = (RawLoad LdL 0) %"chk0";
    %"v7" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v10" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v12" : L = Ptoi %"v8";
    %"v13" : L = Ptoi %"v11";
    %"v14" : L = Sub %"v12", %"v13";
    %"v15" : L = Sub %"v5", %"v14";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" : L = Ptoi %"v21";
    %"v26" : L = Ptoi %"v24";
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => br %"v27" ? "L16" : "L18";
  @"L16":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v33" : W = And %"v32", #256
    => br %"v33" ? "L28" : "L30";
  @"L28":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v37" = %"v0" +p #16;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v40" = %"v0" +p #24;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v42" : L = Ptoi %"v38";
    %"v43" : L = Ptoi %"v41";
    %"v44" : L = Sub %"v42", %"v43";
    %"v45" : L = Sub %"v15", %"v44"
    => goto "L30";
  @"L30" [%"pr.2" : L = phi("L28" => %"v45", "L16" => %"v15")]:
    %"v50" = %"v0" +p #112;
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v50";
    %"v51" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    call %"v53" : L = $"__lseek64"(W %"v51", L %"pr.2", W #0);
    %"v55" : W = (Cmp Ne L) %"v53", %"pr.2"
    => br %"v55" ? "L46" : "L18";
  @"L46":
    %"chk9" : A = (Renew 0 4 Read 1) %"chk5", %"v0";
    %"v57" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v58" : W = Or %"v57", #32;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk10" + 0] <- %"v58"
    => ret #4294967295;
  @"L18" [%"pr.1" : L = phi("L30" => %"pr.2", "start" => %"v15")]:
    %"v62" = %"v0" +p #144;
    %"chk11" : A = (Renew 0 8 Write 1) %"chk0", %"v62";
    store Wl [%"chk11" + 0] <- %"pr.1";
    %"v65" = %"v0" +p #16;
    %"v67" = %"v0" +p #8;
    %"v69" = %"v0" +p #24;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v69";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Renew 0 8 Write 8) %"chk2", %"v67";
    store.ptr [%"chk13" + 0] <- %"v70";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk1", %"v65";
    store.ptr [%"chk14" + 0] <- %"v70"
    => ret #0
} }.

Definition fn__IO_file_underflow_maybe_mmap : func :=
  ir_fn{ "export" "_IO_file_underflow_maybe_mmap"(P %"v0") -> (RClass W) {
  @"start":
    call void $"glibc_fileops#decide_maybe_mmap"(P %"v0");
    %"v4" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v5";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v7" = %"v5" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v8";
    rawcall %"v10" : W = %"chk2"(P %"v0")
    => ret %"v10"
} }.

Definition fn__IO_file_underflow_mmap : func :=
  ir_fn{ "export" "_IO_file_underflow_mmap"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ult L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L4";
  @"L2":
    %"v15" = %"v0" +p #8;
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk3" : A = (Check 0 1 Read 1) %"v16";
    %"v17" : W = (RawLoad (LdNarrow Ub) 0) %"chk3"
    => ret %"v17";
  @"L4":
    call %"v23" : W = $"glibc_fileops#mmap_remap_check"(P %"v0");
    %"v24" : L = (Ext Sw) %"v23";
    %"v25" : W = (Cmp Ne L) %"v24", #0
    => br %"v25" ? "L19" : "L21";
  @"L19":
    %"v27" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v4" : L = Ptoi %"v28";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v30" = %"v28" +p #32;
    %"chk5" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v31";
    rawcall %"v33" : W = %"chk6"(P %"v0")
    => ret %"v33";
  @"L21":
    %"v39" = %"v0" +p #8;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v39";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v42" = %"v0" +p #16;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v44" : L = Ptoi %"v40";
    %"v45" : L = Ptoi %"v43";
    %"v46" : W = (Cmp Ult L) %"v44", %"v45"
    => br %"v46" ? "L35" : "L37";
  @"L35":
    %"v48" = %"v0" +p #8;
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk10" : A = (Check 0 1 Read 1) %"v49";
    %"v50" : W = (RawLoad (LdNarrow Ub) 0) %"chk10"
    => ret %"v50";
  @"L37":
    %"chk11" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v53" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v54" : W = Or %"v53", #16;
    %"chk12" : A = (Renew 0 4 Write 1) %"chk11", %"v0";
    store Ww [%"chk12" + 0] <- %"v54"
    => ret #4294967295
} }.

Definition fn__IO_file_xsgetn_maybe_mmap : func :=
  ir_fn{ "export" "_IO_file_xsgetn_maybe_mmap"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    call void $"glibc_fileops#decide_maybe_mmap"(P %"v0");
    %"v8" = %"v0" +p #216;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v4" : L = Ptoi %"v9";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v11" = %"v9" +p #64;
    %"chk1" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v12";
    rawcall %"v16" : L = %"chk2"(P %"v0", P %"v2", L %"v4")
    => ret %"v16"
} }.

Definition fn__IO_file_xsgetn_mmap : func :=
  ir_fn{ "export" "_IO_file_xsgetn_mmap"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v9" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v19" : L = Ptoi %"v15";
    %"v20" : L = Ptoi %"v18";
    %"v21" : L = Sub %"v19", %"v20";
    %"v27" : W = (Cmp Ult L) %"v21", %"v4"
    => br %"v27" ? "L22" : "L24";
  @"L22":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v33" : W = And %"v32", #256;
    %"v34" : L = (Ext Sw) %"v33";
    %"v35" : W = (Cmp Ne L) %"v34", #0
    => br %"v35" ? "L28" : "L30";
  @"L28":
    call %"v39" : P = $"__GI_mempcpy"(P %"v2", P %"v10", L %"v21");
    %"v42" : L = Sub %"v4", %"v21";
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v45" = %"v0" +p #8;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v48" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v53" : L = Ptoi %"v49";
    %"v54" : L = Ptoi %"v52";
    %"v55" : L = Sub %"v53", %"v54"
    => goto "L30";
  @"L30" [%"pr.11" : P = phi("L28" => %"v39", "L22" => %"v2"); %"pr.7" : P = phi("L28" => %"v46", "L22" => %"v10"); %"pr.4" : L = phi("L28" => %"v55", "L22" => %"v21"); %"pr.2" : L = phi("L28" => %"v42", "L22" => %"v4")]:
    %"v61" : W = (Cmp Ult L) %"pr.4", %"pr.2"
    => br %"v61" ? "L56" : "L24";
  @"L56":
    call %"v66" : W = $"glibc_fileops#mmap_remap_check"(P %"v0");
    %"v67" : L = (Ext Sw) %"v66";
    %"v68" : W = (Cmp Ne L) %"v67", #0
    => br %"v68" ? "L62" : "L64";
  @"L62":
    %"v71" : L = Ptoi %"pr.11";
    %"v72" : L = Ptoi %"v2";
    %"v73" : L = Sub %"v71", %"v72";
    %"v75" = %"v0" +p #216;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v76";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v78" = %"v76" +p #64;
    %"chk8" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : F = CheckFunction %"v79";
    rawcall %"v83" : L = %"chk9"(P %"v0", P %"v2", L %"pr.2");
    %"v84" : L = Add %"v73", %"v83"
    => ret %"v84";
  @"L64":
    %"v87" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk0", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v90" = %"v0" +p #16;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk1", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v93" : L = Ptoi %"v91";
    %"v94" : L = Ptoi %"v88";
    %"v95" : L = Sub %"v93", %"v94"
    => goto "L24";
  @"L24" [%"pr.10" : P = phi("L64" => %"pr.11", "L30" => %"pr.11", "start" => %"v2"); %"pr.6" : P = phi("L64" => %"v88", "L30" => %"pr.7", "start" => %"v10"); %"pr.3" : L = phi("L64" => %"v95", "L30" => %"pr.4", "start" => %"v21"); %"pr.1" : L = phi("L64" => %"pr.2", "L30" => %"pr.2", "start" => %"v4")]:
    %"v101" : W = (Cmp Ult L) %"pr.3", %"pr.1"
    => br %"v101" ? "L96" : "L98";
  @"L96":
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v104" : W = Or %"v103", #16;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk12", %"v0";
    store Ww [%"chk13" + 0] <- %"v104"
    => goto "L98";
  @"L98":
    %"v109" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v109" ? "L105" : "L107";
  @"L105":
    => br %"v101" ? "L112" : "L111";
  @"L111":
    => goto "L112";
  @"L112" [%"v118" : L = phi("L111" => %"pr.1", "L105" => %"pr.3")]:
    call %"v122" : P = $"__GI_mempcpy"(P %"pr.10", P %"pr.6", L %"v118");
    %"v124" = %"v0" +p #8;
    %"v127" = %"pr.6" +p %"v118";
    %"chk14" : A = (Renew 0 8 Write 8) %"chk0", %"v124";
    store.ptr [%"chk14" + 0] <- %"v127"
    => goto "L107";
  @"L107" [%"pr.9" : P = phi("L112" => %"v122", "L98" => %"pr.10")]:
    %"v130" : L = Ptoi %"pr.9";
    %"v131" : L = Ptoi %"v2";
    %"v132" : L = Sub %"v130", %"v131"
    => ret %"v132"
} }.

Definition fn__IO_new_do_write : func :=
  ir_fn{ "export" "_IO_new_do_write"(P %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v10" : W = (Cmp Eq L) %"v4", #0
    => br %"v10" ? "L12" : "iw_1.start";
  @"iw_1.start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"iw_1.v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"iw_1.v12" : W = And %"iw_1.v11", #4096
    => br %"iw_1.v12" ? "iw_1.L7" : "iw_1.L8";
  @"iw_1.L7":
    %"iw_1.v14" = %"v0" +p #144;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v14";
    store Wl [%"chk1" + 0] <- #18446744073709551615
    => goto "iw_1.L9";
  @"iw_1.L8":
    %"iw_1.v21" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v21";
    %"iw_1.v22" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v24" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v24";
    %"iw_1.v25" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" : L = Ptoi %"iw_1.v22";
    %"iw_1.v27" : L = Ptoi %"iw_1.v25";
    %"iw_1.v28" : W = (Cmp Ne L) %"iw_1.v26", %"iw_1.v27"
    => br %"iw_1.v28" ? "iw_1.L17" : "iw_1.L9";
  @"iw_1.L17":
    %"iw_1.v31" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v31";
    %"iw_1.v32" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v32";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join";
  @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join";
  @"iw_1.iw_1.join":
    %"iw_1.v34" = %"iw_1.v32" +p #128;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v34";
    %"iw_1.v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v38" = %"v0" +p #32;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk3", %"iw_1.v38";
    %"iw_1.v39" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v41" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v41";
    %"iw_1.v42" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v43" : L = Ptoi %"iw_1.v39";
    %"iw_1.v44" : L = Ptoi %"iw_1.v42";
    %"iw_1.v45" : L = Sub %"iw_1.v43", %"iw_1.v44";
    %"chk8" : F = CheckFunction %"iw_1.v35";
    rawcall %"iw_1.v46" : L = %"chk8"(P %"v0", L %"iw_1.v45", W #1);
    %"iw_1.v53" : W = (Cmp Eq L) %"iw_1.v46", #18446744073709551615
    => br %"iw_1.v53" ? "iw_1.join" : "iw_1.L49";
  @"iw_1.L49":
    %"iw_1.v56" = %"v0" +p #144;
    %"chk9" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v56";
    store Wl [%"chk9" + 0] <- %"iw_1.v46"
    => goto "iw_1.L9";
  @"iw_1.L9":
    %"iw_1.v59" = %"v0" +p #216;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.iw_2.v4" : L = Ptoi %"iw_1.v60";
    %"iw_1.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_2.v8" : L = Ptoi %"iw_1.iw_2.v7";
    %"iw_1.iw_2.v9" : L = Sub %"iw_1.iw_2.v4", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v15" : W = (Cmp Uge L) %"iw_1.iw_2.v9", #2352
    => br %"iw_1.iw_2.v15" ? "iw_1.iw_2.L10" : "iw_1.iw_2.join";
  @"iw_1.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_2.join";
  @"iw_1.iw_2.join":
    %"iw_1.v62" = %"iw_1.v60" +p #120;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v62";
    %"iw_1.v63" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : F = CheckFunction %"iw_1.v63";
    rawcall %"iw_1.v67" : L = %"chk12"(P %"v0", P %"v2", L %"v4");
    %"iw_1.v72" = %"v0" +p #128;
    %"chk13" : A = (HalfCheck Upper 0 2 Read 1) %"chk0", %"iw_1.v72";
    %"iw_1.v73" : W = (RawLoad (LdNarrow Uh) 0) %"chk13"
    => br %"iw_1.v73" ? "iw_1.L74" : "iw_1.L75";
  @"iw_1.L74":
    %"iw_1.v77" : W = (Cmp Ne L) %"iw_1.v67", #0
    => goto "iw_1.L75";
  @"iw_1.L75" [%"iw_1.v79" : W = phi("iw_1.iw_2.join" => #0, "iw_1.L74" => %"iw_1.v77")]:
    => br %"iw_1.v79" ? "iw_1.L68" : "iw_1.L70";
  @"iw_1.L68":
    %"iw_1.v81" = %"v0" +p #128;
    %"iw_1.v84" : W = (RawLoad (LdNarrow Uh) 0) %"chk13";
    %"iw_1.v85" : W = Sub %"iw_1.v84", #1;
    call %"iw_1.v88" : W = $"__GI__IO_adjust_column"(W %"iw_1.v85", P %"v2", W %"iw_1.v67");
    %"iw_1.v89" : W = Add %"iw_1.v88", #1;
    %"iw_1.v90" : W = (Ext Uh) %"iw_1.v89";
    %"chk15" : A = (Renew 0 2 Write 1) %"chk13", %"iw_1.v81";
    store Wh [%"chk15" + 0] <- %"iw_1.v90"
    => goto "iw_1.L70";
  @"iw_1.L70":
    %"iw_1.v92" = %"v0" +p #24;
    %"iw_1.v94" = %"v0" +p #56;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v94";
    %"iw_1.v95" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v92";
    store.ptr [%"chk17" + 0] <- %"iw_1.v95";
    %"iw_1.v97" = %"v0" +p #8;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk16", %"iw_1.v94";
    %"iw_1.v100" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v97";
    store.ptr [%"chk19" + 0] <- %"iw_1.v100";
    %"iw_1.v102" = %"v0" +p #16;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk16", %"iw_1.v94";
    %"iw_1.v105" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v102";
    store.ptr [%"chk21" + 0] <- %"iw_1.v105";
    %"iw_1.v107" = %"v0" +p #32;
    %"iw_1.v109" = %"v0" +p #40;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk16", %"iw_1.v94";
    %"iw_1.v112" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v109";
    store.ptr [%"chk23" + 0] <- %"iw_1.v112";
    %"chk24" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v107";
    store.ptr [%"chk24" + 0] <- %"iw_1.v112";
    %"iw_1.v114" = %"v0" +p #48;
    %"iw_1.v119" = %"v0" +p #192;
    %"chk25" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_1.v119";
    %"iw_1.v120" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"iw_1.v121" : W = (Cmp Sle W) %"iw_1.v120", #0
    => br %"iw_1.v121" ? "iw_1.L122" : "iw_1.L123";
  @"iw_1.L122":
    %"chk26" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v125" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"iw_1.v127" : W = And %"iw_1.v125", #514;
    %"iw_1.v128" : W = (Cmp Ne W) %"iw_1.v127", #0
    => goto "iw_1.L123";
  @"iw_1.L123" [%"iw_1.v129" : W = phi("iw_1.L70" => #0, "iw_1.L122" => %"iw_1.v128")]:
    => br %"iw_1.v129" ? "iw_1.L115" : "iw_1.L116";
  @"iw_1.L115":
    %"iw_1.v131" = %"v0" +p #56;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk16", %"iw_1.v131";
    %"iw_1.v132" : P = (RawLoadPointer 0 load_effects) %"chk27"
    => goto "iw_1.L117";
  @"iw_1.L116":
    %"iw_1.v134" = %"v0" +p #64;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v134";
    %"iw_1.v135" : P = (RawLoadPointer 0 load_effects) %"chk28"
    => goto "iw_1.L117";
  @"iw_1.L117" [%"iw_1.v136" : P = phi("iw_1.L115" => %"iw_1.v132", "iw_1.L116" => %"iw_1.v135")]:
    %"chk29" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v114";
    store.ptr [%"chk29" + 0] <- %"iw_1.v136"
    => goto "iw_1.join";
  @"iw_1.join" [%"v16" : L = phi("iw_1.L117" => %"iw_1.v67", "iw_1.iw_1.join" => #0)]:
    %"v18" : W = (Cmp Eq L) %"v16", %"v4"
    => goto "L12";
  @"L12" [%"v20" : W = phi("start" => #1, "iw_1.join" => %"v18")]:
    => br %"v20" ? "L8" : "L7";
  @"L7":
    => goto "L8";
  @"L8" [%"v22" : W = phi("L7" => #4294967295, "L12" => #0)]:
    => ret %"v22"
} }.

Definition fn__IO_new_file_close_it : func :=
  ir_fn{ "export" "_IO_new_file_close_it"(P %"v0") -> (RClass W) {
  @"start":
    call %"v4" : W = $"_IO_file_close_maybe_unlink"(P %"v0", W #1)
    => ret %"v4"
} }.

Definition fn__IO_new_file_finish : func :=
  ir_fn{ "export" "_IO_new_file_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = (Cmp Ne W) %"v9", #4294967295
    => br %"v11" ? "L4" : "L6";
  @"L4":
    %"v16" = %"v0" +p #192;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v16";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v18" : W = (Cmp Sle W) %"v17", #0
    => br %"v18" ? "L12" : "L13";
  @"L12":
    %"v21" = %"v0" +p #32;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v24" = %"v0" +p #40;
    %"v25" : P = (RawLoadPointer 8 load_effects) %"chk2";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v29" : L = Ptoi %"v25";
    %"v30" : L = Ptoi %"v28";
    %"v31" : L = Sub %"v29", %"v30";
    call %"v32" : W = $"_IO_new_do_write"(P %"v0", P %"v22", L %"v31")
    => goto "L14";
  @"L13":
    %"v35" = %"v0" +p #160;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v37" = %"v36" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v42" = %"v41" +p #32;
    %"chk8" : A = (Check 0 8 Read 8) %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v47" = %"v46" +p #24;
    %"chk10" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v49" : L = Ptoi %"v43";
    %"v50" : L = Ptoi %"v48";
    %"v51" : L = Sub %"v49", %"v50";
    %"v52" : L = Div %"v51", #4;
    call %"v53" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v38", L %"v52")
    => goto "L14";
  @"L14":
    %"chk11" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v59" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v60" : W = And %"v59", #64;
    %"v61" : W = (Cmp Eq W) %"v60", #0
    => br %"v61" ? "L55" : "L6";
  @"L55":
    %"v63" = %"v0" +p #216;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v4" : L = Ptoi %"v64";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v66" = %"v64" +p #136;
    %"chk13" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : F = CheckFunction %"v67";
    rawcall %"v69" : W = %"chk14"(P %"v0")
    => goto "L6";
  @"L6":
    call void $"__GI__IO_default_finish"(P %"v0", W #0)
    => ret void
} }.

Definition fn__IO_new_file_fopen : func :=
  ir_fn{ "export" "_IO_new_file_fopen"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass P) {
  @"start":
    %"v159" : P = (Alloc 8) #32;
    %"v20" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v23" : W = (Cmp Ne W) %"v21", #4294967295
    => br %"v23" ? "L16" : "L18";
  @"L16":
    => ret #0;
  @"L18":
    %"chk1" : A = (Check 0 1 Read 1) %"v4";
    %"v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v38" : W = (Cmp Eq W) %"v26", #114
    => br %"v38" ? "L45" : "L39";
  @"L35":
    %"v36" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Write 1) %"v36";
    store Ww [%"chk2" + 0] <- #22
    => ret #0;
  @"L39":
    %"v40" : W = (Cmp Eq W) %"v26", #119
    => br %"v40" ? "L45" : "L41";
  @"L41":
    %"v42" : W = (Cmp Eq W) %"v26", #97
    => br %"v42" ? "L45" : poll "L35";
  @"L45" [%"pr.12" : P = phi("L47" => %"pr.13", "L18" => %"v4", "L39" => %"v4", "L41" => %"v4"); %"pr.11" : W = phi("L47" => %"v131", "L18" => #1, "L39" => #1, "L41" => #1); %"pr.9" : W = phi("L47" => %"pr.10", "L18" => #8, "L39" => #4, "L41" => #4100); %"pr.6" : W = phi("L47" => %"pr.7", "L18" => #0, "L39" => #1, "L41" => #1); %"pr.3" : W = phi("L47" => %"pr.4", "L18" => #0, "L39" => #576, "L41" => #1088); %"pr.1" : P = phi("L47" => %"v52", "L18" => %"v4", "L39" => %"v4", "L41" => %"v4")]:
    %"v50" : W = (Cmp Slt W) %"pr.11", #7
    => br %"v50" ? "L46" : "L48";
  @"L46":
    %"v52" = %"pr.1" +p #1;
    %"chk3" : A = (Check 0 1 Read 1) %"v52";
    %"v53" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v111" : W = (Cmp Slt W) %"v53", #99
    => br %"v111" ? "L112" : "L113";
  @"L58":
    %"v60" : W = And %"pr.9", #4096
    => goto "L47";
  @"L62":
    %"v64" : W = Or %"pr.3", #128
    => goto "L47";
  @"L68":
    %"v70" = %"v0" +p #116;
    %"chk4" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v70";
    %"v71" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v72" : W = Shl %"v71", #8;
    %"v73" : W = Sar %"v72", #8;
    %"v74" : W = Or %"v73", #1;
    %"v75" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v76" : W = And %"v75", #4278190080;
    %"v77" : W = And %"v74", #16777215;
    %"v78" : W = Or %"v76", %"v77";
    %"chk6" : A = (Renew 0 4 Write 1) %"chk4", %"v70";
    store Ww [%"chk6" + 0] <- %"v78"
    => goto "L47";
  @"L81":
    %"v83" = %"v0" +p #116;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v83";
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v85" : W = Shl %"v84", #8;
    %"v86" : W = Sar %"v85", #8;
    %"v87" : W = Or %"v86", #2;
    %"v88" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v89" : W = And %"v88", #4278190080;
    %"v90" : W = And %"v87", #16777215;
    %"v91" : W = Or %"v89", %"v90";
    %"chk9" : A = (Renew 0 4 Write 1) %"chk7", %"v83";
    store Ww [%"chk9" + 0] <- %"v91"
    => goto "L47";
  @"L94":
    %"v96" : W = Or %"pr.3", #524288;
    %"v98" = %"v0" +p #116;
    %"chk10" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v98";
    %"v99" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v100" : W = Shl %"v99", #8;
    %"v101" : W = Sar %"v100", #8;
    %"v102" : W = Or %"v101", #64;
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v104" : W = And %"v103", #4278190080;
    %"v105" : W = And %"v102", #16777215;
    %"v106" : W = Or %"v104", %"v105";
    %"chk12" : A = (Renew 0 4 Write 1) %"chk10", %"v98";
    store Ww [%"chk12" + 0] <- %"v106"
    => goto "L47";
  @"L112":
    %"v114" : W = (Cmp Eq W) %"v53", #0
    => br %"v114" ? "L48" : "L115";
  @"L115":
    %"v116" : W = (Cmp Eq W) %"v53", #43
    => br %"v116" ? poll "L58" : "L117";
  @"L117":
    %"v118" : W = (Cmp Eq W) %"v53", #44
    => br %"v118" ? "L48" : "L119";
  @"L119":
    %"v120" : W = (Cmp Eq W) %"v53", #98
    => br %"v120" ? "L47" : "L121";
  @"L121":
    => goto "L47";
  @"L113":
    %"v122" : W = (Cmp Eq W) %"v53", #99
    => br %"v122" ? poll "L81" : "L123";
  @"L123":
    %"v124" : W = (Cmp Eq W) %"v53", #101
    => br %"v124" ? poll "L94" : "L125";
  @"L125":
    %"v126" : W = (Cmp Eq W) %"v53", #109
    => br %"v126" ? poll "L68" : "L127";
  @"L127":
    %"v128" : W = (Cmp Eq W) %"v53", #120
    => br %"v128" ? poll "L62" : "L47";
  @"L47" [%"pr.13" : P = phi("L58" => %"v52", "L62" => %"v52", "L68" => %"pr.12", "L81" => %"pr.12", "L94" => %"pr.12", "L119" => %"v52", "L121" => %"pr.12", "L127" => %"pr.12"); %"pr.10" : W = phi("L58" => %"v60", "L62" => %"pr.9", "L68" => %"pr.9", "L81" => %"pr.9", "L94" => %"pr.9", "L119" => %"pr.9", "L121" => %"pr.9", "L127" => %"pr.9"); %"pr.7" : W = phi("L58" => #2, "L62" => %"pr.6", "L68" => %"pr.6", "L81" => %"pr.6", "L94" => %"pr.6", "L119" => %"pr.6", "L121" => %"pr.6", "L127" => %"pr.6"); %"pr.4" : W = phi("L58" => %"pr.3", "L62" => %"v64", "L68" => %"pr.3", "L81" => %"pr.3", "L94" => %"v96", "L119" => %"pr.3", "L121" => %"pr.3", "L127" => %"pr.3")]:
    %"v131" : W = Add %"pr.11", #1
    => goto poll "L45";
  @"L48":
    %"v136" : W = Or %"pr.6", %"pr.3";
    call %"v140" : P = $"__GI__IO_file_open"(P %"v0", P %"v2", W %"v136", W #438, W %"pr.9", W %"v6");
    %"v145" : L = Ptoi %"v140";
    %"v146" : L = Ptoi #0;
    %"v147" : W = (Cmp Ne L) %"v145", %"v146"
    => br %"v147" ? "L141" : "L143";
  @"L141":
    %"v149" = %"pr.12" +p #1;
    %"v150" : P = Copy $"glibc_fileops#str.265";
    call %"v151" : P = $"__GI_strstr"(P %"v149", P %"v150");
    %"v156" : L = Ptoi %"v151";
    %"v158" : W = (Cmp Ne L) %"v156", %"v146"
    => br %"v158" ? "L152" : "L143";
  @"L152":
    %"v163" = %"v151" +p #5;
    call %"v164" : P = $"__GI___strchrnul"(P %"v163", W #44);
    %"v169" : L = Ptoi %"v164";
    %"v170" : L = Ptoi %"v163";
    %"v171" : L = Sub %"v169", %"v170";
    %"v172" : L = Add %"v171", #3;
    call %"v173" : P = $"malloc"(L %"v172");
    %"v178" : L = Ptoi %"v173";
    %"v180" : W = (Cmp Eq L) %"v178", %"v146"
    => br %"v180" ? "L174" : "L176";
  @"L174":
    %"v182" : P = Copy $"__libc_errno";
    %"chk13" : A = (Check 0 4 Read 1) %"v182";
    %"v183" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    call %"v185" : W = $"_IO_new_file_close_it"(P %"v0");
    %"v186" : P = Copy $"__libc_errno";
    %"chk14" : A = (Check 0 4 Write 1) %"v186";
    store Ww [%"chk14" + 0] <- %"v183"
    => ret #0;
  @"L176":
    %"v191" = %"v151" +p #5;
    %"v196" : L = Ptoi %"v191";
    %"v197" : L = Sub %"v169", %"v196";
    call %"v198" : P = $"__GI_mempcpy"(P %"v173", P %"v191", L %"v197");
    %"chk15" : A = (Check 0 1 Write 1) %"v198";
    store Wb [%"chk15" + 0] <- #0
    => goto "iw_1.L5";
  @"iw_1.L5" [%"iw_1.pr.9" : W = phi("iw_1.L13" => %"iw_1.pr.8", "L176" => #0); %"iw_1.pr.5" : P = phi("iw_1.L13" => %"iw_1.v125", "L176" => %"v173"); %"iw_1.pr.4" : P = phi("iw_1.L13" => %"iw_1.pr.3", "L176" => %"v173")]:
    %"chk16" : A = (Check 0 1 Read 1) %"iw_1.pr.5";
    %"iw_1.v9" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"iw_1.v10" : W = (Cmp Ne W) %"iw_1.v9", #0
    => br %"iw_1.v10" ? "iw_1.L6" : "iw_1.L126";
  @"iw_1.L6":
    %"iw_1.v14" : P = Copy $"_nl_C_locobj";
    %"iw_1.v15" = %"iw_1.v14" +p #104;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v15";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 1 Read 1) %"chk16", %"iw_1.pr.5";
    %"iw_1.v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v19" : L = (Ext Sw) %"iw_1.v18";
    %"iw_1.v20" : L = Shl %"iw_1.v19", #1;
    %"iw_1.v21" = %"iw_1.v16" +p %"iw_1.v20";
    %"chk19" : A = (Check 0 2 Read 1) %"iw_1.v21";
    %"iw_1.v22" : W = (RawLoad (LdNarrow Uh) 0) %"chk19";
    %"iw_1.v23" : W = And %"iw_1.v22", #8
    => br %"iw_1.v23" ? "iw_1.L25" : "iw_1.L24";
  @"iw_1.L24":
    %"iw_1.v27" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v28" : W = (Cmp Eq W) %"iw_1.v27", #95
    => goto "iw_1.L25";
  @"iw_1.L25" [%"iw_1.v30" : W = phi("iw_1.L6" => #1, "iw_1.L24" => %"iw_1.v28")]:
    => br %"iw_1.v30" ? "iw_1.L32" : "iw_1.L31";
  @"iw_1.L31":
    %"iw_1.v34" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v35" : W = (Cmp Eq W) %"iw_1.v34", #45
    => goto "iw_1.L32";
  @"iw_1.L32" [%"iw_1.v37" : W = phi("iw_1.L25" => #1, "iw_1.L31" => %"iw_1.v35")]:
    => br %"iw_1.v37" ? "iw_1.L39" : "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v41" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v42" : W = (Cmp Eq W) %"iw_1.v41", #46
    => goto "iw_1.L39";
  @"iw_1.L39" [%"iw_1.v44" : W = phi("iw_1.L32" => #1, "iw_1.L38" => %"iw_1.v42")]:
    => br %"iw_1.v44" ? "iw_1.L46" : "iw_1.L45";
  @"iw_1.L45":
    %"iw_1.v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v49" : W = (Cmp Eq W) %"iw_1.v48", #44
    => goto "iw_1.L46";
  @"iw_1.L46" [%"iw_1.v51" : W = phi("iw_1.L39" => #1, "iw_1.L45" => %"iw_1.v49")]:
    => br %"iw_1.v51" ? "iw_1.L53" : "iw_1.L52";
  @"iw_1.L52":
    %"iw_1.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v56" : W = (Cmp Eq W) %"iw_1.v55", #58
    => goto "iw_1.L53";
  @"iw_1.L53" [%"iw_1.v58" : W = phi("iw_1.L46" => #1, "iw_1.L52" => %"iw_1.v56")]:
    => br %"iw_1.v58" ? "iw_1.L11" : "iw_1.L12";
  @"iw_1.L11":
    %"iw_1.v60" = %"iw_1.pr.4" +p #1;
    %"iw_1.v98" : P = Copy $"_nl_C_locobj";
    %"iw_1.v99" = %"iw_1.v98" +p #120;
    %"chk25" : A = (Check 0 8 Read 8) %"iw_1.v99";
    %"iw_1.v100" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : A = (Renew 0 1 Read 1) %"chk16", %"iw_1.pr.5";
    %"iw_1.v102" : W = (RawLoad (LdNarrow Sb) 0) %"chk26";
    %"iw_1.v103" : L = (Ext Sw) %"iw_1.v102";
    %"iw_1.v104" : L = Shl %"iw_1.v103", #2;
    %"iw_1.v105" = %"iw_1.v100" +p %"iw_1.v104";
    %"chk27" : A = (Check 0 4 Read 1) %"iw_1.v105";
    %"iw_1.v106" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"iw_1.v108" : W = (Ext Sb) %"iw_1.v106";
    %"chk28" : A = (Check 0 1 Write 1) %"iw_1.pr.4";
    store Wb [%"chk28" + 0] <- %"iw_1.v108"
    => goto "iw_1.L13";
  @"iw_1.L12":
    %"iw_1.v113" : W = (RawLoad (LdNarrow Sb) 0) %"chk18";
    %"iw_1.v114" : W = (Cmp Eq W) %"iw_1.v113", #47
    => br %"iw_1.v114" ? "iw_1.L109" : "iw_1.L13";
  @"iw_1.L109":
    %"iw_1.v119" : W = Add %"iw_1.pr.9", #1;
    %"iw_1.v120" : W = (Cmp Eq W) %"iw_1.v119", #3
    => br %"iw_1.v120" ? "iw_1.L126" : "iw_1.L117";
  @"iw_1.L117":
    %"iw_1.v123" = %"iw_1.pr.4" +p #1;
    %"chk30" : A = (Check 0 1 Write 1) %"iw_1.pr.4";
    store Wb [%"chk30" + 0] <- #47
    => goto "iw_1.L13";
  @"iw_1.L13" [%"iw_1.pr.8" : W = phi("iw_1.L11" => %"iw_1.pr.9", "iw_1.L117" => %"iw_1.v119", "iw_1.L12" => %"iw_1.pr.9"); %"iw_1.pr.3" : P = phi("iw_1.L11" => %"iw_1.v60", "iw_1.L117" => %"iw_1.v123", "iw_1.L12" => %"iw_1.pr.4")]:
    %"iw_1.v125" = %"iw_1.pr.5" +p #1
    => goto poll "iw_1.L5";
  @"iw_1.L126" [%"iw_1.pr.7" : W = phi("iw_1.L127" => %"iw_1.v130", "iw_1.L5" => %"iw_1.pr.9", "iw_1.L109" => %"iw_1.v119"); %"iw_1.pr.2" : P = phi("iw_1.L127" => %"iw_1.v133", "iw_1.L5" => %"iw_1.pr.4", "iw_1.L109" => %"iw_1.pr.4")]:
    %"iw_1.v130" : W = Add %"iw_1.pr.7", #1;
    %"iw_1.v131" : W = (Cmp Slt W) %"iw_1.pr.7", #2
    => br %"iw_1.v131" ? "iw_1.L127" : "iw_1.L128";
  @"iw_1.L127":
    %"iw_1.v133" = %"iw_1.pr.2" +p #1;
    %"chk31" : A = (Check 0 1 Write 1) %"iw_1.pr.2";
    store Wb [%"chk31" + 0] <- #47
    => goto poll "iw_1.L126";
  @"iw_1.L128":
    %"chk32" : A = (Check 0 1 Write 1) %"iw_1.pr.2";
    store Wb [%"chk32" + 0] <- #0;
    %"v208" = %"v173" +p #2;
    %"chk33" : A = (Check 0 1 Read 1) %"v208";
    %"v209" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v210" : W = (Cmp Eq W) %"v209", #0
    => br %"v210" ? "L204" : "L206";
  @"L204":
    %"v213" = %"v151" +p #5
    => goto "iw_2.L6";
  @"iw_2.L6" [%"iw_2.pr.4" : P = phi("iw_2.L6" => %"iw_2.v10", "L204" => %"v173"); %"iw_2.pr.3" : P = phi("iw_2.L6" => %"iw_2.v54", "L204" => %"v213")]:
    %"iw_2.v10" = %"iw_2.pr.4" +p #1;
    %"iw_2.v50" : P = Copy $"_nl_C_locobj";
    %"iw_2.v51" = %"iw_2.v50" +p #120;
    %"chk34" : A = (Check 0 8 Read 8) %"iw_2.v51";
    %"iw_2.v52" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_2.v54" = %"iw_2.pr.3" +p #1;
    %"chk35" : A = (Check 0 1 Read 1) %"iw_2.pr.3";
    %"iw_2.v55" : W = (RawLoad (LdNarrow Sb) 0) %"chk35";
    %"iw_2.v56" : L = (Ext Sw) %"iw_2.v55";
    %"iw_2.v57" : L = Shl %"iw_2.v56", #2;
    %"iw_2.v58" = %"iw_2.v52" +p %"iw_2.v57";
    %"chk36" : A = (Check 0 4 Read 1) %"iw_2.v58";
    %"iw_2.v59" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"iw_2.v61" : W = (Ext Sb) %"iw_2.v59";
    %"chk37" : A = (Check 0 1 Write 1) %"iw_2.pr.4";
    store Wb [%"chk37" + 0] <- %"iw_2.v61";
    %"iw_2.v62" : W = (Cmp Ne W) %"iw_2.v61", #0
    => br %"iw_2.v62" ? poll "iw_2.L6" : "L206";
  @"L206":
    call %"v217" : W = $"__wcsmbs_named_conv"(P %"v159", P %"v173");
    %"v218" : W = (Cmp Ne W) %"v217", #0
    => br %"v218" ? "L201" : "L203";
  @"L201":
    call %"v220" : W = $"_IO_new_file_close_it"(P %"v0");
    call void $"free"(P %"v173");
    %"v222" : P = Copy $"__libc_errno";
    %"chk38" : A = (Check 0 4 Write 1) %"v222";
    store Ww [%"chk38" + 0] <- #22
    => ret #0;
  @"L203":
    call void $"free"(P %"v173");
    %"v228" = %"v159" +p #8;
    %"chk39" : A = (Check 0 8 Read 1) %"v228";
    %"v229" : L = (RawLoad LdL 0) %"chk39";
    %"v230" : W = (Cmp Eq L) %"v229", #1
    => br %"v230" ? "L227" : "L226";
  @"L226":
    %"v231" : P = Copy $"glibc_fileops#str.266";
    %"v232" : P = Copy $"glibc_fileops#str.267";
    %"v233" : P = Copy $"glibc_fileops#str.268";
    call void $"__libc_assert_fail"(P %"v231", P %"v232", W #372, P %"v233")
    => goto "L227";
  @"L227":
    %"v237" = %"v159" +p #24;
    %"chk40" : A = (HalfCheck Upper 0 8 Read 1) %"chk39", %"v237";
    %"v238" : L = (RawLoad LdL 0) %"chk40";
    %"v239" : W = (Cmp Eq L) %"v238", #1
    => br %"v239" ? "L236" : "L235";
  @"L235":
    %"v240" : P = Copy $"glibc_fileops#str.269";
    %"v241" : P = Copy $"glibc_fileops#str.267";
    %"v242" : P = Copy $"glibc_fileops#str.268";
    call void $"__libc_assert_fail"(P %"v240", P %"v241", W #373, P %"v242")
    => goto "L236";
  @"L236":
    code ((app ir[ %"v244" = %"v0" +p #160;
      %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v244";
      %"v245" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"v248" : P = (RawLoadPointer 0 load_effects) %"chk41";
      %"v249" = %"v248" +p #8;
      %"chk43" : A = (Check 0 8 Read 8) %"v249";
      %"v250" : P = (RawLoadPointer 0 load_effects) %"chk43";
      %"chk44" : A = (Check 0 8 Write 8) %"v245";
      store.ptr [%"chk44" + 0] <- %"v250";
      %"chk45" : A = (Renew 0 8 Read 8) %"chk41", %"v244";
      %"v253" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v254" = %"v253" +p #32;
      %"v257" : P = (RawLoadPointer 0 load_effects) %"chk45";
      %"v258" = %"v257" +p #24;
      %"chk47" : A = (Check 0 8 Read 8) %"v258";
      %"v259" : P = (RawLoadPointer 0 load_effects) %"chk47";
      %"chk48" : A = (Check 0 8 Write 8) %"v254";
      store.ptr [%"chk48" + 0] <- %"v259";
      %"chk49" : A = (Renew 0 8 Read 8) %"chk41", %"v244";
      %"v262" : P = (RawLoadPointer 0 load_effects) %"chk49";
      %"v263" = %"v262" +p #88;
      call %"v264" : P = $"__GI_memset"(P %"v263", W #0, L #8);
      %"chk50" : A = (Renew 0 8 Read 8) %"chk41", %"v244";
      %"v267" : P = (RawLoadPointer 0 load_effects) %"chk50";
      %"v268" = %"v267" +p #96;
      call %"v269" : P = $"__GI_memset"(P %"v268", W #0, L #8);
      %"v271" = %"v0" +p #152;
      %"chk51" : A = (Renew 0 8 Read 8) %"chk41", %"v244";
      %"v274" : P = (RawLoadPointer 0 load_effects) %"chk51";
      %"v275" = %"v274" +p #104;
      %"chk52" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v271";
      store.ptr [%"chk52" + 0] <- %"v275";
      %"chk53" : A = (HalfCheck Lower 0 8 Read 8) %"chk39", %"v159";
      %"v277" : P = (RawLoadPointer 0 load_effects) %"chk53";
      %"chk54" : A = (Check 0 8 Write 8) %"v275";
      store.ptr [%"chk54" + 0] <- %"v277";
      %"v279" = %"v275" +p #8;
      %"v280" = %"v279" +p #20;
      %"chk55" : A = (HalfCheck Upper 0 4 Write 1) %"chk54", %"v280";
      store Ww [%"chk55" + 0] <- #0;
      %"v283" = %"v279" +p #24;
      %"chk56" : A = (HalfCheck Upper 0 4 Write 1) %"chk55", %"v283";
      store Ww [%"chk56" + 0] <- #1] ir[ %"v286" = %"v279" +p #16;
      %"chk57" : A = (HalfCheck Lower 0 4 Write 1) %"chk55", %"v286";
      store Ww [%"chk57" + 0] <- #1;
      %"v289" = %"v279" +p #32;
      %"v291" = %"v140" +p #160;
      %"chk58" : A = (Check 0 8 Read 8) %"v291";
      %"v292" : P = (RawLoadPointer 0 load_effects) %"chk58";
      %"v293" = %"v292" +p #88;
      %"chk59" : A = (HalfCheck Upper 0 8 Write 8) %"chk55", %"v289";
      store.ptr [%"chk59" + 0] <- %"v293";
      %"v295" = %"v275" +p #56;
      %"v296" = %"v159" +p #16;
      %"chk60" : A = (HalfCheck Upper 0 8 Read 8) %"chk39", %"v296";
      %"v297" : P = (RawLoadPointer 0 load_effects) %"chk60";
      %"chk61" : A = (HalfCheck Upper 0 8 Write 8) %"chk54", %"v295";
      store.ptr [%"chk61" + 0] <- %"v297";
      %"v300" = %"v295" +p #8;
      %"v301" = %"v300" +p #20;
      %"chk62" : A = (HalfCheck Upper 0 4 Write 1) %"chk61", %"v301";
      store Ww [%"chk62" + 0] <- #0;
      %"v305" = %"v300" +p #24;
      %"chk63" : A = (HalfCheck Upper 0 4 Write 1) %"chk62", %"v305";
      store Ww [%"chk63" + 0] <- #1;
      %"v309" = %"v300" +p #16;
      %"chk64" : A = (HalfCheck Lower 0 4 Write 1) %"chk62", %"v309";
      store Ww [%"chk64" + 0] <- #9;
      %"v314" = %"v300" +p #32;
      %"chk65" : A = (Renew 0 8 Read 8) %"chk58", %"v291";
      %"v317" : P = (RawLoadPointer 0 load_effects) %"chk65";
      %"v318" = %"v317" +p #88;
      %"chk66" : A = (HalfCheck Upper 0 8 Write 8) %"chk62", %"v314";
      store.ptr [%"chk66" + 0] <- %"v318";
      %"v320" = %"v0" +p #216;
      %"chk67" : A = (Renew 0 8 Read 8) %"chk41", %"v244";
      %"v323" : P = (RawLoadPointer 0 load_effects) %"chk67";
      %"v324" = %"v323" +p #224;
      %"chk68" : A = (Check 0 8 Read 8) %"v324";
      %"v325" : P = (RawLoadPointer 0 load_effects) %"chk68";
      %"chk69" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v320";
      store.ptr [%"chk69" + 0] <- %"v325";
      %"v327" = %"v140" +p #192;
      %"chk70" : A = (HalfCheck Upper 0 4 Write 1) %"chk58", %"v327";
      store Ww [%"chk70" + 0] <- #1]))
    => goto "L143";
  @"L143":
    => ret %"v140"
} }.

Definition fn__IO_new_file_init_internal : func :=
  ir_fn{ "export" "_IO_new_file_init_internal"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Write 1) %"v3";
    store Wl [%"chk0" + 0] <- #18446744073709551615;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v11" : W = Or %"v7", #9228;
    store Ww [%"chk1" + 0] <- %"v11";
    %"v13" = %"v0" +p #112;
    store Ww [%"chk0" + (-32)] <- #4294967295;
    call void $"__GI__IO_link_in"(P %"v0")
    => ret void
} }.

Definition fn__IO_new_file_overflow : func :=
  ir_fn{ "export" "_IO_new_file_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v9" : W = And %"v8", #8
    => br %"v9" ? "L4" : "L6";
  @"L4":
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Or %"v11", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v12";
    %"v13" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v13";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L6":
    %"v20" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v21" : W = And %"v20", #2048;
    %"v22" : W = (Cmp Eq W) %"v21", #0
    => br %"v22" ? "L24" : "L23";
  @"L23":
    %"v26" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" : L = Ptoi %"v27";
    %"v29" : L = Ptoi #0;
    %"v30" : W = (Cmp Eq L) %"v28", %"v29"
    => goto "L24";
  @"L24" [%"v32" : W = phi("L6" => #1, "L23" => %"v30")]:
    => br %"v32" ? "L16" : "L18";
  @"L16":
    %"v37" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v39" : L = Ptoi %"v38";
    %"v40" : L = Ptoi #0;
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => br %"v41" ? "L33" : "L35";
  @"L33":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v44" = %"v0" +p #24;
    %"v46" = %"v0" +p #56;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v44";
    store.ptr [%"chk8" + 0] <- %"v47";
    %"v49" = %"v0" +p #8;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk7", %"v46";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk10" + 0] <- %"v52";
    %"v54" = %"v0" +p #16;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk7", %"v46";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v54";
    store.ptr [%"chk12" + 0] <- %"v57"
    => goto "L35";
  @"L35":
    %"chk13" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v63" : W = And %"v62", #256;
    %"v64" : L = (Ext Sw) %"v63";
    %"v65" : W = (Cmp Ne L) %"v64", #0
    => br %"v65" ? "L58" : "L60";
  @"L58":
    %"v68" = %"v0" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v71" = %"v0" +p #8;
    %"v72" : P = (RawLoadPointer (-8) load_effects) %"chk14";
    %"v73" : L = Ptoi %"v69";
    %"v74" : L = Ptoi %"v72";
    %"v75" : L = Sub %"v73", %"v74";
    call void $"__GI__IO_free_backup_area"(P %"v0");
    %"v78" = %"v0" +p #24;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v88" = %"v0" +p #56;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v90" : L = Ptoi %"v86";
    %"v91" : L = Ptoi %"v89";
    %"v92" : L = Sub %"v90", %"v91";
    %"v93" : W = (Cmp Ult L) %"v75", %"v92"
    => br %"v93" ? "L82" : "L81";
  @"L81":
    %"v96" = %"v0" +p #24;
    %"v97" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v99" = %"v0" +p #56;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v101" : L = Ptoi %"v97";
    %"v102" : L = Ptoi %"v100";
    %"v103" : L = Sub %"v101", %"v102"
    => goto "L82";
  @"L82" [%"v104" : L = phi("L81" => %"v103", "L58" => %"v75")]:
    (Flight (a "v105") Sub [(FAddress (t "v79")); (FValue (t "v104"))] (LowerOf (t "v79")));
    %"chk21" : A = (Renew 0 8 Write 8) %"chk16", %"v78";
    store.ptr [%"chk21" + 0] <- %"v105";
    %"v107" = %"v0" +p #8;
    %"v109" = %"v0" +p #24;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk16", %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v107";
    store.ptr [%"chk23" + 0] <- %"v110"
    => goto "L60";
  @"L60":
    %"v115" = %"v0" +p #8;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v118" = %"v0" +p #64;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v118";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v120" : L = Ptoi %"v116";
    %"v121" : L = Ptoi %"v119";
    %"v122" : W = (Cmp Eq L) %"v120", %"v121"
    => br %"v122" ? "L111" : "L113";
  @"L111":
    %"v124" = %"v0" +p #16;
    %"v126" = %"v0" +p #8;
    %"v128" = %"v0" +p #56;
    %"v129" : P = (RawLoadPointer (-8) load_effects) %"chk25";
    %"chk27" : A = (Renew 0 8 Write 8) %"chk24", %"v126";
    store.ptr [%"chk27" + 0] <- %"v129";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v124";
    store.ptr [%"chk28" + 0] <- %"v129"
    => goto "L113";
  @"L113":
    %"v131" = %"v0" +p #40;
    %"v133" = %"v0" +p #8;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk24", %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v131";
    store.ptr [%"chk30" + 0] <- %"v134";
    %"v136" = %"v0" +p #32;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk30", %"v131";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (Renew 0 8 Write 8) %"chk6", %"v136";
    store.ptr [%"chk32" + 0] <- %"v139";
    %"v141" = %"v0" +p #48;
    %"v143" = %"v0" +p #64;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk25", %"v143";
    %"v144" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v141";
    store.ptr [%"chk34" + 0] <- %"v144";
    %"v146" = %"v0" +p #24;
    %"v150" = %"v0" +p #16;
    %"chk35" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Write 8) %"chk24", %"v133";
    store.ptr [%"chk36" + 0] <- %"v151";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v146";
    store.ptr [%"chk37" + 0] <- %"v151";
    %"chk38" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v153" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v154" : W = Or %"v153", #2048;
    %"chk39" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk39" + 0] <- %"v154";
    %"v159" = %"v0" +p #192;
    %"chk40" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v159";
    %"v160" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"v161" : W = (Cmp Sle W) %"v160", #0
    => br %"v161" ? "L162" : "L163";
  @"L162":
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"v167" : W = And %"v165", #514;
    %"v168" : W = (Cmp Ne W) %"v167", #0
    => goto "L163";
  @"L163" [%"v169" : W = phi("L113" => #0, "L162" => %"v168")]:
    => br %"v169" ? "L155" : "L18";
  @"L155":
    %"v171" = %"v0" +p #48;
    %"v173" = %"v0" +p #40;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk30", %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk34", %"v171";
    store.ptr [%"chk43" + 0] <- %"v174"
    => goto "L18";
  @"L18":
    %"v180" : W = (Cmp Eq W) %"v2", #4294967295
    => br %"v180" ? "L175" : "L177";
  @"L175":
    %"v183" = %"v0" +p #32;
    %"chk44" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v183";
    %"v184" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v186" = %"v0" +p #40;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v191" : L = Ptoi %"v187";
    %"v192" : L = Ptoi %"v190";
    %"v193" : L = Sub %"v191", %"v192";
    call %"v194" : W = $"_IO_new_do_write"(P %"v0", P %"v184", L %"v193")
    => ret %"v194";
  @"L177":
    %"v200" = %"v0" +p #40;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v200";
    %"v201" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v203" = %"v0" +p #64;
    %"chk48" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v203";
    %"v204" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v205" : L = Ptoi %"v201";
    %"v206" : L = Ptoi %"v204";
    %"v207" : W = (Cmp Eq L) %"v205", %"v206"
    => br %"v207" ? "L196" : "L198";
  @"L196":
    %"v215" = %"v0" +p #192;
    %"chk49" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v215";
    %"v216" : W = (RawLoad (LdNarrow Sw) 0) %"chk49";
    %"v217" : W = (Cmp Sle W) %"v216", #0
    => br %"v217" ? "L211" : "L212";
  @"L211":
    %"v220" = %"v0" +p #32;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v223" = %"v0" +p #40;
    %"v224" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v227" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"v228" : L = Ptoi %"v224";
    %"v229" : L = Ptoi %"v227";
    %"v230" : L = Sub %"v228", %"v229";
    call %"v231" : W = $"_IO_new_do_write"(P %"v0", P %"v221", L %"v230")
    => goto "L213";
  @"L212":
    %"v234" = %"v0" +p #160;
    %"v235" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v236" = %"v235" +p #24;
    %"chk54" : A = (Check 0 8 Read 8) %"v236";
    %"v237" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v240" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v241" = %"v240" +p #32;
    %"chk56" : A = (Check 0 8 Read 8) %"v241";
    %"v242" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"v245" : P = (RawLoadPointer 96 load_effects) %"chk48";
    %"v246" = %"v245" +p #24;
    %"chk58" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v248" : L = Ptoi %"v242";
    %"v249" : L = Ptoi %"v247";
    %"v250" : L = Sub %"v248", %"v249";
    %"v251" : L = Div %"v250", #4;
    call %"v252" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v237", L %"v251")
    => goto "L213";
  @"L213" [%"v253" : W = phi("L211" => %"v231", "L212" => %"v252")]:
    %"v255" : W = (Cmp Eq W) %"v253", #4294967295
    => br %"v255" ? "L208" : "L198";
  @"L208":
    => ret #4294967295;
  @"L198":
    %"v259" = %"v0" +p #40;
    %"chk59" : A = (Renew 0 8 Read 8) %"chk47", %"v259";
    %"v260" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"v261" = %"v260" +p #1;
    %"chk60" : A = (Renew 0 8 Write 8) %"chk47", %"v259";
    store.ptr [%"chk60" + 0] <- %"v261";
    %"v263" : W = (Ext Sb) %"v2";
    %"chk61" : A = (Check 0 1 Write 1) %"v260";
    store Wb [%"chk61" + 0] <- %"v263";
    %"chk62" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v268" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v269" : W = And %"v268", #2
    => br %"v269" ? "L271" : "L270";
  @"L270":
    %"v273" : W = (RawLoad (LdNarrow Sw) 0) %"chk62";
    %"v274" : W = And %"v273", #512
    => br %"v274" ? "L275" : "L271";
  @"L275":
    %"v278" : W = (Cmp Eq W) %"v2", #10
    => goto "L271";
  @"L271" [%"v282" : W = phi("L198" => #1, "L270" => #0, "L275" => %"v278")]:
    => br %"v282" ? "L264" : "L266";
  @"L264":
    %"v288" = %"v0" +p #32;
    %"chk64" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v288";
    %"v289" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v291" = %"v0" +p #40;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk47", %"v291";
    %"v292" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"v295" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"v296" : L = Ptoi %"v292";
    %"v297" : L = Ptoi %"v295";
    %"v298" : L = Sub %"v296", %"v297";
    call %"v299" : W = $"_IO_new_do_write"(P %"v0", P %"v289", L %"v298");
    %"v301" : W = (Cmp Eq W) %"v299", #4294967295
    => br %"v301" ? "L283" : "L266";
  @"L283":
    => ret #4294967295;
  @"L266":
    %"v305" : W = (Ext Ub) %"v2"
    => ret %"v305"
} }.

Definition fn__IO_new_file_seekoff : func :=
  ir_fn{ "export" "_IO_new_file_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) blocks ((app [ir_blk{ @"start":
    %"v170" : P = (Alloc 8) #144;
    %"v16" : W = (Cmp Eq W) %"v6", #0
    => br %"v16" ? "iw_1.start" : "L14" };
  ir_blk{ @"iw_1.start":
    %"iw_1.v8" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" : L = Ptoi %"iw_1.v9";
    %"iw_1.v11" : L = Ptoi #0;
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.L6" };
  ir_blk{ @"iw_1.L4":
    %"iw_1.v15" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v15";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v18" = %"v0" +p #32;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v18";
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v20" : L = Ptoi %"iw_1.v16";
    %"iw_1.v21" : L = Ptoi %"iw_1.v19";
    %"iw_1.v22" : W = (Cmp Ugt L) %"iw_1.v20", %"iw_1.v21";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"iw_1.v27" : W = And %"iw_1.v26", #4096;
    %"iw_1.v28" : W = (Cmp Eq W) %"iw_1.v27", #4096
    => br %"iw_1.v22" ? "iw_1.L34" : "iw_1.L35" };
  ir_blk{ @"iw_1.L34":
    => goto "iw_1.L35" };
  ir_blk{ @"iw_1.L35" [%"iw_1.v38" : W = phi("iw_1.L4" => #0, "iw_1.L34" => %"iw_1.v28")]:
    => br %"iw_1.v38" ? "iw_1.L30" : "iw_1.L32" };
  ir_blk{ @"iw_1.L30":
    %"iw_1.v40" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.iw_1.v4" : L = Ptoi %"iw_1.v41";
    %"iw_1.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_1.v8" : L = Ptoi %"iw_1.iw_1.v7";
    %"iw_1.iw_1.v9" : L = Sub %"iw_1.iw_1.v4", %"iw_1.iw_1.v8";
    %"iw_1.iw_1.v15" : W = (Cmp Uge L) %"iw_1.iw_1.v9", #2352
    => br %"iw_1.iw_1.v15" ? "iw_1.iw_1.L10" : "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_1.join" };
  ir_blk{ @"iw_1.iw_1.join":
    %"iw_1.v43" = %"iw_1.v41" +p #128;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"iw_1.v44";
    rawcall %"iw_1.v46" : L = %"chk6"(P %"v0", L #0, W #2);
    %"iw_1.v53" : W = (Cmp Eq L) %"iw_1.v46", #18446744073709551615
    => br %"iw_1.v53" ? "iw_1.join" : "iw_1.L48" };
  ir_blk{ @"iw_1.L48":
    %"iw_1.v58" = %"v0" +p #144;
    %"chk7" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v58";
    store Wl [%"chk7" + 0] <- %"iw_1.v46"
    => goto "iw_1.L32" };
  ir_blk{ @"iw_1.L32":
    %"iw_1.v64" : W = (Cmp Ule L) %"iw_1.v20", %"iw_1.v21"
    => br %"iw_1.v64" ? "iw_1.L60" : "iw_1.L61" };
  ir_blk{ @"iw_1.L60":
    %"iw_1.v67" = %"v0" +p #16;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v67";
    %"iw_1.v68" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v70" = %"v0" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v72" : L = Ptoi %"iw_1.v68";
    %"iw_1.v73" : L = Ptoi %"iw_1.v71";
    %"iw_1.v74" : L = Sub %"iw_1.v72", %"iw_1.v73";
    %"iw_1.v75" : L = Sub #0, %"iw_1.v74"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L61":
    => br %"iw_1.v28" ? "iw_1.L76" : "iw_1.L77" };
  ir_blk{ @"iw_1.L76":
    %"iw_1.v82" = %"v0" +p #40;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v82";
    %"iw_1.v83" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v85" = %"v0" +p #32;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v85";
    %"iw_1.v86" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v87" : L = Ptoi %"iw_1.v83";
    %"iw_1.v88" : L = Ptoi %"iw_1.v86";
    %"iw_1.v89" : L = Sub %"iw_1.v87", %"iw_1.v88"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L77":
    %"iw_1.v93" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v93";
    %"iw_1.v94" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v96" = %"v0" +p #16;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v96";
    %"iw_1.v97" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v98" : L = Ptoi %"iw_1.v94";
    %"iw_1.v99" : L = Ptoi %"iw_1.v97";
    %"iw_1.v100" : L = Sub %"iw_1.v98", %"iw_1.v99"
    => goto "iw_1.L6" };
  ir_blk{ @"iw_1.L6" [%"iw_1.pr.2" : L = phi("iw_1.L60" => %"iw_1.v75", "iw_1.L76" => %"iw_1.v89", "iw_1.L77" => %"iw_1.v100", "iw_1.start" => #0)]:
    %"iw_1.v106" = %"v0" +p #144;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"iw_1.v106";
    %"iw_1.v107" : L = (RawLoad LdL 0) %"chk14";
    %"iw_1.v110" : W = (Cmp Ne L) %"iw_1.v107", #18446744073709551615
    => br %"iw_1.v110" ? "iw_1.L102" : "iw_1.L103" };
  ir_blk{ @"iw_1.L102":
    %"iw_1.v112" = %"v0" +p #144;
    %"iw_1.v113" : L = (RawLoad LdL 0) %"chk14"
    => goto "iw_1.L104" };
  ir_blk{ @"iw_1.L103":
    %"iw_1.v115" = %"v0" +p #216;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v115";
    %"iw_1.v116" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_1.iw_2.v4" : L = Ptoi %"iw_1.v116";
    %"iw_1.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_1.iw_2.v8" : L = Ptoi %"iw_1.iw_2.v7";
    %"iw_1.iw_2.v9" : L = Sub %"iw_1.iw_2.v4", %"iw_1.iw_2.v8";
    %"iw_1.iw_2.v15" : W = (Cmp Uge L) %"iw_1.iw_2.v9", #2352
    => br %"iw_1.iw_2.v15" ? "iw_1.iw_2.L10" : "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.iw_2.join" };
  ir_blk{ @"iw_1.iw_2.join":
    %"iw_1.v118" = %"iw_1.v116" +p #128;
    %"chk17" : A = (Check 0 8 Read 8) %"iw_1.v118";
    %"iw_1.v119" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : F = CheckFunction %"iw_1.v119";
    rawcall %"iw_1.v121" : L = %"chk18"(P %"v0", L #0, W #1)
    => goto "iw_1.L104" };
  ir_blk{ @"iw_1.L104" [%"iw_1.pr.1" : L = phi("iw_1.L102" => %"iw_1.v113", "iw_1.iw_2.join" => %"iw_1.v121")]:
    %"iw_1.v128" : W = (Cmp Eq L) %"iw_1.pr.1", #18446744073709551615
    => br %"iw_1.v128" ? "iw_1.join" : "iw_1.L124" };
  ir_blk{ @"iw_1.L124":
    %"iw_1.v135" : W = (Cmp Eq L) %"iw_1.pr.1", #0
    => br %"iw_1.v135" ? "iw_1.L136" : "iw_1.L137" };
  ir_blk{ @"iw_1.L136":
    %"iw_1.v139" : W = (Cmp Slt L) %"iw_1.pr.2", #0
    => goto "iw_1.L137" };
  ir_blk{ @"iw_1.L137" [%"iw_1.v141" : W = phi("iw_1.L124" => #0, "iw_1.L136" => %"iw_1.v139")]:
    => br %"iw_1.v141" ? "iw_1.L131" : "iw_1.L133" };
  ir_blk{ @"iw_1.L131":
    %"iw_1.v142" : P = Copy $"__libc_errno";
    %"chk19" : A = (Check 0 4 Write 1) %"iw_1.v142";
    store Ww [%"chk19" + 0] <- #29
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.L133":
    %"iw_1.v148" : L = Add %"iw_1.pr.1", %"iw_1.pr.2";
    %"iw_1.v153" : W = (Cmp Slt L) %"iw_1.v148", #0
    => br %"iw_1.v153" ? "iw_1.L149" : "iw_1.join" };
  ir_blk{ @"iw_1.L149":
    %"iw_1.v154" : P = Copy $"__libc_errno";
    %"chk20" : A = (Check 0 4 Write 1) %"iw_1.v154";
    store Ww [%"chk20" + 0] <- #22
    => goto "iw_1.join" };
  ir_blk{ @"iw_1.join" [%"v18" : L = phi("iw_1.L131" => #18446744073709551615, "iw_1.L149" => #18446744073709551615, "iw_1.iw_1.join" => #18446744073709551615, "iw_1.L104" => %"iw_1.pr.1", "iw_1.L133" => %"iw_1.v148")]:
    => ret %"v18" };
  ir_blk{ @"L14":
    %"v22" = %"v0" +p #24;
    %"chk21" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v25" = %"v0" +p #16;
    %"chk22" : A = (HalfCheck Lower 0 8 Read 8) %"chk21", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v27" : L = Ptoi %"v23";
    %"v28" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L30" : "L31" };
  ir_blk{ @"L30":
    %"v33" = %"v0" +p #32;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v36" = %"v0" +p #40;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v38" : L = Ptoi %"v34";
    %"v39" : L = Ptoi %"v37";
    %"v40" : W = (Cmp Eq L) %"v38", %"v39"
    => goto "L31" };
  ir_blk{ @"L31" [%"v42" : W = phi("L14" => #0, "L30" => %"v40")]:
    %"v45" = %"v0" +p #40;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v48" = %"v0" +p #32;
    %"v49" : P = (RawLoadPointer (-8) load_effects) %"chk25";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ugt L) %"v50", %"v51"
    => br %"v52" ? "L54" : "L53" };
  ir_blk{ @"L53":
    %"chk27" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v56" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"v57" : W = And %"v56", #2048;
    %"v58" : W = (Cmp Ne W) %"v57", #0
    => goto "L54" };
  ir_blk{ @"L54" [%"v59" : W = phi("L31" => #1, "L53" => %"v58")]:
    => br %"v59" ? "L65" : "L66" };
  ir_blk{ @"L65":
    call %"v68" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v69" : W = (Cmp Ne W) %"v68", #0
    => goto "L66" };
  ir_blk{ @"L66" [%"v70" : W = phi("L54" => #0, "L65" => %"v69")]:
    => br %"v70" ? "L61" : "L63" };
  ir_blk{ @"L61":
    => ret #18446744073709551615 };
  ir_blk{ @"L63":
    %"v78" = %"v0" +p #56;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v80" : L = Ptoi %"v79";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L74" : "L129" };
  ir_blk{ @"L74":
    %"v87" = %"v0" +p #24;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk21", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v89" : L = Ptoi %"v88";
    %"v91" : W = (Cmp Ne L) %"v89", %"v81"
    => br %"v91" ? "L83" : "L85" };
  ir_blk{ @"L83":
    %"v94" = %"v0" +p #24;
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v9" = %"v0" +p #119;
    %"iw_2.v10" : L = Ptoi %"v95";
    %"iw_2.v11" : L = Ptoi %"iw_2.v9";
    %"iw_2.v12" : W = (Cmp Ne L) %"iw_2.v10", %"iw_2.v11"
    => br %"iw_2.v12" ? "iw_2.L4" : "iw_2.join" };
  ir_blk{ @"iw_2.L4":
    call void $"free"(P %"v95")
    => goto "iw_2.join" };
  ir_blk{ @"iw_2.join":
    %"chk31" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v99" : W = And %"v97", #4294967039;
    %"chk32" : A = (Renew 0 4 Write 1) %"chk31", %"v0";
    store Ww [%"chk32" + 0] <- %"v99"
    => goto "L85" };
  ir_blk{ @"L85":
    call void $"__GI__IO_doallocbuf"(P %"v0");
    %"v102" = %"v0" +p #32;
    %"v104" = %"v0" +p #40;
    %"v106" = %"v0" +p #56;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v107" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Renew 0 8 Write 8) %"chk25", %"v104";
    store.ptr [%"chk34" + 0] <- %"v107";
    %"chk35" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v102";
    store.ptr [%"chk35" + 0] <- %"v107";
    %"v109" = %"v0" +p #48;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v109";
    store.ptr [%"chk37" + 0] <- %"v112";
    %"v114" = %"v0" +p #24;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Renew 0 8 Write 8) %"chk21", %"v114";
    store.ptr [%"chk39" + 0] <- %"v117";
    %"v119" = %"v0" +p #8;
    %"chk40" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v119";
    store.ptr [%"chk41" + 0] <- %"v122";
    %"v124" = %"v0" +p #16;
    %"chk42" : A = (Renew 0 8 Read 8) %"chk28", %"v106";
    %"v127" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : A = (Renew 0 8 Write 8) %"chk22", %"v124";
    store.ptr [%"chk43" + 0] <- %"v127"
    => goto "L129" };
  ir_blk{ @"L131":
    %"v134" = %"v0" +p #16;
    %"chk44" : A = (Renew 0 8 Read 8) %"chk22", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v137" = %"v0" +p #8;
    %"chk45" : A = (HalfCheck Lower 0 8 Read 8) %"chk21", %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v139" : L = Ptoi %"v135";
    %"v140" : L = Ptoi %"v138";
    %"v141" : L = Sub %"v139", %"v140";
    %"v142" : L = Sub %"v2", %"v141";
    %"v147" = %"v0" +p #144;
    %"chk46" : A = (HalfCheck Upper 0 8 Read 1) %"chk21", %"v147";
    %"v148" : L = (RawLoad LdL 0) %"chk46";
    %"v151" : W = (Cmp Eq L) %"v148", #18446744073709551615
    => br %"v151" ? "L152" : "L145" };
  ir_blk{ @"L145":
    %"v156" = %"v0" +p #144;
    %"v157" : L = (RawLoad LdL 0) %"chk46";
    %"v158" : L = Add %"v142", %"v157";
    %"v163" : W = (Cmp Slt L) %"v158", #0
    => br %"v163" ? "L159" : "L130" }] [ir_blk{ @"L159":
    %"v164" : P = Copy $"__libc_errno";
    %"chk48" : A = (Check 0 4 Write 1) %"v164";
    store Ww [%"chk48" + 0] <- #22
    => ret #18446744073709551615 };
  ir_blk{ @"L169":
    %"v175" = %"v0" +p #216;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v175";
    %"v176" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_3.v4" : L = Ptoi %"v176";
    %"iw_3.v7" : P = Copy $"__io_vtables";
    %"iw_3.v8" : L = Ptoi %"iw_3.v7";
    %"iw_3.v9" : L = Sub %"iw_3.v4", %"iw_3.v8";
    %"iw_3.v15" : W = (Cmp Uge L) %"iw_3.v9", #2352
    => br %"iw_3.v15" ? "iw_3.L10" : "iw_3.join" };
  ir_blk{ @"iw_3.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_3.join" };
  ir_blk{ @"iw_3.join":
    %"v178" = %"v176" +p #144;
    %"chk50" : A = (Check 0 8 Read 8) %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : F = CheckFunction %"v179";
    rawcall %"v181" : W = %"chk51"(P %"v0", P %"v170");
    %"v182" : W = (Cmp Eq W) %"v181", #0
    => br %"v182" ? "L183" : "L184" };
  ir_blk{ @"L183":
    %"v185" = %"v170" +p #24;
    %"chk52" : A = (Check 0 4 Read 1) %"v185";
    %"v186" : W = (RawLoad (LdNarrow Uw) 0) %"chk52";
    %"v187" : W = And %"v186", #61440;
    %"v188" : W = (Cmp Eq W) %"v187", #32768
    => goto "L184" };
  ir_blk{ @"L184" [%"v190" : W = phi("iw_3.join" => #0, "L183" => %"v188")]:
    => br %"v190" ? "L171" : "L152" };
  ir_blk{ @"L171":
    %"v192" = %"v170" +p #48;
    %"chk53" : A = (Check 0 8 Read 1) %"v192";
    %"v193" : L = (RawLoad LdL 0) %"chk53";
    %"v194" : L = Add %"v2", %"v193"
    => goto "L130" };
  ir_blk{ @"L129":
    %"v195" : W = (Cmp Eq W) %"v4", #1
    => br %"v195" ? poll "L131" : "L196" };
  ir_blk{ @"L196":
    %"v197" : W = (Cmp Eq W) %"v4", #0
    => br %"v197" ? "L130" : "L198" };
  ir_blk{ @"L198":
    %"v199" : W = (Cmp Eq W) %"v4", #2
    => br %"v199" ? poll "L169" : "L130" };
  ir_blk{ @"L130" [%"pr.3" : W = phi("L145" => #0, "L196" => %"v4", "L171" => #0, "L198" => %"v4"); %"pr.1" : L = phi("L145" => %"v158", "L196" => %"v2", "L171" => %"v194", "L198" => %"v2")]:
    call void $"__GI__IO_free_backup_area"(P %"v0");
    %"v206" = %"v0" +p #144;
    %"chk54" : A = (HalfCheck Upper 0 8 Read 1) %"chk21", %"v206";
    %"v207" : L = (RawLoad LdL 0) %"chk54";
    %"v210" : W = (Cmp Ne L) %"v207", #18446744073709551615
    => br %"v210" ? "L211" : "L212" };
  ir_blk{ @"L211":
    %"v214" = %"v0" +p #24;
    %"chk55" : A = (Renew 0 8 Read 8) %"chk21", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk55";
    %"v216" : L = Ptoi %"v215";
    %"v218" : W = (Cmp Ne L) %"v216", %"v81"
    => goto "L212" };
  ir_blk{ @"L212" [%"v220" : W = phi("L130" => #0, "L211" => %"v218")]:
    => br %"v220" ? "L221" : "L222" };
  ir_blk{ @"L221":
    %"chk56" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v224" : W = (RawLoad (LdNarrow Sw) 0) %"chk56";
    %"v225" : W = And %"v224", #256;
    %"v226" : W = (Cmp Eq W) %"v225", #0
    => goto "L222" };
  ir_blk{ @"L222" [%"v228" : W = phi("L212" => #0, "L221" => %"v226")]:
    => br %"v228" ? "L202" : "L204" };
  ir_blk{ @"L202":
    %"v231" = %"v0" +p #144;
    %"v232" : L = (RawLoad LdL 0) %"chk54";
    %"v234" = %"v0" +p #16;
    %"chk58" : A = (Renew 0 8 Read 8) %"chk22", %"v234";
    %"v235" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"v237" = %"v0" +p #56;
    %"v238" : P = (RawLoadPointer 40 load_effects) %"chk58";
    %"v239" : L = Ptoi %"v235";
    %"v240" : L = Ptoi %"v238";
    %"v241" : L = Sub %"v239", %"v240";
    %"v242" : L = Sub %"v232", %"v241";
    %"v248" : W = (Cmp Sge L) %"pr.1", %"v242"
    => br %"v248" ? "L249" : "L250" };
  ir_blk{ @"L249":
    %"v253" = %"v0" +p #144;
    %"v254" : L = (RawLoad LdL 0) %"chk54";
    %"v255" : W = (Cmp Slt L) %"pr.1", %"v254"
    => goto "L250" };
  ir_blk{ @"L250" [%"v257" : W = phi("L202" => #0, "L249" => %"v255")]:
    => br %"v257" ? "L243" : "L204" };
  ir_blk{ @"L243":
    %"v259" = %"v0" +p #24;
    %"v261" = %"v0" +p #56;
    %"v262" : P = (RawLoadPointer 40 load_effects) %"chk58";
    %"chk62" : A = (Renew 0 8 Write 8) %"chk21", %"v259";
    store.ptr [%"chk62" + 0] <- %"v262";
    %"v264" = %"v0" +p #8;
    %"chk63" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v267" : P = (RawLoadPointer 0 load_effects) %"chk63";
    %"v270" : L = Sub %"pr.1", %"v242";
    %"v271" = %"v267" +p %"v270";
    %"chk64" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v264";
    store.ptr [%"chk64" + 0] <- %"v271";
    %"v273" = %"v0" +p #16;
    %"chk65" : A = (Renew 0 8 Read 8) %"chk22", %"v273";
    %"v276" : P = (RawLoadPointer 0 load_effects) %"chk65";
    %"chk66" : A = (Renew 0 8 Write 8) %"chk22", %"v273";
    store.ptr [%"chk66" + 0] <- %"v276";
    %"v278" = %"v0" +p #32;
    %"v280" = %"v0" +p #40;
    %"chk67" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v283" : P = (RawLoadPointer 0 load_effects) %"chk67";
    %"chk68" : A = (Renew 0 8 Write 8) %"chk25", %"v280";
    store.ptr [%"chk68" + 0] <- %"v283";
    %"chk69" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v278";
    store.ptr [%"chk69" + 0] <- %"v283";
    %"v285" = %"v0" +p #48;
    %"chk70" : A = (Renew 0 8 Read 8) %"chk28", %"v261";
    %"v288" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"chk71" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v285";
    store.ptr [%"chk71" + 0] <- %"v288";
    %"chk72" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk72";
    %"v293" : W = And %"v291", #4294967279;
    %"chk73" : A = (Renew 0 4 Write 1) %"chk72", %"v0";
    store Ww [%"chk73" + 0] <- %"v293";
    %"v507" = %"v0" +p #144;
    %"chk74" : A = (Renew 0 8 Read 1) %"chk54", %"v507";
    %"v508" : L = (RawLoad LdL 0) %"chk74";
    %"v509" : W = (Cmp Sge L) %"v508", #0
    => br %"v509" ? "L503" : "L505" };
  ir_blk{ @"L204":
    %"chk75" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v302" : W = (RawLoad (LdNarrow Sw) 0) %"chk75";
    %"v303" : W = And %"v302", #4
    => br %"v303" ? "L152" : "L300" };
  ir_blk{ @"L300":
    %"v307" = %"v0" +p #64;
    %"chk76" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v307";
    %"v308" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v310" = %"v0" +p #56;
    %"v311" : P = (RawLoadPointer (-8) load_effects) %"chk76";
    %"v312" : L = Ptoi %"v308";
    %"v313" : L = Ptoi %"v311";
    %"v314" : L = Sub %"v312", %"v313";
    %"v315" : L = Sub %"v314", #1;
    %"v316" : L = Xor %"v315", #(-1);
    %"v317" : L = And %"pr.1", %"v316";
    %"v320" : L = Sub %"pr.1", %"v317";
    %"v327" : P = (RawLoadPointer 0 load_effects) %"chk76";
    %"v330" : P = (RawLoadPointer (-8) load_effects) %"chk76";
    %"v331" : L = Ptoi %"v327";
    %"v332" : L = Ptoi %"v330";
    %"v333" : L = Sub %"v331", %"v332";
    %"v334" : W = (Cmp Sgt L) %"v320", %"v333"
    => br %"v334" ? "L323" : "L322" };
  ir_blk{ @"L322":
    => goto "L323" };
  ir_blk{ @"L323" [%"pr.6" : L = phi("L322" => %"v317", "L300" => %"pr.1"); %"pr.5" : L = phi("L322" => %"v320", "L300" => #0)]:
    %"v337" = %"v0" +p #216;
    %"chk80" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v337";
    %"v338" : P = (RawLoadPointer 0 load_effects) %"chk80";
    %"iw_4.v4" : L = Ptoi %"v338";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join" };
  ir_blk{ @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join" };
  ir_blk{ @"iw_4.join":
    %"v340" = %"v338" +p #128;
    %"chk81" : A = (Check 0 8 Read 8) %"v340";
    %"v341" : P = (RawLoadPointer 0 load_effects) %"chk81";
    %"chk82" : F = CheckFunction %"v341";
    rawcall %"v344" : L = %"chk82"(P %"v0", L %"pr.6", W #0);
    %"v349" : W = (Cmp Slt L) %"v344", #0
    => br %"v349" ? "L345" : "L347" };
  ir_blk{ @"L345":
    => ret #18446744073709551615 };
  ir_blk{ @"L347":
    %"v357" : W = (Cmp Eq L) %"pr.5", #0
    => br %"v357" ? "L355" : "L354" };
  ir_blk{ @"L354":
    %"v359" = %"v0" +p #216;
    %"chk83" : A = (Renew 0 8 Read 8) %"chk80", %"v359";
    %"v360" : P = (RawLoadPointer 0 load_effects) %"chk83";
    %"iw_5.v4" : L = Ptoi %"v360";
    %"iw_5.v7" : P = Copy $"__io_vtables";
    %"iw_5.v8" : L = Ptoi %"iw_5.v7";
    %"iw_5.v9" : L = Sub %"iw_5.v4", %"iw_5.v8";
    %"iw_5.v15" : W = (Cmp Uge L) %"iw_5.v9", #2352
    => br %"iw_5.v15" ? "iw_5.L10" : "iw_5.join" };
  ir_blk{ @"iw_5.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_5.join" };
  ir_blk{ @"iw_5.join":
    %"v362" = %"v360" +p #112;
    %"chk84" : A = (Check 0 8 Read 8) %"v362";
    %"v363" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"v366" = %"v0" +p #56;
    %"chk85" : A = (Renew 0 8 Read 8) %"chk28", %"v366";
    %"v367" : P = (RawLoadPointer 0 load_effects) %"chk85"
    => br %"v42" ? "L370" : "L369" };
  ir_blk{ @"L369":
    %"v374" = %"v0" +p #64;
    %"chk86" : A = (Renew 0 8 Read 8) %"chk76", %"v374";
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk86";
    %"v377" = %"v0" +p #56;
    %"v378" : P = (RawLoadPointer 0 load_effects) %"chk85";
    %"v379" : L = Ptoi %"v375";
    %"v380" : L = Ptoi %"v378";
    %"v381" : L = Sub %"v379", %"v380"
    => goto "L370" };
  ir_blk{ @"L370" [%"v382" : L = phi("L369" => %"v381", "iw_5.join" => %"pr.5")]:
    %"chk88" : F = CheckFunction %"v363";
    rawcall %"v383" : L = %"chk88"(P %"v0", P %"v367", L %"v382");
    %"v389" : W = (Cmp Slt L) %"v383", %"pr.5"
    => br %"v389" ? "L384" : "L355" };
  ir_blk{ @"L384":
    %"v396" : W = (Cmp Eq L) %"v383", #18446744073709551615
    => br %"v396" ? "L152" : "L391" };
  ir_blk{ @"L391":
    %"v400" : L = Sub %"pr.5", %"v383"
    => goto "L152" };
  ir_blk{ @"L355" [%"pr.7" : L = phi("L347" => #0, "L370" => %"v383")]:
    %"v404" = %"v0" +p #24;
    %"v406" = %"v0" +p #56;
    %"chk89" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v407" : P = (RawLoadPointer 0 load_effects) %"chk89";
    %"chk90" : A = (Renew 0 8 Write 8) %"chk21", %"v404";
    store.ptr [%"chk90" + 0] <- %"v407";
    %"v409" = %"v0" +p #8;
    %"chk91" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v412" : P = (RawLoadPointer 0 load_effects) %"chk91";
    %"v414" = %"v412" +p %"pr.5";
    %"chk92" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v409";
    store.ptr [%"chk92" + 0] <- %"v414";
    %"v416" = %"v0" +p #16;
    %"chk93" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v419" : P = (RawLoadPointer 0 load_effects) %"chk93";
    %"v421" = %"v419" +p %"pr.7";
    %"chk94" : A = (Renew 0 8 Write 8) %"chk22", %"v416";
    store.ptr [%"chk94" + 0] <- %"v421";
    %"v423" = %"v0" +p #32;
    %"v425" = %"v0" +p #40;
    %"chk95" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v428" : P = (RawLoadPointer 0 load_effects) %"chk95";
    %"chk96" : A = (Renew 0 8 Write 8) %"chk25", %"v425";
    store.ptr [%"chk96" + 0] <- %"v428";
    %"chk97" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v423";
    store.ptr [%"chk97" + 0] <- %"v428";
    %"v430" = %"v0" +p #48;
    %"chk98" : A = (Renew 0 8 Read 8) %"chk28", %"v406";
    %"v433" : P = (RawLoadPointer 0 load_effects) %"chk98";
    %"chk99" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v430";
    store.ptr [%"chk99" + 0] <- %"v433";
    %"v435" = %"v0" +p #144;
    %"v438" : L = Add %"v344", %"pr.7";
    %"chk100" : A = (Renew 0 8 Write 1) %"chk54", %"v435";
    store Wl [%"chk100" + 0] <- %"v438";
    %"chk101" : A = (Renew 0 4 Read 1) %"chk75", %"v0";
    %"v441" : W = (RawLoad (LdNarrow Sw) 0) %"chk101";
    %"v443" : W = And %"v441", #4294967279;
    store Ww [%"chk101" + 0] <- %"v443"
    => ret %"pr.1" };
  ir_blk{ @"L152" [%"pr.4" : W = phi("L131" => %"v4", "L184" => %"v4", "L204" => %"pr.3", "L391" => #1, "L384" => #1); %"pr.2" : L = phi("L131" => %"v142", "L184" => %"v2", "L204" => %"pr.1", "L391" => %"v400", "L384" => %"pr.5")]:
    call void $"__GI__IO_unsave_markers"(P %"v0");
    %"v449" = %"v0" +p #216;
    %"chk103" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v449";
    %"v450" : P = (RawLoadPointer 0 load_effects) %"chk103";
    %"iw_6.v4" : L = Ptoi %"v450";
    %"iw_6.v7" : P = Copy $"__io_vtables";
    %"iw_6.v8" : L = Ptoi %"iw_6.v7";
    %"iw_6.v9" : L = Sub %"iw_6.v4", %"iw_6.v8";
    %"iw_6.v15" : W = (Cmp Uge L) %"iw_6.v9", #2352
    => br %"iw_6.v15" ? "iw_6.L10" : "iw_6.join" };
  ir_blk{ @"iw_6.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_6.join" };
  ir_blk{ @"iw_6.join":
    %"v452" = %"v450" +p #128;
    %"chk104" : A = (Check 0 8 Read 8) %"v452";
    %"v453" : P = (RawLoadPointer 0 load_effects) %"chk104";
    %"chk105" : F = CheckFunction %"v453";
    rawcall %"v457" : L = %"chk105"(P %"v0", L %"pr.2", W %"pr.4");
    %"v464" : W = (Cmp Ne L) %"v457", #18446744073709551615
    => br %"v464" ? "L458" : "L460" };
  ir_blk{ @"L458":
    %"chk106" : A = (HalfCheck Lower 0 4 Read 1) %"chk21", %"v0";
    %"v467" : W = (RawLoad (LdNarrow Sw) 0) %"chk106";
    %"v469" : W = And %"v467", #4294967279;
    %"chk107" : A = (Renew 0 4 Write 1) %"chk106", %"v0";
    store Ww [%"chk107" + 0] <- %"v469";
    %"v473" = %"v0" +p #144;
    %"chk108" : A = (HalfCheck Upper 0 8 Write 1) %"chk21", %"v473";
    store Wl [%"chk108" + 0] <- %"v457";
    %"v476" = %"v0" +p #24;
    %"v478" = %"v0" +p #56;
    %"chk109" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v479" : P = (RawLoadPointer 0 load_effects) %"chk109";
    %"chk110" : A = (Renew 0 8 Write 8) %"chk21", %"v476";
    store.ptr [%"chk110" + 0] <- %"v479";
    %"v481" = %"v0" +p #8;
    %"chk111" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v484" : P = (RawLoadPointer 0 load_effects) %"chk111";
    %"chk112" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v481";
    store.ptr [%"chk112" + 0] <- %"v484";
    %"v486" = %"v0" +p #16;
    %"chk113" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v489" : P = (RawLoadPointer 0 load_effects) %"chk113";
    %"chk114" : A = (Renew 0 8 Write 8) %"chk22", %"v486";
    store.ptr [%"chk114" + 0] <- %"v489";
    %"v491" = %"v0" +p #32;
    %"v493" = %"v0" +p #40;
    %"chk115" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v496" : P = (RawLoadPointer 0 load_effects) %"chk115";
    %"chk116" : A = (Renew 0 8 Write 8) %"chk25", %"v493";
    store.ptr [%"chk116" + 0] <- %"v496";
    %"chk117" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v491";
    store.ptr [%"chk117" + 0] <- %"v496";
    %"v498" = %"v0" +p #48;
    %"chk118" : A = (Renew 0 8 Read 8) %"chk28", %"v478";
    %"v501" : P = (RawLoadPointer 0 load_effects) %"chk118";
    %"chk119" : A = (HalfCheck Upper 0 8 Write 8) %"chk21", %"v498";
    store.ptr [%"chk119" + 0] <- %"v501"
    => goto "L460" };
  ir_blk{ @"L460":
    => ret %"v457" };
  ir_blk{ @"L503":
    %"v511" = %"v0" +p #216;
    %"chk120" : A = (HalfCheck Upper 0 8 Read 8) %"chk21", %"v511";
    %"v512" : P = (RawLoadPointer 0 load_effects) %"chk120";
    %"iw_7.v4" : L = Ptoi %"v512";
    %"iw_7.v7" : P = Copy $"__io_vtables";
    %"iw_7.v8" : L = Ptoi %"iw_7.v7";
    %"iw_7.v9" : L = Sub %"iw_7.v4", %"iw_7.v8";
    %"iw_7.v15" : W = (Cmp Uge L) %"iw_7.v9", #2352
    => br %"iw_7.v15" ? "iw_7.L10" : "iw_7.join" };
  ir_blk{ @"iw_7.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_7.join" };
  ir_blk{ @"iw_7.join":
    %"v514" = %"v512" +p #128;
    %"chk121" : A = (Check 0 8 Read 8) %"v514";
    %"v515" : P = (RawLoadPointer 0 load_effects) %"chk121";
    %"v518" = %"v0" +p #144;
    %"chk122" : A = (Renew 0 8 Read 1) %"chk54", %"v518";
    %"v519" : L = (RawLoad LdL 0) %"chk122";
    %"chk123" : F = CheckFunction %"v515";
    rawcall %"v520" : L = %"chk123"(P %"v0", L %"v519", W #0)
    => goto "L505" };
  ir_blk{ @"L505":
    => ret %"pr.1" }])) }.

Definition fn__IO_new_file_setbuf : func :=
  ir_fn{ "export" "_IO_new_file_setbuf"(P %"v0", P %"v2", L %"v4") -> (RClass P) {
  @"start":
    call %"v12" : P = $"_IO_default_setbuf"(P %"v0", P %"v2", L %"v4");
    %"v13" : L = Ptoi %"v12";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L6" : "L8";
  @"L6":
    => ret #0;
  @"L8":
    %"v18" = %"v0" +p #32;
    %"v20" = %"v0" +p #40;
    %"v22" = %"v0" +p #48;
    %"v24" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v22";
    store.ptr [%"chk1" + 0] <- %"v25";
    %"chk2" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v20";
    store.ptr [%"chk2" + 0] <- %"v25";
    %"chk3" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v18";
    store.ptr [%"chk3" + 0] <- %"v25";
    %"v27" = %"v0" +p #24;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk0", %"v24";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk5" + 0] <- %"v30";
    %"v32" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v24";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v32";
    store.ptr [%"chk7" + 0] <- %"v35";
    %"v37" = %"v0" +p #16;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v24";
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk9" + 0] <- %"v40"
    => ret %"v0"
} }.

Definition fn__IO_new_file_sync : func :=
  ir_fn{ "export" "_IO_new_file_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #32;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ugt L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L6";
  @"L4":
    %"v23" = %"v0" +p #192;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v25" : W = (Cmp Sle W) %"v24", #0
    => br %"v25" ? "L19" : "L20";
  @"L19":
    %"v28" = %"v0" +p #32;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v31" = %"v0" +p #40;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v36" : L = Ptoi %"v32";
    %"v37" : L = Ptoi %"v35";
    %"v38" : L = Sub %"v36", %"v37";
    call %"v39" : W = $"_IO_new_do_write"(P %"v0", P %"v29", L %"v38")
    => goto "L21";
  @"L20":
    %"v42" = %"v0" +p #160;
    %"v43" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v44" = %"v43" +p #24;
    %"chk7" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v48" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v49" = %"v48" +p #32;
    %"chk9" : A = (Check 0 8 Read 8) %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" : P = (RawLoadPointer 120 load_effects) %"chk0";
    %"v54" = %"v53" +p #24;
    %"chk11" : A = (Check 0 8 Read 8) %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v56" : L = Ptoi %"v50";
    %"v57" : L = Ptoi %"v55";
    %"v58" : L = Sub %"v56", %"v57";
    %"v59" : L = Div %"v58", #4;
    call %"v60" : W = $"__GI__IO_wdo_write"(P %"v0", P %"v45", L %"v59")
    => goto "L21";
  @"L21" [%"v61" : W = phi("L19" => %"v39", "L20" => %"v60")]:
    => br %"v61" ? "L16" : "L6";
  @"L16":
    => ret #4294967295;
  @"L6":
    %"v65" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v68" = %"v0" +p #16;
    %"chk13" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v70" : L = Ptoi %"v66";
    %"v71" : L = Ptoi %"v69";
    %"v72" : L = Sub %"v70", %"v71";
    %"chk14" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v77" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"v78" : W = And %"v77", #256
    => br %"v78" ? "L73" : "L75";
  @"L73":
    call void $"_IO_switch_to_main_get_area"(P %"v0");
    %"v82" = %"v0" +p #8;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk12", %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v85" = %"v0" +p #16;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk13", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v87" : L = Ptoi %"v83";
    %"v88" : L = Ptoi %"v86";
    %"v89" : L = Sub %"v87", %"v88";
    %"v90" : L = Add %"v72", %"v89"
    => goto "L75";
  @"L75" [%"pr.1" : L = phi("L73" => %"v90", "L6" => %"v72")]:
    %"v95" : W = (Cmp Ne L) %"pr.1", #0
    => br %"v95" ? "L91" : "L93";
  @"L91":
    %"v98" = %"v0" +p #216;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v4" : L = Ptoi %"v99";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v101" = %"v99" +p #128;
    %"chk18" : A = (Check 0 8 Read 8) %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : F = CheckFunction %"v102";
    rawcall %"v105" : L = %"chk19"(P %"v0", L %"pr.1", W #1);
    %"v112" : W = (Cmp Ne L) %"v105", #18446744073709551615
    => br %"v112" ? "L106" : "L107";
  @"L106":
    %"v114" = %"v0" +p #16;
    %"v116" = %"v0" +p #8;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk12", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk13", %"v114";
    store.ptr [%"chk21" + 0] <- %"v117"
    => goto "L93";
  @"L107":
    %"v121" : P = Copy $"__libc_errno";
    %"chk22" : A = (Check 0 4 Read 1) %"v121";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"v123" : W = (Cmp Eq W) %"v122", #29
    => br %"v123" ? "L93" : "L119";
  @"L119":
    => goto "L93";
  @"L93" [%"pr.4" : W = phi("L106" => #0, "L119" => #4294967295, "L107" => #0, "L75" => #0)]:
    %"v130" : W = (Cmp Ne W) %"pr.4", #4294967295
    => br %"v130" ? "L125" : "L127";
  @"L125":
    %"v132" = %"v0" +p #144;
    %"chk23" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v132";
    store Wl [%"chk23" + 0] <- #18446744073709551615
    => goto "L127";
  @"L127":
    => ret %"pr.4"
} }.

Definition fn__IO_new_file_underflow : func :=
  ir_fn{ "export" "_IO_new_file_underflow"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = And %"v7", #16
    => br %"v8" ? "L3" : "L5";
  @"L3":
    => ret #4294967295;
  @"L5":
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v16" : W = And %"v15", #4
    => br %"v16" ? "L11" : "L13";
  @"L11":
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v19" : W = Or %"v18", #32;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk3" + 0] <- %"v19";
    %"v20" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v20";
    store Ww [%"chk4" + 0] <- #9
    => ret #4294967295;
  @"L13":
    %"v27" = %"v0" +p #8;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v30" = %"v0" +p #16;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v32" : L = Ptoi %"v28";
    %"v33" : L = Ptoi %"v31";
    %"v34" : W = (Cmp Ult L) %"v32", %"v33"
    => br %"v34" ? "L23" : "L25";
  @"L23":
    %"v36" = %"v0" +p #8;
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk8" : A = (Check 0 1 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Ub) 0) %"chk8"
    => ret %"v38";
  @"L25":
    %"v44" = %"v0" +p #56;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v46" : L = Ptoi %"v45";
    %"v47" : L = Ptoi #0;
    %"v48" : W = (Cmp Eq L) %"v46", %"v47"
    => br %"v48" ? "L40" : "L42";
  @"L40":
    %"v53" = %"v0" +p #72;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v55" : L = Ptoi %"v54";
    %"v57" : W = (Cmp Ne L) %"v55", %"v47"
    => br %"v57" ? "L49" : "L51";
  @"L49":
    %"v60" = %"v0" +p #72;
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v61";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v61")
    => goto "iw_1.join";
  @"iw_1.join":
    %"chk12" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v63" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v65" : W = And %"v63", #4294967039;
    %"chk13" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk13" + 0] <- %"v65"
    => goto "L51";
  @"L51":
    call void $"__GI__IO_doallocbuf"(P %"v0")
    => goto "L42";
  @"L42":
    %"chk14" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v71" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    %"v73" : W = And %"v71", #514
    => br %"v73" ? "L74" : "L69";
  @"L74":
    %"v78" : P = Copy $"stdout";
    %"chk15" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 4 Read 1) %"v79";
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v85" : W = And %"v84", #32768;
    %"v86" : W = (Cmp Eq W) %"v85", #0
    => br %"v86" ? "L87" : "L82";
  @"L87":
    call %"v91" : P = $"zthread_self_cookie"();
    %"v95" : P = Copy $"__libc_single_threaded_internal";
    %"chk17" : A = (Check 0 1 Read 1) %"v95";
    %"v96" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v97" : W = (Cmp Ne W) %"v96", #0
    => br %"v97" ? "L98" : "L99";
  @"L98":
    %"v101" = %"v79" +p #136;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v103" = %"v102" +p #8;
    %"chk19" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v105" : L = Ptoi %"v104";
    %"v107" : W = (Cmp Eq L) %"v105", %"v47"
    => goto "L99";
  @"L99" [%"v109" : W = phi("L87" => #0, "L98" => %"v107")]:
    => br %"v109" ? "L92" : "L93";
  @"L92":
    %"v111" = %"v79" +p #136;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"v111";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 4 Write 1) %"v112";
    store Ww [%"chk21" + 0] <- #1;
    %"v115" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v116" = %"v115" +p #8;
    %"chk23" : A = (Check 0 8 Write 8) %"v116";
    store.ptr [%"chk23" + 0] <- %"v91"
    => goto "L82";
  @"L93":
    %"v122" = %"v79" +p #136;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"v122";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v124" = %"v123" +p #8;
    %"chk25" : A = (Check 0 8 Read 8) %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v127" : L = Ptoi %"v125";
    %"v128" : L = Ptoi %"v91";
    %"v129" : W = (Cmp Ne L) %"v127", %"v128"
    => br %"v129" ? "L118" : "L119";
  @"L118":
    %"v132" = %"v79" +p #136;
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk27" : A = (Check 0 4 Write 4) %"v133";
    %"v140" : W = (RawCas (CasNarrow Sw) 0) %"chk27", #0, #1;
    %"v141" : W = (Cmp Eq W) %"v140", #0
    => br %"v141" ? "L143" : "L142";
  @"L142":
    => goto "L143";
  @"L143":
    %"v144" : W = (Cmp Ne W) %"v140", #0
    => br %"v144" ? "L147" : "L136";
  @"L147":
    call void $"__GI___lll_lock_wait_private"(P %"v133")
    => goto "L136";
  @"L136":
    %"v158" = %"v79" +p #136;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk24", %"v158";
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v160" = %"v159" +p #8;
    %"chk29" : A = (Check 0 8 Write 8) %"v160";
    store.ptr [%"chk29" + 0] <- %"v91"
    => goto "L82";
  @"L119":
    %"v163" = %"v79" +p #136;
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v165" = %"v164" +p #4;
    %"chk31" : A = (Check 0 4 Read 1) %"v165";
    %"v166" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v167" : W = Add %"v166", #1;
    %"chk32" : A = (Renew 0 4 Write 1) %"chk31", %"v165";
    store Ww [%"chk32" + 0] <- %"v167"
    => goto "L82";
  @"L82":
    %"v171" : P = Copy $"stdout";
    %"chk33" : A = (Check 0 8 Read 8) %"v171";
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Check 0 4 Read 1) %"v172";
    %"v173" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"v176" : W = And %"v173", #648;
    %"v178" : W = (Cmp Eq W) %"v176", #640
    => br %"v178" ? "L168" : "iw_3.start";
  @"L168":
    %"v179" : P = Copy $"stdout";
    %"chk35" : A = (Check 0 8 Read 8) %"v179";
    %"v180" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"v181" = %"v180" +p #216;
    %"chk36" : A = (Check 0 8 Read 8) %"v181";
    %"v182" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"iw_2.v4" : L = Ptoi %"v182";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join";
  @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join";
  @"iw_2.join":
    %"v184" = %"v182" +p #24;
    %"chk37" : A = (Check 0 8 Read 8) %"v184";
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v186" : P = Copy $"stdout";
    %"chk38" : A = (Check 0 8 Read 8) %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : F = CheckFunction %"v185";
    rawcall %"v189" : W = %"chk39"(P %"v187", W #4294967295)
    => goto "iw_3.start";
  @"iw_3.start":
    %"chk40" : A = (Renew 0 4 Read 1) %"chk16", %"v79";
    %"iw_3.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"iw_3.v10" : W = And %"iw_3.v9", #32768;
    %"iw_3.v11" : W = (Cmp Eq W) %"iw_3.v10", #0
    => br %"iw_3.v11" ? "iw_3.L5" : "L69";
  @"iw_3.L5":
    %"iw_3.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"iw_3.v17" : W = And %"iw_3.v16", #32768;
    %"iw_3.v18" : W = (Cmp Eq W) %"iw_3.v17", #0
    => br %"iw_3.v18" ? "iw_3.L19" : "L69";
  @"iw_3.L19":
    %"iw_3.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk42" : A = (Check 0 1 Read 1) %"iw_3.v25";
    %"iw_3.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk42";
    %"iw_3.v27" : W = (Cmp Ne W) %"iw_3.v26", #0
    => br %"iw_3.v27" ? "iw_3.L28" : "iw_3.L29";
  @"iw_3.L28":
    %"iw_3.v31" = %"v79" +p #136;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_3.v31";
    %"iw_3.v32" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_3.v33" = %"iw_3.v32" +p #4;
    %"chk44" : A = (Check 0 4 Read 1) %"iw_3.v33";
    %"iw_3.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"iw_3.v35" : W = (Cmp Eq W) %"iw_3.v34", #0
    => goto "iw_3.L29";
  @"iw_3.L29" [%"iw_3.v37" : W = phi("iw_3.L19" => #0, "iw_3.L28" => %"iw_3.v35")]:
    => br %"iw_3.v37" ? "iw_3.L22" : "iw_3.L23";
  @"iw_3.L22":
    %"iw_3.v39" = %"v79" +p #136;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_3.v39";
    %"iw_3.v40" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"iw_3.v41" = %"iw_3.v40" +p #8;
    %"chk46" : A = (Check 0 8 Write 8) %"iw_3.v41";
    store.ptr [%"chk46" + 0] <- #0;
    %"chk47" : A = (Renew 0 8 Read 8) %"chk45", %"iw_3.v39";
    %"iw_3.v44" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 4 Write 1) %"iw_3.v44";
    store Ww [%"chk48" + 0] <- #0
    => goto "L69";
  @"iw_3.L23":
    %"iw_3.v49" = %"v79" +p #136;
    %"chk49" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_3.v49";
    %"iw_3.v50" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_3.v51" = %"iw_3.v50" +p #4;
    %"chk50" : A = (Check 0 4 Read 1) %"iw_3.v51";
    %"iw_3.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk50";
    %"iw_3.v53" : W = (Cmp Eq W) %"iw_3.v52", #0
    => br %"iw_3.v53" ? "iw_3.L45" : "iw_3.L46";
  @"iw_3.L45":
    %"iw_3.v55" = %"v79" +p #136;
    %"iw_3.v56" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_3.v57" = %"iw_3.v56" +p #8;
    %"chk52" : A = (Check 0 8 Write 8) %"iw_3.v57";
    store.ptr [%"chk52" + 0] <- #0;
    %"chk53" : A = (Renew 0 8 Read 8) %"chk49", %"iw_3.v55";
    %"iw_3.v61" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"chk54" : A = (Check 0 4 Read 1) %"iw_3.v61";
    %"iw_3.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk54"
    => goto "iw_3.L66";
  @"iw_3.L66" [%"iw_3.v68" : W = phi("iw_3.L45" => %"iw_3.v65", "iw_3.L66" => %"iw_3.v69")]:
    %"chk55" : A = (HalfCheck Lower 0 4 Write 4) %"chk54", %"iw_3.v61";
    %"iw_3.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk55", %"iw_3.v68", #0;
    %"iw_3.v70" : W = (Cmp Eq W) %"iw_3.v69", %"iw_3.v68"
    => br %"iw_3.v70" ? "iw_3.L67" : poll "iw_3.L66";
  @"iw_3.L67":
    %"iw_3.v75" : W = (Cmp Sgt W) %"iw_3.v68", #1
    => br %"iw_3.v75" ? "iw_3.L78" : "L69";
  @"iw_3.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_3.v61")
    => goto "L69";
  @"iw_3.L46":
    %"iw_3.v90" = %"v79" +p #136;
    %"iw_3.v91" : P = (RawLoadPointer 0 load_effects) %"chk49";
    %"iw_3.v92" = %"iw_3.v91" +p #4;
    %"chk57" : A = (Check 0 4 Read 1) %"iw_3.v92";
    %"iw_3.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk57";
    %"iw_3.v94" : W = Sub %"iw_3.v93", #1;
    %"chk58" : A = (Renew 0 4 Write 1) %"chk57", %"iw_3.v92";
    store Ww [%"chk58" + 0] <- %"iw_3.v94"
    => goto "L69";
  @"L69":
    call %"v191" : W = $"__GI__IO_switch_to_get_mode"(P %"v0");
    %"v193" = %"v0" +p #24;
    %"v195" = %"v0" +p #8;
    %"v197" = %"v0" +p #56;
    %"chk59" : A = (Renew 0 8 Read 8) %"chk9", %"v197";
    %"v198" : P = (RawLoadPointer 0 load_effects) %"chk59";
    %"chk60" : A = (Renew 0 8 Write 8) %"chk5", %"v195";
    store.ptr [%"chk60" + 0] <- %"v198";
    %"chk61" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v193";
    store.ptr [%"chk61" + 0] <- %"v198";
    %"v200" = %"v0" +p #16;
    %"chk62" : A = (Renew 0 8 Read 8) %"chk9", %"v197";
    %"v203" : P = (RawLoadPointer 0 load_effects) %"chk62";
    %"chk63" : A = (Renew 0 8 Write 8) %"chk6", %"v200";
    store.ptr [%"chk63" + 0] <- %"v203";
    %"v205" = %"v0" +p #32;
    %"v207" = %"v0" +p #40;
    %"v209" = %"v0" +p #48;
    %"chk64" : A = (Renew 0 8 Read 8) %"chk9", %"v197";
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk64";
    %"chk65" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v209";
    store.ptr [%"chk65" + 0] <- %"v212";
    %"chk66" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v207";
    store.ptr [%"chk66" + 0] <- %"v212";
    %"chk67" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v205";
    store.ptr [%"chk67" + 0] <- %"v212";
    %"v214" = %"v0" +p #216;
    %"chk68" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk68";
    %"iw_4.v4" : L = Ptoi %"v215";
    %"iw_4.v7" : P = Copy $"__io_vtables";
    %"iw_4.v8" : L = Ptoi %"iw_4.v7";
    %"iw_4.v9" : L = Sub %"iw_4.v4", %"iw_4.v8";
    %"iw_4.v15" : W = (Cmp Uge L) %"iw_4.v9", #2352
    => br %"iw_4.v15" ? "iw_4.L10" : "iw_4.join";
  @"iw_4.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_4.join";
  @"iw_4.join":
    %"v217" = %"v215" +p #112;
    %"chk69" : A = (Check 0 8 Read 8) %"v217";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk69";
    %"v221" = %"v0" +p #56;
    %"chk70" : A = (Renew 0 8 Read 8) %"chk9", %"v221";
    %"v222" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v224" = %"v0" +p #64;
    %"chk71" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk71";
    %"v228" : P = (RawLoadPointer 0 load_effects) %"chk70";
    %"v229" : L = Ptoi %"v225";
    %"v230" : L = Ptoi %"v228";
    %"v231" : L = Sub %"v229", %"v230";
    %"chk73" : F = CheckFunction %"v218";
    rawcall %"v232" : L = %"chk73"(P %"v0", P %"v222", L %"v231");
    %"v237" : W = (Cmp Sle L) %"v232", #0
    => br %"v237" ? "L233" : "L235";
  @"L233":
    %"v242" : W = (Cmp Eq L) %"v232", #0
    => br %"v242" ? "L238" : "L239";
  @"L238":
    %"chk74" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v244" : W = (RawLoad (LdNarrow Sw) 0) %"chk74";
    %"v245" : W = Or %"v244", #16;
    %"chk75" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk75" + 0] <- %"v245"
    => goto "L235";
  @"L239":
    %"chk76" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v247" : W = (RawLoad (LdNarrow Sw) 0) %"chk76";
    %"v248" : W = Or %"v247", #32;
    %"chk77" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk77" + 0] <- %"v248"
    => goto "L235";
  @"L235" [%"pr.1" : L = phi("L238" => %"v232", "L239" => #0, "iw_4.join" => %"v232")]:
    %"v250" = %"v0" +p #16;
    %"chk78" : A = (Renew 0 8 Read 8) %"chk6", %"v250";
    %"v251" : P = (RawLoadPointer 0 load_effects) %"chk78";
    %"v253" = %"v251" +p %"pr.1";
    %"chk79" : A = (Renew 0 8 Write 8) %"chk6", %"v250";
    store.ptr [%"chk79" + 0] <- %"v253";
    %"v258" : W = (Cmp Eq L) %"pr.1", #0
    => br %"v258" ? "L254" : "L256";
  @"L254":
    %"v260" = %"v0" +p #144;
    %"chk80" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"v260";
    store Wl [%"chk80" + 0] <- #18446744073709551615
    => ret #4294967295;
  @"L256":
    %"v269" = %"v0" +p #144;
    %"chk81" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v269";
    %"v270" : L = (RawLoad LdL 0) %"chk81";
    %"v273" : W = (Cmp Ne L) %"v270", #18446744073709551615
    => br %"v273" ? "L265" : "L267";
  @"L265":
    %"v275" = %"v0" +p #144;
    %"v276" : L = (RawLoad LdL 0) %"chk81";
    %"v278" : L = Add %"v276", %"pr.1";
    %"chk83" : A = (Renew 0 8 Write 1) %"chk81", %"v275";
    store Wl [%"chk83" + 0] <- %"v278"
    => goto "L267";
  @"L267":
    %"v280" = %"v0" +p #8;
    %"chk84" : A = (Renew 0 8 Read 8) %"chk5", %"v280";
    %"v281" : P = (RawLoadPointer 0 load_effects) %"chk84";
    %"chk85" : A = (Check 0 1 Read 1) %"v281";
    %"v282" : W = (RawLoad (LdNarrow Ub) 0) %"chk85"
    => ret %"v282"
} }.

Definition fn__IO_new_file_write : func :=
  ir_fn{ "export" "_IO_new_file_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => goto "L8";
  @"L8" [%"pr.2" : L = phi("L40" => %"v54", "start" => %"v4"); %"pr.1" : P = phi("L40" => %"v57", "start" => %"v2")]:
    %"v12" : W = (Cmp Sgt L) %"pr.2", #0
    => br %"v12" ? "L9" : "L10";
  @"L9":
    %"v18" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v20" : W = Shl %"v19", #8;
    %"v21" : W = Sar %"v20", #8;
    %"v22" : W = And %"v21", #2;
    %"v23" : L = (Ext Sw) %"v22";
    %"v24" : W = (Cmp Ne L) %"v23", #0
    => br %"v24" ? "L14" : "L15";
  @"L14":
    %"v26" = %"v0" +p #112;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"v30" : L = $"__GI___write_nocancel"(W %"v27", P %"pr.1", L %"pr.2")
    => goto "L16";
  @"L15":
    %"v32" = %"v0" +p #112;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    call %"v36" : L = $"__GI___write"(W %"v33", P %"pr.1", L %"pr.2")
    => goto "L16";
  @"L16" [%"v37" : L = phi("L14" => %"v30", "L15" => %"v36")]:
    %"v42" : W = (Cmp Slt L) %"v37", #0
    => br %"v42" ? "L38" : "L40";
  @"L38":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v44" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v45" : W = Or %"v44", #32;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v45"
    => goto "L10";
  @"L40":
    %"v48" = %"v0" +p #200;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk5";
    %"v51" : L = Add %"v49", %"v37";
    %"chk6" : A = (Renew 0 8 Write 1) %"chk5", %"v48";
    store Wl [%"chk6" + 0] <- %"v51";
    %"v54" : L = Sub %"pr.2", %"v37";
    %"v57" = %"pr.1" +p %"v37"
    => goto poll "L8";
  @"L10":
    %"v60" : L = Sub %"v4", %"pr.2";
    %"v65" = %"v0" +p #144;
    %"chk7" : A = (Check 0 8 Read 1) %"v65";
    %"v66" : L = (RawLoad LdL 0) %"chk7";
    %"v67" : W = (Cmp Sge L) %"v66", #0
    => br %"v67" ? "L61" : "L63";
  @"L61":
    %"v69" = %"v0" +p #144;
    %"v70" : L = (RawLoad LdL 0) %"chk7";
    %"v72" : L = Add %"v70", %"v60";
    %"chk9" : A = (Renew 0 8 Write 1) %"chk7", %"v69";
    store Wl [%"chk9" + 0] <- %"v72"
    => goto "L63";
  @"L63":
    => ret %"v60"
} }.

Definition fn__IO_new_file_xsputn : func :=
  ir_fn{ "export" "_IO_new_file_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v16" : W = (Cmp Ule L) %"v4", #0
    => br %"v16" ? "L12" : "L14";
  @"L12":
    => ret #0;
  @"L14":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v23" : W = And %"v22", #512
    => br %"v23" ? "L24" : "L25";
  @"L24":
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v28" : W = And %"v27", #2048;
    %"v29" : W = (Cmp Ne W) %"v28", #0
    => goto "L25";
  @"L25" [%"v30" : W = phi("L14" => #0, "L24" => %"v29")]:
    => br %"v30" ? "L18" : "L19";
  @"L18":
    %"v32" = %"v0" +p #64;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v35" = %"v0" +p #40;
    %"v36" : P = (RawLoadPointer (-24) load_effects) %"chk2";
    %"v37" : L = Ptoi %"v33";
    %"v38" : L = Ptoi %"v36";
    %"v39" : L = Sub %"v37", %"v38";
    %"v45" : W = (Cmp Uge L) %"v39", %"v4"
    => br %"v45" ? "L40" : "L20";
  @"L40":
    %"v49" = %"v2" +p %"v4"
    => goto "L50";
  @"L50" [%"pr.14" : P = phi("L40" => %"v49", "L51" => %"v63")]:
    %"v56" : L = Ptoi %"pr.14";
    %"v57" : L = Ptoi %"v2";
    %"v58" : W = (Cmp Ugt L) %"v56", %"v57"
    => br %"v58" ? "L51" : "L20";
  @"L51":
    (Flight (a "v63") Sub [(FAddress (t "pr.14")); (FValue (Const 1))] (LowerOf (t "pr.14")));
    %"chk4" : A = (Check 0 1 Read 1) %"v63";
    %"v64" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v65" : W = (Cmp Eq W) %"v64", #10
    => br %"v65" ? "L59" : poll "L50";
  @"L59":
    %"v68" : L = Ptoi %"v63";
    %"v70" : L = Sub %"v68", %"v57";
    %"v71" : L = Add %"v70", #1
    => goto "L20";
  @"L19":
    %"v77" = %"v0" +p #48;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v80" = %"v0" +p #40;
    %"v81" : P = (RawLoadPointer (-8) load_effects) %"chk5";
    %"v82" : L = Ptoi %"v78";
    %"v83" : L = Ptoi %"v81";
    %"v84" : W = (Cmp Ugt L) %"v82", %"v83"
    => br %"v84" ? "L73" : "L20";
  @"L73":
    %"v86" = %"v0" +p #48;
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v89" = %"v0" +p #40;
    %"v90" : P = (RawLoadPointer (-8) load_effects) %"chk5";
    %"v91" : L = Ptoi %"v87";
    %"v92" : L = Ptoi %"v90";
    %"v93" : L = Sub %"v91", %"v92"
    => goto "L20";
  @"L20" [%"pr.10" : L = phi("L50" => %"v39", "L59" => %"v71", "L18" => %"v39", "L73" => %"v93", "L19" => #0); %"pr.6" : W = phi("L50" => #0, "L59" => #1, "L18" => #0, "L73" => #0, "L19" => #0)]:
    %"v98" : W = (Cmp Ugt L) %"pr.10", #0
    => br %"v98" ? "L94" : "L96";
  @"L94":
    %"v104" : W = (Cmp Ugt L) %"pr.10", %"v4"
    => br %"v104" ? "L101" : "L100";
  @"L100":
    => goto "L101";
  @"L101" [%"pr.9" : L = phi("L100" => %"pr.10", "L94" => %"v4")]:
    %"v107" = %"v0" +p #40;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v107";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call %"v113" : P = $"__GI_mempcpy"(P %"v110", P %"v2", L %"pr.9");
    %"chk10" : A = (Renew 0 8 Write 8) %"chk9", %"v107";
    store.ptr [%"chk10" + 0] <- %"v113";
    %"v116" = %"v2" +p %"pr.9";
    %"v119" : L = Sub %"v4", %"pr.9"
    => goto "L96";
  @"L96" [%"pr.5" : L = phi("L101" => %"v119", "L20" => %"v4"); %"pr.1" : P = phi("L101" => %"v116", "L20" => %"v2")]:
    %"v125" : L = (Ext Sw) %"pr.6";
    %"v126" : L = Add %"pr.5", %"v125";
    %"v127" : W = (Cmp Ugt L) %"v126", #0
    => br %"v127" ? "L120" : "L122";
  @"L120":
    %"v134" = %"v0" +p #216;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v4" : L = Ptoi %"v135";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v137" = %"v135" +p #24;
    %"chk12" : A = (Check 0 8 Read 8) %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : F = CheckFunction %"v138";
    rawcall %"v141" : W = %"chk13"(P %"v0", W #4294967295);
    %"v143" : W = (Cmp Eq W) %"v141", #4294967295
    => br %"v143" ? "L130" : "L132";
  @"L130":
    %"v148" : W = (Cmp Eq L) %"pr.5", #0
    => br %"v148" ? "L146" : "L145";
  @"L145":
    %"v153" : L = Sub %"v4", %"pr.5"
    => goto "L146";
  @"L146" [%"v154" : L = phi("L145" => %"v153", "L130" => #18446744073709551615)]:
    => ret %"v154";
  @"L132":
    %"v157" = %"v0" +p #64;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v157";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v160" = %"v0" +p #56;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v162" : L = Ptoi %"v158";
    %"v163" : L = Ptoi %"v161";
    %"v164" : L = Sub %"v162", %"v163";
    %"v170" : W = (Cmp Uge L) %"v164", #128
    => br %"v170" ? "L166" : "L168";
  @"L166":
    %"v173" : L = Urem %"pr.5", %"v164"
    => goto "L168";
  @"L168" [%"v174" : L = phi("L166" => %"v173", "L132" => #0)]:
    %"v175" : L = Sub %"pr.5", %"v174";
    %"v180" : W = (Cmp Ne L) %"v175", #0
    => br %"v180" ? "iw_2.start" : "L178";
  @"iw_2.start":
    %"chk16" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"iw_2.v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"iw_2.v12" : W = And %"iw_2.v11", #4096
    => br %"iw_2.v12" ? "iw_2.L7" : "iw_2.L8";
  @"iw_2.L7":
    %"iw_2.v14" = %"v0" +p #144;
    %"chk17" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_2.v14";
    store Wl [%"chk17" + 0] <- #18446744073709551615
    => goto "iw_2.L9";
  @"iw_2.L8":
    %"iw_2.v21" = %"v0" +p #16;
    %"iw_2.v22" : P = (RawLoadPointer (-40) load_effects) %"chk15";
    %"iw_2.v24" = %"v0" +p #32;
    %"iw_2.v25" : P = (RawLoadPointer (-24) load_effects) %"chk15";
    %"iw_2.v26" : L = Ptoi %"iw_2.v22";
    %"iw_2.v27" : L = Ptoi %"iw_2.v25";
    %"iw_2.v28" : W = (Cmp Ne L) %"iw_2.v26", %"iw_2.v27"
    => br %"iw_2.v28" ? "iw_2.L17" : "iw_2.L9";
  @"iw_2.L17":
    %"iw_2.v31" = %"v0" +p #216;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk11", %"iw_2.v31";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_2.iw_1.v4" : L = Ptoi %"iw_2.v32";
    %"iw_2.iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_2.iw_1.v8" : L = Ptoi %"iw_2.iw_1.v7";
    %"iw_2.iw_1.v9" : L = Sub %"iw_2.iw_1.v4", %"iw_2.iw_1.v8";
    %"iw_2.iw_1.v15" : W = (Cmp Uge L) %"iw_2.iw_1.v9", #2352
    => br %"iw_2.iw_1.v15" ? "iw_2.iw_1.L10" : "iw_2.iw_1.join";
  @"iw_2.iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.iw_1.join";
  @"iw_2.iw_1.join":
    %"iw_2.v34" = %"iw_2.v32" +p #128;
    %"chk21" : A = (Check 0 8 Read 8) %"iw_2.v34";
    %"iw_2.v35" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_2.v38" = %"v0" +p #32;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v38";
    %"iw_2.v39" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_2.v41" = %"v0" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v41";
    %"iw_2.v42" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"iw_2.v43" : L = Ptoi %"iw_2.v39";
    %"iw_2.v44" : L = Ptoi %"iw_2.v42";
    %"iw_2.v45" : L = Sub %"iw_2.v43", %"iw_2.v44";
    %"chk24" : F = CheckFunction %"iw_2.v35";
    rawcall %"iw_2.v46" : L = %"chk24"(P %"v0", L %"iw_2.v45", W #1);
    %"iw_2.v53" : W = (Cmp Eq L) %"iw_2.v46", #18446744073709551615
    => br %"iw_2.v53" ? "iw_2.join" : "iw_2.L49";
  @"iw_2.L49":
    %"iw_2.v56" = %"v0" +p #144;
    %"chk25" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_2.v56";
    store Wl [%"chk25" + 0] <- %"iw_2.v46"
    => goto "iw_2.L9";
  @"iw_2.L9":
    %"iw_2.v59" = %"v0" +p #216;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk11", %"iw_2.v59";
    %"iw_2.v60" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"iw_2.iw_2.v4" : L = Ptoi %"iw_2.v60";
    %"iw_2.iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.iw_2.v8" : L = Ptoi %"iw_2.iw_2.v7";
    %"iw_2.iw_2.v9" : L = Sub %"iw_2.iw_2.v4", %"iw_2.iw_2.v8";
    %"iw_2.iw_2.v15" : W = (Cmp Uge L) %"iw_2.iw_2.v9", #2352
    => br %"iw_2.iw_2.v15" ? "iw_2.iw_2.L10" : "iw_2.iw_2.join";
  @"iw_2.iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.iw_2.join";
  @"iw_2.iw_2.join":
    %"iw_2.v62" = %"iw_2.v60" +p #120;
    %"chk27" : A = (Check 0 8 Read 8) %"iw_2.v62";
    %"iw_2.v63" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : F = CheckFunction %"iw_2.v63";
    rawcall %"iw_2.v67" : L = %"chk28"(P %"v0", P %"pr.1", L %"v175");
    %"iw_2.v72" = %"v0" +p #128;
    %"chk29" : A = (HalfCheck Upper 0 2 Read 1) %"chk0", %"iw_2.v72";
    %"iw_2.v73" : W = (RawLoad (LdNarrow Uh) 0) %"chk29"
    => br %"iw_2.v73" ? "iw_2.L74" : "iw_2.L75";
  @"iw_2.L74":
    %"iw_2.v77" : W = (Cmp Ne L) %"iw_2.v67", #0
    => goto "iw_2.L75";
  @"iw_2.L75" [%"iw_2.v79" : W = phi("iw_2.iw_2.join" => #0, "iw_2.L74" => %"iw_2.v77")]:
    => br %"iw_2.v79" ? "iw_2.L68" : "iw_2.L70";
  @"iw_2.L68":
    %"iw_2.v81" = %"v0" +p #128;
    %"iw_2.v84" : W = (RawLoad (LdNarrow Uh) 0) %"chk29";
    %"iw_2.v85" : W = Sub %"iw_2.v84", #1;
    call %"iw_2.v88" : W = $"__GI__IO_adjust_column"(W %"iw_2.v85", P %"pr.1", W %"iw_2.v67");
    %"iw_2.v89" : W = Add %"iw_2.v88", #1;
    %"iw_2.v90" : W = (Ext Uh) %"iw_2.v89";
    %"chk31" : A = (Renew 0 2 Write 1) %"chk29", %"iw_2.v81";
    store Wh [%"chk31" + 0] <- %"iw_2.v90"
    => goto "iw_2.L70";
  @"iw_2.L70":
    %"iw_2.v92" = %"v0" +p #24;
    %"iw_2.v94" = %"v0" +p #56;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk15", %"iw_2.v94";
    %"iw_2.v95" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v92";
    store.ptr [%"chk33" + 0] <- %"iw_2.v95";
    %"iw_2.v97" = %"v0" +p #8;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk15", %"iw_2.v94";
    %"iw_2.v100" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v97";
    store.ptr [%"chk35" + 0] <- %"iw_2.v100";
    %"iw_2.v102" = %"v0" +p #16;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk15", %"iw_2.v94";
    %"iw_2.v105" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v102";
    store.ptr [%"chk37" + 0] <- %"iw_2.v105";
    %"iw_2.v107" = %"v0" +p #32;
    %"iw_2.v109" = %"v0" +p #40;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk15", %"iw_2.v94";
    %"iw_2.v112" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v109";
    store.ptr [%"chk39" + 0] <- %"iw_2.v112";
    %"chk40" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v107";
    store.ptr [%"chk40" + 0] <- %"iw_2.v112";
    %"iw_2.v114" = %"v0" +p #48;
    %"iw_2.v119" = %"v0" +p #192;
    %"chk41" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"iw_2.v119";
    %"iw_2.v120" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"iw_2.v121" : W = (Cmp Sle W) %"iw_2.v120", #0
    => br %"iw_2.v121" ? "iw_2.L122" : "iw_2.L123";
  @"iw_2.L122":
    %"chk42" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"iw_2.v125" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"iw_2.v127" : W = And %"iw_2.v125", #514;
    %"iw_2.v128" : W = (Cmp Ne W) %"iw_2.v127", #0
    => goto "iw_2.L123";
  @"iw_2.L123" [%"iw_2.v129" : W = phi("iw_2.L70" => #0, "iw_2.L122" => %"iw_2.v128")]:
    => br %"iw_2.v129" ? "iw_2.L115" : "iw_2.L116";
  @"iw_2.L115":
    %"iw_2.v131" = %"v0" +p #56;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk15", %"iw_2.v131";
    %"iw_2.v132" : P = (RawLoadPointer 0 load_effects) %"chk43"
    => goto "iw_2.L117";
  @"iw_2.L116":
    %"iw_2.v134" = %"v0" +p #64;
    %"chk44" : A = (Renew 0 8 Read 8) %"chk14", %"iw_2.v134";
    %"iw_2.v135" : P = (RawLoadPointer 0 load_effects) %"chk44"
    => goto "iw_2.L117";
  @"iw_2.L117" [%"iw_2.v136" : P = phi("iw_2.L115" => %"iw_2.v132", "iw_2.L116" => %"iw_2.v135")]:
    %"chk45" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_2.v114";
    store.ptr [%"chk45" + 0] <- %"iw_2.v136"
    => goto "iw_2.join";
  @"iw_2.join" [%"v184" : L = phi("iw_2.L117" => %"iw_2.v67", "iw_2.iw_1.join" => #0)]:
    %"v187" : L = Sub %"pr.5", %"v184";
    %"v193" : W = (Cmp Ult L) %"v184", %"v175"
    => br %"v193" ? "L188" : "L178";
  @"L188":
    %"v196" : L = Sub %"v4", %"v187"
    => ret %"v196";
  @"L178" [%"pr.3" : L = phi("iw_2.join" => %"v187", "L168" => %"pr.5")]:
    %"v202" : W = (Cmp Ne L) %"pr.3", #0
    => br %"v202" ? "L198" : "L122";
  @"L198":
    %"v207" = %"pr.1" +p %"v175";
    call %"v209" : L = $"__GI__IO_default_xsputn"(P %"v0", P %"v207", L %"pr.3");
    %"v210" : L = Sub %"pr.3", %"v209"
    => goto "L122";
  @"L122" [%"pr.2" : L = phi("L198" => %"v210", "L178" => %"pr.3", "L96" => %"pr.5")]:
    %"v213" : L = Sub %"v4", %"pr.2"
    => ret %"v213"
} }.

Definition item___GI__IO_do_write : item :=
  (IAlias (a "__GI__IO_do_write") (a "export") (a "_IO_new_do_write")).

Definition fn___GI__IO_file_close : func :=
  ir_fn{ "export" "__GI__IO_file_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v5" : W = $"__GI___close_nocancel"(W %"v4")
    => ret %"v5"
} }.

Definition item___GI__IO_file_finish : item :=
  (IAlias (a "__GI__IO_file_finish") (a "export") (a "_IO_new_file_finish")).

Definition item___GI__IO_file_fopen : item :=
  (IAlias (a "__GI__IO_file_fopen") (a "export") (a "_IO_new_file_fopen")).

Definition fn___GI__IO_file_open : func :=
  ir_fn{ "export" "__GI__IO_file_open"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8", W %"v10") -> (RClass P) {
  @"start":
    %"v17" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v17";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v19" : W = Shl %"v18", #8;
    %"v20" : W = Sar %"v19", #8;
    %"v21" : W = And %"v20", #2;
    %"v22" : L = (Ext Sw) %"v21";
    %"v23" : W = (Cmp Ne L) %"v22", #0
    => br %"v23" ? "L13" : "L14";
  @"L13":
    => br %"v10" ? "L28" : "L27";
  @"L27":
    => goto "L28";
  @"L28":
    call %"v33" : W = $"__GI___open_nocancel"(P %"v2", W %"v4", W %"v6")
    => goto "L15";
  @"L14":
    => br %"v10" ? "L38" : "L37";
  @"L37":
    => goto "L38";
  @"L38":
    call %"v43" : W = $"__GI___open"(P %"v2", W %"v4", W %"v6")
    => goto "L15";
  @"L15" [%"pr.1" : W = phi("L28" => %"v33", "L38" => %"v43")]:
    %"v48" : W = (Cmp Slt W) %"pr.1", #0
    => br %"v48" ? "L44" : "L46";
  @"L44":
    => ret #0;
  @"L46":
    %"v51" = %"v0" +p #112;
    %"chk1" : A = (HalfCheck Lower 0 4 Write 1) %"chk0", %"v51";
    store Ww [%"chk1" + 0] <- %"pr.1";
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v59" : W = And %"v55", #4294963187;
    %"v63" : W = And %"v8", #4108;
    %"v64" : W = Or %"v59", %"v63";
    store Ww [%"chk2" + 0] <- %"v64";
    %"v70" : W = And %"v8", #4100;
    %"v72" : W = (Cmp Eq W) %"v70", #4100
    => br %"v72" ? "L65" : "L67";
  @"L65":
    %"v75" = %"v0" +p #216;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v4" : L = Ptoi %"v76";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v78" = %"v76" +p #128;
    %"chk5" : A = (Check 0 8 Read 8) %"v78";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v79";
    rawcall %"v81" : L = %"chk6"(P %"v0", L #0, W #2);
    %"v88" : W = (Cmp Eq L) %"v81", #18446744073709551615
    => br %"v88" ? "L89" : "L90";
  @"L89":
    %"v91" : P = Copy $"__libc_errno";
    %"chk7" : A = (Check 0 4 Read 1) %"v91";
    %"v92" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v93" : W = (Cmp Ne W) %"v92", #29
    => goto "L90";
  @"L90" [%"v95" : W = phi("iw_1.join" => #0, "L89" => %"v93")]:
    => br %"v95" ? "L82" : "L67";
  @"L82":
    call %"v97" : W = $"__GI___close_nocancel"(W %"pr.1")
    => ret #0;
  @"L67":
    %"v103" = %"v0" +p #116;
    %"chk8" : A = (Renew 0 4 Read 1) %"chk0", %"v103";
    %"v104" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v105" : W = Shl %"v104", #8;
    %"v106" : W = Sar %"v105", #8;
    %"v107" : W = And %"v106", #32;
    %"v108" : W = (Cmp Eq W) %"v107", #0
    => br %"v108" ? "L99" : "L101";
  @"L99":
    call void $"__GI__IO_link_in"(P %"v0")
    => goto "L101";
  @"L101":
    => ret %"v0"
} }.

Definition item___GI__IO_file_overflow : item :=
  (IAlias (a "__GI__IO_file_overflow") (a "export") (a "_IO_new_file_overflow")).

Definition fn___GI__IO_file_read : func :=
  ir_fn{ "export" "__GI__IO_file_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Shl %"v11", #8;
    %"v13" : W = Sar %"v12", #8;
    %"v14" : W = And %"v13", #2;
    %"v15" : L = (Ext Sw) %"v14";
    %"v16" : W = (Cmp Ne L) %"v15", #0
    => br %"v16" ? "L6" : "L7";
  @"L6":
    %"v18" = %"v0" +p #112;
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    call %"v22" : L = $"__GI___read_nocancel"(W %"v19", P %"v2", L %"v4")
    => goto "L8";
  @"L7":
    %"v24" = %"v0" +p #112;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v24";
    %"v25" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    call %"v28" : L = $"__GI___read"(W %"v25", P %"v2", L %"v4")
    => goto "L8";
  @"L8" [%"v29" : L = phi("L6" => %"v22", "L7" => %"v28")]:
    => ret %"v29"
} }.

Definition fn___GI__IO_file_seek : func :=
  ir_fn{ "export" "__GI__IO_file_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v7" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v7";
    %"v8" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v11" : L = $"__lseek64"(W %"v8", L %"v2", W %"v4")
    => ret %"v11"
} }.

Definition item___GI__IO_file_seekoff : item :=
  (IAlias (a "__GI__IO_file_seekoff") (a "export") (a "_IO_new_file_seekoff")).

Definition item___GI__IO_file_setbuf : item :=
  (IAlias (a "__GI__IO_file_setbuf") (a "export") (a "_IO_new_file_setbuf")).

Definition fn___GI__IO_file_stat : func :=
  ir_fn{ "export" "__GI__IO_file_stat"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v5" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v5";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    call %"v8" : W = $"__GI___fstat64"(W %"v6", P %"v2")
    => ret %"v8"
} }.

Definition item___GI__IO_file_sync : item :=
  (IAlias (a "__GI__IO_file_sync") (a "export") (a "_IO_new_file_sync")).

Definition item___GI__IO_file_underflow : item :=
  (IAlias (a "__GI__IO_file_underflow") (a "export") (a "_IO_new_file_underflow")).

Definition fn___GI__IO_file_xsgetn : func :=
  ir_fn{ "export" "__GI__IO_file_xsgetn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v16" = %"v0" +p #56;
    %"chk0" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" : L = Ptoi %"v17";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L12" : "L39";
  @"L12":
    %"v25" = %"v0" +p #72;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Ne L) %"v27", %"v19"
    => br %"v29" ? "L21" : "L23";
  @"L21":
    %"v32" = %"v0" +p #72;
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v33";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v33")
    => goto "iw_1.join";
  @"iw_1.join":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v35" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v37" : W = And %"v35", #4294967039;
    %"chk4" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk4" + 0] <- %"v37"
    => goto "L23";
  @"L23":
    call void $"__GI__IO_doallocbuf"(P %"v0")
    => goto "L39";
  @"L39" [%"pr.7" : P = phi("L89" => %"pr.9", "L23" => %"v2", "start" => %"v2", "L97" => %"pr.9", "L53" => %"pr.7", "L218" => %"v214", "L197" => %"v214"); %"pr.1" : L = phi("L89" => %"pr.4", "L23" => %"v4", "start" => %"v4", "L97" => %"pr.4", "L53" => #0, "L218" => %"v217", "L197" => %"v217")]:
    %"v43" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v43" ? "L40" : "L41";
  @"L40":
    %"v45" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v48" = %"v0" +p #8;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : L = Sub %"v50", %"v51";
    %"v58" : W = (Cmp Ule L) %"pr.1", %"v52"
    => br %"v58" ? "L53" : "L54";
  @"L53":
    %"v61" = %"v0" +p #8;
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v64" : P = $"__GI_memcpy"(P %"pr.7", P %"v62", L %"pr.1");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk6", %"v61";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v69" = %"v67" +p %"pr.1";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"v61";
    store.ptr [%"chk9" + 0] <- %"v69"
    => goto poll "L39";
  @"L54":
    %"v74" : W = (Cmp Ugt L) %"v52", #0
    => br %"v74" ? "L70" : "L72";
  @"L70":
    %"v77" = %"v0" +p #8;
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v80" : P = $"__GI_mempcpy"(P %"pr.7", P %"v78", L %"v52");
    %"v83" : L = Sub %"pr.1", %"v52";
    %"chk11" : A = (Renew 0 8 Read 8) %"chk6", %"v77";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v88" = %"v86" +p %"v52";
    %"chk12" : A = (Renew 0 8 Write 8) %"chk6", %"v77";
    store.ptr [%"chk12" + 0] <- %"v88"
    => goto "L72";
  @"L72" [%"pr.9" : P = phi("L70" => %"v80", "L54" => %"pr.7"); %"pr.4" : L = phi("L70" => %"v83", "L54" => %"pr.1")]:
    %"chk13" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v94" : W = And %"v93", #256
    => br %"v94" ? "L89" : "L91";
  @"L89":
    call void $"_IO_switch_to_main_get_area"(P %"v0")
    => goto poll "L39";
  @"L91":
    %"v101" = %"v0" +p #56;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v103" : L = Ptoi %"v102";
    %"v104" : W = (Cmp Ne L) %"v103", #0
    => br %"v104" ? "L105" : "L106";
  @"L105":
    %"v109" = %"v0" +p #64;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v109";
    %"v110" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v112" = %"v0" +p #56;
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v114" : L = Ptoi %"v110";
    %"v115" : L = Ptoi %"v113";
    %"v116" : L = Sub %"v114", %"v115";
    %"v117" : W = (Cmp Ult L) %"pr.4", %"v116"
    => goto "L106";
  @"L106" [%"v119" : W = phi("L91" => #0, "L105" => %"v117")]:
    => br %"v119" ? "L97" : "L99";
  @"L97":
    call %"v124" : W = $"__GI___underflow"(P %"v0");
    %"v126" : W = (Cmp Eq W) %"v124", #4294967295
    => br %"v126" ? "L41" : poll "L39";
  @"L99":
    %"v130" = %"v0" +p #24;
    %"v132" = %"v0" +p #56;
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v130";
    store.ptr [%"chk18" + 0] <- %"v133";
    %"v135" = %"v0" +p #8;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Renew 0 8 Write 8) %"chk6", %"v135";
    store.ptr [%"chk20" + 0] <- %"v138";
    %"v140" = %"v0" +p #16;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (Renew 0 8 Write 8) %"chk5", %"v140";
    store.ptr [%"chk22" + 0] <- %"v143";
    %"v145" = %"v0" +p #32;
    %"v147" = %"v0" +p #40;
    %"chk23" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v147";
    store.ptr [%"chk24" + 0] <- %"v150";
    %"chk25" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v145";
    store.ptr [%"chk25" + 0] <- %"v150";
    %"v152" = %"v0" +p #48;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v152";
    store.ptr [%"chk27" + 0] <- %"v155";
    %"chk28" : A = (Renew 0 8 Read 8) %"chk0", %"v132";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v163" : L = Ptoi %"v162";
    %"v164" : W = (Cmp Ne L) %"v163", #0
    => br %"v164" ? "L157" : "L159";
  @"L157":
    %"v167" = %"v0" +p #64;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v170" = %"v0" +p #56;
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v172" : L = Ptoi %"v168";
    %"v173" : L = Ptoi %"v171";
    %"v174" : L = Sub %"v172", %"v173";
    %"v179" : W = (Cmp Uge L) %"v174", #128
    => br %"v179" ? "L175" : "L159";
  @"L175":
    %"v183" : L = Urem %"pr.4", %"v174";
    %"v184" : L = Sub %"pr.4", %"v183"
    => goto "L159";
  @"L159" [%"pr.5" : L = phi("L175" => %"v184", "L157" => %"pr.4", "L99" => %"pr.4")]:
    %"v186" = %"v0" +p #216;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_2.v4" : L = Ptoi %"v187";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join";
  @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join";
  @"iw_2.join":
    %"v189" = %"v187" +p #112;
    %"chk32" : A = (Check 0 8 Read 8) %"v189";
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : F = CheckFunction %"v190";
    rawcall %"v194" : L = %"chk33"(P %"v0", P %"pr.9", L %"pr.5");
    %"v199" : W = (Cmp Sle L) %"v194", #0
    => br %"v199" ? "L195" : "L197";
  @"L195":
    %"v204" : W = (Cmp Eq L) %"v194", #0
    => br %"v204" ? "L200" : "L201";
  @"L200":
    %"chk34" : A = (Renew 0 4 Read 1) %"chk13", %"v0";
    %"v206" : W = (RawLoad (LdNarrow Sw) 0) %"chk34";
    %"v207" : W = Or %"v206", #16;
    %"chk35" : A = (Renew 0 4 Write 1) %"chk13", %"v0";
    store Ww [%"chk35" + 0] <- %"v207"
    => goto "L41";
  @"L201":
    %"chk36" : A = (Renew 0 4 Read 1) %"chk13", %"v0";
    %"v209" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v210" : W = Or %"v209", #32;
    %"chk37" : A = (Renew 0 4 Write 1) %"chk13", %"v0";
    store Ww [%"chk37" + 0] <- %"v210"
    => goto "L41";
  @"L197":
    %"v214" = %"pr.9" +p %"v194";
    %"v217" : L = Sub %"pr.4", %"v194";
    %"v222" = %"v0" +p #144;
    %"chk38" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v222";
    %"v223" : L = (RawLoad LdL 0) %"chk38";
    %"v226" : W = (Cmp Ne L) %"v223", #18446744073709551615
    => br %"v226" ? "L218" : poll "L39";
  @"L218":
    %"v228" = %"v0" +p #144;
    %"v229" : L = (RawLoad LdL 0) %"chk38";
    %"v231" : L = Add %"v229", %"v194";
    %"chk40" : A = (Renew 0 8 Write 1) %"chk38", %"v228";
    store Wl [%"chk40" + 0] <- %"v231"
    => goto poll "L39";
  @"L41" [%"pr.2" : L = phi("L39" => %"pr.1", "L97" => %"pr.4", "L200" => %"pr.4", "L201" => %"pr.4")]:
    %"v234" : L = Sub %"v4", %"pr.2"
    => ret %"v234"
} }.

Definition item___GI__IO_file_xsputn : item :=
  (IAlias (a "__GI__IO_file_xsputn") (a "export") (a "_IO_new_file_xsputn")).

Definition fn_glibc_fileops'23decide_maybe_mmap : func :=
  ir_fn{ "local" "glibc_fileops#decide_maybe_mmap"(P %"v0") -> RVoid {
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
    => br %"v44" ? "L45" : "L46";
  @"L45":
    %"v48" = %"v0" +p #144;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v48";
    %"v49" : L = (RawLoad LdL 0) %"chk5";
    %"v52" : W = (Cmp Eq L) %"v49", #18446744073709551615
    => br %"v52" ? "L46" : "L53";
  @"L53":
    %"v56" = %"v0" +p #144;
    %"v57" : L = (RawLoad LdL 0) %"chk5";
    %"v58" = %"v2" +p #48;
    %"chk7" : A = (Check 0 8 Read 1) %"v58";
    %"v59" : L = (RawLoad LdL 0) %"chk7";
    %"v60" : W = (Cmp Sle L) %"v57", %"v59"
    => goto "L46";
  @"L46" [%"v64" : W = phi("L31" => #0, "L45" => #1, "L53" => %"v60")]:
    => br %"v64" ? "L3" : "L5";
  @"L3":
    %"v66" = %"v2" +p #48;
    %"chk8" : A = (Check 0 8 Read 1) %"v66";
    %"v67" : L = (RawLoad LdL 0) %"chk8";
    %"v69" = %"v0" +p #112;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v69";
    %"v70" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    call %"v71" : P = $"__GI___mmap64"(P #0, L %"v67", W #1, W #1, W %"v70", L #0);
    (Flight (a "v78") Copy [(FValue (Const 18446744073709551615))] LowerNone);
    %"v79" : L = Ptoi %"v71";
    %"v80" : L = Ptoi %"v78";
    %"v81" : W = (Cmp Ne L) %"v79", %"v80"
    => br %"v81" ? "L72" : "L5";
  @"L72":
    %"v86" = %"v0" +p #112;
    %"chk10" : A = (Renew 0 4 Read 1) %"chk9", %"v86";
    %"v87" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"v88" = %"v2" +p #48;
    %"chk11" : A = (Renew 0 8 Read 1) %"chk8", %"v88";
    %"v89" : L = (RawLoad LdL 0) %"chk11";
    call %"v90" : L = $"__lseek64"(W %"v87", L %"v89", W #0);
    %"chk12" : A = (Renew 0 8 Read 1) %"chk8", %"v88";
    %"v92" : L = (RawLoad LdL 0) %"chk12";
    %"v93" : W = (Cmp Ne L) %"v90", %"v92"
    => br %"v93" ? "L82" : "L83";
  @"L82":
    %"v95" = %"v2" +p #48;
    %"v96" : L = (RawLoad LdL 0) %"chk12";
    call %"v97" : W = $"__GI___munmap"(P %"v71", L %"v96");
    %"v99" = %"v0" +p #144;
    %"chk14" : A = (HalfCheck Lower 0 8 Write 1) %"chk0", %"v99";
    store Wl [%"chk14" + 0] <- #18446744073709551615
    => goto "L5";
  @"L83":
    %"v105" = %"v2" +p #48;
    %"v106" : L = (RawLoad LdL 0) %"chk12";
    %"v107" = %"v71" +p %"v106";
    call void $"__GI__IO_setb"(P %"v0", P %"v71", P %"v107", W #0);
    %"v112" = %"v0" +p #144;
    %"chk16" : A = (HalfCheck Lower 0 8 Read 1) %"chk0", %"v112";
    %"v113" : L = (RawLoad LdL 0) %"chk16";
    %"v116" : W = (Cmp Eq L) %"v113", #18446744073709551615
    => br %"v116" ? "L108" : "L110";
  @"L108":
    %"v118" = %"v0" +p #144;
    %"chk17" : A = (Renew 0 8 Write 1) %"chk16", %"v118";
    store Wl [%"chk17" + 0] <- #0
    => goto "L110";
  @"L110":
    %"v120" = %"v0" +p #24;
    %"chk18" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v120";
    store.ptr [%"chk18" + 0] <- %"v71";
    %"v123" = %"v0" +p #8;
    %"v126" = %"v0" +p #144;
    %"chk19" : A = (Renew 0 8 Read 1) %"chk16", %"v126";
    %"v127" : L = (RawLoad LdL 0) %"chk19";
    %"v128" = %"v71" +p %"v127";
    %"chk20" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v123";
    store.ptr [%"chk20" + 0] <- %"v128";
    %"v130" = %"v0" +p #16;
    %"v132" = %"v2" +p #48;
    %"chk21" : A = (Renew 0 8 Read 1) %"chk8", %"v132";
    %"v133" : L = (RawLoad LdL 0) %"chk21";
    %"v134" = %"v71" +p %"v133";
    %"chk22" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v130";
    store.ptr [%"chk22" + 0] <- %"v134";
    %"chk23" : A = (Renew 0 8 Read 1) %"chk8", %"v132";
    %"v138" : L = (RawLoad LdL 0) %"chk23";
    %"chk24" : A = (Renew 0 8 Write 1) %"chk16", %"v126";
    store Wl [%"chk24" + 0] <- %"v138";
    %"v143" = %"v0" +p #192;
    %"chk25" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v143";
    %"v144" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v145" : W = (Cmp Sle W) %"v144", #0
    => br %"v145" ? "L139" : "L140";
  @"L139":
    %"v147" = %"v0" +p #216;
    %"v148" : P = Copy $"__io_vtables";
    %"v149" = %"v148" +p #504;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk0", %"v147";
    store.ptr [%"chk26" + 0] <- %"v149"
    => goto "L141";
  @"L140":
    %"v151" = %"v0" +p #216;
    %"v152" : P = Copy $"__io_vtables";
    %"v153" = %"v152" +p #1008;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"v151";
    store.ptr [%"chk27" + 0] <- %"v153"
    => goto "L141";
  @"L141":
    %"v155" = %"v0" +p #160;
    %"chk28" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v155";
    %"v156" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v157" = %"v156" +p #224;
    %"v158" : P = Copy $"__io_vtables";
    %"v159" = %"v158" +p #1008;
    %"chk29" : A = (Check 0 8 Write 8) %"v157";
    store.ptr [%"chk29" + 0] <- %"v159"
    => ret void;
  @"L5":
    %"v164" = %"v0" +p #192;
    %"chk30" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v164";
    %"v165" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v166" : W = (Cmp Sle W) %"v165", #0
    => br %"v166" ? "L160" : "L161";
  @"L160":
    %"v168" = %"v0" +p #216;
    %"v169" : P = Copy $"__io_vtables";
    %"v170" = %"v169" +p #336;
    %"chk31" : A = (Renew 0 8 Write 8) %"chk0", %"v168";
    store.ptr [%"chk31" + 0] <- %"v170"
    => goto "L162";
  @"L161":
    %"v172" = %"v0" +p #216;
    %"v173" : P = Copy $"__io_vtables";
    %"v174" = %"v173" +p #840;
    %"chk32" : A = (Renew 0 8 Write 8) %"chk0", %"v172";
    store.ptr [%"chk32" + 0] <- %"v174"
    => goto "L162";
  @"L162":
    %"v176" = %"v0" +p #160;
    %"chk33" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v176";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v178" = %"v177" +p #224;
    %"v179" : P = Copy $"__io_vtables";
    %"v180" = %"v179" +p #840;
    %"chk34" : A = (Check 0 8 Write 8) %"v178";
    store.ptr [%"chk34" + 0] <- %"v180"
    => ret void
} }.

Definition fn_glibc_fileops'23mmap_remap_check : func :=
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

Definition item_glibc_fileops'23str'2e265 : item :=
  (IData (a "glibc_fileops#str.265") (LRo (a "local")) 1 [(Item Wb 44); (Item Wb 99); (Item Wb 99); (Item Wb 115); (Item Wb 61); (Item Wb 0)]).

Definition item_glibc_fileops'23str'2e266 : item :=
  (IData (a "glibc_fileops#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 99); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 116); (Item Wb 111); (Item Wb 119); (Item Wb 99); (Item Wb 95); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition item_glibc_fileops'23str'2e267 : item :=
  (IData (a "glibc_fileops#str.267") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 111); (Item Wb 112); (Item Wb 115); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_fileops'23str'2e268 : item :=
  (IData (a "glibc_fileops#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 110); (Item Wb 101); (Item Wb 119); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 102); (Item Wb 111); (Item Wb 112); (Item Wb 101); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_fileops'23str'2e269 : item :=
  (IData (a "glibc_fileops#str.269") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 99); (Item Wb 116); (Item Wb 115); (Item Wb 46); (Item Wb 116); (Item Wb 111); (Item Wb 109); (Item Wb 98); (Item Wb 95); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 101); (Item Wb 112); (Item Wb 115); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).
