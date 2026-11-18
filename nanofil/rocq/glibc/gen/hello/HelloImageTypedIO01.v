(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn__IO_ferror : func :=
  ir_fn{ "export" "_IO_ferror"(P %"v0") -> (RClass W) {
  @"start":
    %"v10" = %"v0" +p #116;
    %"chk0" : A = (Check 0 4 Read 1) %"v10";
    %"v11" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v12" : W = Shl %"v11", #8;
    %"v13" : W = Sar %"v12", #8;
    %"v14" : W = And %"v13", #128;
    %"v16" : W = (Cmp Eq W) %"v14", #0
    => br %"v16" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v19" : W = And %"v18", #32;
    %"v20" : W = (Cmp Ne W) %"v19", #0
    => ret %"v20";
  @"L8":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v27" : W = And %"v26", #32768;
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L29" : "L24";
  @"L29":
    call %"v33" : P = $"zthread_self_cookie"();
    %"v37" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v39" : W = (Cmp Ne W) %"v38", #0
    => br %"v39" ? "L40" : "L41";
  @"L40":
    %"v43" = %"v0" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v45" = %"v44" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v47" : L = Ptoi %"v46";
    %"v48" : L = Ptoi #0;
    %"v49" : W = (Cmp Eq L) %"v47", %"v48"
    => goto "L41";
  @"L41" [%"v51" : W = phi("L29" => #0, "L40" => %"v49")]:
    => br %"v51" ? "L34" : "L35";
  @"L34":
    %"v53" = %"v0" +p #136;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 4 Write 1) %"v54";
    store Ww [%"chk7" + 0] <- #1;
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v58" = %"v57" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v58";
    store.ptr [%"chk9" + 0] <- %"v33"
    => goto "L24";
  @"L35":
    %"v64" = %"v0" +p #136;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" = %"v65" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"v66";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v69" : L = Ptoi %"v67";
    %"v70" : L = Ptoi %"v33";
    %"v71" : W = (Cmp Ne L) %"v69", %"v70"
    => br %"v71" ? "L60" : "L61";
  @"L60":
    %"v74" = %"v0" +p #136;
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Check 0 4 Write 4) %"v75";
    %"v82" : W = (RawCas (CasNarrow Sw) 0) %"chk13", #0, #1;
    %"v83" : W = (Cmp Eq W) %"v82", #0
    => br %"v83" ? "L85" : "L84";
  @"L84":
    => goto "L85";
  @"L85":
    %"v86" : W = (Cmp Ne W) %"v82", #0
    => br %"v86" ? "L89" : "L78";
  @"L89":
    call void $"__GI___lll_lock_wait_private"(P %"v75")
    => goto "L78";
  @"L78":
    %"v100" = %"v0" +p #136;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk10", %"v100";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v102" = %"v101" +p #8;
    %"chk15" : A = (Check 0 8 Write 8) %"v102";
    store.ptr [%"chk15" + 0] <- %"v33"
    => goto "L24";
  @"L61":
    %"v105" = %"v0" +p #136;
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v107" = %"v106" +p #4;
    %"chk17" : A = (Check 0 4 Read 1) %"v107";
    %"v108" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v109" : W = Add %"v108", #1;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v107";
    store Ww [%"chk18" + 0] <- %"v109"
    => goto "L24";
  @"L24":
    %"chk19" : A = (Renew 0 4 Read 1) %"chk2", %"v0";
    %"v111" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v112" : W = And %"v111", #32;
    %"v113" : W = (Cmp Ne W) %"v112", #0;
    %"v118" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v119" : W = And %"v118", #32768;
    %"v120" : W = (Cmp Eq W) %"v119", #0
    => br %"v120" ? "L121" : "L116";
  @"L121":
    %"v127" : P = Copy $"__libc_single_threaded_internal";
    %"chk21" : A = (Check 0 1 Read 1) %"v127";
    %"v128" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v129" : W = (Cmp Ne W) %"v128", #0
    => br %"v129" ? "L130" : "L131";
  @"L130":
    %"v133" = %"v0" +p #136;
    %"chk22" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v135" = %"v134" +p #4;
    %"chk23" : A = (Check 0 4 Read 1) %"v135";
    %"v136" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"v137" : W = (Cmp Eq W) %"v136", #0
    => goto "L131";
  @"L131" [%"v139" : W = phi("L121" => #0, "L130" => %"v137")]:
    => br %"v139" ? "L124" : "L125";
  @"L124":
    %"v141" = %"v0" +p #136;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v141";
    %"v142" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v143" = %"v142" +p #8;
    %"chk25" : A = (Check 0 8 Write 8) %"v143";
    store.ptr [%"chk25" + 0] <- #0;
    %"chk26" : A = (Renew 0 8 Read 8) %"chk24", %"v141";
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"chk27" : A = (Check 0 4 Write 1) %"v146";
    store Ww [%"chk27" + 0] <- #0
    => goto "L116";
  @"L125":
    %"v151" = %"v0" +p #136;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v151";
    %"v152" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v153" = %"v152" +p #4;
    %"chk29" : A = (Check 0 4 Read 1) %"v153";
    %"v154" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v155" : W = (Cmp Eq W) %"v154", #0
    => br %"v155" ? "L147" : "L148";
  @"L147":
    %"v157" = %"v0" +p #136;
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v159" = %"v158" +p #8;
    %"chk31" : A = (Check 0 8 Write 8) %"v159";
    store.ptr [%"chk31" + 0] <- #0;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk28", %"v157";
    %"v163" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 4 Read 1) %"v163";
    %"v167" : W = (RawLoad (LdNarrow Sw) 0) %"chk33"
    => goto "L168";
  @"L168" [%"v170" : W = phi("L147" => %"v167", "L168" => %"v171")]:
    %"chk34" : A = (HalfCheck Lower 0 4 Write 4) %"chk33", %"v163";
    %"v171" : W = (RawCas (CasNarrow Sw) 0) %"chk34", %"v170", #0;
    %"v172" : W = (Cmp Eq W) %"v171", %"v170"
    => br %"v172" ? "L169" : poll "L168";
  @"L169":
    %"v177" : W = (Cmp Sgt W) %"v170", #1
    => br %"v177" ? "L180" : "L116";
  @"L180":
    call void $"__GI___lll_lock_wake_private"(P %"v163")
    => goto "L116";
  @"L148":
    %"v192" = %"v0" +p #136;
    %"v193" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v194" = %"v193" +p #4;
    %"chk36" : A = (Check 0 4 Read 1) %"v194";
    %"v195" : W = (RawLoad (LdNarrow Sw) 0) %"chk36";
    %"v196" : W = Sub %"v195", #1;
    %"chk37" : A = (Renew 0 4 Write 1) %"chk36", %"v194";
    store Ww [%"chk37" + 0] <- %"v196"
    => goto "L116";
  @"L116":
    => ret %"v113"
} }.

Definition hello_image_fn___GI__IO_file_doallocate : func :=
  ir_fn{ "export" "__GI__IO_file_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #144;
    %"v9" = %"v0" +p #112;
    %"chk0" : A = (Check 0 4 Read 1) %"v9";
    %"v10" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v11" : W = (Cmp Sge W) %"v10", #0
    => br %"v11" ? "L12" : "L13";
  @"L12":
    %"v15" = %"v0" +p #216;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" : L = Ptoi %"v16";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v18" = %"v16" +p #144;
    %"chk2" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v19";
    rawcall %"v21" : W = %"chk3"(P %"v0", P %"v4");
    %"v22" : L = (Ext Sw) %"v21";
    %"v23" : W = (Cmp Sge L) %"v22", #0
    => goto "L13";
  @"L13" [%"v25" : W = phi("start" => #0, "iw_1.join" => %"v23")]:
    => br %"v25" ? "L5" : "L7";
  @"L5":
    %"v29" = %"v4" +p #24;
    %"chk4" : A = (Check 0 4 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"v31" : W = And %"v30", #61440;
    %"v32" : W = (Cmp Eq W) %"v31", #8192
    => br %"v32" ? "L26" : "L28";
  @"L26":
    %"v37" = %"v4" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 1) %"chk4", %"v37";
    %"v38" : L = (RawLoad LdL 0) %"chk5";
    call %"v39" : W = $"__gnu_dev_major"(L %"v38");
    %"v41" : W = (Cmp Sge W) %"v39", #136
    => br %"v41" ? "L42" : "L43";
  @"L42":
    %"v45" : W = (Cmp Sle W) %"v39", #143
    => goto "L43";
  @"L43" [%"v47" : W = phi("L26" => #0, "L42" => %"v45")]:
    => br %"v47" ? "L49" : "L48";
  @"L48":
    %"v51" = %"v0" +p #112;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk0", %"v51";
    %"v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk6";
    call %"v53" : W = $"__isatty_nostatus"(W %"v52");
    %"v54" : W = (Cmp Ne W) %"v53", #0
    => goto "L49";
  @"L49" [%"v55" : W = phi("L43" => #1, "L48" => %"v54")]:
    => br %"v55" ? "L33" : "L28";
  @"L33":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v57" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v58" : W = Or %"v57", #512;
    %"chk8" : A = (Renew 0 4 Write 1) %"chk7", %"v0";
    store Ww [%"chk8" + 0] <- %"v58"
    => goto "L28";
  @"L28":
    %"v62" = %"v4" +p #56;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 1) %"chk4", %"v62";
    %"v63" : L = (RawLoad LdL 0) %"chk9";
    %"v64" : W = (Cmp Sgt L) %"v63", #0
    => br %"v64" ? "L65" : "L66";
  @"L65":
    %"v67" = %"v4" +p #56;
    %"v68" : L = (RawLoad LdL 0) %"chk9";
    %"v69" : W = (Cmp Slt L) %"v68", #8192
    => goto "L66";
  @"L66" [%"v71" : W = phi("L28" => #0, "L65" => %"v69")]:
    => br %"v71" ? "L59" : "L7";
  @"L59":
    %"v72" = %"v4" +p #56;
    %"v73" : L = (RawLoad LdL 0) %"chk9"
    => goto "L7";
  @"L7" [%"pr.2" : L = phi("L59" => %"v73", "L66" => #8192, "L13" => #8192)]:
    call %"v75" : P = $"malloc"(L %"pr.2");
    %"v80" : L = Ptoi %"v75";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L76" : "L78";
  @"L76":
    => ret #4294967295;
  @"L78":
    %"v91" = %"v75" +p %"pr.2";
    call void $"__GI__IO_setb"(P %"v0", P %"v75", P %"v91", W #1)
    => ret #1
} }.

Definition hello_image_fn__IO_new_file_init_internal : func :=
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

Definition hello_image_fn__IO_file_close_maybe_unlink : func :=
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

Definition hello_image_fn__IO_new_file_close_it : func :=
  ir_fn{ "export" "_IO_new_file_close_it"(P %"v0") -> (RClass W) {
  @"start":
    call %"v4" : W = $"_IO_file_close_maybe_unlink"(P %"v0", W #1)
    => ret %"v4"
} }.

Definition hello_image_fn__IO_new_file_finish : func :=
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

Definition hello_image_fn___GI__IO_file_open : func :=
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

Definition hello_image_fn__IO_new_file_fopen : func :=
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

Definition hello_image_fn__IO_new_file_setbuf : func :=
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

Definition hello_image_fn__IO_file_setbuf_mmap : func :=
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

Definition hello_image_fn__IO_new_do_write : func :=
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
