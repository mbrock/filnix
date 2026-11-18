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

Definition hi_fn__IO_ferror : func :=
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

Definition hi_fn___GI__IO_file_doallocate : func :=
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

Definition hi_fn__IO_file_close_maybe_unlink : func :=
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

Definition hi_fn__IO_new_file_finish : func :=
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

Definition hi_fn__IO_new_file_setbuf : func :=
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

Definition hi_fn__IO_file_setbuf_mmap : func :=
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

Definition hi_fn__IO_new_do_write : func :=
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

Definition hi_fn__IO_new_file_underflow : func :=
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

Definition hi_fn__IO_file_underflow_mmap : func :=
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

Definition hi_fn__IO_file_underflow_maybe_mmap : func :=
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
