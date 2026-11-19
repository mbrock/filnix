(** This file defines checked IR from glibc’s `libio/iofclose.os` object.
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

Definition fn__IO_new_fclose : func :=
  ir_fn{ "export" "_IO_new_fclose"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v15" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v16" : W = And %"v15", #32768;
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => br %"v17" ? "L18" : "L13";
  @"L18":
    call %"v22" : P = $"zthread_self_cookie"();
    %"v26" : P = Copy $"__libc_single_threaded_internal";
    %"chk1" : A = (Check 0 1 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v28" : W = (Cmp Ne W) %"v27", #0
    => br %"v28" ? "L29" : "L30";
  @"L29":
    %"v32" = %"v0" +p #136;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v34" = %"v33" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v36" : L = Ptoi %"v35";
    %"v37" : L = Ptoi #0;
    %"v38" : W = (Cmp Eq L) %"v36", %"v37"
    => goto "L30";
  @"L30" [%"v40" : W = phi("L18" => #0, "L29" => %"v38")]:
    => br %"v40" ? "L23" : "L24";
  @"L23":
    %"v42" = %"v0" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v43";
    store Ww [%"chk5" + 0] <- #1;
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v47" = %"v46" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v47";
    store.ptr [%"chk7" + 0] <- %"v22"
    => goto "L13";
  @"L24":
    %"v53" = %"v0" +p #136;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v53";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v55" = %"v54" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v58" : L = Ptoi %"v56";
    %"v59" : L = Ptoi %"v22";
    %"v60" : W = (Cmp Ne L) %"v58", %"v59"
    => br %"v60" ? "L49" : "L50";
  @"L49":
    %"v63" = %"v0" +p #136;
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 4 Write 4) %"v64";
    %"v71" : W = (RawCas (CasNarrow Sw) 0) %"chk11", #0, #1;
    %"v72" : W = (Cmp Eq W) %"v71", #0
    => br %"v72" ? "L74" : "L73";
  @"L73":
    => goto "L74";
  @"L74":
    %"v75" : W = (Cmp Ne W) %"v71", #0
    => br %"v75" ? "L78" : "L67";
  @"L78":
    call void $"__GI___lll_lock_wait_private"(P %"v64")
    => goto "L67";
  @"L67":
    %"v89" = %"v0" +p #136;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk8", %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v91" = %"v90" +p #8;
    %"chk13" : A = (Check 0 8 Write 8) %"v91";
    store.ptr [%"chk13" + 0] <- %"v22"
    => goto "L13";
  @"L50":
    %"v94" = %"v0" +p #136;
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v96" = %"v95" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v96";
    %"v97" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v98" : W = Add %"v97", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v96";
    store Ww [%"chk16" + 0] <- %"v98"
    => goto "L13";
  @"L13":
    %"chk17" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v104" : W = And %"v103", #8192
    => br %"v104" ? "L99" : "L100";
  @"L99":
    call %"v107" : W = $"_IO_file_close_maybe_unlink"(P %"v0", W #0);
    %"v109" = %"v0" +p #116;
    %"chk18" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v109";
    %"v110" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v111" : W = Shl %"v110", #8;
    %"v112" : W = Sar %"v111", #8;
    %"v113" : W = Or %"v112", #32;
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v115" : W = And %"v114", #4278190080;
    %"v116" : W = And %"v113", #16777215;
    %"v117" : W = Or %"v115", %"v116";
    %"chk20" : A = (Renew 0 4 Write 1) %"chk18", %"v109";
    store Ww [%"chk20" + 0] <- %"v117"
    => goto "L101";
  @"L100":
    %"v124" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v125" : W = And %"v124", #32
    => br %"v125" ? "L101" : "L121";
  @"L121":
    => goto "L101";
  @"L101" [%"pr.1" : W = phi("L99" => %"v107", "L121" => #0, "L100" => #4294967295)]:
    %"chk22" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"iw_1.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"iw_1.v10" : W = And %"iw_1.v9", #32768;
    %"iw_1.v11" : W = (Cmp Eq W) %"iw_1.v10", #0
    => br %"iw_1.v11" ? "iw_1.L5" : "L8";
  @"iw_1.L5":
    %"iw_1.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk22";
    %"iw_1.v17" : W = And %"iw_1.v16", #32768;
    %"iw_1.v18" : W = (Cmp Eq W) %"iw_1.v17", #0
    => br %"iw_1.v18" ? "iw_1.L19" : "L8";
  @"iw_1.L19":
    %"iw_1.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk24" : A = (Check 0 1 Read 1) %"iw_1.v25";
    %"iw_1.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk24";
    %"iw_1.v27" : W = (Cmp Ne W) %"iw_1.v26", #0
    => br %"iw_1.v27" ? "iw_1.L28" : "iw_1.L29";
  @"iw_1.L28":
    %"iw_1.v31" = %"v0" +p #136;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v31";
    %"iw_1.v32" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v33" = %"iw_1.v32" +p #4;
    %"chk26" : A = (Check 0 4 Read 1) %"iw_1.v33";
    %"iw_1.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"iw_1.v35" : W = (Cmp Eq W) %"iw_1.v34", #0
    => goto "iw_1.L29";
  @"iw_1.L29" [%"iw_1.v37" : W = phi("iw_1.L19" => #0, "iw_1.L28" => %"iw_1.v35")]:
    => br %"iw_1.v37" ? "iw_1.L22" : "iw_1.L23";
  @"iw_1.L22":
    %"iw_1.v39" = %"v0" +p #136;
    %"chk27" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v39";
    %"iw_1.v40" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"iw_1.v41" = %"iw_1.v40" +p #8;
    %"chk28" : A = (Check 0 8 Write 8) %"iw_1.v41";
    store.ptr [%"chk28" + 0] <- #0;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk27", %"iw_1.v39";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Check 0 4 Write 1) %"iw_1.v44";
    store Ww [%"chk30" + 0] <- #0
    => goto "L8";
  @"iw_1.L23":
    %"iw_1.v49" = %"v0" +p #136;
    %"chk31" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v49";
    %"iw_1.v50" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_1.v51" = %"iw_1.v50" +p #4;
    %"chk32" : A = (Check 0 4 Read 1) %"iw_1.v51";
    %"iw_1.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"iw_1.v53" : W = (Cmp Eq W) %"iw_1.v52", #0
    => br %"iw_1.v53" ? "iw_1.L45" : "iw_1.L46";
  @"iw_1.L45":
    %"iw_1.v55" = %"v0" +p #136;
    %"iw_1.v56" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_1.v57" = %"iw_1.v56" +p #8;
    %"chk34" : A = (Check 0 8 Write 8) %"iw_1.v57";
    store.ptr [%"chk34" + 0] <- #0;
    %"chk35" : A = (Renew 0 8 Read 8) %"chk31", %"iw_1.v55";
    %"iw_1.v61" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Check 0 4 Read 1) %"iw_1.v61";
    %"iw_1.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk36"
    => goto "iw_1.L66";
  @"iw_1.L66" [%"iw_1.v68" : W = phi("iw_1.L45" => %"iw_1.v65", "iw_1.L66" => %"iw_1.v69")]:
    %"chk37" : A = (HalfCheck Lower 0 4 Write 4) %"chk36", %"iw_1.v61";
    %"iw_1.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk37", %"iw_1.v68", #0;
    %"iw_1.v70" : W = (Cmp Eq W) %"iw_1.v69", %"iw_1.v68"
    => br %"iw_1.v70" ? "iw_1.L67" : poll "iw_1.L66";
  @"iw_1.L67":
    %"iw_1.v75" : W = (Cmp Sgt W) %"iw_1.v68", #1
    => br %"iw_1.v75" ? "iw_1.L78" : "L8";
  @"iw_1.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_1.v61")
    => goto "L8";
  @"iw_1.L46":
    %"iw_1.v90" = %"v0" +p #136;
    %"iw_1.v91" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_1.v92" = %"iw_1.v91" +p #4;
    %"chk39" : A = (Check 0 4 Read 1) %"iw_1.v92";
    %"iw_1.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk39";
    %"iw_1.v94" : W = Sub %"iw_1.v93", #1;
    %"chk40" : A = (Renew 0 4 Write 1) %"chk39", %"iw_1.v92";
    store Ww [%"chk40" + 0] <- %"iw_1.v94"
    => goto "L8";
  @"L8":
    call void $"__GI__IO_un_link"(P %"v0");
    %"v130" = %"v0" +p #216;
    %"chk41" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"iw_2.v4" : L = Ptoi %"v131";
    %"iw_2.v7" : P = Copy $"__io_vtables";
    %"iw_2.v8" : L = Ptoi %"iw_2.v7";
    %"iw_2.v9" : L = Sub %"iw_2.v4", %"iw_2.v8";
    %"iw_2.v15" : W = (Cmp Uge L) %"iw_2.v9", #2352
    => br %"iw_2.v15" ? "iw_2.L10" : "iw_2.join";
  @"iw_2.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_2.join";
  @"iw_2.join":
    %"v133" = %"v131" +p #16;
    %"chk42" : A = (Check 0 8 Read 8) %"v133";
    %"v134" : P = (RawLoadPointer 0 load_effects) %"chk42";
    %"chk43" : F = CheckFunction %"v134";
    rawcall void %"chk43"(P %"v0", W #0);
    %"v140" = %"v0" +p #192;
    %"chk44" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v140";
    %"v141" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"v142" : W = (Cmp Sgt W) %"v141", #0
    => br %"v142" ? "L136" : "L137";
  @"L136":
    %"v147" = %"v0" +p #160;
    %"chk45" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v147";
    %"v148" : P = (RawLoadPointer 0 load_effects) %"chk45";
    %"v149" = %"v148" +p #72;
    %"chk46" : A = (Check 0 8 Read 8) %"v149";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v151" : L = Ptoi %"v150";
    %"v152" : L = Ptoi #0;
    %"v153" : W = (Cmp Ne L) %"v151", %"v152"
    => br %"v153" ? "L143" : "L145";
  @"L143":
    call void $"__GI__IO_free_wbackup_area"(P %"v0")
    => goto "L145";
  @"L145":
    %"v157" = %"v0" +p #152;
    %"chk47" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v157";
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"v160" : P = Copy $"__gconv_lock";
    %"chk48" : A = (Check 0 4 Write 4) %"v160";
    %"v167" : W = (RawCas (CasNarrow Sw) 0) %"chk48", #0, #1;
    %"v168" : W = (Cmp Eq W) %"v167", #0
    => br %"v168" ? "L170" : "L169";
  @"L169":
    => goto "L170";
  @"L170":
    %"v171" : W = (Cmp Ne W) %"v167", #0
    => br %"v171" ? "L174" : "L163";
  @"L174":
    call void $"__GI___lll_lock_wait_private"(P %"v160")
    => goto "L163";
  @"L163":
    %"chk49" : A = (Check 0 8 Read 8) %"v158";
    %"v185" : P = (RawLoadPointer 0 load_effects) %"chk49";
    call void $"__gconv_release_step"(P %"v185");
    %"v187" = %"v158" +p #56;
    %"chk50" : A = (HalfCheck Upper 0 8 Read 8) %"chk49", %"v187";
    %"v188" : P = (RawLoadPointer 0 load_effects) %"chk50";
    call void $"__gconv_release_step"(P %"v188");
    %"v190" : P = Copy $"__gconv_lock";
    %"chk51" : A = (Check 0 4 Read 1) %"v190";
    %"v194" : W = (RawLoad (LdNarrow Sw) 0) %"chk51"
    => goto "L195";
  @"L195" [%"v197" : W = phi("L163" => %"v194", "L195" => %"v198")]:
    %"chk52" : A = (HalfCheck Lower 0 4 Write 4) %"chk51", %"v190";
    %"v198" : W = (RawCas (CasNarrow Sw) 0) %"chk52", %"v197", #0;
    %"v199" : W = (Cmp Eq W) %"v198", %"v197"
    => br %"v199" ? "L196" : poll "L195";
  @"L196":
    %"v204" : W = (Cmp Sgt W) %"v197", #1
    => br %"v204" ? "L207" : "iw_3.start";
  @"L207":
    call void $"__GI___lll_lock_wake_private"(P %"v190")
    => goto "iw_3.start";
  @"L137":
    %"v222" = %"v0" +p #80;
    %"chk53" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v222";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk53";
    %"v224" : L = Ptoi %"v223";
    %"v225" : L = Ptoi #0;
    %"v226" : W = (Cmp Ne L) %"v224", %"v225"
    => br %"v226" ? "L218" : "iw_3.start";
  @"L218":
    call void $"__GI__IO_free_backup_area"(P %"v0")
    => goto "iw_3.start";
  @"iw_3.start":
    %"iw_3.v6" : P = Copy $"_IO_2_1_stdin_";
    %"iw_3.v7" : L = Ptoi %"v0";
    %"iw_3.v8" : L = Ptoi %"iw_3.v6";
    %"iw_3.v9" : W = (Cmp Eq L) %"iw_3.v7", %"iw_3.v8"
    => br %"iw_3.v9" ? "iw_3.L11" : "iw_3.L10";
  @"iw_3.L10":
    %"iw_3.v13" : P = Copy $"_IO_2_1_stdout_";
    %"iw_3.v15" : L = Ptoi %"iw_3.v13";
    %"iw_3.v16" : W = (Cmp Eq L) %"iw_3.v7", %"iw_3.v15"
    => goto "iw_3.L11";
  @"iw_3.L11" [%"iw_3.v18" : W = phi("iw_3.start" => #1, "iw_3.L10" => %"iw_3.v16")]:
    => br %"iw_3.v18" ? "iw_3.L20" : "iw_3.L19";
  @"iw_3.L19":
    %"iw_3.v22" : P = Copy $"_IO_2_1_stderr_";
    %"iw_3.v24" : L = Ptoi %"iw_3.v22";
    %"iw_3.v25" : W = (Cmp Eq L) %"iw_3.v7", %"iw_3.v24"
    => goto "iw_3.L20";
  @"iw_3.L20" [%"iw_3.v27" : W = phi("iw_3.L11" => #1, "iw_3.L19" => %"iw_3.v25")]:
    => br %"iw_3.v27" ? "iw_3.join" : "iw_3.L4";
  @"iw_3.L4":
    call void $"free"(P %"v0")
    => goto "iw_3.join";
  @"iw_3.join":
    => ret %"pr.1"
} }.

Definition item_fclose : item :=
  (IAlias (a "fclose") (a "export") (a "_IO_new_fclose")).
