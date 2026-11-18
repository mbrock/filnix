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

Definition hello_image_fn___vfxprintf : func :=
  ir_fn{ "export" "__vfxprintf"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v12" : L = Ptoi %"v0";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"stderr";
    %"chk0" : A = (Check 0 8 Read 8) %"v15";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L10";
  @"L10" [%"pr.1" : P = phi("L8" => %"v16", "start" => %"v0")]:
    %"chk1" : A = (Check 0 4 Read 1) %"pr.1";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v22" : W = And %"v21", #32768;
    %"v23" : W = (Cmp Eq W) %"v22", #0
    => br %"v23" ? "L24" : "iw_1.start";
  @"L24":
    call %"v28" : P = $"zthread_self_cookie"();
    %"v32" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v34" : W = (Cmp Ne W) %"v33", #0
    => br %"v34" ? "L35" : "L36";
  @"L35":
    %"v38" = %"pr.1" +p #136;
    %"chk3" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v40" = %"v39" +p #8;
    %"chk4" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v42" : L = Ptoi %"v41";
    %"v44" : W = (Cmp Eq L) %"v42", %"v13"
    => goto "L36";
  @"L36" [%"v46" : W = phi("L24" => #0, "L35" => %"v44")]:
    => br %"v46" ? "L29" : "L30";
  @"L29":
    %"v48" = %"pr.1" +p #136;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 4 Write 1) %"v49";
    store Ww [%"chk6" + 0] <- #1;
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v53" = %"v52" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v53";
    store.ptr [%"chk8" + 0] <- %"v28"
    => goto "iw_1.start";
  @"L30":
    %"v59" = %"pr.1" +p #136;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v61" = %"v60" +p #8;
    %"chk10" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Ptoi %"v28";
    %"v66" : W = (Cmp Ne L) %"v64", %"v65"
    => br %"v66" ? "L55" : "L56";
  @"L55":
    %"v69" = %"pr.1" +p #136;
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk12" : A = (Check 0 4 Write 4) %"v70";
    %"v77" : W = (RawCas (CasNarrow Sw) 0) %"chk12", #0, #1;
    %"v78" : W = (Cmp Eq W) %"v77", #0
    => br %"v78" ? "L80" : "L79";
  @"L79":
    => goto "L80";
  @"L80":
    %"v81" : W = (Cmp Ne W) %"v77", #0
    => br %"v81" ? "L84" : "L73";
  @"L84":
    call void $"__GI___lll_lock_wait_private"(P %"v70")
    => goto "L73";
  @"L73":
    %"v95" = %"pr.1" +p #136;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk9", %"v95";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v97" = %"v96" +p #8;
    %"chk14" : A = (Check 0 8 Write 8) %"v97";
    store.ptr [%"chk14" + 0] <- %"v28"
    => goto "iw_1.start";
  @"L56":
    %"v100" = %"pr.1" +p #136;
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v102" = %"v101" +p #4;
    %"chk16" : A = (Check 0 4 Read 1) %"v102";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v104" : W = Add %"v103", #1;
    %"chk17" : A = (Renew 0 4 Write 1) %"chk16", %"v102";
    store Ww [%"chk17" + 0] <- %"v104"
    => goto "iw_1.start";
  @"iw_1.start":
    %"iw_1.v3" : P = (Alloc 8) #8;
    %"iw_1.v63" : P = (Alloc 4) #8;
    %"iw_1.v69" : P = (Alloc 16) #1040;
    %"chk18" : A = (Check 0 8 Write 8) %"iw_1.v3";
    store.ptr [%"chk18" + 0] <- %"v2";
    %"iw_1.v48" = %"pr.1" +p #192;
    %"chk19" : A = (HalfCheck Upper 0 4 Read 1) %"chk1", %"iw_1.v48";
    %"iw_1.v49" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"iw_1.v55" : W = (Cmp Sle W) %"iw_1.v49", #0
    => br %"iw_1.v55" ? "iw_1.L8" : "iw_1.L10";
  @"iw_1.L8":
    %"chk20" : A = (Renew 0 8 Read 8) %"chk18", %"iw_1.v3";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk20";
    call %"iw_1.v60" : W = $"__vfprintf_internal"(P %"pr.1", P %"iw_1.v57", P %"v4", W %"v6")
    => goto "iw_1.join";
  @"iw_1.L10":
    %"chk21" : A = (Renew 0 8 Read 8) %"chk18", %"iw_1.v3";
    %"iw_1.v66" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"iw_1.v67" : L = $"__GI_strlen"(P %"iw_1.v66");
    %"iw_1.v68" : L = Add %"iw_1.v67", #1;
    %"iw_1.iw_1.v4" = %"iw_1.v69" +p #16;
    %"chk22" : A = (Check 0 8 Write 8) %"iw_1.v69";
    store.ptr [%"chk22" + 0] <- %"iw_1.iw_1.v4";
    %"iw_1.iw_1.v6" = %"iw_1.v69" +p #8;
    %"chk23" : A = (HalfCheck Upper 0 8 Write 1) %"chk22", %"iw_1.iw_1.v6";
    store Wl [%"chk23" + 0] <- #1024;
    %"iw_1.v75" : W = (Cmp Ugt L) %"iw_1.v68", #4611686018427387903
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.iw_2.start";
  @"iw_1.L70":
    %"iw_1.v78" : P = Copy $"__libc_errno";
    %"chk24" : A = (Check 0 4 Write 1) %"iw_1.v78";
    store Ww [%"chk24" + 0] <- #75
    => goto "iw_1.join";
  @"iw_1.iw_2.start":
    call %"iw_1.iw_2.v9" : W = $"__GI___libc_scratch_buffer_set_array_size"(P %"iw_1.v69", L #4, L %"iw_1.v68");
    %"iw_1.iw_2.v10" : W = (Ext Ub) %"iw_1.iw_2.v9";
    %"iw_1.iw_2.v11" : L = (Ext Uw) %"iw_1.iw_2.v10";
    %"iw_1.v87" : W = (Cmp Eq L) %"iw_1.iw_2.v11", #0
    => br %"iw_1.v87" ? "iw_1.join" : "iw_1.L83";
  @"iw_1.L83":
    %"chk25" : A = (Renew 0 8 Read 8) %"chk22", %"iw_1.v69";
    %"iw_1.v90" : P = (RawLoadPointer 0 load_effects) %"chk25";
    call %"iw_1.v91" : P = $"__GI_memset"(P %"iw_1.v63", W #0, L #8);
    call %"iw_1.v94" : L = $"__mbsrtowcs"(P %"iw_1.v90", P %"iw_1.v3", L %"iw_1.v68", P %"iw_1.v63");
    %"iw_1.v98" : W = Copy %"iw_1.v94";
    %"iw_1.v100" : W = (Cmp Ne W) %"iw_1.v98", #4294967295
    => br %"iw_1.v100" ? "iw_1.L95" : "iw_1.L97";
  @"iw_1.L95":
    call %"iw_1.v105" : W = $"__vfwprintf_internal"(P %"pr.1", P %"iw_1.v90", P %"v4", W %"v6")
    => goto "iw_1.L97";
  @"iw_1.L97" [%"iw_1.pr.3" : W = phi("iw_1.L95" => %"iw_1.v105", "iw_1.L83" => %"iw_1.v94")]:
    %"chk26" : A = (Renew 0 8 Read 8) %"chk22", %"iw_1.v69";
    %"iw_1.iw_3.v6" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"iw_1.iw_3.v8" = %"iw_1.v69" +p #16;
    %"iw_1.iw_3.v9" : L = Ptoi %"iw_1.iw_3.v6";
    %"iw_1.iw_3.v10" : L = Ptoi %"iw_1.iw_3.v8";
    %"iw_1.iw_3.v11" : W = (Cmp Ne L) %"iw_1.iw_3.v9", %"iw_1.iw_3.v10"
    => br %"iw_1.iw_3.v11" ? "iw_1.iw_3.L2" : "iw_1.join";
  @"iw_1.iw_3.L2":
    %"iw_1.iw_3.v13" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call void $"free"(P %"iw_1.iw_3.v13")
    => goto "iw_1.join";
  @"iw_1.join" [%"v110" : W = phi("iw_1.L8" => %"iw_1.v60", "iw_1.L70" => #4294967295, "iw_1.iw_2.start" => #4294967295, "iw_1.L97" => %"iw_1.pr.3", "iw_1.iw_3.L2" => %"iw_1.pr.3")]:
    %"chk28" : A = (Renew 0 4 Read 1) %"chk1", %"pr.1";
    %"v115" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    %"v116" : W = And %"v115", #32768;
    %"v117" : W = (Cmp Eq W) %"v116", #0
    => br %"v117" ? "L118" : "L113";
  @"L118":
    %"v124" : P = Copy $"__libc_single_threaded_internal";
    %"chk29" : A = (Check 0 1 Read 1) %"v124";
    %"v125" : W = (RawLoad (LdNarrow Sb) 0) %"chk29";
    %"v126" : W = (Cmp Ne W) %"v125", #0
    => br %"v126" ? "L127" : "L128";
  @"L127":
    %"v130" = %"pr.1" +p #136;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v130";
    %"v131" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v132" = %"v131" +p #4;
    %"chk31" : A = (Check 0 4 Read 1) %"v132";
    %"v133" : W = (RawLoad (LdNarrow Sw) 0) %"chk31";
    %"v134" : W = (Cmp Eq W) %"v133", #0
    => goto "L128";
  @"L128" [%"v136" : W = phi("L118" => #0, "L127" => %"v134")]:
    => br %"v136" ? "L121" : "L122";
  @"L121":
    %"v138" = %"pr.1" +p #136;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v138";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v140" = %"v139" +p #8;
    %"chk33" : A = (Check 0 8 Write 8) %"v140";
    store.ptr [%"chk33" + 0] <- #0;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk32", %"v138";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (Check 0 4 Write 1) %"v143";
    store Ww [%"chk35" + 0] <- #0
    => goto "L113";
  @"L122":
    %"v148" = %"pr.1" +p #136;
    %"chk36" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"v148";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v150" = %"v149" +p #4;
    %"chk37" : A = (Check 0 4 Read 1) %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"v152" : W = (Cmp Eq W) %"v151", #0
    => br %"v152" ? "L144" : "L145";
  @"L144":
    %"v154" = %"pr.1" +p #136;
    %"v155" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v156" = %"v155" +p #8;
    %"chk39" : A = (Check 0 8 Write 8) %"v156";
    store.ptr [%"chk39" + 0] <- #0;
    %"chk40" : A = (Renew 0 8 Read 8) %"chk36", %"v154";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"chk41" : A = (Check 0 4 Read 1) %"v160";
    %"v164" : W = (RawLoad (LdNarrow Sw) 0) %"chk41"
    => goto "L165";
  @"L165" [%"v167" : W = phi("L144" => %"v164", "L165" => %"v168")]:
    %"chk42" : A = (HalfCheck Lower 0 4 Write 4) %"chk41", %"v160";
    %"v168" : W = (RawCas (CasNarrow Sw) 0) %"chk42", %"v167", #0;
    %"v169" : W = (Cmp Eq W) %"v168", %"v167"
    => br %"v169" ? "L166" : poll "L165";
  @"L166":
    %"v174" : W = (Cmp Sgt W) %"v167", #1
    => br %"v174" ? "L177" : "L113";
  @"L177":
    call void $"__GI___lll_lock_wake_private"(P %"v160")
    => goto "L113";
  @"L145":
    %"v189" = %"pr.1" +p #136;
    %"v190" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v191" = %"v190" +p #4;
    %"chk44" : A = (Check 0 4 Read 1) %"v191";
    %"v192" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"v193" : W = Sub %"v192", #1;
    %"chk45" : A = (Renew 0 4 Write 1) %"chk44", %"v191";
    store Ww [%"chk45" + 0] <- %"v193"
    => goto "L113";
  @"L113":
    => ret %"v110"
} }.

Definition hello_image_fn___vfprintf_internal : func :=
  ir_fn{ "export" "__vfprintf_internal"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v178" : P = (Alloc 8) #176;
    %"v187" : P = (Alloc 8) #32;
    %"v290" : P = (Alloc 8) #176;
    %"v30" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v30";
    %"v31" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v32" : W = (Cmp Eq W) %"v31", #0
    => br %"v32" ? "L26" : "L28";
  @"L26":
    %"v34" = %"v0" +p #192;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v34";
    store Ww [%"chk1" + 0] <- #4294967295
    => goto "L28";
  @"L28":
    %"v37" = %"v0" +p #192;
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v61" : W = (Cmp Ne W) %"v38", #4294967295
    => br %"v61" ? "L8" : "L71";
  @"L8":
    => ret #4294967295;
  @"L71":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v76" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v77" : W = And %"v76", #8
    => br %"v77" ? "L72" : "L74";
  @"L72":
    %"v79" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v80" : W = Or %"v79", #32;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk5" + 0] <- %"v80";
    %"v81" : P = Copy $"__libc_errno";
    %"chk6" : A = (Check 0 4 Write 1) %"v81";
    store Ww [%"chk6" + 0] <- #9
    => ret #4294967295;
  @"L74":
    %"v88" : L = Ptoi %"v2";
    %"v89" : L = Ptoi #0;
    %"v90" : W = (Cmp Eq L) %"v88", %"v89"
    => br %"v90" ? "L84" : "L107";
  @"L84":
    %"v91" : P = Copy $"__libc_errno";
    %"chk7" : A = (Check 0 4 Write 1) %"v91";
    store Ww [%"chk7" + 0] <- #22
    => ret #4294967295;
  @"L107":
    %"v121" = %"v0" +p #192;
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v123" : W = (Cmp Eq W) %"v122", #0
    => br %"v123" ? "L117" : "L119";
  @"L117":
    %"v125" = %"v0" +p #192;
    %"chk9" : A = (Renew 0 4 Write 1) %"chk0", %"v125";
    store Ww [%"chk9" + 0] <- #4294967295
    => goto "L119";
  @"L119":
    %"v128" = %"v0" +p #192;
    %"v129" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v162" : W = (Cmp Ne W) %"v129", #4294967295
    => br %"v162" ? "L94" : "L96";
  @"L94":
    => ret #4294967295;
  @"L96":
    %"v171" = %"v0" +p #116;
    %"v172" : W = (RawLoad (LdNarrow Sw) (-76)) %"chk0";
    %"v173" : W = Shl %"v172", #8;
    %"v174" : W = Sar %"v173", #8;
    %"v175" : W = And %"v174", #128;
    %"v177" : W = (Cmp Eq W) %"v175", #0
    => br %"v177" ? "L167" : "L169";
  @"L167":
    call void $"__printf_buffer_to_file_init"(P %"v178", P %"v0");
    call void $"__printf_buffer"(P %"v178", P %"v2", P %"v4", W %"v6");
    call %"v183" : W = $"__printf_buffer_to_file_done"(P %"v178")
    => ret %"v183";
  @"L169":
    %"v189" : P = Copy $"_IO_funlockfile";
    %"v190" = %"v187" +p #8;
    %"chk12" : A = (Check 0 8 Write 8) %"v190";
    store.ptr [%"chk12" + 0] <- %"v0";
    %"chk13" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v196" : W = (RawLoad (LdNarrow Sw) 0) %"chk13";
    %"v197" : W = And %"v196", #32768;
    %"v198" : W = (Cmp Eq W) %"v197", #0
    => br %"v198" ? "L192" : "L194";
  @"L192":
    %"chk14" : A = (HalfCheck Lower 0 8 Write 8) %"chk12", %"v187";
    store.ptr [%"chk14" + 0] <- %"v189";
    call void $"__GI___libc_cleanup_push_defer"(P %"v187")
    => goto "L194";
  @"L194" [%"pr.5" : W = phi("L192" => #1, "L169" => #0)]:
    %"chk15" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v206" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v207" : W = And %"v206", #32768;
    %"v208" : W = (Cmp Eq W) %"v207", #0
    => br %"v208" ? "L209" : "L204";
  @"L209":
    call %"v213" : P = $"zthread_self_cookie"();
    %"v217" : P = Copy $"__libc_single_threaded_internal";
    %"chk16" : A = (Check 0 1 Read 1) %"v217";
    %"v218" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v219" : W = (Cmp Ne W) %"v218", #0
    => br %"v219" ? "L220" : "L221";
  @"L220":
    %"v223" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v223";
    %"v224" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v225" = %"v224" +p #8;
    %"chk18" : A = (Check 0 8 Read 8) %"v225";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v227" : L = Ptoi %"v226";
    %"v229" : W = (Cmp Eq L) %"v227", %"v89"
    => goto "L221";
  @"L221" [%"v231" : W = phi("L209" => #0, "L220" => %"v229")]:
    => br %"v231" ? "L214" : "L215";
  @"L214":
    %"v233" = %"v0" +p #136;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v233";
    %"v234" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"chk20" : A = (Check 0 4 Write 1) %"v234";
    store Ww [%"chk20" + 0] <- #1;
    %"v237" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v238" = %"v237" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v238";
    store.ptr [%"chk22" + 0] <- %"v213"
    => goto "L204";
  @"L215":
    %"v244" = %"v0" +p #136;
    %"chk23" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v244";
    %"v245" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v246" = %"v245" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v246";
    %"v247" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v249" : L = Ptoi %"v247";
    %"v250" : L = Ptoi %"v213";
    %"v251" : W = (Cmp Ne L) %"v249", %"v250"
    => br %"v251" ? "L240" : "L241";
  @"L240":
    %"v254" = %"v0" +p #136;
    %"v255" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk26" : A = (Check 0 4 Write 4) %"v255";
    %"v262" : W = (RawCas (CasNarrow Sw) 0) %"chk26", #0, #1;
    %"v263" : W = (Cmp Eq W) %"v262", #0
    => br %"v263" ? "L265" : "L264";
  @"L264":
    => goto "L265";
  @"L265":
    %"v266" : W = (Cmp Ne W) %"v262", #0
    => br %"v266" ? "L269" : "L258";
  @"L269":
    call void $"__GI___lll_lock_wait_private"(P %"v255")
    => goto "L258";
  @"L258":
    %"v280" = %"v0" +p #136;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk23", %"v280";
    %"v281" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v282" = %"v281" +p #8;
    %"chk28" : A = (Check 0 8 Write 8) %"v282";
    store.ptr [%"chk28" + 0] <- %"v213"
    => goto "L204";
  @"L241":
    %"v285" = %"v0" +p #136;
    %"v286" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v287" = %"v286" +p #4;
    %"chk30" : A = (Check 0 4 Read 1) %"v287";
    %"v288" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v289" : W = Add %"v288", #1;
    %"chk31" : A = (Renew 0 4 Write 1) %"chk30", %"v287";
    store Ww [%"chk31" + 0] <- %"v289"
    => goto "L204";
  @"L204":
    call void $"__printf_buffer_to_file_init"(P %"v290", P %"v0");
    call void $"__printf_buffer"(P %"v290", P %"v2", P %"v4", W %"v6");
    call %"v295" : W = $"__printf_buffer_to_file_done"(P %"v290");
    %"chk32" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v300" : W = (RawLoad (LdNarrow Sw) 0) %"chk32";
    %"v301" : W = And %"v300", #32768;
    %"v302" : W = (Cmp Eq W) %"v301", #0
    => br %"v302" ? "L303" : "L298";
  @"L303":
    %"v309" : P = Copy $"__libc_single_threaded_internal";
    %"chk33" : A = (Check 0 1 Read 1) %"v309";
    %"v310" : W = (RawLoad (LdNarrow Sb) 0) %"chk33";
    %"v311" : W = (Cmp Ne W) %"v310", #0
    => br %"v311" ? "L312" : "L313";
  @"L312":
    %"v315" = %"v0" +p #136;
    %"chk34" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v315";
    %"v316" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v317" = %"v316" +p #4;
    %"chk35" : A = (Check 0 4 Read 1) %"v317";
    %"v318" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v319" : W = (Cmp Eq W) %"v318", #0
    => goto "L313";
  @"L313" [%"v321" : W = phi("L303" => #0, "L312" => %"v319")]:
    => br %"v321" ? "L306" : "L307";
  @"L306":
    %"v323" = %"v0" +p #136;
    %"chk36" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v323";
    %"v324" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v325" = %"v324" +p #8;
    %"chk37" : A = (Check 0 8 Write 8) %"v325";
    store.ptr [%"chk37" + 0] <- #0;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk36", %"v323";
    %"v328" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 4 Write 1) %"v328";
    store Ww [%"chk39" + 0] <- #0
    => goto "L298";
  @"L307":
    %"v333" = %"v0" +p #136;
    %"chk40" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v333";
    %"v334" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v335" = %"v334" +p #4;
    %"chk41" : A = (Check 0 4 Read 1) %"v335";
    %"v336" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"v337" : W = (Cmp Eq W) %"v336", #0
    => br %"v337" ? "L329" : "L330";
  @"L329":
    %"v339" = %"v0" +p #136;
    %"v340" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v341" = %"v340" +p #8;
    %"chk43" : A = (Check 0 8 Write 8) %"v341";
    store.ptr [%"chk43" + 0] <- #0;
    %"chk44" : A = (Renew 0 8 Read 8) %"chk40", %"v339";
    %"v345" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"chk45" : A = (Check 0 4 Read 1) %"v345";
    %"v349" : W = (RawLoad (LdNarrow Sw) 0) %"chk45"
    => goto "L350";
  @"L350" [%"v352" : W = phi("L329" => %"v349", "L350" => %"v353")]:
    %"chk46" : A = (HalfCheck Lower 0 4 Write 4) %"chk45", %"v345";
    %"v353" : W = (RawCas (CasNarrow Sw) 0) %"chk46", %"v352", #0;
    %"v354" : W = (Cmp Eq W) %"v353", %"v352"
    => br %"v354" ? "L351" : poll "L350";
  @"L351":
    %"v359" : W = (Cmp Sgt W) %"v352", #1
    => br %"v359" ? "L362" : "L298";
  @"L362":
    call void $"__GI___lll_lock_wake_private"(P %"v345")
    => goto "L298";
  @"L330":
    %"v374" = %"v0" +p #136;
    %"v375" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v376" = %"v375" +p #4;
    %"chk48" : A = (Check 0 4 Read 1) %"v376";
    %"v377" : W = (RawLoad (LdNarrow Sw) 0) %"chk48";
    %"v378" : W = Sub %"v377", #1;
    %"chk49" : A = (Renew 0 4 Write 1) %"chk48", %"v376";
    store Ww [%"chk49" + 0] <- %"v378"
    => goto "L298";
  @"L298":
    => br %"pr.5" ? "L379" : "L385";
  @"L379":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v187")
    => goto "L385";
  @"L385":
    => ret %"v295"
} }.

Definition hello_image_fn___vfwprintf_internal : func :=
  ir_fn{ "export" "__vfwprintf_internal"(P %"v0", P %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v169" : P = (Alloc 8) #560;
    %"v178" : P = (Alloc 8) #32;
    %"v281" : P = (Alloc 8) #560;
    call %"v53" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v55" : W = (Cmp Ne W) %"v53", #1
    => br %"v55" ? "L8" : "L63";
  @"L8":
    => ret #4294967295;
  @"L63":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v68" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v69" : W = And %"v68", #8
    => br %"v69" ? "L64" : "L66";
  @"L64":
    %"v71" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v72" : W = Or %"v71", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk2" + 0] <- %"v72";
    %"v73" : P = Copy $"__libc_errno";
    %"chk3" : A = (Check 0 4 Write 1) %"v73";
    store Ww [%"chk3" + 0] <- #9
    => ret #4294967295;
  @"L66":
    %"v80" : L = Ptoi %"v2";
    %"v81" : L = Ptoi #0;
    %"v82" : W = (Cmp Eq L) %"v80", %"v81"
    => br %"v82" ? "L76" : "L123";
  @"L76":
    %"v83" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v83";
    store Ww [%"chk4" + 0] <- #22
    => ret #4294967295;
  @"L123":
    call %"v146" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v154" : W = (Cmp Ne W) %"v146", #1
    => br %"v154" ? "L86" : "L88";
  @"L86":
    => ret #(-1);
  @"L88":
    %"v162" = %"v0" +p #116;
    %"chk5" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v162";
    %"v163" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v164" : W = Shl %"v163", #8;
    %"v165" : W = Sar %"v164", #8;
    %"v166" : W = And %"v165", #128;
    %"v168" : W = (Cmp Eq W) %"v166", #0
    => br %"v168" ? "L158" : "L160";
  @"L158":
    call void $"__wprintf_buffer_to_file_init"(P %"v169", P %"v0");
    call void $"__wprintf_buffer"(P %"v169", P %"v2", P %"v4", W %"v6");
    call %"v174" : W = $"__wprintf_buffer_to_file_done"(P %"v169")
    => ret %"v174";
  @"L160":
    %"v180" : P = Copy $"_IO_funlockfile";
    %"v181" = %"v178" +p #8;
    %"chk6" : A = (Check 0 8 Write 8) %"v181";
    store.ptr [%"chk6" + 0] <- %"v0";
    %"chk7" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v187" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v188" : W = And %"v187", #32768;
    %"v189" : W = (Cmp Eq W) %"v188", #0
    => br %"v189" ? "L183" : "L185";
  @"L183":
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk6", %"v178";
    store.ptr [%"chk8" + 0] <- %"v180";
    call void $"__GI___libc_cleanup_push_defer"(P %"v178")
    => goto "L185";
  @"L185" [%"pr.5" : W = phi("L183" => #1, "L160" => #0)]:
    %"chk9" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v197" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v198" : W = And %"v197", #32768;
    %"v199" : W = (Cmp Eq W) %"v198", #0
    => br %"v199" ? "L200" : "L195";
  @"L200":
    call %"v204" : P = $"zthread_self_cookie"();
    %"v208" : P = Copy $"__libc_single_threaded_internal";
    %"chk10" : A = (Check 0 1 Read 1) %"v208";
    %"v209" : W = (RawLoad (LdNarrow Sb) 0) %"chk10";
    %"v210" : W = (Cmp Ne W) %"v209", #0
    => br %"v210" ? "L211" : "L212";
  @"L211":
    %"v214" = %"v0" +p #136;
    %"chk11" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v216" = %"v215" +p #8;
    %"chk12" : A = (Check 0 8 Read 8) %"v216";
    %"v217" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v218" : L = Ptoi %"v217";
    %"v220" : W = (Cmp Eq L) %"v218", %"v81"
    => goto "L212";
  @"L212" [%"v222" : W = phi("L200" => #0, "L211" => %"v220")]:
    => br %"v222" ? "L205" : "L206";
  @"L205":
    %"v224" = %"v0" +p #136;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 4 Write 1) %"v225";
    store Ww [%"chk14" + 0] <- #1;
    %"v228" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v229" = %"v228" +p #8;
    %"chk16" : A = (Check 0 8 Write 8) %"v229";
    store.ptr [%"chk16" + 0] <- %"v204"
    => goto "L195";
  @"L206":
    %"v235" = %"v0" +p #136;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v235";
    %"v236" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v237" = %"v236" +p #8;
    %"chk18" : A = (Check 0 8 Read 8) %"v237";
    %"v238" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v240" : L = Ptoi %"v238";
    %"v241" : L = Ptoi %"v204";
    %"v242" : W = (Cmp Ne L) %"v240", %"v241"
    => br %"v242" ? "L231" : "L232";
  @"L231":
    %"v245" = %"v0" +p #136;
    %"v246" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk20" : A = (Check 0 4 Write 4) %"v246";
    %"v253" : W = (RawCas (CasNarrow Sw) 0) %"chk20", #0, #1;
    %"v254" : W = (Cmp Eq W) %"v253", #0
    => br %"v254" ? "L256" : "L255";
  @"L255":
    => goto "L256";
  @"L256":
    %"v257" : W = (Cmp Ne W) %"v253", #0
    => br %"v257" ? "L260" : "L249";
  @"L260":
    call void $"__GI___lll_lock_wait_private"(P %"v246")
    => goto "L249";
  @"L249":
    %"v271" = %"v0" +p #136;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk17", %"v271";
    %"v272" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v273" = %"v272" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v273";
    store.ptr [%"chk22" + 0] <- %"v204"
    => goto "L195";
  @"L232":
    %"v276" = %"v0" +p #136;
    %"v277" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v278" = %"v277" +p #4;
    %"chk24" : A = (Check 0 4 Read 1) %"v278";
    %"v279" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"v280" : W = Add %"v279", #1;
    %"chk25" : A = (Renew 0 4 Write 1) %"chk24", %"v278";
    store Ww [%"chk25" + 0] <- %"v280"
    => goto "L195";
  @"L195":
    call void $"__wprintf_buffer_to_file_init"(P %"v281", P %"v0");
    call void $"__wprintf_buffer"(P %"v281", P %"v2", P %"v4", W %"v6");
    call %"v286" : W = $"__wprintf_buffer_to_file_done"(P %"v281");
    %"chk26" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v291" : W = (RawLoad (LdNarrow Sw) 0) %"chk26";
    %"v292" : W = And %"v291", #32768;
    %"v293" : W = (Cmp Eq W) %"v292", #0
    => br %"v293" ? "L294" : "L289";
  @"L294":
    %"v300" : P = Copy $"__libc_single_threaded_internal";
    %"chk27" : A = (Check 0 1 Read 1) %"v300";
    %"v301" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v302" : W = (Cmp Ne W) %"v301", #0
    => br %"v302" ? "L303" : "L304";
  @"L303":
    %"v306" = %"v0" +p #136;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v306";
    %"v307" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v308" = %"v307" +p #4;
    %"chk29" : A = (Check 0 4 Read 1) %"v308";
    %"v309" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    %"v310" : W = (Cmp Eq W) %"v309", #0
    => goto "L304";
  @"L304" [%"v312" : W = phi("L294" => #0, "L303" => %"v310")]:
    => br %"v312" ? "L297" : "L298";
  @"L297":
    %"v314" = %"v0" +p #136;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v314";
    %"v315" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v316" = %"v315" +p #8;
    %"chk31" : A = (Check 0 8 Write 8) %"v316";
    store.ptr [%"chk31" + 0] <- #0;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk30", %"v314";
    %"v319" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Check 0 4 Write 1) %"v319";
    store Ww [%"chk33" + 0] <- #0
    => goto "L289";
  @"L298":
    %"v324" = %"v0" +p #136;
    %"chk34" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v324";
    %"v325" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v326" = %"v325" +p #4;
    %"chk35" : A = (Check 0 4 Read 1) %"v326";
    %"v327" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v328" : W = (Cmp Eq W) %"v327", #0
    => br %"v328" ? "L320" : "L321";
  @"L320":
    %"v330" = %"v0" +p #136;
    %"v331" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v332" = %"v331" +p #8;
    %"chk37" : A = (Check 0 8 Write 8) %"v332";
    store.ptr [%"chk37" + 0] <- #0;
    %"chk38" : A = (Renew 0 8 Read 8) %"chk34", %"v330";
    %"v336" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"chk39" : A = (Check 0 4 Read 1) %"v336";
    %"v340" : W = (RawLoad (LdNarrow Sw) 0) %"chk39"
    => goto "L341";
  @"L341" [%"v343" : W = phi("L320" => %"v340", "L341" => %"v344")]:
    %"chk40" : A = (HalfCheck Lower 0 4 Write 4) %"chk39", %"v336";
    %"v344" : W = (RawCas (CasNarrow Sw) 0) %"chk40", %"v343", #0;
    %"v345" : W = (Cmp Eq W) %"v344", %"v343"
    => br %"v345" ? "L342" : poll "L341";
  @"L342":
    %"v350" : W = (Cmp Sgt W) %"v343", #1
    => br %"v350" ? "L353" : "L289";
  @"L353":
    call void $"__GI___lll_lock_wake_private"(P %"v336")
    => goto "L289";
  @"L321":
    %"v365" = %"v0" +p #136;
    %"v366" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v367" = %"v366" +p #4;
    %"chk42" : A = (Check 0 4 Read 1) %"v367";
    %"v368" : W = (RawLoad (LdNarrow Sw) 0) %"chk42";
    %"v369" : W = Sub %"v368", #1;
    %"chk43" : A = (Renew 0 4 Write 1) %"chk42", %"v367";
    store Ww [%"chk43" + 0] <- %"v369"
    => goto "L289";
  @"L289":
    => br %"pr.5" ? "L370" : "L376";
  @"L370":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v178")
    => goto "L376";
  @"L376":
    => ret %"v286"
} }.
