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

Definition hello_image_fn__IO_new_file_underflow : func :=
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

Definition hello_image_fn__IO_file_underflow_mmap : func :=
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

Definition hello_image_fn__IO_file_underflow_maybe_mmap : func :=
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

Definition hello_image_fn__IO_new_file_overflow : func :=
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

Definition hello_image_fn__IO_new_file_sync : func :=
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

Definition hello_image_fn__IO_file_sync_mmap : func :=
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
