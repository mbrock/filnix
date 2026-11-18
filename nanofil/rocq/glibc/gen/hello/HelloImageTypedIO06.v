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

Definition hello_image_fn___GI__IO_default_pbackfail : func :=
  ir_fn{ "export" "__GI__IO_default_pbackfail"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #24;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ugt L) %"v13", %"v14"
    => br %"v15" ? "L16" : "L17";
  @"L16":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v20" : W = And %"v19", #256;
    %"v21" : W = (Cmp Eq W) %"v20", #0
    => goto "L17";
  @"L17" [%"v23" : W = phi("start" => #0, "L16" => %"v21")]:
    => br %"v23" ? "L24" : "L25";
  @"L24":
    %"v27" = %"v0" +p #8;
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v31" = %"v28" +p #18446744073709551615;
    %"chk4" : A = (Check 0 1 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"v33" : W = (Ext Ub) %"v32";
    %"v35" : W = (Cmp Eq W) %"v33", %"v2"
    => goto "L25";
  @"L25" [%"v37" : W = phi("L17" => #0, "L24" => %"v35")]:
    => br %"v37" ? "L4" : "L5";
  @"L4":
    %"v39" = %"v0" +p #8;
    %"v40" : P = (RawLoadPointer 0 load_effects) %"chk0";
    (Flight (a "v41") Sub [(FAddress (t "v40")); (FValue (Const 1))] (LowerOf (t "v40")));
    %"chk6" : A = (Renew 0 8 Write 8) %"chk0", %"v39";
    store.ptr [%"chk6" + 0] <- %"v41"
    => goto "L6";
  @"L5":
    %"chk7" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v46" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v47" : W = And %"v46", #256;
    %"v48" : W = (Cmp Eq W) %"v47", #0
    => br %"v48" ? "L42" : "L43";
  @"L42":
    %"v53" = %"v0" +p #8;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v56" = %"v0" +p #24;
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v58" : L = Ptoi %"v54";
    %"v59" : L = Ptoi %"v57";
    %"v60" : W = (Cmp Ugt L) %"v58", %"v59"
    => br %"v60" ? "L61" : "L62";
  @"L61":
    %"v64" = %"v0" +p #80;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v66" : L = Ptoi %"v65";
    %"v67" : L = Ptoi #0;
    %"v68" : W = (Cmp Ne L) %"v66", %"v67"
    => goto "L62";
  @"L62" [%"v70" : W = phi("L42" => #0, "L61" => %"v68")]:
    => br %"v70" ? "L49" : "L50";
  @"L49":
    %"v76" = %"v0" +p #8;
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v78" : W = $"glibc_genops#save_for_backup"(P %"v0", P %"v77")
    => br %"v78" ? "L71" : "L51";
  @"L71":
    => ret #4294967295;
  @"L50":
    %"v85" = %"v0" +p #80;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v85";
    %"v86" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v87" : L = Ptoi %"v86";
    %"v88" : L = Ptoi #0;
    %"v90" : W = (Cmp Eq L) %"v87", %"v88"
    => br %"v90" ? "L81" : "L51";
  @"L81":
    call %"v95" : P = $"malloc"(L #128);
    %"v100" : L = Ptoi %"v95";
    %"v102" : W = (Cmp Eq L) %"v100", %"v88"
    => br %"v102" ? "L96" : "L98";
  @"L96":
    %"v104" = %"v0" +p #119
    => goto "L98";
  @"L98" [%"pr.2" : P = phi("L96" => %"v104", "L81" => %"v95"); %"pr.1" : W = phi("L96" => #1, "L81" => #128)]:
    %"v106" = %"v0" +p #72;
    %"chk13" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v106";
    store.ptr [%"chk13" + 0] <- %"pr.2";
    %"v109" = %"v0" +p #88;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk13", %"v106";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v114" : L = (Ext Sw) %"pr.1";
    %"v115" = %"v112" +p %"v114";
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v109";
    store.ptr [%"chk15" + 0] <- %"v115";
    %"v117" = %"v0" +p #80;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk15", %"v109";
    %"v120" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Renew 0 8 Write 8) %"chk12", %"v117";
    store.ptr [%"chk17" + 0] <- %"v120"
    => goto "L51";
  @"L51":
    %"v122" = %"v0" +p #24;
    %"v124" = %"v0" +p #8;
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v124";
    %"v125" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Renew 0 8 Write 8) %"chk1", %"v122";
    store.ptr [%"chk19" + 0] <- %"v125";
    call void $"_IO_switch_to_backup_area"(P %"v0")
    => goto "L44";
  @"L43":
    %"v131" = %"v0" +p #8;
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v134" = %"v0" +p #24;
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v136" : L = Ptoi %"v132";
    %"v137" : L = Ptoi %"v135";
    %"v138" : W = (Cmp Ule L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L44";
  @"L127":
    %"v142" = %"v0" +p #16;
    %"v143" : P = (RawLoadPointer (-8) load_effects) %"chk1";
    %"v145" = %"v0" +p #24;
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v147" : L = Ptoi %"v143";
    %"v148" : L = Ptoi %"v146";
    %"v149" : L = Sub %"v147", %"v148";
    %"v152" : L = Shl %"v149", #1;
    call %"v154" : P = $"malloc"(L %"v152");
    %"v159" : L = Ptoi %"v154";
    %"v160" : L = Ptoi #0;
    %"v161" : W = (Cmp Eq L) %"v159", %"v160"
    => br %"v161" ? "L155" : "L157";
  @"L155":
    => ret #4294967295;
  @"L157":
    %"v167" : L = Sub %"v152", %"v149";
    %"v168" = %"v154" +p %"v167";
    %"v170" = %"v0" +p #24;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk24";
    call %"v173" : P = $"__GI_memcpy"(P %"v168", P %"v171", L %"v149");
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v170";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_1.v9" = %"v0" +p #119;
    %"iw_1.v10" : L = Ptoi %"v177";
    %"iw_1.v11" : L = Ptoi %"iw_1.v9";
    %"iw_1.v12" : W = (Cmp Ne L) %"iw_1.v10", %"iw_1.v11"
    => br %"iw_1.v12" ? "iw_1.L4" : "iw_1.join";
  @"iw_1.L4":
    call void $"free"(P %"v177")
    => goto "iw_1.join";
  @"iw_1.join":
    %"v179" = %"v0" +p #24;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v179";
    store.ptr [%"chk26" + 0] <- %"v154";
    %"v182" = %"v0" +p #8;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk0", %"v182";
    store.ptr [%"chk27" + 0] <- %"v168";
    %"v189" = %"v0" +p #16;
    %"v192" = %"v154" +p %"v152";
    %"chk28" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v189";
    store.ptr [%"chk28" + 0] <- %"v192";
    %"v194" = %"v0" +p #80;
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v182";
    %"v197" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v194";
    store.ptr [%"chk30" + 0] <- %"v197"
    => goto "L44";
  @"L44":
    %"v199" = %"v0" +p #8;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk0", %"v199";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk31";
    (Flight (a "v201") Sub [(FAddress (t "v200")); (FValue (Const 1))] (LowerOf (t "v200")));
    %"chk32" : A = (Renew 0 8 Write 8) %"chk0", %"v199";
    store.ptr [%"chk32" + 0] <- %"v201";
    %"v203" : W = (Ext Sb) %"v2";
    %"chk33" : A = (Check 0 1 Write 1) %"v201";
    store Wb [%"chk33" + 0] <- %"v203"
    => goto "L6";
  @"L6":
    %"v205" : W = (Ext Ub) %"v2"
    => ret %"v205"
} }.

Definition hello_image_fn__IO_default_seek : func :=
  ir_fn{ "export" "_IO_default_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    => ret #18446744073709551615
} }.

Definition hello_image_fn__IO_default_stat : func :=
  ir_fn{ "export" "_IO_default_stat"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    => ret #4294967295
} }.

Definition hello_image_fn__IO_default_read : func :=
  ir_fn{ "export" "_IO_default_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => ret #18446744073709551615
} }.

Definition hello_image_fn__IO_default_write : func :=
  ir_fn{ "export" "_IO_default_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => ret #0
} }.

Definition hello_image_fn__IO_default_showmanyc : func :=
  ir_fn{ "export" "_IO_default_showmanyc"(P %"v0") -> (RClass W) {
  @"start":
    => ret #4294967295
} }.

Definition hello_image_fn__IO_default_imbue : func :=
  ir_fn{ "export" "_IO_default_imbue"(P %"v0", P %"v2") -> RVoid {
  @"start":
    => ret void
} }.

Definition hello_image_fn__IO_new_fclose : func :=
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

Definition hello_image_fn___GI__IO_fflush : func :=
  ir_fn{ "export" "__GI__IO_fflush"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" : L = Ptoi %"v0";
    %"v7" : L = Ptoi #0;
    %"v8" : W = (Cmp Eq L) %"v6", %"v7"
    => br %"v8" ? "L2" : "L15";
  @"L2":
    call %"v9" : W = $"__GI__IO_flush_all"()
    => ret %"v9";
  @"L15":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v25" : W = And %"v24", #32768;
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => br %"v26" ? "L27" : "L22";
  @"L27":
    call %"v31" : P = $"zthread_self_cookie"();
    %"v35" : P = Copy $"__libc_single_threaded_internal";
    %"chk1" : A = (Check 0 1 Read 1) %"v35";
    %"v36" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v37" : W = (Cmp Ne W) %"v36", #0
    => br %"v37" ? "L38" : "L39";
  @"L38":
    %"v41" = %"v0" +p #136;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v43" = %"v42" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v45" : L = Ptoi %"v44";
    %"v47" : W = (Cmp Eq L) %"v45", %"v7"
    => goto "L39";
  @"L39" [%"v49" : W = phi("L27" => #0, "L38" => %"v47")]:
    => br %"v49" ? "L32" : "L33";
  @"L32":
    %"v51" = %"v0" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v52";
    store Ww [%"chk5" + 0] <- #1;
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v56" = %"v55" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v56";
    store.ptr [%"chk7" + 0] <- %"v31"
    => goto "L22";
  @"L33":
    %"v62" = %"v0" +p #136;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v62";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v64" = %"v63" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v67" : L = Ptoi %"v65";
    %"v68" : L = Ptoi %"v31";
    %"v69" : W = (Cmp Ne L) %"v67", %"v68"
    => br %"v69" ? "L58" : "L59";
  @"L58":
    %"v72" = %"v0" +p #136;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 4 Write 4) %"v73";
    %"v80" : W = (RawCas (CasNarrow Sw) 0) %"chk11", #0, #1;
    %"v81" : W = (Cmp Eq W) %"v80", #0
    => br %"v81" ? "L83" : "L82";
  @"L82":
    => goto "L83";
  @"L83":
    %"v84" : W = (Cmp Ne W) %"v80", #0
    => br %"v84" ? "L87" : "L76";
  @"L87":
    call void $"__GI___lll_lock_wait_private"(P %"v73")
    => goto "L76";
  @"L76":
    %"v98" = %"v0" +p #136;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk8", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v100" = %"v99" +p #8;
    %"chk13" : A = (Check 0 8 Write 8) %"v100";
    store.ptr [%"chk13" + 0] <- %"v31"
    => goto "L22";
  @"L59":
    %"v103" = %"v0" +p #136;
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v105" = %"v104" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v105";
    %"v106" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v107" : W = Add %"v106", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v105";
    store Ww [%"chk16" + 0] <- %"v107"
    => goto "L22";
  @"L22":
    %"v112" = %"v0" +p #216;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_1.v4" : L = Ptoi %"v113";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v115" = %"v113" +p #96;
    %"chk18" : A = (Check 0 8 Read 8) %"v115";
    %"v116" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : F = CheckFunction %"v116";
    rawcall %"v118" : W = %"chk19"(P %"v0")
    => br %"v118" ? "L110" : "L109";
  @"L109":
    => goto "L110";
  @"L110" [%"v120" : W = phi("L109" => #0, "iw_1.join" => #4294967295)]:
    %"chk20" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"iw_2.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"iw_2.v10" : W = And %"iw_2.v9", #32768;
    %"iw_2.v11" : W = (Cmp Eq W) %"iw_2.v10", #0
    => br %"iw_2.v11" ? "iw_2.L5" : "L17";
  @"iw_2.L5":
    %"iw_2.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk20";
    %"iw_2.v17" : W = And %"iw_2.v16", #32768;
    %"iw_2.v18" : W = (Cmp Eq W) %"iw_2.v17", #0
    => br %"iw_2.v18" ? "iw_2.L19" : "L17";
  @"iw_2.L19":
    %"iw_2.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk22" : A = (Check 0 1 Read 1) %"iw_2.v25";
    %"iw_2.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk22";
    %"iw_2.v27" : W = (Cmp Ne W) %"iw_2.v26", #0
    => br %"iw_2.v27" ? "iw_2.L28" : "iw_2.L29";
  @"iw_2.L28":
    %"iw_2.v31" = %"v0" +p #136;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v31";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"iw_2.v33" = %"iw_2.v32" +p #4;
    %"chk24" : A = (Check 0 4 Read 1) %"iw_2.v33";
    %"iw_2.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"iw_2.v35" : W = (Cmp Eq W) %"iw_2.v34", #0
    => goto "iw_2.L29";
  @"iw_2.L29" [%"iw_2.v37" : W = phi("iw_2.L19" => #0, "iw_2.L28" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L22" : "iw_2.L23";
  @"iw_2.L22":
    %"iw_2.v39" = %"v0" +p #136;
    %"chk25" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v39";
    %"iw_2.v40" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_2.v41" = %"iw_2.v40" +p #8;
    %"chk26" : A = (Check 0 8 Write 8) %"iw_2.v41";
    store.ptr [%"chk26" + 0] <- #0;
    %"chk27" : A = (Renew 0 8 Read 8) %"chk25", %"iw_2.v39";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : A = (Check 0 4 Write 1) %"iw_2.v44";
    store Ww [%"chk28" + 0] <- #0
    => goto "L17";
  @"iw_2.L23":
    %"iw_2.v49" = %"v0" +p #136;
    %"chk29" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v49";
    %"iw_2.v50" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v51" = %"iw_2.v50" +p #4;
    %"chk30" : A = (Check 0 4 Read 1) %"iw_2.v51";
    %"iw_2.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"iw_2.v53" : W = (Cmp Eq W) %"iw_2.v52", #0
    => br %"iw_2.v53" ? "iw_2.L45" : "iw_2.L46";
  @"iw_2.L45":
    %"iw_2.v55" = %"v0" +p #136;
    %"iw_2.v56" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v57" = %"iw_2.v56" +p #8;
    %"chk32" : A = (Check 0 8 Write 8) %"iw_2.v57";
    store.ptr [%"chk32" + 0] <- #0;
    %"chk33" : A = (Renew 0 8 Read 8) %"chk29", %"iw_2.v55";
    %"iw_2.v61" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Check 0 4 Read 1) %"iw_2.v61";
    %"iw_2.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk34"
    => goto "iw_2.L66";
  @"iw_2.L66" [%"iw_2.v68" : W = phi("iw_2.L45" => %"iw_2.v65", "iw_2.L66" => %"iw_2.v69")]:
    %"chk35" : A = (HalfCheck Lower 0 4 Write 4) %"chk34", %"iw_2.v61";
    %"iw_2.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk35", %"iw_2.v68", #0;
    %"iw_2.v70" : W = (Cmp Eq W) %"iw_2.v69", %"iw_2.v68"
    => br %"iw_2.v70" ? "iw_2.L67" : poll "iw_2.L66";
  @"iw_2.L67":
    %"iw_2.v75" : W = (Cmp Sgt W) %"iw_2.v68", #1
    => br %"iw_2.v75" ? "iw_2.L78" : "L17";
  @"iw_2.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_2.v61")
    => goto "L17";
  @"iw_2.L46":
    %"iw_2.v90" = %"v0" +p #136;
    %"iw_2.v91" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"iw_2.v92" = %"iw_2.v91" +p #4;
    %"chk37" : A = (Check 0 4 Read 1) %"iw_2.v92";
    %"iw_2.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"iw_2.v94" : W = Sub %"iw_2.v93", #1;
    %"chk38" : A = (Renew 0 4 Write 1) %"chk37", %"iw_2.v92";
    store Ww [%"chk38" + 0] <- %"iw_2.v94"
    => goto "L17";
  @"L17":
    => ret %"v120"
} }.

Definition hello_image_fn__IO_new_fopen : func :=
  ir_fn{ "export" "_IO_new_fopen"(P %"v0", P %"v2") -> (RClass P) {
  @"start":
    call %"v6" : P = $"__fopen_internal"(P %"v0", P %"v2", W #1)
    => ret %"v6"
} }.

Definition hello_image_fn__IO_cookie_read : func :=
  ir_fn{ "export" "_IO_cookie_read"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #232;
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v17" : L = Ptoi %"v11";
    %"v18" : L = Ptoi #0;
    %"v19" : W = (Cmp Eq L) %"v17", %"v18"
    => br %"v19" ? "L13" : "L15";
  @"L13":
    => ret #18446744073709551615;
  @"L15":
    %"v25" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v11";
    rawcall %"v29" : L = %"chk2"(P %"v26", P %"v2", L %"v4")
    => ret %"v29"
} }.

Definition hello_image_fn__IO_cookie_write : func :=
  ir_fn{ "export" "_IO_cookie_write"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v10" = %"v0" +p #232;
    %"v11" = %"v10" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" : L = Ptoi %"v12";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L14" : "L16";
  @"L14":
    %"chk1" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v23" : W = Or %"v22", #32;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk1", %"v0";
    store Ww [%"chk2" + 0] <- %"v23"
    => ret #0;
  @"L16":
    %"v28" = %"v0" +p #224;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v12";
    rawcall %"v32" : L = %"chk4"(P %"v29", P %"v2", L %"v4");
    %"v38" : W = (Cmp Slt L) %"v32", %"v4"
    => br %"v38" ? "L33" : "L35";
  @"L33":
    %"chk5" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"v41" : W = Or %"v40", #32;
    %"chk6" : A = (Renew 0 4 Write 1) %"chk5", %"v0";
    store Ww [%"chk6" + 0] <- %"v41"
    => goto "L35";
  @"L35":
    => ret %"v32"
} }.

Definition hello_image_fn__IO_cookie_seek : func :=
  ir_fn{ "export" "_IO_cookie_seek"(P %"v0", L %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v3" : P = (Alloc 8) #8;
    %"chk0" : A = (Check 0 8 Write 1) %"v3";
    store Wl [%"chk0" + 0] <- %"v2";
    %"v10" = %"v0" +p #232;
    %"v11" = %"v10" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" : L = Ptoi %"v12";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Eq L) %"v18", %"v19"
    => br %"v20" ? "L22" : "L21";
  @"L21":
    %"v25" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v12";
    rawcall %"v28" : W = %"chk3"(P %"v26", P %"v3", W %"v4");
    %"v30" : W = (Cmp Eq W) %"v28", #4294967295
    => goto "L22";
  @"L22" [%"v32" : W = phi("start" => #1, "L21" => %"v30")]:
    => br %"v32" ? "L34" : "L33";
  @"L33":
    %"chk4" : A = (Renew 0 8 Read 1) %"chk0", %"v3";
    %"v35" : L = (RawLoad LdL 0) %"chk4";
    %"v38" : W = (Cmp Eq L) %"v35", #18446744073709551615
    => goto "L34";
  @"L34" [%"v40" : W = phi("L22" => #1, "L33" => %"v38")]:
    => br %"v40" ? "L16" : "L15";
  @"L15":
    %"chk5" : A = (Renew 0 8 Read 1) %"chk0", %"v3";
    %"v43" : L = (RawLoad LdL 0) %"chk5"
    => goto "L16";
  @"L16" [%"v44" : L = phi("L15" => %"v43", "L34" => #18446744073709551615)]:
    => ret %"v44"
} }.

Definition hello_image_fn__IO_cookie_close : func :=
  ir_fn{ "export" "_IO_cookie_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #232;
    %"v7" = %"v6" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" : L = Ptoi %"v8";
    %"v15" : L = Ptoi #0;
    %"v16" : W = (Cmp Eq L) %"v14", %"v15"
    => br %"v16" ? "L10" : "L12";
  @"L10":
    => ret #0;
  @"L12":
    %"v20" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : F = CheckFunction %"v8";
    rawcall %"v22" : W = %"chk2"(P %"v21")
    => ret %"v22"
} }.

Definition hello_image_fn__IO_cookie_seekoff : func :=
  ir_fn{ "export" "_IO_cookie_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6") -> (RClass L) {
  @"start":
    %"v9" = %"v0" +p #144;
    %"chk0" : A = (Check 0 8 Write 1) %"v9";
    store Wl [%"chk0" + 0] <- #18446744073709551615;
    call %"v16" : L = $"__GI__IO_file_seekoff"(P %"v0", L %"v2", W %"v4", W %"v6")
    => ret %"v16"
} }.

Definition hello_image_fn___GI__IO_fputs : func :=
  ir_fn{ "export" "__GI__IO_fputs"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v6" : L = $"__GI_strlen"(P %"v0");
    %"chk0" : A = (Check 0 4 Read 1) %"v2";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v22" : W = And %"v21", #32768;
    %"v23" : W = (Cmp Eq W) %"v22", #0
    => br %"v23" ? "L24" : "L113";
  @"L24":
    call %"v28" : P = $"zthread_self_cookie"();
    %"v32" : P = Copy $"__libc_single_threaded_internal";
    %"chk1" : A = (Check 0 1 Read 1) %"v32";
    %"v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v34" : W = (Cmp Ne W) %"v33", #0
    => br %"v34" ? "L35" : "L36";
  @"L35":
    %"v38" = %"v2" +p #136;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v40" = %"v39" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v42" : L = Ptoi %"v41";
    %"v43" : L = Ptoi #0;
    %"v44" : W = (Cmp Eq L) %"v42", %"v43"
    => goto "L36";
  @"L36" [%"v46" : W = phi("L24" => #0, "L35" => %"v44")]:
    => br %"v46" ? "L29" : "L30";
  @"L29":
    %"v48" = %"v2" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 4 Write 1) %"v49";
    store Ww [%"chk5" + 0] <- #1;
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v53" = %"v52" +p #8;
    %"chk7" : A = (Check 0 8 Write 8) %"v53";
    store.ptr [%"chk7" + 0] <- %"v28"
    => goto "L113";
  @"L30":
    %"v59" = %"v2" +p #136;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v61" = %"v60" +p #8;
    %"chk9" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Ptoi %"v28";
    %"v66" : W = (Cmp Ne L) %"v64", %"v65"
    => br %"v66" ? "L55" : "L56";
  @"L55":
    %"v69" = %"v2" +p #136;
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk11" : A = (Check 0 4 Write 4) %"v70";
    %"v77" : W = (RawCas (CasNarrow Sw) 0) %"chk11", #0, #1;
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
    %"v95" = %"v2" +p #136;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk8", %"v95";
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v97" = %"v96" +p #8;
    %"chk13" : A = (Check 0 8 Write 8) %"v97";
    store.ptr [%"chk13" + 0] <- %"v28"
    => goto "L113";
  @"L56":
    %"v100" = %"v2" +p #136;
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v102" = %"v101" +p #4;
    %"chk15" : A = (Check 0 4 Read 1) %"v102";
    %"v103" : W = (RawLoad (LdNarrow Sw) 0) %"chk15";
    %"v104" : W = Add %"v103", #1;
    %"chk16" : A = (Renew 0 4 Write 1) %"chk15", %"v102";
    store Ww [%"chk16" + 0] <- %"v104"
    => goto "L113";
  @"L113":
    %"v127" = %"v2" +p #192;
    %"chk17" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v127";
    %"v128" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v129" : W = (Cmp Eq W) %"v128", #0
    => br %"v129" ? "L123" : "L125";
  @"L123":
    %"v131" = %"v2" +p #192;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v131";
    store Ww [%"chk18" + 0] <- #4294967295
    => goto "L125";
  @"L125":
    %"v134" = %"v2" +p #192;
    %"v135" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v158" : W = (Cmp Eq W) %"v135", #4294967295
    => br %"v158" ? "L161" : "L162";
  @"L161":
    %"v164" = %"v2" +p #216;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_1.v4" : L = Ptoi %"v165";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v167" = %"v165" +p #56;
    %"chk21" : A = (Check 0 8 Read 8) %"v167";
    %"v168" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : F = CheckFunction %"v168";
    rawcall %"v172" : L = %"chk22"(P %"v2", P %"v0", L %"v6");
    %"v174" : W = (Cmp Eq L) %"v172", %"v6"
    => goto "L162";
  @"L162" [%"v176" : W = phi("L125" => #0, "iw_1.join" => %"v174")]:
    => br %"v176" ? "L107" : "L106";
  @"L106":
    => goto "L107";
  @"L107" [%"pr.1" : W = phi("L106" => #4294967295, "L162" => #1)]:
    %"chk23" : A = (Renew 0 4 Read 1) %"chk0", %"v2";
    %"iw_2.v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"iw_2.v10" : W = And %"iw_2.v9", #32768;
    %"iw_2.v11" : W = (Cmp Eq W) %"iw_2.v10", #0
    => br %"iw_2.v11" ? "iw_2.L5" : "L14";
  @"iw_2.L5":
    %"iw_2.v16" : W = (RawLoad (LdNarrow Sw) 0) %"chk23";
    %"iw_2.v17" : W = And %"iw_2.v16", #32768;
    %"iw_2.v18" : W = (Cmp Eq W) %"iw_2.v17", #0
    => br %"iw_2.v18" ? "iw_2.L19" : "L14";
  @"iw_2.L19":
    %"iw_2.v25" : P = Copy $"__libc_single_threaded_internal";
    %"chk25" : A = (Check 0 1 Read 1) %"iw_2.v25";
    %"iw_2.v26" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"iw_2.v27" : W = (Cmp Ne W) %"iw_2.v26", #0
    => br %"iw_2.v27" ? "iw_2.L28" : "iw_2.L29";
  @"iw_2.L28":
    %"iw_2.v31" = %"v2" +p #136;
    %"chk26" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v31";
    %"iw_2.v32" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"iw_2.v33" = %"iw_2.v32" +p #4;
    %"chk27" : A = (Check 0 4 Read 1) %"iw_2.v33";
    %"iw_2.v34" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    %"iw_2.v35" : W = (Cmp Eq W) %"iw_2.v34", #0
    => goto "iw_2.L29";
  @"iw_2.L29" [%"iw_2.v37" : W = phi("iw_2.L19" => #0, "iw_2.L28" => %"iw_2.v35")]:
    => br %"iw_2.v37" ? "iw_2.L22" : "iw_2.L23";
  @"iw_2.L22":
    %"iw_2.v39" = %"v2" +p #136;
    %"chk28" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v39";
    %"iw_2.v40" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_2.v41" = %"iw_2.v40" +p #8;
    %"chk29" : A = (Check 0 8 Write 8) %"iw_2.v41";
    store.ptr [%"chk29" + 0] <- #0;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk28", %"iw_2.v39";
    %"iw_2.v44" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"chk31" : A = (Check 0 4 Write 1) %"iw_2.v44";
    store Ww [%"chk31" + 0] <- #0
    => goto "L14";
  @"iw_2.L23":
    %"iw_2.v49" = %"v2" +p #136;
    %"chk32" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_2.v49";
    %"iw_2.v50" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_2.v51" = %"iw_2.v50" +p #4;
    %"chk33" : A = (Check 0 4 Read 1) %"iw_2.v51";
    %"iw_2.v52" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"iw_2.v53" : W = (Cmp Eq W) %"iw_2.v52", #0
    => br %"iw_2.v53" ? "iw_2.L45" : "iw_2.L46";
  @"iw_2.L45":
    %"iw_2.v55" = %"v2" +p #136;
    %"iw_2.v56" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_2.v57" = %"iw_2.v56" +p #8;
    %"chk35" : A = (Check 0 8 Write 8) %"iw_2.v57";
    store.ptr [%"chk35" + 0] <- #0;
    %"chk36" : A = (Renew 0 8 Read 8) %"chk32", %"iw_2.v55";
    %"iw_2.v61" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"chk37" : A = (Check 0 4 Read 1) %"iw_2.v61";
    %"iw_2.v65" : W = (RawLoad (LdNarrow Sw) 0) %"chk37"
    => goto "iw_2.L66";
  @"iw_2.L66" [%"iw_2.v68" : W = phi("iw_2.L45" => %"iw_2.v65", "iw_2.L66" => %"iw_2.v69")]:
    %"chk38" : A = (HalfCheck Lower 0 4 Write 4) %"chk37", %"iw_2.v61";
    %"iw_2.v69" : W = (RawCas (CasNarrow Sw) 0) %"chk38", %"iw_2.v68", #0;
    %"iw_2.v70" : W = (Cmp Eq W) %"iw_2.v69", %"iw_2.v68"
    => br %"iw_2.v70" ? "iw_2.L67" : poll "iw_2.L66";
  @"iw_2.L67":
    %"iw_2.v75" : W = (Cmp Sgt W) %"iw_2.v68", #1
    => br %"iw_2.v75" ? "iw_2.L78" : "L14";
  @"iw_2.L78":
    call void $"__GI___lll_lock_wake_private"(P %"iw_2.v61")
    => goto "L14";
  @"iw_2.L46":
    %"iw_2.v90" = %"v2" +p #136;
    %"iw_2.v91" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"iw_2.v92" = %"iw_2.v91" +p #4;
    %"chk40" : A = (Check 0 4 Read 1) %"iw_2.v92";
    %"iw_2.v93" : W = (RawLoad (LdNarrow Sw) 0) %"chk40";
    %"iw_2.v94" : W = Sub %"iw_2.v93", #1;
    %"chk41" : A = (Renew 0 4 Write 1) %"chk40", %"iw_2.v92";
    store Ww [%"chk41" + 0] <- %"iw_2.v94"
    => goto "L14";
  @"L14":
    => ret %"pr.1"
} }.

Definition hello_image_fn__IO_fwide : func :=
  ir_fn{ "export" "_IO_fwide"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v73" : P = (Alloc 8) #32;
    %"v8" : W = (Cmp Slt W) %"v2", #0
    => br %"v8" ? "L6" : "L5";
  @"L5":
    %"v14" : W = (Cmp Eq W) %"v2", #0
    => br %"v14" ? "L6" : "L11";
  @"L11":
    => goto "L6";
  @"L6" [%"v16" : W = phi("start" => #4294967295, "L11" => #1, "L5" => #0)]:
    %"v21" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v23" : W = (Cmp Ne W) %"v22", #0
    => br %"v23" ? "L25" : "L24";
  @"L24":
    %"v27" : W = (Cmp Eq W) %"v16", #0
    => goto "L25";
  @"L25" [%"v29" : W = phi("L6" => #1, "L24" => %"v27")]:
    => br %"v29" ? "L17" : "L19";
  @"L17":
    %"v31" = %"v0" +p #192;
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v32";
  @"L19":
    %"v38" : W = (Cmp Sgt W) %"v16", #0
    => br %"v38" ? "L34" : "L36";
  @"L34":
    %"v41" = %"v0" +p #152;
    %"v43" = %"v0" +p #160;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v45" = %"v44" +p #104;
    %"chk3" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v41";
    store.ptr [%"chk3" + 0] <- %"v45";
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v52" = %"v51" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v48";
    store.ptr [%"chk7" + 0] <- %"v53";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v57" = %"v56" +p #32;
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v61" = %"v60" +p #24;
    %"chk10" : A = (Check 0 8 Read 8) %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 8 Write 8) %"v57";
    store.ptr [%"chk11" + 0] <- %"v62";
    %"chk12" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v66" = %"v65" +p #88;
    call %"v67" : P = $"__GI_memset"(P %"v66", W #0, L #8);
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"v43";
    %"v70" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v71" = %"v70" +p #96;
    call %"v72" : P = $"__GI_memset"(P %"v71", W #0, L #8);
    call void $"__wcsmbs_clone_conv"(P %"v73");
    %"v77" = %"v73" +p #8;
    %"chk14" : A = (Check 0 8 Read 1) %"v77";
    %"v78" : L = (RawLoad LdL 0) %"chk14";
    %"v79" : W = (Cmp Eq L) %"v78", #1
    => br %"v79" ? "L76" : "L75";
  @"L75":
    %"v80" : P = Copy $"glibc_iofwide#str.288";
    %"v81" : P = Copy $"glibc_iofwide#str.289";
    %"v82" : P = Copy $"glibc_iofwide#str.290";
    call void $"__libc_assert_fail"(P %"v80", P %"v81", W #80, P %"v82")
    => goto "L76";
  @"L76":
    %"v86" = %"v73" +p #24;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 1) %"chk14", %"v86";
    %"v87" : L = (RawLoad LdL 0) %"chk15";
    %"v88" : W = (Cmp Eq L) %"v87", #1
    => br %"v88" ? "L85" : "L84";
  @"L84":
    %"v89" : P = Copy $"glibc_iofwide#str.291";
    %"v90" : P = Copy $"glibc_iofwide#str.289";
    %"v91" : P = Copy $"glibc_iofwide#str.290";
    call void $"__libc_assert_fail"(P %"v89", P %"v90", W #81, P %"v91")
    => goto "L85";
  @"L85":
    %"chk16" : A = (HalfCheck Lower 0 8 Read 8) %"chk14", %"v73";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Write 8) %"v45";
    store.ptr [%"chk17" + 0] <- %"v93";
    %"v95" = %"v45" +p #8;
    %"v96" = %"v95" +p #20;
    %"chk18" : A = (HalfCheck Upper 0 4 Write 1) %"chk17", %"v96";
    store Ww [%"chk18" + 0] <- #0;
    %"v99" = %"v95" +p #24;
    %"chk19" : A = (HalfCheck Upper 0 4 Write 1) %"chk18", %"v99";
    store Ww [%"chk19" + 0] <- #1;
    %"v102" = %"v95" +p #16;
    %"chk20" : A = (HalfCheck Lower 0 4 Write 1) %"chk18", %"v102";
    store Ww [%"chk20" + 0] <- #1;
    %"v105" = %"v95" +p #32;
    %"v107" = %"v0" +p #160;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v109" = %"v108" +p #88;
    %"chk22" : A = (HalfCheck Upper 0 8 Write 8) %"chk18", %"v105";
    store.ptr [%"chk22" + 0] <- %"v109";
    %"v111" = %"v45" +p #56;
    %"v112" = %"v73" +p #16;
    %"chk23" : A = (HalfCheck Upper 0 8 Read 8) %"chk14", %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (HalfCheck Upper 0 8 Write 8) %"chk17", %"v111";
    store.ptr [%"chk24" + 0] <- %"v113";
    %"v116" = %"v111" +p #8;
    %"v117" = %"v116" +p #20;
    %"chk25" : A = (HalfCheck Upper 0 4 Write 1) %"chk24", %"v117";
    store Ww [%"chk25" + 0] <- #0;
    %"v121" = %"v116" +p #24;
    %"chk26" : A = (HalfCheck Upper 0 4 Write 1) %"chk25", %"v121";
    store Ww [%"chk26" + 0] <- #1;
    %"v125" = %"v116" +p #16;
    %"chk27" : A = (HalfCheck Lower 0 4 Write 1) %"chk25", %"v125";
    store Ww [%"chk27" + 0] <- #9;
    %"v130" = %"v116" +p #32;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v133" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v134" = %"v133" +p #88;
    %"chk29" : A = (HalfCheck Upper 0 8 Write 8) %"chk25", %"v130";
    store.ptr [%"chk29" + 0] <- %"v134";
    %"v136" = %"v0" +p #216;
    %"chk30" : A = (Renew 0 8 Read 8) %"chk2", %"v107";
    %"v139" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v140" = %"v139" +p #224;
    %"chk31" : A = (Check 0 8 Read 8) %"v140";
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"chk32" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v136";
    store.ptr [%"chk32" + 0] <- %"v141"
    => goto "L36";
  @"L36":
    %"v143" = %"v0" +p #192;
    %"chk33" : A = (Renew 0 4 Write 1) %"chk0", %"v143";
    store Ww [%"chk33" + 0] <- %"v16"
    => ret %"v16"
} }.

Definition hello_image_fn___GI__IO_getline : func :=
  ir_fn{ "export" "__GI__IO_getline"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8") -> (RClass L) {
  @"start":
    call %"v15" : L = $"__GI__IO_getline_info"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8", P #0)
    => ret %"v15"
} }.

Definition hello_image_fn___GI__IO_getline_info : func :=
  ir_fn{ "export" "__GI__IO_getline_info"(P %"v0", P %"v2", L %"v4", W %"v6", W %"v8", P %"v10") -> (RClass L) {
  @"start":
    %"v18" : L = Ptoi %"v10";
    %"v19" : L = Ptoi #0;
    %"v20" : W = (Cmp Ne L) %"v18", %"v19"
    => br %"v20" ? "L14" : "L16";
  @"L14":
    %"chk0" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk0" + 0] <- #0
    => goto "L16";
  @"L16":
    %"v26" = %"v0" +p #192;
    %"chk1" : A = (Check 0 4 Read 1) %"v26";
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v29" : L = (Ext Sw) %"v27";
    %"v30" : W = (Cmp Eq L) %"v29", #0
    => br %"v30" ? "L33" : "L77";
  @"L33":
    %"v47" = %"v0" +p #192;
    %"v48" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v49" : W = (Cmp Eq W) %"v48", #0
    => br %"v49" ? "L43" : "L45";
  @"L43":
    %"v51" = %"v0" +p #192;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk1", %"v51";
    store Ww [%"chk3" + 0] <- #4294967295
    => goto "L45";
  @"L45":
    %"v54" = %"v0" +p #192;
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L77";
  @"L77" [%"pr.4" : P = phi("L45" => %"v2", "L16" => %"v2", "L117" => %"v152", "L173" => %"v231"); %"pr.1" : L = phi("L45" => %"v4", "L16" => %"v4", "L117" => %"v156", "L173" => %"v234")]:
    %"v81" : W = (Cmp Ne L) %"pr.1", #0
    => br %"v81" ? "L78" : "L79";
  @"L78":
    %"v84" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v87" = %"v0" +p #8;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v89" : L = Ptoi %"v85";
    %"v90" : L = Ptoi %"v88";
    %"v91" : L = Sub %"v89", %"v90";
    %"v96" : W = (Cmp Sle L) %"v91", #0
    => br %"v96" ? "L92" : "L93";
  @"L92":
    call %"v99" : W = $"__GI___uflow"(P %"v0");
    %"v105" : W = (Cmp Eq W) %"v99", #4294967295
    => br %"v105" ? "L100" : "L102";
  @"L100":
    %"v111" : W = (Cmp Ne L) %"v18", #0
    => br %"v111" ? "L106" : "L79";
  @"L106":
    %"chk7" : A = (Check 0 4 Write 1) %"v10";
    store Ww [%"chk7" + 0] <- %"v99"
    => goto "L79";
  @"L102":
    %"v120" : W = (Cmp Eq W) %"v99", %"v6"
    => br %"v120" ? "L115" : "L117";
  @"L115":
    %"v125" : W = (Cmp Sgt W) %"v8", #0
    => br %"v125" ? "L121" : "L122";
  @"L121":
    %"v127" = %"pr.4" +p #1;
    %"v129" : W = (Ext Sb) %"v99";
    %"chk8" : A = (Check 0 1 Write 1) %"pr.4";
    store Wb [%"chk8" + 0] <- %"v129"
    => goto "L123";
  @"L122":
    %"v134" : W = (Cmp Slt W) %"v8", #0
    => br %"v134" ? "L130" : "L123";
  @"L130":
    call %"v137" : W = $"__GI__IO_sputbackc"(P %"v0", W %"v99")
    => goto "L123";
  @"L123" [%"pr.3" : P = phi("L121" => %"v127", "L130" => %"pr.4", "L122" => %"pr.4")]:
    => br %"v125" ? "L140" : "L139";
  @"L139":
    => goto "L140";
  @"L140":
    %"v147" : L = Ptoi %"pr.3";
    %"v148" : L = Ptoi %"v2";
    %"v149" : L = Sub %"v147", %"v148"
    => ret %"v149";
  @"L117":
    %"v152" = %"pr.4" +p #1;
    %"v154" : W = (Ext Sb) %"v99";
    %"chk9" : A = (Check 0 1 Write 1) %"pr.4";
    store Wb [%"chk9" + 0] <- %"v154";
    %"v156" : L = Sub %"pr.1", #1
    => goto poll "L77";
  @"L93":
    %"v163" : W = (Cmp Uge L) %"v91", %"pr.1"
    => br %"v163" ? "L160" : "L159";
  @"L159":
    => goto "L160";
  @"L160" [%"pr.8" : L = phi("L159" => %"v91", "L93" => %"pr.1")]:
    %"v166" = %"v0" +p #8;
    %"v167" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v170" : P = $"__GI_memchr"(P %"v167", W %"v6", L %"pr.8");
    %"v175" : L = Ptoi %"v170";
    %"v177" : W = (Cmp Ne L) %"v175", %"v19"
    => br %"v177" ? "L171" : "L173";
  @"L171":
    %"v181" : L = Ptoi %"pr.4";
    %"v182" : L = Ptoi %"v2";
    %"v183" : L = Sub %"v181", %"v182";
    %"v186" = %"v0" +p #8;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk6", %"v186";
    %"v187" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v189" : L = Ptoi %"v187";
    %"v190" : L = Sub %"v175", %"v189";
    %"v195" : W = (Cmp Sge W) %"v8", #0
    => br %"v195" ? "L191" : "L193";
  @"L191":
    %"v197" = %"v170" +p #1;
    %"v202" : W = (Cmp Sgt W) %"v8", #0
    => br %"v202" ? "L198" : "L193";
  @"L198":
    %"v204" : L = Add %"v190", #1
    => goto "L193";
  @"L193" [%"pr.11" : P = phi("L198" => %"v197", "L191" => %"v197", "L171" => %"v170"); %"pr.9" : L = phi("L198" => %"v204", "L191" => %"v190", "L171" => %"v190")]:
    %"v207" = %"v0" +p #8;
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk11";
    call %"v210" : P = $"__GI_memcpy"(P %"pr.4", P %"v208", L %"pr.9");
    %"chk13" : A = (Renew 0 8 Write 8) %"chk6", %"v207";
    store.ptr [%"chk13" + 0] <- %"pr.11";
    %"v216" : L = Add %"v183", %"pr.9"
    => ret %"v216";
  @"L173":
    %"v220" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk6", %"v220";
    %"v221" : P = (RawLoadPointer 0 load_effects) %"chk14";
    call %"v223" : P = $"__GI_memcpy"(P %"pr.4", P %"v221", L %"pr.8");
    %"chk15" : A = (Renew 0 8 Read 8) %"chk6", %"v220";
    %"v226" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v228" = %"v226" +p %"pr.8";
    %"chk16" : A = (Renew 0 8 Write 8) %"chk6", %"v220";
    store.ptr [%"chk16" + 0] <- %"v228";
    %"v231" = %"pr.4" +p %"pr.8";
    %"v234" : L = Sub %"pr.1", %"pr.8"
    => goto poll "L77";
  @"L79":
    %"v237" : L = Ptoi %"pr.4";
    %"v238" : L = Ptoi %"v2";
    %"v239" : L = Sub %"v237", %"v238"
    => ret %"v239"
} }.

Definition hello_image_fn__IO_new_proc_close : func :=
  ir_fn{ "export" "_IO_new_proc_close"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 4) #4;
    %"v9" : P = (Alloc 8) #32;
    %"v204" : P = (Alloc 4) #4;
    %"v4" : P = Copy $"glibc_iopopen#proc_file_chain";
    %"v11" : P = Copy $"glibc_iopopen#unlock";
    %"v12" = %"v9" +p #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v12";
    store.ptr [%"chk0" + 0] <- #0;
    %"chk1" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v9";
    store.ptr [%"chk1" + 0] <- %"v11";
    call void $"__GI___libc_cleanup_push_defer"(P %"v9");
    call %"v23" : P = $"zthread_self_cookie"();
    %"v27" : P = Copy $"__libc_single_threaded_internal";
    %"chk2" : A = (Check 0 1 Read 1) %"v27";
    %"v28" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"v29" : W = (Cmp Ne W) %"v28", #0
    => br %"v29" ? "L30" : "L31";
  @"L30":
    %"v32" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v33" = %"v32" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v33";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v35" : L = Ptoi %"v34";
    %"v36" : L = Ptoi #0;
    %"v37" : W = (Cmp Eq L) %"v35", %"v36"
    => goto "L31";
  @"L31" [%"v39" : W = phi("start" => #0, "L30" => %"v37")]:
    => br %"v39" ? "L24" : "L25";
  @"L24":
    %"v40" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk4" : A = (Check 0 4 Write 1) %"v40";
    store Ww [%"chk4" + 0] <- #1;
    %"v41" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v42" = %"v41" +p #8;
    %"chk5" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk5" + 0] <- %"v23"
    => goto "L86";
  @"L25":
    %"v47" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v48" = %"v47" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v51" : L = Ptoi %"v49";
    %"v52" : L = Ptoi %"v23";
    %"v53" : W = (Cmp Ne L) %"v51", %"v52"
    => br %"v53" ? "L44" : "L45";
  @"L44":
    %"v55" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk7" : A = (Check 0 4 Write 4) %"v55";
    %"v62" : W = (RawCas (CasNarrow Sw) 0) %"chk7", #0, #1;
    %"v63" : W = (Cmp Eq W) %"v62", #0
    => br %"v63" ? "L65" : "L64";
  @"L64":
    => goto "L65";
  @"L65":
    %"v66" : W = (Cmp Ne W) %"v62", #0
    => br %"v66" ? "L69" : "L58";
  @"L69":
    call void $"__GI___lll_lock_wait_private"(P %"v55")
    => goto "L58";
  @"L58":
    %"v79" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v80" = %"v79" +p #8;
    %"chk8" : A = (Check 0 8 Write 8) %"v80";
    store.ptr [%"chk8" + 0] <- %"v23"
    => goto "L86";
  @"L45":
    %"v82" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v83" = %"v82" +p #4;
    %"chk9" : A = (Check 0 4 Read 1) %"v83";
    %"v84" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v85" : W = Add %"v84", #1;
    %"chk10" : A = (Renew 0 4 Write 1) %"chk9", %"v83";
    store Ww [%"chk10" + 0] <- %"v85"
    => goto "L86";
  @"L86" [%"pr.1" : P = phi("L88" => %"v112", "L24" => %"v4", "L58" => %"v4", "L45" => %"v4")]:
    %"chk11" : A = (Check 0 8 Read 8) %"pr.1";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v92" : L = Ptoi %"v91";
    %"v93" : L = Ptoi #0;
    %"v94" : W = (Cmp Ne L) %"v92", %"v93"
    => br %"v94" ? "L87" : "L89";
  @"L87":
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v101" : L = Ptoi %"v99";
    %"v102" : L = Ptoi %"v0";
    %"v103" : W = (Cmp Eq L) %"v101", %"v102"
    => br %"v103" ? "L95" : "L88";
  @"L95":
    %"v106" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v107" = %"v106" +p #232;
    %"chk14" : A = (Check 0 8 Read 8) %"v107";
    %"v108" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Renew 0 8 Write 8) %"chk11", %"pr.1";
    store.ptr [%"chk15" + 0] <- %"v108"
    => goto "L89";
  @"L88":
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v112" = %"v111" +p #232
    => goto poll "L86";
  @"L89" [%"pr.2" : W = phi("L86" => #4294967295, "L95" => #0)]:
    %"v119" : P = Copy $"__libc_single_threaded_internal";
    %"chk17" : A = (Check 0 1 Read 1) %"v119";
    %"v120" : W = (RawLoad (LdNarrow Sb) 0) %"chk17";
    %"v121" : W = (Cmp Ne W) %"v120", #0
    => br %"v121" ? "L122" : "L123";
  @"L122":
    %"v124" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v125" = %"v124" +p #4;
    %"chk18" : A = (Check 0 4 Read 1) %"v125";
    %"v126" : W = (RawLoad (LdNarrow Sw) 0) %"chk18";
    %"v127" : W = (Cmp Eq W) %"v126", #0
    => goto "L123";
  @"L123" [%"v129" : W = phi("L89" => #0, "L122" => %"v127")]:
    => br %"v129" ? "L116" : "L117";
  @"L116":
    %"v130" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v131" = %"v130" +p #8;
    %"chk19" : A = (Check 0 8 Write 8) %"v131";
    store.ptr [%"chk19" + 0] <- #0;
    %"v132" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk20" : A = (Check 0 4 Write 1) %"v132";
    store Ww [%"chk20" + 0] <- #0
    => goto "L175";
  @"L117":
    %"v136" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v137" = %"v136" +p #4;
    %"chk21" : A = (Check 0 4 Read 1) %"v137";
    %"v138" : W = (RawLoad (LdNarrow Sw) 0) %"chk21";
    %"v139" : W = (Cmp Eq W) %"v138", #0
    => br %"v139" ? "L133" : "L134";
  @"L133":
    %"v140" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v141" = %"v140" +p #8;
    %"chk22" : A = (Check 0 8 Write 8) %"v141";
    store.ptr [%"chk22" + 0] <- #0;
    %"v143" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"chk23" : A = (Check 0 4 Read 1) %"v143";
    %"v147" : W = (RawLoad (LdNarrow Sw) 0) %"chk23"
    => goto "L148";
  @"L148" [%"v150" : W = phi("L133" => %"v147", "L148" => %"v151")]:
    %"chk24" : A = (HalfCheck Lower 0 4 Write 4) %"chk23", %"v143";
    %"v151" : W = (RawCas (CasNarrow Sw) 0) %"chk24", %"v150", #0;
    %"v152" : W = (Cmp Eq W) %"v151", %"v150"
    => br %"v152" ? "L149" : poll "L148";
  @"L149":
    %"v157" : W = (Cmp Sgt W) %"v150", #1
    => br %"v157" ? "L160" : "L175";
  @"L160":
    call void $"__GI___lll_lock_wake_private"(P %"v143")
    => goto "L175";
  @"L134":
    %"v171" : P = Copy $"glibc_iopopen#proc_file_chain_lock";
    %"v172" = %"v171" +p #4;
    %"chk25" : A = (Check 0 4 Read 1) %"v172";
    %"v173" : W = (RawLoad (LdNarrow Sw) 0) %"chk25";
    %"v174" : W = Sub %"v173", #1;
    %"chk26" : A = (Renew 0 4 Write 1) %"chk25", %"v172";
    store Ww [%"chk26" + 0] <- %"v174"
    => goto "L175";
  @"L175":
    call void $"__GI___libc_cleanup_pop_restore"(P %"v9");
    %"v189" : W = (Cmp Slt W) %"pr.2", #0
    => br %"v189" ? "L191" : "L190";
  @"L190":
    %"v193" = %"v0" +p #112;
    %"chk27" : A = (Check 0 4 Read 1) %"v193";
    %"v194" : W = (RawLoad (LdNarrow Sw) 0) %"chk27";
    call %"v195" : W = $"__GI___close_nocancel"(W %"v194");
    %"v196" : W = (Cmp Slt W) %"v195", #0
    => goto "L191";
  @"L191" [%"v198" : W = phi("L175" => #1, "L190" => %"v196")]:
    => br %"v198" ? "L185" : "L201";
  @"L185":
    => ret #4294967295;
  @"L201":
    call %"v205" : W = $"__GI___pthread_setcancelstate"(W #1, P %"v204");
    %"v207" = %"v0" +p #224;
    %"chk28" : A = (Check 0 4 Read 1) %"v207";
    %"v208" : W = (RawLoad (LdNarrow Sw) 0) %"chk28";
    call %"v209" : W = $"__GI___waitpid"(W %"v208", P %"v2", W #0);
    %"chk29" : A = (Check 0 4 Read 1) %"v204";
    %"v210" : W = (RawLoad (LdNarrow Sw) 0) %"chk29";
    call %"v211" : W = $"__GI___pthread_setcancelstate"(W %"v210", P #0);
    %"v214" : W = (Cmp Eq W) %"v209", #4294967295
    => br %"v214" ? "L215" : "L216";
  @"L215":
    %"v217" : P = Copy $"__libc_errno";
    %"chk30" : A = (Check 0 4 Read 1) %"v217";
    %"v218" : W = (RawLoad (LdNarrow Sw) 0) %"chk30";
    %"v219" : W = (Cmp Eq W) %"v218", #4
    => goto "L216";
  @"L216" [%"v221" : W = phi("L201" => #0, "L215" => %"v219")]:
    => br %"v221" ? poll "L201" : "L203";
  @"L203":
    => br %"v214" ? "L222" : "L224";
  @"L222":
    => ret #4294967295;
  @"L224":
    %"chk31" : A = (Check 0 4 Read 1) %"v2";
    %"v230" : W = (RawLoad (LdNarrow Sw) 0) %"chk31"
    => ret %"v230"
} }.

Definition hello_image_fn__IO_mem_sync : func :=
  ir_fn{ "export" "_IO_mem_sync"(P %"v0") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #48;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L6";
  @"L4":
    call %"v17" : W = $"__GI__IO_str_overflow"(P %"v0", W #0);
    %"v19" = %"v0" +p #40;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk0", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk2";
    (Flight (a "v21") Sub [(FAddress (t "v20")); (FValue (Const 1))] (LowerOf (t "v20")));
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v19";
    store.ptr [%"chk3" + 0] <- %"v21"
    => goto "L6";
  @"L6":
    %"v23" = %"v0" +p #240;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v26" = %"v0" +p #32;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk6" + 0] <- %"v27";
    %"v29" = %"v0" +p #248;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v32" = %"v0" +p #40;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Renew 0 8 Read 8) %"chk5", %"v26";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v37" : L = Ptoi %"v33";
    %"v38" : L = Ptoi %"v36";
    %"v39" : L = Sub %"v37", %"v38";
    %"chk10" : A = (Check 0 8 Write 1) %"v30";
    store Wl [%"chk10" + 0] <- %"v39"
    => ret #0
} }.
