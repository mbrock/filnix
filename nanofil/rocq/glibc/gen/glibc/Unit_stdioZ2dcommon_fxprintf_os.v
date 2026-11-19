(** This file defines checked IR from glibc’s `stdio-common/fxprintf.os` object.
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

Definition fn___fxprintf : func :=
  ir_fn{ "export" "__fxprintf"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v4" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #16;
    %"chk0" : A = (Check 0 8 Write 8) %"v4";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call %"v8" : W = $"__vfxprintf"(P %"v0", P %"v2", P %"v4", W #0)
    => ret %"v8"
} }.

Definition fn___fxprintf_nocancel : func :=
  ir_fn{ "export" "__fxprintf_nocancel"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v13" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #16;
    %"v8" : L = Ptoi %"v0";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Eq L) %"v8", %"v9"
    => br %"v10" ? "L4" : "L6";
  @"L4":
    %"v11" : P = Copy $"stderr";
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L6";
  @"L6" [%"pr.1" : P = phi("L4" => %"v12", "start" => %"v0")]:
    %"chk1" : A = (Check 0 8 Write 8) %"v13";
    store.ptr [%"chk1" + 0] <- %"va_args";
    %"chk2" : A = (Check 0 4 Read 1) %"pr.1";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v19" : W = And %"v18", #32768;
    %"v20" : W = (Cmp Eq W) %"v19", #0
    => br %"v20" ? "L21" : "L16";
  @"L21":
    call %"v25" : P = $"zthread_self_cookie"();
    %"v29" : P = Copy $"__libc_single_threaded_internal";
    %"chk3" : A = (Check 0 1 Read 1) %"v29";
    %"v30" : W = (RawLoad (LdNarrow Sb) 0) %"chk3";
    %"v31" : W = (Cmp Ne W) %"v30", #0
    => br %"v31" ? "L32" : "L33";
  @"L32":
    %"v35" = %"pr.1" +p #136;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v37" = %"v36" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v39" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Eq L) %"v39", %"v9"
    => goto "L33";
  @"L33" [%"v43" : W = phi("L21" => #0, "L32" => %"v41")]:
    => br %"v43" ? "L26" : "L27";
  @"L26":
    %"v45" = %"pr.1" +p #136;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 4 Write 1) %"v46";
    store Ww [%"chk7" + 0] <- #1;
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v50" = %"v49" +p #8;
    %"chk9" : A = (Check 0 8 Write 8) %"v50";
    store.ptr [%"chk9" + 0] <- %"v25"
    => goto "L16";
  @"L27":
    %"v56" = %"pr.1" +p #136;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v58" = %"v57" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v61" : L = Ptoi %"v59";
    %"v62" : L = Ptoi %"v25";
    %"v63" : W = (Cmp Ne L) %"v61", %"v62"
    => br %"v63" ? "L52" : "L53";
  @"L52":
    %"v66" = %"pr.1" +p #136;
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk13" : A = (Check 0 4 Write 4) %"v67";
    %"v74" : W = (RawCas (CasNarrow Sw) 0) %"chk13", #0, #1;
    %"v75" : W = (Cmp Eq W) %"v74", #0
    => br %"v75" ? "L77" : "L76";
  @"L76":
    => goto "L77";
  @"L77":
    %"v78" : W = (Cmp Ne W) %"v74", #0
    => br %"v78" ? "L81" : "L70";
  @"L81":
    call void $"__GI___lll_lock_wait_private"(P %"v67")
    => goto "L70";
  @"L70":
    %"v92" = %"pr.1" +p #136;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk10", %"v92";
    %"v93" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v94" = %"v93" +p #8;
    %"chk15" : A = (Check 0 8 Write 8) %"v94";
    store.ptr [%"chk15" + 0] <- %"v25"
    => goto "L16";
  @"L53":
    %"v97" = %"pr.1" +p #136;
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v99" = %"v98" +p #4;
    %"chk17" : A = (Check 0 4 Read 1) %"v99";
    %"v100" : W = (RawLoad (LdNarrow Sw) 0) %"chk17";
    %"v101" : W = Add %"v100", #1;
    %"chk18" : A = (Renew 0 4 Write 1) %"chk17", %"v99";
    store Ww [%"chk18" + 0] <- %"v101"
    => goto "L16";
  @"L16":
    %"v104" = %"pr.1" +p #116;
    %"chk19" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"v104";
    %"v105" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v106" : W = Shl %"v105", #8;
    %"v107" : W = Sar %"v106", #8;
    %"v110" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v111" : W = Shl %"v110", #8;
    %"v112" : W = Sar %"v111", #8;
    %"v113" : W = Or %"v112", #2;
    %"v114" : W = (RawLoad (LdNarrow Sw) 0) %"chk19";
    %"v115" : W = And %"v114", #4278190080;
    %"v116" : W = And %"v113", #16777215;
    %"v117" : W = Or %"v115", %"v116";
    %"chk22" : A = (Renew 0 4 Write 1) %"chk19", %"v104";
    store Ww [%"chk22" + 0] <- %"v117";
    %"iw_1.v3" : P = (Alloc 8) #8;
    %"iw_1.v63" : P = (Alloc 4) #8;
    %"iw_1.v69" : P = (Alloc 16) #1040;
    %"chk23" : A = (Check 0 8 Write 8) %"iw_1.v3";
    store.ptr [%"chk23" + 0] <- %"v2";
    %"iw_1.v48" = %"pr.1" +p #192;
    %"chk24" : A = (HalfCheck Upper 0 4 Read 1) %"chk2", %"iw_1.v48";
    %"iw_1.v49" : W = (RawLoad (LdNarrow Sw) 0) %"chk24";
    %"iw_1.v55" : W = (Cmp Sle W) %"iw_1.v49", #0
    => br %"iw_1.v55" ? "iw_1.L8" : "iw_1.L10";
  @"iw_1.L8":
    %"chk25" : A = (Renew 0 8 Read 8) %"chk23", %"iw_1.v3";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk25";
    call %"iw_1.v60" : W = $"__vfprintf_internal"(P %"pr.1", P %"iw_1.v57", P %"v13", W #0)
    => goto "iw_1.join";
  @"iw_1.L10":
    %"chk26" : A = (Renew 0 8 Read 8) %"chk23", %"iw_1.v3";
    %"iw_1.v66" : P = (RawLoadPointer 0 load_effects) %"chk26";
    call %"iw_1.v67" : L = $"__GI_strlen"(P %"iw_1.v66");
    %"iw_1.v68" : L = Add %"iw_1.v67", #1;
    %"iw_1.iw_1.v4" = %"iw_1.v69" +p #16;
    %"chk27" : A = (Check 0 8 Write 8) %"iw_1.v69";
    store.ptr [%"chk27" + 0] <- %"iw_1.iw_1.v4";
    %"iw_1.iw_1.v6" = %"iw_1.v69" +p #8;
    %"chk28" : A = (HalfCheck Upper 0 8 Write 1) %"chk27", %"iw_1.iw_1.v6";
    store Wl [%"chk28" + 0] <- #1024;
    %"iw_1.v75" : W = (Cmp Ugt L) %"iw_1.v68", #4611686018427387903
    => br %"iw_1.v75" ? "iw_1.L70" : "iw_1.iw_2.start";
  @"iw_1.L70":
    %"iw_1.v78" : P = Copy $"__libc_errno";
    %"chk29" : A = (Check 0 4 Write 1) %"iw_1.v78";
    store Ww [%"chk29" + 0] <- #75
    => goto "iw_1.join";
  @"iw_1.iw_2.start":
    call %"iw_1.iw_2.v9" : W = $"__GI___libc_scratch_buffer_set_array_size"(P %"iw_1.v69", L #4, L %"iw_1.v68");
    %"iw_1.iw_2.v10" : W = (Ext Ub) %"iw_1.iw_2.v9";
    %"iw_1.iw_2.v11" : L = (Ext Uw) %"iw_1.iw_2.v10";
    %"iw_1.v87" : W = (Cmp Eq L) %"iw_1.iw_2.v11", #0
    => br %"iw_1.v87" ? "iw_1.join" : "iw_1.L83";
  @"iw_1.L83":
    %"chk30" : A = (Renew 0 8 Read 8) %"chk27", %"iw_1.v69";
    %"iw_1.v90" : P = (RawLoadPointer 0 load_effects) %"chk30";
    call %"iw_1.v91" : P = $"__GI_memset"(P %"iw_1.v63", W #0, L #8);
    call %"iw_1.v94" : L = $"__mbsrtowcs"(P %"iw_1.v90", P %"iw_1.v3", L %"iw_1.v68", P %"iw_1.v63");
    %"iw_1.v98" : W = Copy %"iw_1.v94";
    %"iw_1.v100" : W = (Cmp Ne W) %"iw_1.v98", #4294967295
    => br %"iw_1.v100" ? "iw_1.L95" : "iw_1.L97";
  @"iw_1.L95":
    call %"iw_1.v105" : W = $"__vfwprintf_internal"(P %"pr.1", P %"iw_1.v90", P %"v13", W #0)
    => goto "iw_1.L97";
  @"iw_1.L97" [%"iw_1.pr.3" : W = phi("iw_1.L95" => %"iw_1.v105", "iw_1.L83" => %"iw_1.v94")]:
    %"chk31" : A = (Renew 0 8 Read 8) %"chk27", %"iw_1.v69";
    %"iw_1.iw_3.v6" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_1.iw_3.v8" = %"iw_1.v69" +p #16;
    %"iw_1.iw_3.v9" : L = Ptoi %"iw_1.iw_3.v6";
    %"iw_1.iw_3.v10" : L = Ptoi %"iw_1.iw_3.v8";
    %"iw_1.iw_3.v11" : W = (Cmp Ne L) %"iw_1.iw_3.v9", %"iw_1.iw_3.v10"
    => br %"iw_1.iw_3.v11" ? "iw_1.iw_3.L2" : "iw_1.join";
  @"iw_1.iw_3.L2":
    %"iw_1.iw_3.v13" : P = (RawLoadPointer 0 load_effects) %"chk31";
    call void $"free"(P %"iw_1.iw_3.v13")
    => goto "iw_1.join";
  @"iw_1.join" [%"v123" : W = phi("iw_1.L8" => %"iw_1.v60", "iw_1.L70" => #4294967295, "iw_1.iw_2.start" => #4294967295, "iw_1.L97" => %"iw_1.pr.3", "iw_1.iw_3.L2" => %"iw_1.pr.3")]:
    %"v125" = %"pr.1" +p #116;
    %"chk33" : A = (Renew 0 4 Read 1) %"chk19", %"v125";
    %"v127" : W = (RawLoad (LdNarrow Sw) 0) %"chk33";
    %"v128" : W = And %"v127", #4278190080;
    %"v129" : W = And %"v107", #16777215;
    %"v130" : W = Or %"v128", %"v129";
    %"chk34" : A = (Renew 0 4 Write 1) %"chk19", %"v125";
    store Ww [%"chk34" + 0] <- %"v130";
    %"chk35" : A = (Renew 0 4 Read 1) %"chk2", %"pr.1";
    %"v137" : W = (RawLoad (LdNarrow Sw) 0) %"chk35";
    %"v138" : W = And %"v137", #32768;
    %"v139" : W = (Cmp Eq W) %"v138", #0
    => br %"v139" ? "L140" : "L135";
  @"L140":
    %"v146" : P = Copy $"__libc_single_threaded_internal";
    %"chk36" : A = (Check 0 1 Read 1) %"v146";
    %"v147" : W = (RawLoad (LdNarrow Sb) 0) %"chk36";
    %"v148" : W = (Cmp Ne W) %"v147", #0
    => br %"v148" ? "L149" : "L150";
  @"L149":
    %"v152" = %"pr.1" +p #136;
    %"chk37" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v152";
    %"v153" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v154" = %"v153" +p #4;
    %"chk38" : A = (Check 0 4 Read 1) %"v154";
    %"v155" : W = (RawLoad (LdNarrow Sw) 0) %"chk38";
    %"v156" : W = (Cmp Eq W) %"v155", #0
    => goto "L150";
  @"L150" [%"v158" : W = phi("L140" => #0, "L149" => %"v156")]:
    => br %"v158" ? "L143" : "L144";
  @"L143":
    %"v160" = %"pr.1" +p #136;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v160";
    %"v161" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v162" = %"v161" +p #8;
    %"chk40" : A = (Check 0 8 Write 8) %"v162";
    store.ptr [%"chk40" + 0] <- #0;
    %"chk41" : A = (Renew 0 8 Read 8) %"chk39", %"v160";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"chk42" : A = (Check 0 4 Write 1) %"v165";
    store Ww [%"chk42" + 0] <- #0
    => goto "L135";
  @"L144":
    %"v170" = %"pr.1" +p #136;
    %"chk43" : A = (HalfCheck Upper 0 8 Read 8) %"chk2", %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v172" = %"v171" +p #4;
    %"chk44" : A = (Check 0 4 Read 1) %"v172";
    %"v173" : W = (RawLoad (LdNarrow Sw) 0) %"chk44";
    %"v174" : W = (Cmp Eq W) %"v173", #0
    => br %"v174" ? "L166" : "L167";
  @"L166":
    %"v176" = %"pr.1" +p #136;
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v178" = %"v177" +p #8;
    %"chk46" : A = (Check 0 8 Write 8) %"v178";
    store.ptr [%"chk46" + 0] <- #0;
    %"chk47" : A = (Renew 0 8 Read 8) %"chk43", %"v176";
    %"v182" : P = (RawLoadPointer 0 load_effects) %"chk47";
    %"chk48" : A = (Check 0 4 Read 1) %"v182";
    %"v186" : W = (RawLoad (LdNarrow Sw) 0) %"chk48"
    => goto "L187";
  @"L187" [%"v189" : W = phi("L166" => %"v186", "L187" => %"v190")]:
    %"chk49" : A = (HalfCheck Lower 0 4 Write 4) %"chk48", %"v182";
    %"v190" : W = (RawCas (CasNarrow Sw) 0) %"chk49", %"v189", #0;
    %"v191" : W = (Cmp Eq W) %"v190", %"v189"
    => br %"v191" ? "L188" : poll "L187";
  @"L188":
    %"v196" : W = (Cmp Sgt W) %"v189", #1
    => br %"v196" ? "L199" : "L135";
  @"L199":
    call void $"__GI___lll_lock_wake_private"(P %"v182")
    => goto "L135";
  @"L167":
    %"v211" = %"pr.1" +p #136;
    %"v212" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v213" = %"v212" +p #4;
    %"chk51" : A = (Check 0 4 Read 1) %"v213";
    %"v214" : W = (RawLoad (LdNarrow Sw) 0) %"chk51";
    %"v215" : W = Sub %"v214", #1;
    %"chk52" : A = (Renew 0 4 Write 1) %"chk51", %"v213";
    store Ww [%"chk52" + 0] <- %"v215"
    => goto "L135";
  @"L135":
    => ret %"v123"
} }.

Definition fn___vfxprintf : func :=
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
