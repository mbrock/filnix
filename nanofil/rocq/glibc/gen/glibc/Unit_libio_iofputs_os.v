(** This file defines checked IR from glibc’s `libio/iofputs.os` object.
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

Definition fn___GI__IO_fputs : func :=
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

Definition item_fputs : item :=
  (IAlias (a "fputs") (a "weak") (a "__GI__IO_fputs")).
