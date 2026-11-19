(** This file defines checked IR from glibc’s `libio/iofflush.os` object.
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

Definition fn___GI__IO_fflush : func :=
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
