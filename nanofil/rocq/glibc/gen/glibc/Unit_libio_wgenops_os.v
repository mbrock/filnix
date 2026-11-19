(** This file defines checked IR from glibc’s `libio/wgenops.os` object.
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

Definition fn___GI__IO_free_wbackup_area : func :=
  ir_fn{ "export" "__GI__IO_free_wbackup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #256
    => br %"v7" ? "L2" : "L4";
  @"L2":
    call void $"__GI__IO_switch_to_main_wget_area"(P %"v0")
    => goto "L4";
  @"L4":
    %"v10" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" = %"v11" +p #64;
    %"chk2" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    call void $"free"(P %"v13");
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v17" = %"v16" +p #64;
    %"chk4" : A = (Check 0 8 Write 8) %"v17";
    store.ptr [%"chk4" + 0] <- #0;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v21" = %"v20" +p #80;
    %"chk6" : A = (Check 0 8 Write 8) %"v21";
    store.ptr [%"chk6" + 0] <- #0;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v25" = %"v24" +p #72;
    %"chk8" : A = (Check 0 8 Write 8) %"v25";
    store.ptr [%"chk8" + 0] <- #0
    => ret void
} }.

Definition fn___GI__IO_least_wmarker : func :=
  ir_fn{ "export" "__GI__IO_least_wmarker"(P %"v0", P %"v2") -> (RClass L) {
  @"start":
    %"v7" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v8" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v2";
    %"v12" : L = Ptoi %"v10";
    %"v13" : L = Sub %"v11", %"v12";
    %"v14" : L = Div %"v13", #4;
    %"v17" = %"v0" +p #96;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk2"
    => goto "L19";
  @"L19" [%"pr.3" : P = phi("L29" => %"v41", "start" => %"v18"); %"pr.1" : L = phi("L29" => %"pr.2", "start" => %"v14")]:
    %"v24" : L = Ptoi %"pr.3";
    %"v25" : L = Ptoi #0;
    %"v26" : W = (Cmp Ne L) %"v24", %"v25"
    => br %"v26" ? "L20" : "L22";
  @"L20":
    %"v31" = %"pr.3" +p #16;
    %"chk3" : A = (Check 0 4 Read 1) %"v31";
    %"v32" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v34" : L = (Ext Sw) %"v32";
    %"v35" : W = (Cmp Slt L) %"v34", %"pr.1"
    => br %"v35" ? "L27" : "L29";
  @"L27":
    %"v37" = %"pr.3" +p #16;
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v39" : L = (Ext Sw) %"v38"
    => goto "L29";
  @"L29" [%"pr.2" : L = phi("L27" => %"v39", "L20" => %"pr.1")]:
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk3", %"pr.3";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk5"
    => goto poll "L19";
  @"L22":
    => ret %"pr.1"
} }.

Definition fn___GI__IO_switch_to_main_wget_area : func :=
  ir_fn{ "export" "__GI__IO_switch_to_main_wget_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v6" : W = And %"v4", #4294967039;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v6";
    %"v8" = %"v0" +p #160;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v10" = %"v9" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v15" = %"v14" +p #8;
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v19" = %"v18" +p #80;
    %"chk6" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v15";
    store.ptr [%"chk7" + 0] <- %"v20";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v24" = %"v23" +p #80;
    %"chk9" : A = (Check 0 8 Write 8) %"v24";
    store.ptr [%"chk9" + 0] <- %"v11";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v29" = %"v28" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v34" = %"v33" +p #16;
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v38" = %"v37" +p #64;
    %"chk14" : A = (Check 0 8 Read 8) %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk15" + 0] <- %"v39";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v43" = %"v42" +p #64;
    %"chk17" : A = (Check 0 8 Write 8) %"v43";
    store.ptr [%"chk17" + 0] <- %"v30";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk2", %"v8";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v51" = %"v50" +p #16;
    %"chk20" : A = (Check 0 8 Read 8) %"v51";
    %"v52" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 8 Write 8) %"v47";
    store.ptr [%"chk21" + 0] <- %"v52"
    => ret void
} }.

Definition fn___GI__IO_switch_to_wbackup_area : func :=
  ir_fn{ "export" "__GI__IO_switch_to_wbackup_area"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v5" : W = Or %"v4", #256;
    %"chk1" : A = (Renew 0 4 Write 1) %"chk0", %"v0";
    store Ww [%"chk1" + 0] <- %"v5";
    %"v7" = %"v0" +p #160;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v9" = %"v8" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v14" = %"v13" +p #8;
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v18" = %"v17" +p #80;
    %"chk6" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Write 8) %"v14";
    store.ptr [%"chk7" + 0] <- %"v19";
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v23" = %"v22" +p #80;
    %"chk9" : A = (Check 0 8 Write 8) %"v23";
    store.ptr [%"chk9" + 0] <- %"v10";
    %"chk10" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v28" = %"v27" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v33" = %"v32" +p #16;
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v37" = %"v36" +p #64;
    %"chk14" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"v33";
    store.ptr [%"chk15" + 0] <- %"v38";
    %"chk16" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v42" = %"v41" +p #64;
    %"chk17" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk17" + 0] <- %"v29";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk2", %"v7";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v50" = %"v49" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Check 0 8 Write 8) %"v46";
    store.ptr [%"chk21" + 0] <- %"v51"
    => ret void
} }.

Definition fn___GI__IO_switch_to_wget_mode : func :=
  ir_fn{ "export" "__GI__IO_switch_to_wget_mode"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v7" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #24;
    %"chk3" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v15" : L = Ptoi %"v9";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Ugt L) %"v15", %"v16"
    => br %"v17" ? "L2" : "L4";
  @"L2":
    %"v22" = %"v0" +p #160;
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v24" = %"v23" +p #224;
    %"chk5" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v26" = %"v25" +p #24;
    %"chk6" : A = (Check 0 8 Read 8) %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : F = CheckFunction %"v27";
    rawcall %"v29" : W = %"chk7"(P %"v0", W #(-1));
    %"v30" : W = (Cmp Eq W) %"v29", #4294967295
    => br %"v30" ? "L18" : "L4";
  @"L18":
    => ret #4294967295;
  @"L4":
    %"chk8" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk8";
    %"v38" : W = And %"v37", #256
    => br %"v38" ? "L33" : "L34";
  @"L33":
    %"v40" = %"v0" +p #160;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v42" = %"v41" +p #16;
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v46" = %"v45" +p #72;
    %"chk11" : A = (Check 0 8 Read 8) %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk12" + 0] <- %"v47"
    => goto "L35";
  @"L34":
    %"v49" = %"v0" +p #160;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"v49";
    %"v50" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v51" = %"v50" +p #16;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v55" = %"v54" +p #48;
    %"chk15" : A = (Check 0 8 Read 8) %"v55";
    %"v56" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (Check 0 8 Write 8) %"v51";
    store.ptr [%"chk16" + 0] <- %"v56";
    %"chk17" : A = (Renew 0 8 Read 8) %"chk0", %"v49";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v63" = %"v62" +p #32;
    %"chk18" : A = (Check 0 8 Read 8) %"v63";
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v68" = %"v67" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"v68";
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v70" : L = Ptoi %"v64";
    %"v71" : L = Ptoi %"v69";
    %"v72" : W = (Cmp Ugt L) %"v70", %"v71"
    => br %"v72" ? "L57" : "L35";
  @"L57":
    %"v74" = %"v0" +p #160;
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v76" = %"v75" +p #8;
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v80" = %"v79" +p #32;
    %"chk23" : A = (Check 0 8 Read 8) %"v80";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Check 0 8 Write 8) %"v76";
    store.ptr [%"chk24" + 0] <- %"v81"
    => goto "L35";
  @"L35":
    %"v83" = %"v0" +p #160;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk0", %"v83";
    %"v84" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v88" = %"v87" +p #32;
    %"chk27" : A = (Check 0 8 Read 8) %"v88";
    %"v89" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"chk28" : A = (Check 0 8 Write 8) %"v84";
    store.ptr [%"chk28" + 0] <- %"v89";
    %"chk29" : A = (Renew 0 8 Read 8) %"chk0", %"v83";
    %"v92" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v93" = %"v92" +p #24;
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v97" = %"v96" +p #32;
    %"v100" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v101" = %"v100" +p #40;
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk33" : A = (Check 0 8 Read 8) %"v104";
    %"v105" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"chk34" : A = (Check 0 8 Write 8) %"v101";
    store.ptr [%"chk34" + 0] <- %"v105";
    %"chk35" : A = (Check 0 8 Write 8) %"v97";
    store.ptr [%"chk35" + 0] <- %"v105";
    %"chk36" : A = (Check 0 8 Write 8) %"v93";
    store.ptr [%"chk36" + 0] <- %"v105";
    %"chk37" : A = (Renew 0 4 Read 1) %"chk8", %"v0";
    %"v107" : W = (RawLoad (LdNarrow Sw) 0) %"chk37";
    %"v109" : W = And %"v107", #4294965247;
    %"chk38" : A = (Renew 0 4 Write 1) %"chk8", %"v0";
    store Ww [%"chk38" + 0] <- %"v109"
    => ret #0
} }.

Definition fn___GI__IO_wdefault_doallocate : func :=
  ir_fn{ "export" "__GI__IO_wdefault_doallocate"(P %"v0") -> (RClass W) {
  @"start":
    call %"v3" : P = $"malloc"(L #8192);
    %"v8" : L = Ptoi %"v3";
    %"v9" : L = Ptoi #0;
    %"v10" : W = (Cmp Eq L) %"v8", %"v9"
    => br %"v10" ? "L4" : "L6";
  @"L4":
    => ret #4294967295;
  @"L6":
    %"v20" = %"v3" +p #8192;
    call void $"__GI__IO_wsetb"(P %"v0", P %"v3", P %"v20", W #1)
    => ret #1
} }.

Definition fn___GI__IO_wdefault_finish : func :=
  ir_fn{ "export" "__GI__IO_wdefault_finish"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v9" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v10" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v12";
    %"v14" : W = (Cmp Ne L) %"v13", #0
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v18" = %"v0" +p #116;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v18";
    %"v19" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v20" : W = Shl %"v19", #8;
    %"v21" : W = Sar %"v20", #8;
    %"v22" : W = And %"v21", #8;
    %"v23" : W = (Cmp Eq W) %"v22", #0
    => goto "L16";
  @"L16" [%"v25" : W = phi("start" => #0, "L15" => %"v23")]:
    => br %"v25" ? "L5" : "L7";
  @"L5":
    %"v27" = %"v0" +p #160;
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v29" = %"v28" +p #48;
    %"chk4" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk4";
    call void $"free"(P %"v30");
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v27";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v34" = %"v33" +p #48;
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v38" = %"v37" +p #56;
    %"chk7" : A = (Check 0 8 Write 8) %"v38";
    store.ptr [%"chk7" + 0] <- #0;
    %"chk8" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk8" + 0] <- #0
    => goto "L7";
  @"L7":
    %"v40" = %"v0" +p #96;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v40";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk9"
    => goto "L42";
  @"L42" [%"pr.1" : P = phi("L43" => %"v53", "L7" => %"v41")]:
    %"v47" : L = Ptoi %"pr.1";
    %"v48" : L = Ptoi #0;
    %"v49" : W = (Cmp Ne L) %"v47", %"v48"
    => br %"v49" ? "L43" : "L45";
  @"L43":
    %"v51" = %"pr.1" +p #8;
    %"chk10" : A = (Check 0 8 Write 8) %"v51";
    store.ptr [%"chk10" + 0] <- #0;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk10", %"pr.1";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk11"
    => goto poll "L42";
  @"L45":
    %"v58" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v60" = %"v59" +p #72;
    %"chk13" : A = (Check 0 8 Read 8) %"v60";
    %"v61" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v62" : L = Ptoi %"v61";
    %"v64" : W = (Cmp Ne L) %"v62", %"v48"
    => br %"v64" ? "L54" : "L56";
  @"L54":
    call void $"__GI__IO_free_wbackup_area"(P %"v0")
    => goto "L56";
  @"L56":
    %"v70" = %"v0" +p #136;
    %"chk14" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v70";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v72" : L = Ptoi %"v71";
    %"v74" : W = (Cmp Ne L) %"v72", %"v48"
    => br %"v74" ? "L68" : "L67";
  @"L67":
    => goto "L68";
  @"L68":
    call void $"__GI__IO_un_link"(P %"v0")
    => ret void
} }.

Definition fn___GI__IO_wdefault_pbackfail : func :=
  ir_fn{ "export" "__GI__IO_wdefault_pbackfail"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v13" +p #16;
    %"chk3" : A = (Check 0 8 Read 8) %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v16" : L = Ptoi %"v10";
    %"v17" : L = Ptoi %"v15";
    %"v18" : W = (Cmp Ugt L) %"v16", %"v17"
    => br %"v18" ? "L19" : "L20";
  @"L19":
    %"chk4" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk4";
    %"v23" : W = And %"v22", #256;
    %"v24" : W = (Cmp Eq W) %"v23", #0
    => goto "L20";
  @"L20" [%"v26" : W = phi("start" => #0, "L19" => %"v24")]:
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v30" = %"v0" +p #160;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk6" : A = (Check 0 8 Read 8) %"v31";
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v36" = %"v32" +p #18446744073709551612;
    %"chk7" : A = (Check 0 4 Read 1) %"v36";
    %"v37" : W = (RawLoad (LdNarrow Sw) 0) %"chk7";
    %"v39" : W = (Cmp Eq W) %"v37", %"v2"
    => goto "L28";
  @"L28" [%"v41" : W = phi("L20" => #0, "L27" => %"v39")]:
    => br %"v41" ? "L4" : "L5";
  @"L4":
    %"v43" = %"v0" +p #160;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk9" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    (Flight (a "v46") Sub [(FAddress (t "v45")); (FValue (Const 4))] (LowerOf (t "v45")));
    %"chk10" : A = (Renew 0 8 Write 8) %"chk9", %"v44";
    store.ptr [%"chk10" + 0] <- %"v46"
    => goto "L6";
  @"L5":
    %"chk11" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v51" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v52" : W = And %"v51", #256;
    %"v53" : W = (Cmp Eq W) %"v52", #0
    => br %"v53" ? "L47" : "L48";
  @"L47":
    %"v58" = %"v0" +p #160;
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk13" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v64" = %"v63" +p #16;
    %"chk15" : A = (Check 0 8 Read 8) %"v64";
    %"v65" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v66" : L = Ptoi %"v60";
    %"v67" : L = Ptoi %"v65";
    %"v68" : W = (Cmp Ugt L) %"v66", %"v67"
    => br %"v68" ? "L69" : "L70";
  @"L69":
    %"v72" = %"v0" +p #160;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v74" = %"v73" +p #72;
    %"chk17" : A = (Check 0 8 Read 8) %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"v76" : L = Ptoi %"v75";
    %"v77" : L = Ptoi #0;
    %"v78" : W = (Cmp Ne L) %"v76", %"v77"
    => goto "L70";
  @"L70" [%"v80" : W = phi("L47" => #0, "L69" => %"v78")]:
    => br %"v80" ? "L54" : "L55";
  @"L54":
    %"v86" = %"v0" +p #160;
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk19" : A = (Check 0 8 Read 8) %"v87";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk19";
    call %"v89" : W = $"glibc_wgenops#save_for_wbackup"(P %"v0", P %"v88")
    => br %"v89" ? "L81" : "L56";
  @"L81":
    => ret #4294967295;
  @"L55":
    %"v95" = %"v0" +p #160;
    %"v96" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v97" = %"v96" +p #72;
    %"chk21" : A = (Check 0 8 Read 8) %"v97";
    %"v98" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v99" : L = Ptoi %"v98";
    %"v100" : L = Ptoi #0;
    %"v102" : W = (Cmp Eq L) %"v99", %"v100"
    => br %"v102" ? "L91" : "L56";
  @"L91":
    call %"v108" : P = $"malloc"(L #512);
    %"v113" : L = Ptoi %"v108";
    %"v115" : W = (Cmp Eq L) %"v113", %"v100"
    => br %"v115" ? "L109" : "L111";
  @"L109":
    => ret #4294967295;
  @"L111":
    %"v118" = %"v0" +p #160;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk0", %"v118";
    %"v119" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v120" = %"v119" +p #64;
    %"chk23" : A = (Check 0 8 Write 8) %"v120";
    store.ptr [%"chk23" + 0] <- %"v108";
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v118";
    %"v124" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v125" = %"v124" +p #80;
    %"v128" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v129" = %"v128" +p #64;
    %"chk26" : A = (Check 0 8 Read 8) %"v129";
    %"v130" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v134" = %"v130" +p #512;
    %"chk27" : A = (Check 0 8 Write 8) %"v125";
    store.ptr [%"chk27" + 0] <- %"v134";
    %"chk28" : A = (Renew 0 8 Read 8) %"chk0", %"v118";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v138" = %"v137" +p #72;
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"v142" = %"v141" +p #80;
    %"chk30" : A = (Check 0 8 Read 8) %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"chk31" : A = (Check 0 8 Write 8) %"v138";
    store.ptr [%"chk31" + 0] <- %"v143"
    => goto "L56";
  @"L56":
    %"v145" = %"v0" +p #160;
    %"chk32" : A = (Renew 0 8 Read 8) %"chk0", %"v145";
    %"v146" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"v147" = %"v146" +p #16;
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk34" : A = (Check 0 8 Read 8) %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"chk35" : A = (Check 0 8 Write 8) %"v147";
    store.ptr [%"chk35" + 0] <- %"v151";
    call void $"__GI__IO_switch_to_wbackup_area"(P %"v0")
    => goto "L49";
  @"L48":
    %"v157" = %"v0" +p #160;
    %"v158" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk37" : A = (Check 0 8 Read 8) %"v158";
    %"v159" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v163" = %"v162" +p #16;
    %"chk39" : A = (Check 0 8 Read 8) %"v163";
    %"v164" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v165" : L = Ptoi %"v159";
    %"v166" : L = Ptoi %"v164";
    %"v167" : W = (Cmp Ule L) %"v165", %"v166"
    => br %"v167" ? "L153" : "L49";
  @"L153":
    %"v171" = %"v0" +p #160;
    %"v172" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v173" = %"v172" +p #8;
    %"chk41" : A = (Check 0 8 Read 8) %"v173";
    %"v174" : P = (RawLoadPointer 0 load_effects) %"chk41";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v178" = %"v177" +p #16;
    %"chk43" : A = (Check 0 8 Read 8) %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"v180" : L = Ptoi %"v174";
    %"v181" : L = Ptoi %"v179";
    %"v182" : L = Sub %"v180", %"v181";
    %"v183" : L = Div %"v182", #4;
    %"v186" : L = Shl %"v183", #1;
    %"v188" : L = Shl %"v186", #2;
    call %"v189" : P = $"malloc"(L %"v188");
    %"v194" : L = Ptoi %"v189";
    %"v195" : L = Ptoi #0;
    %"v196" : W = (Cmp Eq L) %"v194", %"v195"
    => br %"v196" ? "L190" : "L192";
  @"L190":
    => ret #4294967295;
  @"L192":
    %"v201" : L = Sub %"v186", %"v183";
    %"v202" : L = Shl %"v201", #2;
    %"v203" = %"v189" +p %"v202";
    %"v205" = %"v0" +p #160;
    %"chk44" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk44";
    %"v207" = %"v206" +p #16;
    %"chk45" : A = (Check 0 8 Read 8) %"v207";
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk45";
    call %"v210" : P = $"__wmemcpy"(P %"v203", P %"v208", L %"v183");
    %"chk46" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v213" : P = (RawLoadPointer 0 load_effects) %"chk46";
    %"v214" = %"v213" +p #16;
    %"chk47" : A = (Check 0 8 Read 8) %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk47";
    call void $"free"(P %"v215");
    %"chk48" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk48";
    %"v219" = %"v218" +p #16;
    %"chk49" : A = (Check 0 8 Write 8) %"v219";
    store.ptr [%"chk49" + 0] <- %"v189";
    %"chk50" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk50";
    %"chk51" : A = (Check 0 8 Write 8) %"v223";
    store.ptr [%"chk51" + 0] <- %"v203";
    %"chk52" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk52";
    %"v233" = %"v232" +p #8;
    %"v237" = %"v189" +p %"v188";
    %"chk53" : A = (Check 0 8 Write 8) %"v233";
    store.ptr [%"chk53" + 0] <- %"v237";
    %"chk54" : A = (Renew 0 8 Read 8) %"chk0", %"v205";
    %"v240" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"v241" = %"v240" +p #72;
    %"v244" : P = (RawLoadPointer 0 load_effects) %"chk54";
    %"chk56" : A = (Check 0 8 Read 8) %"v244";
    %"v245" : P = (RawLoadPointer 0 load_effects) %"chk56";
    %"chk57" : A = (Check 0 8 Write 8) %"v241";
    store.ptr [%"chk57" + 0] <- %"v245"
    => goto "L49";
  @"L49":
    %"v247" = %"v0" +p #160;
    %"chk58" : A = (Renew 0 8 Read 8) %"chk0", %"v247";
    %"v248" : P = (RawLoadPointer 0 load_effects) %"chk58";
    %"chk59" : A = (Check 0 8 Read 8) %"v248";
    %"v249" : P = (RawLoadPointer 0 load_effects) %"chk59";
    (Flight (a "v250") Sub [(FAddress (t "v249")); (FValue (Const 4))] (LowerOf (t "v249")));
    %"chk60" : A = (Renew 0 8 Write 8) %"chk59", %"v248";
    store.ptr [%"chk60" + 0] <- %"v250";
    %"chk61" : A = (Check 0 4 Write 1) %"v250";
    store Ww [%"chk61" + 0] <- %"v2"
    => goto "L6";
  @"L6":
    => ret %"v2"
} }.

Definition fn___GI__IO_wdefault_uflow : func :=
  ir_fn{ "export" "__GI__IO_wdefault_uflow"(P %"v0") -> (RClass W) {
  @"start":
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
    rawcall %"v10" : W = %"chk2"(P %"v0");
    %"v15" : W = (Cmp Eq W) %"v10", #4294967295
    => br %"v15" ? "L11" : "L13";
  @"L11":
    => ret #4294967295;
  @"L13":
    %"v18" = %"v0" +p #160;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v21" = %"v20" +p #4;
    %"chk5" : A = (Renew 0 8 Write 8) %"chk4", %"v19";
    store.ptr [%"chk5" + 0] <- %"v21";
    %"chk6" : A = (Check 0 4 Read 1) %"v20";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk6"
    => ret %"v22"
} }.

Definition fn___GI__IO_wdefault_xsgetn : func :=
  ir_fn{ "export" "__GI__IO_wdefault_xsgetn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    => goto "L10";
  @"L10" [%"pr.3" : P = phi("start" => %"v2", "L95" => %"pr.4"); %"pr.1" : L = phi("start" => %"v4", "L95" => %"pr.2")]:
    %"v16" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v18" = %"v17" +p #8;
    %"chk1" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk3" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v24" : L = Ptoi %"v19";
    %"v25" : L = Ptoi %"v23";
    %"v26" : L = Sub %"v24", %"v25";
    %"v27" : L = Div %"v26", #4;
    %"v32" : W = (Cmp Sgt L) %"v27", #0
    => br %"v32" ? "L28" : "L30";
  @"L28":
    %"v38" : W = (Cmp Ugt L) %"v27", %"pr.1"
    => br %"v38" ? "L35" : "L34";
  @"L34":
    => goto "L35";
  @"L35" [%"pr.8" : L = phi("L34" => %"v27", "L28" => %"pr.1")]:
    %"v44" : W = (Cmp Sgt L) %"pr.8", #20
    => br %"v44" ? "L40" : "L41";
  @"L40":
    %"v47" = %"v0" +p #160;
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk5" : A = (Check 0 8 Read 8) %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk5";
    call %"v51" : P = $"__wmempcpy"(P %"pr.3", P %"v49", L %"pr.8");
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v47";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (Check 0 8 Read 8) %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v57" : L = Shl %"pr.8", #2;
    %"v58" = %"v55" +p %"v57";
    %"chk8" : A = (Renew 0 8 Write 8) %"chk7", %"v54";
    store.ptr [%"chk8" + 0] <- %"v58"
    => goto "L42";
  @"L41":
    %"v63" : W = (Cmp Sle L) %"pr.8", #0
    => br %"v63" ? "L42" : "L60";
  @"L60":
    %"v66" = %"v0" +p #160;
    %"v67" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk10" : A = (Check 0 8 Read 8) %"v67";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk10"
    => goto "L71";
  @"L71" [%"pr.12" : W = phi("L60" => %"pr.8", "L72" => %"v75"); %"pr.11" : P = phi("L60" => %"v68", "L72" => %"v80"); %"pr.7" : P = phi("L60" => %"pr.3", "L72" => %"v78")]:
    %"v75" : W = Sub %"pr.12", #1;
    %"v76" : W = (Cmp Sge W) %"v75", #0
    => br %"v76" ? "L72" : "L73";
  @"L72":
    %"v78" = %"pr.7" +p #4;
    %"v80" = %"pr.11" +p #4;
    %"chk11" : A = (Check 0 4 Read 1) %"pr.11";
    %"v81" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"chk12" : A = (Check 0 4 Write 1) %"pr.7";
    store Ww [%"chk12" + 0] <- %"v81"
    => goto poll "L71";
  @"L73":
    %"v83" = %"v0" +p #160;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"v83";
    %"v84" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"v84";
    store.ptr [%"chk14" + 0] <- %"pr.11"
    => goto "L42";
  @"L42" [%"pr.9" : L = phi("L40" => %"pr.8", "L73" => %"pr.8", "L41" => #0); %"pr.5" : P = phi("L40" => %"v51", "L73" => %"pr.7", "L41" => %"pr.3")]:
    %"v88" : L = Sub %"pr.1", %"pr.9"
    => goto "L30";
  @"L30" [%"pr.4" : P = phi("L42" => %"pr.5", "L10" => %"pr.3"); %"pr.2" : L = phi("L42" => %"v88", "L10" => %"pr.1")]:
    %"v93" : W = (Cmp Eq L) %"pr.2", #0
    => br %"v93" ? "L95" : "L94";
  @"L94":
    call %"v97" : W = $"__GI___wunderflow"(P %"v0");
    %"v98" : W = (Cmp Eq W) %"v97", #4294967295
    => goto "L95";
  @"L95" [%"v100" : W = phi("L30" => #1, "L94" => %"v98")]:
    => br %"v100" ? "L13" : poll "L10";
  @"L13":
    %"v104" : L = Sub %"v4", %"pr.2"
    => ret %"v104"
} }.

Definition fn___GI__IO_wdefault_xsputn : func :=
  ir_fn{ "export" "__GI__IO_wdefault_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"v14" : W = (Cmp Ule L) %"v4", #0
    => br %"v14" ? "L10" : "L16";
  @"L10":
    => ret #0;
  @"L16" [%"pr.7" : L = phi("start" => %"v4", "L103" => %"v118"); %"pr.2" : P = phi("start" => %"v2", "L103" => %"pr.1")]:
    %"v22" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v24" = %"v23" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v29" = %"v28" +p #32;
    %"chk3" : A = (Check 0 8 Read 8) %"v29";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v31" : L = Ptoi %"v25";
    %"v32" : L = Ptoi %"v30";
    %"v33" : L = Sub %"v31", %"v32";
    %"v34" : L = Div %"v33", #4;
    %"v39" : W = (Cmp Sgt L) %"v34", #0
    => br %"v39" ? "L35" : "L37";
  @"L35":
    %"v45" : W = (Cmp Ugt L) %"v34", %"pr.7"
    => br %"v45" ? "L42" : "L41";
  @"L41":
    => goto "L42";
  @"L42" [%"pr.9" : L = phi("L41" => %"v34", "L35" => %"pr.7")]:
    %"v51" : W = (Cmp Sgt L) %"pr.9", #20
    => br %"v51" ? "L47" : "L48";
  @"L47":
    %"v53" = %"v0" +p #160;
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v55" = %"v54" +p #32;
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v59" = %"v58" +p #32;
    %"chk6" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v63" : P = $"__wmempcpy"(P %"v60", P %"pr.2", L %"pr.9");
    %"chk7" : A = (Check 0 8 Write 8) %"v55";
    store.ptr [%"chk7" + 0] <- %"v63";
    %"v66" : L = Shl %"pr.9", #2;
    %"v67" = %"pr.2" +p %"v66"
    => goto "L49";
  @"L48":
    %"v72" : W = (Cmp Sle L) %"pr.9", #0
    => br %"v72" ? "L49" : "L69";
  @"L69":
    %"v75" = %"v0" +p #160;
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v77" = %"v76" +p #32;
    %"chk9" : A = (Check 0 8 Read 8) %"v77";
    %"v78" : P = (RawLoadPointer 0 load_effects) %"chk9"
    => goto "L81";
  @"L81" [%"pr.13" : L = phi("L69" => %"pr.9", "L82" => %"v86"); %"pr.12" : P = phi("L69" => %"v78", "L82" => %"v89"); %"pr.6" : P = phi("L69" => %"pr.2", "L82" => %"v91")]:
    %"v86" : L = Sub %"pr.13", #1;
    %"v87" : W = (Cmp Sge L) %"v86", #0
    => br %"v87" ? "L82" : "L84";
  @"L82":
    %"v89" = %"pr.12" +p #4;
    %"v91" = %"pr.6" +p #4;
    %"chk10" : A = (Check 0 4 Read 1) %"pr.6";
    %"v92" : W = (RawLoad (LdNarrow Sw) 0) %"chk10";
    %"chk11" : A = (Check 0 4 Write 1) %"pr.12";
    store Ww [%"chk11" + 0] <- %"v92"
    => goto poll "L81";
  @"L84":
    %"v94" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v94";
    %"v95" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v96" = %"v95" +p #32;
    %"chk13" : A = (Check 0 8 Write 8) %"v96";
    store.ptr [%"chk13" + 0] <- %"pr.12"
    => goto "L49";
  @"L49" [%"pr.10" : L = phi("L47" => %"pr.9", "L84" => %"pr.9", "L48" => #0); %"pr.4" : P = phi("L47" => %"v67", "L84" => %"pr.6", "L48" => %"pr.2")]:
    %"v100" : L = Sub %"pr.7", %"pr.10"
    => goto "L37";
  @"L37" [%"pr.8" : L = phi("L49" => %"v100", "L16" => %"pr.7"); %"pr.3" : P = phi("L49" => %"pr.4", "L16" => %"pr.2")]:
    %"v105" : W = (Cmp Eq L) %"pr.8", #0
    => br %"v105" ? "L107" : "L106";
  @"L106":
    %"v110" = %"pr.3" +p #4;
    %"chk14" : A = (Check 0 4 Read 1) %"pr.3";
    %"v111" : W = (RawLoad (LdNarrow Sw) 0) %"chk14";
    call %"v112" : W = $"__GI___woverflow"(P %"v0", W %"v111");
    %"v113" : W = (Cmp Eq W) %"v112", #4294967295
    => goto "L107";
  @"L107" [%"v115" : W = phi("L37" => #1, "L106" => %"v113"); %"pr.1" : P = phi("L106" => %"v110", "L37" => %"pr.3")]:
    => br %"v115" ? "L19" : "L103";
  @"L103":
    %"v118" : L = Sub %"pr.8", #1
    => goto poll "L16";
  @"L19":
    %"v121" : L = Sub %"v4", %"pr.8"
    => ret %"v121"
} }.

Definition fn___GI__IO_wdoallocbuf : func :=
  ir_fn{ "export" "__GI__IO_wdoallocbuf"(P %"v0") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v7" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v10" : L = Ptoi %"v9";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L2" : "L4";
  @"L2":
    => ret void;
  @"L4":
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v17" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v18" : W = And %"v17", #2;
    %"v19" : W = (Cmp Eq W) %"v18", #0
    => br %"v19" ? "L13" : "L15";
  @"L13":
    %"v24" = %"v0" +p #160;
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v26" = %"v25" +p #224;
    %"chk4" : A = (Check 0 8 Read 8) %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v28" = %"v27" +p #104;
    %"chk5" : A = (Check 0 8 Read 8) %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : F = CheckFunction %"v29";
    rawcall %"v31" : W = %"chk6"(P %"v0");
    %"v32" : W = (Cmp Ne W) %"v31", #4294967295
    => br %"v32" ? "L20" : "L15";
  @"L20":
    => ret void;
  @"L15":
    %"v36" = %"v0" +p #160;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v36";
    %"v37" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v38" = %"v37" +p #216;
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v42" = %"v41" +p #216;
    %"v43" = %"v42" +p #4;
    call void $"__GI__IO_wsetb"(P %"v0", P %"v38", P %"v43", W #0)
    => ret void
} }.

Definition fn___GI__IO_wsetb : func :=
  ir_fn{ "export" "__GI__IO_wsetb"(P %"v0", P %"v2", P %"v4", W %"v6") -> RVoid {
  @"start":
    %"v12" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v14" = %"v13" +p #48;
    %"chk1" : A = (Check 0 8 Read 8) %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v16" : L = Ptoi %"v15";
    %"v17" : W = (Cmp Ne L) %"v16", #0
    => br %"v17" ? "L18" : "L19";
  @"L18":
    %"v21" = %"v0" +p #116;
    %"chk2" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v21";
    %"v22" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v23" : W = Shl %"v22", #8;
    %"v24" : W = Sar %"v23", #8;
    %"v25" : W = And %"v24", #8;
    %"v26" : W = (Cmp Eq W) %"v25", #0
    => goto "L19";
  @"L19" [%"v28" : W = phi("start" => #0, "L18" => %"v26")]:
    => br %"v28" ? "L8" : "L10";
  @"L8":
    %"v30" = %"v0" +p #160;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v32" = %"v31" +p #48;
    %"chk4" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk4";
    call void $"free"(P %"v33")
    => goto "L10";
  @"L10":
    %"v35" = %"v0" +p #160;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v37" = %"v36" +p #48;
    %"chk6" : A = (Check 0 8 Write 8) %"v37";
    store.ptr [%"chk6" + 0] <- %"v2";
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v35";
    %"v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v42" = %"v41" +p #56;
    %"chk8" : A = (Check 0 8 Write 8) %"v42";
    store.ptr [%"chk8" + 0] <- %"v4"
    => br %"v6" ? "L44" : "L45";
  @"L44":
    %"v49" = %"v0" +p #116;
    %"chk9" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v49";
    %"v50" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v51" : W = Shl %"v50", #8;
    %"v52" : W = Sar %"v51", #8;
    %"v54" : W = And %"v52", #4294967287;
    %"v55" : W = (RawLoad (LdNarrow Sw) 0) %"chk9";
    %"v56" : W = And %"v55", #4278190080;
    %"v57" : W = And %"v54", #16777215;
    %"v58" : W = Or %"v56", %"v57";
    %"chk11" : A = (Renew 0 4 Write 1) %"chk9", %"v49";
    store Ww [%"chk11" + 0] <- %"v58"
    => goto "L46";
  @"L45":
    %"v62" = %"v0" +p #116;
    %"chk12" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v62";
    %"v63" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v64" : W = Shl %"v63", #8;
    %"v65" : W = Sar %"v64", #8;
    %"v66" : W = Or %"v65", #8;
    %"v67" : W = (RawLoad (LdNarrow Sw) 0) %"chk12";
    %"v68" : W = And %"v67", #4278190080;
    %"v69" : W = And %"v66", #16777215;
    %"v70" : W = Or %"v68", %"v69";
    %"chk14" : A = (Renew 0 4 Write 1) %"chk12", %"v62";
    store Ww [%"chk14" + 0] <- %"v70"
    => goto "L46";
  @"L46":
    => ret void
} }.

Definition fn___GI___woverflow : func :=
  ir_fn{ "export" "__GI___woverflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"v8" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v10" : W = (Cmp Eq W) %"v9", #0
    => br %"v10" ? "L36" : "L6";
  @"L36":
    call %"v53" : W = $"_IO_fwide"(P %"v0", W #1)
    => goto "L6";
  @"L6":
    %"v56" = %"v0" +p #216;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v4" : L = Ptoi %"v57";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v59" = %"v57" +p #24;
    %"chk2" : A = (Check 0 8 Read 8) %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : F = CheckFunction %"v60";
    rawcall %"v63" : W = %"chk3"(P %"v0", W %"v2")
    => ret %"v63"
} }.

Definition fn___GI___wunderflow : func :=
  ir_fn{ "export" "__GI___wunderflow"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = (Cmp Slt W) %"v7", #0
    => br %"v8" ? "L10" : "L9";
  @"L9":
    %"v12" = %"v0" +p #192;
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v14" : W = (Cmp Eq W) %"v13", #0
    => br %"v14" ? "L42" : "L10";
  @"L42":
    call %"v59" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v61" : W = (Cmp Ne W) %"v59", #1
    => goto "L10";
  @"L10" [%"v65" : W = phi("start" => #1, "L9" => #0, "L42" => %"v61")]:
    => br %"v65" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v71" = %"v0" +p #192;
    %"chk2" : A = (Renew 0 4 Read 1) %"chk0", %"v71";
    %"v72" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v73" : W = (Cmp Eq W) %"v72", #0
    => br %"v73" ? "L99" : "L69";
  @"L99":
    call %"v116" : W = $"_IO_fwide"(P %"v0", W #1)
    => goto "L69";
  @"L69":
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v122" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v123" : W = And %"v122", #2048
    => br %"v123" ? "L118" : "L120";
  @"L118":
    call %"v128" : W = $"__GI__IO_switch_to_wget_mode"(P %"v0");
    %"v130" : W = (Cmp Eq W) %"v128", #4294967295
    => br %"v130" ? "L124" : "L120";
  @"L124":
    => ret #4294967295;
  @"L120":
    %"v136" = %"v0" +p #160;
    %"chk4" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v136";
    %"v137" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (Check 0 8 Read 8) %"v137";
    %"v138" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v142" = %"v141" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v144" : L = Ptoi %"v138";
    %"v145" : L = Ptoi %"v143";
    %"v146" : W = (Cmp Ult L) %"v144", %"v145"
    => br %"v146" ? "L132" : "L134";
  @"L132":
    %"v148" = %"v0" +p #160;
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk9" : A = (Check 0 8 Read 8) %"v149";
    %"v150" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (Check 0 4 Read 1) %"v150";
    %"v151" : W = (RawLoad (LdNarrow Sw) 0) %"chk10"
    => ret %"v151";
  @"L134":
    %"chk11" : A = (Renew 0 4 Read 1) %"chk3", %"v0";
    %"v157" : W = (RawLoad (LdNarrow Sw) 0) %"chk11";
    %"v158" : W = And %"v157", #256
    => br %"v158" ? "L153" : "L155";
  @"L153":
    call void $"__GI__IO_switch_to_main_wget_area"(P %"v0");
    %"v164" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk4", %"v164";
    %"v165" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (Check 0 8 Read 8) %"v165";
    %"v166" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v170" = %"v169" +p #8;
    %"chk15" : A = (Check 0 8 Read 8) %"v170";
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v172" : L = Ptoi %"v166";
    %"v173" : L = Ptoi %"v171";
    %"v174" : W = (Cmp Ult L) %"v172", %"v173"
    => br %"v174" ? "L160" : "L155";
  @"L160":
    %"v176" = %"v0" +p #160;
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk17" : A = (Check 0 8 Read 8) %"v177";
    %"v178" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 4 Read 1) %"v178";
    %"v179" : W = (RawLoad (LdNarrow Sw) 0) %"chk18"
    => ret %"v179";
  @"L155":
    %"v185" = %"v0" +p #96;
    %"chk19" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v185";
    %"v186" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v187" : L = Ptoi %"v186";
    %"v188" : L = Ptoi #0;
    %"v189" : W = (Cmp Ne L) %"v187", %"v188"
    => br %"v189" ? "L181" : "L182";
  @"L181":
    %"v195" = %"v0" +p #160;
    %"chk20" : A = (Renew 0 8 Read 8) %"chk4", %"v195";
    %"v196" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v197" = %"v196" +p #8;
    %"chk21" : A = (Check 0 8 Read 8) %"v197";
    %"v198" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v199" : W = $"glibc_wgenops#save_for_wbackup"(P %"v0", P %"v198")
    => br %"v199" ? "L190" : "L183";
  @"L190":
    => ret #4294967295;
  @"L182":
    %"v205" = %"v0" +p #160;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk4", %"v205";
    %"v206" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"v207" = %"v206" +p #72;
    %"chk23" : A = (Check 0 8 Read 8) %"v207";
    %"v208" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v209" : L = Ptoi %"v208";
    %"v211" : W = (Cmp Ne L) %"v209", %"v188"
    => br %"v211" ? "L201" : "L183";
  @"L201":
    call void $"__GI__IO_free_wbackup_area"(P %"v0")
    => goto "L183";
  @"L183":
    %"v214" = %"v0" +p #216;
    %"chk24" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v214";
    %"v215" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"iw_1.v4" : L = Ptoi %"v215";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v217" = %"v215" +p #32;
    %"chk25" : A = (Check 0 8 Read 8) %"v217";
    %"v218" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"chk26" : F = CheckFunction %"v218";
    rawcall %"v220" : W = %"chk26"(P %"v0")
    => ret %"v220"
} }.

Definition fn_glibc_wgenops'23save_for_wbackup : func :=
  ir_fn{ "local" "glibc_wgenops#save_for_wbackup"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    call %"v7" : L = $"__GI__IO_least_wmarker"(P %"v0", P %"v2");
    %"v11" = %"v0" +p #160;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #16;
    %"chk1" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v15" : L = Ptoi %"v2";
    %"v16" : L = Ptoi %"v14";
    %"v17" : L = Sub %"v15", %"v16";
    %"v18" : L = Div %"v17", #4;
    %"v20" : L = Sub %"v18", %"v7";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v25" = %"v24" +p #80;
    %"chk3" : A = (Check 0 8 Read 8) %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v30" = %"v29" +p #64;
    %"chk5" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v32" : L = Ptoi %"v26";
    %"v33" : L = Ptoi %"v31";
    %"v34" : L = Sub %"v32", %"v33";
    %"v35" : L = Div %"v34", #4;
    %"v44" : W = (Cmp Ugt L) %"v20", %"v35"
    => br %"v44" ? "L39" : "L40";
  @"L39":
    %"v48" : L = Add %"v20", #100;
    %"v49" : L = Shl %"v48", #2;
    call %"v50" : P = $"malloc"(L %"v49");
    %"v55" : L = Ptoi %"v50";
    %"v56" : L = Ptoi #0;
    %"v57" : W = (Cmp Eq L) %"v55", %"v56"
    => br %"v57" ? "L51" : "L53";
  @"L51":
    => ret #4294967295;
  @"L53":
    %"v64" : W = (Cmp Slt L) %"v7", #0
    => br %"v64" ? "L60" : "L61";
  @"L60":
    %"v68" = %"v50" +p #400;
    %"v70" = %"v0" +p #160;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk0", %"v70";
    %"v71" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v72" = %"v71" +p #80;
    %"chk7" : A = (Check 0 8 Read 8) %"v72";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v75" : L = Shl %"v7", #2;
    %"v76" = %"v73" +p %"v75";
    %"v78" : L = Neg %"v7";
    call %"v79" : P = $"__wmempcpy"(P %"v68", P %"v76", L %"v78");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk0", %"v70";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" = %"v82" +p #16;
    %"chk9" : A = (Check 0 8 Read 8) %"v83";
    %"v84" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v88" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v89" = %"v88" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"v89";
    %"v90" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"v92" : L = Ptoi %"v90";
    %"v93" : L = Sub %"v15", %"v92";
    %"v94" : L = Div %"v93", #4;
    call %"v95" : P = $"__wmempcpy"(P %"v79", P %"v84", L %"v94")
    => goto "L62";
  @"L61":
    %"v99" = %"v50" +p #400;
    %"v101" = %"v0" +p #160;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk0", %"v101";
    %"v102" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"v103" = %"v102" +p #16;
    %"chk13" : A = (Check 0 8 Read 8) %"v103";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"v106" : L = Shl %"v7", #2;
    %"v107" = %"v104" +p %"v106";
    call %"v109" : P = $"__wmemcpy"(P %"v99", P %"v107", L %"v20")
    => goto "L62";
  @"L62":
    %"v111" = %"v0" +p #160;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v112" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"v113" = %"v112" +p #64;
    %"chk15" : A = (Check 0 8 Read 8) %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call void $"free"(P %"v114");
    %"chk16" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v118" = %"v117" +p #64;
    %"chk17" : A = (Check 0 8 Write 8) %"v118";
    store.ptr [%"chk17" + 0] <- %"v50";
    %"chk18" : A = (Renew 0 8 Read 8) %"chk0", %"v111";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v123" = %"v122" +p #80;
    %"v127" = %"v50" +p #400;
    %"v129" : L = Shl %"v20", #2;
    %"v130" = %"v127" +p %"v129";
    %"chk19" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk19" + 0] <- %"v130"
    => goto "L41";
  @"L40":
    %"v133" : L = Sub %"v35", %"v20";
    %"v138" : W = (Cmp Slt L) %"v7", #0
    => br %"v138" ? "L134" : "L135";
  @"L134":
    %"v140" = %"v0" +p #160;
    %"v141" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v142" = %"v141" +p #64;
    %"chk21" : A = (Check 0 8 Read 8) %"v142";
    %"v143" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v145" : L = Shl %"v133", #2;
    %"v146" = %"v143" +p %"v145";
    %"v149" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v150" = %"v149" +p #80;
    %"chk23" : A = (Check 0 8 Read 8) %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"v153" : L = Shl %"v7", #2;
    %"v154" = %"v151" +p %"v153";
    %"v156" : L = Neg %"v7";
    call %"v157" : P = $"__wmemmove"(P %"v146", P %"v154", L %"v156");
    %"chk24" : A = (Renew 0 8 Read 8) %"chk0", %"v140";
    %"v160" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v161" = %"v160" +p #64;
    %"chk25" : A = (Check 0 8 Read 8) %"v161";
    %"v162" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v165" = %"v162" +p %"v145";
    (Flight (a "v168") Sub [(FAddress (t "v165")); (FValue (t "v153"))] (LowerOf (t "v165")));
    %"v171" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v172" = %"v171" +p #16;
    %"chk27" : A = (Check 0 8 Read 8) %"v172";
    %"v173" : P = (RawLoadPointer 0 load_effects) %"chk27";
    %"v177" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v178" = %"v177" +p #16;
    %"chk29" : A = (Check 0 8 Read 8) %"v178";
    %"v179" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"v181" : L = Ptoi %"v179";
    %"v182" : L = Sub %"v15", %"v181";
    %"v183" : L = Div %"v182", #4;
    call %"v184" : P = $"__wmemcpy"(P %"v168", P %"v173", L %"v183")
    => goto "L41";
  @"L135":
    %"v189" : W = (Cmp Ugt L) %"v20", #0
    => br %"v189" ? "L185" : "L41";
  @"L185":
    %"v191" = %"v0" +p #160;
    %"v192" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v193" = %"v192" +p #64;
    %"chk31" : A = (Check 0 8 Read 8) %"v193";
    %"v194" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"v196" : L = Shl %"v133", #2;
    %"v197" = %"v194" +p %"v196";
    %"v200" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v201" = %"v200" +p #16;
    %"chk33" : A = (Check 0 8 Read 8) %"v201";
    %"v202" : P = (RawLoadPointer 0 load_effects) %"chk33";
    %"v204" : L = Shl %"v7", #2;
    %"v205" = %"v202" +p %"v204";
    call %"v207" : P = $"__wmemcpy"(P %"v197", P %"v205", L %"v20")
    => goto "L41";
  @"L41" [%"pr.1" : L = phi("L62" => #100, "L134" => %"v133", "L185" => %"v133", "L135" => %"v133")]:
    %"v209" = %"v0" +p #160;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk0", %"v209";
    %"v210" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v211" = %"v210" +p #72;
    %"v214" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"v215" = %"v214" +p #64;
    %"chk36" : A = (Check 0 8 Read 8) %"v215";
    %"v216" : P = (RawLoadPointer 0 load_effects) %"chk36";
    %"v218" : L = Shl %"pr.1", #2;
    %"v219" = %"v216" +p %"v218";
    %"chk37" : A = (Check 0 8 Write 8) %"v211";
    store.ptr [%"chk37" + 0] <- %"v219";
    %"chk38" : A = (Renew 0 8 Read 8) %"chk0", %"v209";
    %"v223" : P = (RawLoadPointer 0 load_effects) %"chk38";
    %"v224" = %"v223" +p #16;
    %"chk39" : A = (Check 0 8 Read 8) %"v224";
    %"v225" : P = (RawLoadPointer 0 load_effects) %"chk39";
    %"v227" : L = Ptoi %"v225";
    %"v228" : L = Sub %"v15", %"v227";
    %"v229" : L = Div %"v228", #4;
    %"v231" = %"v0" +p #96;
    %"chk40" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v231";
    %"v232" : P = (RawLoadPointer 0 load_effects) %"chk40"
    => goto "L233";
  @"L233" [%"pr.2" : P = phi("L234" => %"v248", "L41" => %"v232")]:
    %"v238" : L = Ptoi %"pr.2";
    %"v239" : L = Ptoi #0;
    %"v240" : W = (Cmp Ne L) %"v238", %"v239"
    => br %"v240" ? "L234" : "L236";
  @"L234":
    %"v242" = %"pr.2" +p #16;
    %"chk41" : A = (Check 0 4 Read 1) %"v242";
    %"v243" : W = (RawLoad (LdNarrow Sw) 0) %"chk41";
    %"v245" : L = (Ext Sw) %"v243";
    %"v246" : L = Sub %"v245", %"v229";
    %"chk42" : A = (Renew 0 4 Write 1) %"chk41", %"v242";
    store Ww [%"chk42" + 0] <- %"v246";
    %"chk43" : A = (HalfCheck Lower 0 8 Read 8) %"chk41", %"pr.2";
    %"v248" : P = (RawLoadPointer 0 load_effects) %"chk43"
    => goto poll "L233";
  @"L236":
    => ret #0
} }.
