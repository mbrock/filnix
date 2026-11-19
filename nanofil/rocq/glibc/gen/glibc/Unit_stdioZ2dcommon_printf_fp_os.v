(** This file defines checked IR from glibc’s `stdio-common/printf_fp.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation Unit_stdioZ2dcommon_printf_fp_os_Blocks_676c6962635f7072696e74665f6670235f5f7072696e74665f66705f6275666665725f31_1 Unit_stdioZ2dcommon_printf_fp_os_Blocks_676c6962635f7072696e74665f6670235f5f7072696e74665f66705f6275666665725f31_2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fn___printf_buffer_flush_fp : func :=
  ir_fn{ "export" "__printf_buffer_flush_fp"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #80
    => goto "L5";
  @"L5" [%"pr.8" : W = phi("L7" => %"pr.5", "start" => #0); %"pr.1" : P = phi("L7" => %"v108", "start" => %"v4")]:
    %"v11" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" : L = Ptoi %"pr.1";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ult L) %"v13", %"v14"
    => br %"v15" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v25" : W = (Cmp Eq W) %"v18", #44
    => br %"v25" ? "L21" : "L22";
  @"L21":
    %"v27" = %"v0" +p #40;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" = %"v0" +p #57;
    %"chk3" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v30";
    %"v31" : W = (RawLoad (LdNarrow Ub) 0) %"chk3"
    => goto "L23";
  @"L22":
    %"v36" : W = (Cmp Eq W) %"v18", #46
    => br %"v36" ? "L32" : "L33";
  @"L32":
    %"v38" = %"v0" +p #48;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v41" = %"v0" +p #56;
    %"chk5" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v41";
    %"v42" : W = (RawLoad (LdNarrow Ub) 0) %"chk5"
    => goto "L23";
  @"L33":
    %"v47" = %"v0" +p #72;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v49" : L = Ptoi %"v48";
    %"v50" : L = Ptoi #0;
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L52" : "L53";
  @"L52":
    %"v55" : W = (Cmp Sge W) %"v18", #48
    => goto "L53";
  @"L53" [%"v57" : W = phi("L33" => #0, "L52" => %"v55")]:
    => br %"v57" ? "L58" : "L59";
  @"L58":
    %"v61" : W = (Cmp Sle W) %"v18", #57
    => goto "L59";
  @"L59" [%"v63" : W = phi("L53" => #0, "L58" => %"v61")]:
    => br %"v63" ? "L43" : "L23";
  @"L43":
    %"v66" : W = Sub %"v18", #48;
    %"v68" = %"v0" +p #72;
    %"v69" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v70" = %"v69" +p #56;
    %"v73" : W = Add %"v66", #41;
    %"v74" : L = (Ext Sw) %"v73";
    %"v75" : L = Shl %"v74", #3;
    %"v76" = %"v70" +p %"v75";
    %"chk8" : A = (Check 0 8 Read 8) %"v76";
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v82" = %"v81" +p #32;
    %"chk10" : A = (Check 0 8 Read 8) %"v82";
    %"v83" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"v85" = %"v83" +p #9;
    %"v87" : L = (Ext Sw) %"v66";
    %"v88" = %"v85" +p %"v87";
    %"chk11" : A = (Check 0 1 Read 1) %"v88";
    %"v89" : W = (RawLoad (LdNarrow Ub) 0) %"chk11"
    => goto "L23";
  @"L23" [%"pr.5" : W = phi("L21" => %"v31", "L32" => %"v42", "L43" => %"v89", "L59" => %"pr.8"); %"pr.2" : P = phi("L21" => %"v28", "L32" => %"v39", "L43" => %"v77", "L59" => #0)]:
    %"v94" : L = Ptoi %"pr.2";
    %"v95" : L = Ptoi #0;
    %"v96" : W = (Cmp Eq L) %"v94", %"v95"
    => br %"v96" ? "L90" : "L91";
  @"L90":
    %"v98" = %"v0" +p #64;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v98";
    %"v99" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v8" = %"v99" +p #8;
    %"chk13" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v11" = %"v99" +p #16;
    %"chk14" : A = (HalfCheck Upper 0 8 Read 8) %"chk13", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v99" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v19" = %"iw_1.v18" +p #1;
    %"chk16" : A = (Renew 0 8 Write 8) %"chk13", %"iw_1.v17";
    store.ptr [%"chk16" + 0] <- %"iw_1.v19";
    %"chk17" : A = (Check 0 1 Write 1) %"iw_1.v18";
    store Wb [%"chk17" + 0] <- %"v18"
    => goto "L7";
  @"iw_1.L5":
    call void $"__printf_buffer_putc_1"(P %"v99", W %"v18")
    => goto "L7";
  @"L91":
    %"v102" = %"v0" +p #64;
    %"chk18" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v102";
    %"v103" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v106" : L = (Ext Uw) %"pr.5";
    call void $"__printf_buffer_write"(P %"v103", P %"pr.2", L %"v106")
    => goto "L7";
  @"L7":
    %"v108" = %"pr.1" +p #1
    => goto poll "L5";
  @"L8":
    %"v113" = %"v0" +p #64;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v113";
    %"v114" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_2.v3" = %"v114" +p #32;
    %"chk20" : A = (Check 0 4 Read 1) %"iw_2.v3";
    %"iw_2.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk20";
    %"v117" : W = (Cmp Ne W) %"iw_2.v4", #0
    => br %"v117" ? "L109" : "iw_3.start";
  @"L109":
    %"v119" = %"v0" +p #8;
    %"v121" = %"v0" +p #80;
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"v119";
    store.ptr [%"chk21" + 0] <- %"v121"
    => goto "L111";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk22" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk22" + 0] <- #0
    => goto "L111";
  @"L111":
    => ret void
} }.

Definition fn___printf_buffer_flush_fp_to_wide : func :=
  ir_fn{ "export" "__printf_buffer_flush_fp_to_wide"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #64
    => goto "L5";
  @"L5" [%"pr.1" : P = phi("L7" => %"v79", "start" => %"v4")]:
    %"v11" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" : L = Ptoi %"pr.1";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ult L) %"v13", %"v14"
    => br %"v15" ? "L6" : "L8";
  @"L6":
    %"chk1" : A = (Check 0 1 Read 1) %"pr.1";
    %"v18" : W = (RawLoad (LdNarrow Sb) 0) %"chk1";
    %"v23" : W = (Cmp Eq W) %"v18", #44
    => br %"v23" ? "L19" : "L20";
  @"L19":
    %"v25" = %"v0" +p #40;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v25";
    %"v26" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v31" : W = (Cmp Eq W) %"v26", #0
    => br %"v31" ? "L7" : "L21";
  @"L20":
    %"v37" : W = (Cmp Eq W) %"v18", #46
    => br %"v37" ? "L33" : "L34";
  @"L33":
    %"v39" = %"v0" +p #44;
    %"chk3" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v39";
    %"v40" : W = (RawLoad (LdNarrow Sw) 0) %"chk3"
    => goto "L21";
  @"L34":
    %"v45" = %"v0" +p #56;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v47" : L = Ptoi %"v46";
    %"v48" : L = Ptoi #0;
    %"v49" : W = (Cmp Ne L) %"v47", %"v48"
    => br %"v49" ? "L50" : "L51";
  @"L50":
    %"v53" : W = (Cmp Sge W) %"v18", #48
    => goto "L51";
  @"L51" [%"v55" : W = phi("L34" => #0, "L50" => %"v53")]:
    => br %"v55" ? "L56" : "L57";
  @"L56":
    %"v59" : W = (Cmp Sle W) %"v18", #57
    => goto "L57";
  @"L57" [%"v61" : W = phi("L51" => #0, "L56" => %"v59")]:
    => br %"v61" ? "L41" : "L21";
  @"L41":
    %"v63" = %"v0" +p #56;
    %"v64" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v65" = %"v64" +p #56;
    %"v68" : W = Add %"v18", #51;
    %"v69" : W = Sub %"v68", #48;
    %"v70" : L = (Ext Sw) %"v69";
    %"v71" : L = Shl %"v70", #3;
    %"v72" = %"v65" +p %"v71";
    %"chk6" : A = (Check 0 4 Read 1) %"v72";
    %"v73" : W = (RawLoad (LdNarrow Uw) 0) %"chk6"
    => goto "L21";
  @"L21" [%"pr.2" : W = phi("L19" => %"v26", "L33" => %"v40", "L41" => %"v73", "L57" => %"v18")]:
    %"v75" = %"v0" +p #48;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v8" = %"v76" +p #8;
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v11" = %"v76" +p #16;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk8", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v76" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk11" : A = (Renew 0 8 Write 8) %"chk8", %"iw_1.v17";
    store.ptr [%"chk11" + 0] <- %"iw_1.v19";
    %"chk12" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk12" + 0] <- %"pr.2"
    => goto "L7";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v76", W %"pr.2")
    => goto "L7";
  @"L7":
    %"v79" = %"pr.1" +p #1
    => goto poll "L5";
  @"L8":
    %"v84" = %"v0" +p #48;
    %"chk13" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v84";
    %"v85" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_2.v3" = %"v85" +p #32;
    %"chk14" : A = (Check 0 4 Read 1) %"iw_2.v3";
    %"iw_2.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk14";
    %"v88" : W = (Cmp Ne W) %"iw_2.v4", #0
    => br %"v88" ? "L80" : "iw_3.start";
  @"L80":
    %"v90" = %"v0" +p #8;
    %"v92" = %"v0" +p #64;
    %"chk15" : A = (Renew 0 8 Write 8) %"chk0", %"v90";
    store.ptr [%"chk15" + 0] <- %"v92"
    => goto "L82";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk16" + 0] <- #0
    => goto "L82";
  @"L82":
    => ret void
} }.

Definition fn___printf_fp_l_buffer : func :=
  ir_fn{ "export" "__printf_fp_l_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #144;
    %"v13" = %"v4" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v15" : W = Shl %"v14", #23;
    %"v16" : W = Shr %"v15", #31
    => br %"v16" ? "L9" : "L10";
  @"L9":
    %"v17" = %"v8" +p #40;
    %"iw_1.v10" = %"v2" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" = %"iw_1.v11" +p #56;
    %"iw_1.v17" = %"iw_1.v12" +p #24;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v17";
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Write 8) %"v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v18";
    %"v20" = %"v8" +p #48;
    %"iw_2.v10" = %"v2" +p #32;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v10";
    %"iw_2.v11" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_2.v12" = %"iw_2.v11" +p #56;
    %"iw_2.v17" = %"iw_2.v12" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_2.v17";
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Upper 0 8 Write 8) %"chk3", %"v20";
    store.ptr [%"chk6" + 0] <- %"iw_2.v18";
    %"v26" = %"v8" +p #48;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk6", %"v26";
    %"v27" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 1 Read 1) %"v27";
    %"v29" : W = (RawLoad (LdNarrow Sb) 0) %"chk8";
    %"v30" : W = (Cmp Eq W) %"v29", #0
    => br %"v30" ? "L23" : "L11";
  @"L23":
    %"v31" = %"v8" +p #48;
    %"iw_3.v10" = %"v2" +p #8;
    %"chk9" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"iw_3.v10";
    %"iw_3.v11" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_3.v12" = %"iw_3.v11" +p #56;
    %"chk10" : A = (Check 0 8 Read 8) %"iw_3.v12";
    %"iw_3.v18" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Renew 0 8 Write 8) %"chk6", %"v31";
    store.ptr [%"chk11" + 0] <- %"iw_3.v18"
    => goto "L11";
  @"L10":
    %"v34" = %"v8" +p #40;
    %"iw_4.v10" = %"v2" +p #8;
    %"chk12" : A = (Check 0 8 Read 8) %"iw_4.v10";
    %"iw_4.v11" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_4.v12" = %"iw_4.v11" +p #56;
    %"iw_4.v17" = %"iw_4.v12" +p #8;
    %"chk13" : A = (Check 0 8 Read 8) %"iw_4.v17";
    %"iw_4.v18" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"v34";
    store.ptr [%"chk14" + 0] <- %"iw_4.v18";
    %"v37" = %"v8" +p #48;
    %"iw_5.v10" = %"v2" +p #8;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk12", %"iw_5.v10";
    %"iw_5.v11" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_5.v12" = %"iw_5.v11" +p #56;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_5.v12";
    %"iw_5.v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Upper 0 8 Write 8) %"chk14", %"v37";
    store.ptr [%"chk17" + 0] <- %"iw_5.v18"
    => goto "L11";
  @"L11":
    %"v40" = %"v8" +p #57;
    %"v41" = %"v8" +p #40;
    %"chk18" : A = (Check 0 8 Read 8) %"v41";
    %"v42" : P = (RawLoadPointer 0 load_effects) %"chk18";
    call %"v43" : L = $"__GI_strlen"(P %"v42");
    %"v44" : W = (Ext Ub) %"v43";
    %"chk19" : A = (HalfCheck Upper 0 1 Write 1) %"chk18", %"v40";
    store Wb [%"chk19" + 0] <- %"v44";
    %"v48" = %"v8" +p #48;
    %"chk20" : A = (HalfCheck Upper 0 8 Read 8) %"chk18", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v50" = %"v49" +p #1;
    %"chk21" : A = (Check 0 1 Read 1) %"v50";
    %"v51" : W = (RawLoad (LdNarrow Sb) 0) %"chk21";
    %"v52" : W = (Cmp Eq W) %"v51", #0
    => br %"v52" ? "L53" : "L54";
  @"L53":
    %"v55" = %"v8" +p #57;
    %"v56" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    %"v57" : W = (Cmp Sle W) %"v56", #1
    => goto "L54";
  @"L54" [%"v59" : W = phi("L11" => #0, "L53" => %"v57")]:
    => br %"v59" ? "L60" : "L61";
  @"L60":
    %"v63" = %"v4" +p #12;
    %"chk23" : A = (Renew 0 4 Read 1) %"chk0", %"v63";
    %"v64" : W = (RawLoad (LdNarrow Uw) 0) %"chk23";
    %"v65" : W = Shl %"v64", #20;
    %"v66" : W = Shr %"v65", #31;
    %"v67" : W = (Cmp Eq W) %"v66", #0
    => goto "L61";
  @"L61" [%"v69" : W = phi("L54" => #0, "L60" => %"v67")]:
    => br %"v69" ? "L45" : "L47";
  @"L45":
    %"v72" = %"v8" +p #40;
    %"chk24" : A = (Renew 0 8 Read 8) %"chk18", %"v72";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"chk25" : A = (Check 0 1 Read 1) %"v73";
    %"v75" : W = (RawLoad (LdNarrow Sb) 0) %"chk25";
    %"v76" = %"v8" +p #48;
    %"v77" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk27" : A = (Check 0 1 Read 1) %"v77";
    %"v79" : W = (RawLoad (LdNarrow Sb) 0) %"chk27";
    %"v80" = %"v8" +p #57;
    %"v81" : W = (RawLoad (LdNarrow Ub) 0) %"chk19";
    call void $"glibc_printf_fp#__printf_fp_buffer_1"(P %"v0", P %"v2", W %"v75", W %"v79", W %"v81", P %"v4", P %"v6")
    => ret void;
  @"L47":
    %"v85" = %"v8" +p #56;
    %"v86" = %"v8" +p #48;
    %"v87" : P = (RawLoadPointer 0 load_effects) %"chk20";
    call %"v88" : L = $"__GI_strlen"(P %"v87");
    %"v89" : W = (Ext Ub) %"v88";
    %"chk30" : A = (HalfCheck Upper 0 1 Write 1) %"chk18", %"v85";
    store Wb [%"chk30" + 0] <- %"v89";
    %"v94" = %"v4" +p #12;
    %"chk31" : A = (Renew 0 4 Read 1) %"chk0", %"v94";
    %"v95" : W = (RawLoad (LdNarrow Uw) 0) %"chk31";
    %"v96" : W = Shl %"v95", #20;
    %"v97" : W = Shr %"v96", #31
    => br %"v97" ? "L90" : "L91";
  @"L90":
    %"v98" = %"v8" +p #72;
    %"chk32" : A = (Check 0 8 Read 8) %"v2";
    %"v101" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (HalfCheck Upper 0 8 Write 8) %"chk18", %"v98";
    store.ptr [%"chk33" + 0] <- %"v101"
    => goto "L92";
  @"L91":
    %"v102" = %"v8" +p #72;
    %"chk34" : A = (HalfCheck Upper 0 8 Write 8) %"chk18", %"v102";
    store.ptr [%"chk34" + 0] <- #0
    => goto "L92";
  @"L92":
    %"v103" = %"v8" +p #64;
    %"chk35" : A = (HalfCheck Upper 0 8 Write 8) %"chk18", %"v103";
    store.ptr [%"chk35" + 0] <- %"v0";
    %"v105" = %"v8" +p #80;
    %"iw_6.v12" = %"v105" +p #64;
    %"chk36" : A = (HalfCheck Lower 0 8 Write 8) %"chk18", %"v8";
    store.ptr [%"chk36" + 0] <- %"v105";
    %"iw_6.iw_1.v11" = %"v8" +p #8;
    %"chk37" : A = (HalfCheck Lower 0 8 Write 8) %"chk18", %"iw_6.iw_1.v11";
    store.ptr [%"chk37" + 0] <- %"v105";
    %"iw_6.iw_1.v14" = %"v8" +p #16;
    %"chk38" : A = (HalfCheck Lower 0 8 Write 8) %"chk18", %"iw_6.iw_1.v14";
    store.ptr [%"chk38" + 0] <- %"iw_6.v12";
    %"iw_6.iw_1.v17" = %"v8" +p #24;
    %"chk39" : A = (HalfCheck Lower 0 8 Write 1) %"chk18", %"iw_6.iw_1.v17";
    store Wl [%"chk39" + 0] <- #0;
    %"iw_6.iw_1.v19" = %"v8" +p #32;
    %"chk40" : A = (HalfCheck Lower 0 4 Write 1) %"chk18", %"iw_6.iw_1.v19";
    store Ww [%"chk40" + 0] <- #8;
    %"v107" = %"v8" +p #57;
    %"chk41" : A = (Renew 0 1 Read 1) %"chk19", %"v107";
    %"v108" : W = (RawLoad (LdNarrow Ub) 0) %"chk41";
    call void $"glibc_printf_fp#__printf_fp_buffer_1"(P %"v8", P %"v2", W #44, W #46, W %"v108", P %"v4", P %"v6");
    %"iw_7.v3" = %"v8" +p #32;
    %"chk42" : A = (Renew 0 4 Read 1) %"chk40", %"iw_7.v3";
    %"iw_7.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk42";
    %"iw_7.v5" : W = (Cmp Eq W) %"iw_7.v4", #0
    => br %"iw_7.v5" ? "L111" : "L113";
  @"L111":
    %"v116" = %"v8" +p #64;
    %"chk43" : A = (Renew 0 8 Read 8) %"chk35", %"v116";
    %"v117" : P = (RawLoadPointer 0 load_effects) %"chk43";
    %"iw_8.v3" = %"v117" +p #32;
    %"chk44" : A = (Check 0 4 Write 1) %"iw_8.v3";
    store Ww [%"chk44" + 0] <- #0
    => ret void;
  @"L113":
    call void $"__printf_buffer_flush_fp"(P %"v8")
    => ret void
} }.

Definition fn___wprintf_fp_l_buffer : func :=
  ir_fn{ "export" "__wprintf_fp_l_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #128;
    %"v13" = %"v4" +p #12;
    %"chk0" : A = (Check 0 4 Read 1) %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v15" : W = Shl %"v14", #23;
    %"v16" : W = Shr %"v15", #31
    => br %"v16" ? "L9" : "L10";
  @"L9":
    %"v17" = %"v8" +p #44;
    %"iw_1.v10" = %"v2" +p #32;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" = %"iw_1.v11" +p #56;
    %"iw_1.v17" = %"iw_1.v12" +p #344;
    %"chk2" : A = (Check 0 4 Read 1) %"iw_1.v17";
    %"iw_1.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"chk3" : A = (Check 0 4 Write 1) %"v17";
    store Ww [%"chk3" + 0] <- %"iw_1.v18";
    %"v20" = %"v8" +p #40;
    %"iw_2.v10" = %"v2" +p #32;
    %"iw_2.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_2.v12" = %"iw_2.v11" +p #56;
    %"iw_2.v17" = %"iw_2.v12" +p #352;
    %"chk5" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 4 Write 1) %"chk3", %"v20";
    store Ww [%"chk6" + 0] <- %"iw_2.v18";
    %"v26" = %"v8" +p #44;
    %"v27" : W = (RawLoad (LdNarrow Sw) 0) %"chk3";
    %"v28" : W = (Cmp Eq W) %"v27", #0
    => br %"v28" ? "L23" : "L11";
  @"L23":
    %"v29" = %"v8" +p #44;
    %"iw_3.v10" = %"v2" +p #8;
    %"chk8" : A = (HalfCheck Lower 0 8 Read 8) %"chk1", %"iw_3.v10";
    %"iw_3.v11" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_3.v12" = %"iw_3.v11" +p #56;
    %"iw_3.v17" = %"iw_3.v12" +p #24;
    %"chk9" : A = (Check 0 4 Read 1) %"iw_3.v17";
    %"iw_3.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    store Ww [%"chk3" + 0] <- %"iw_3.v18"
    => goto "L11";
  @"L10":
    %"v32" = %"v8" +p #44;
    %"iw_4.v10" = %"v2" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_4.v10";
    %"iw_4.v11" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_4.v12" = %"iw_4.v11" +p #56;
    %"iw_4.v17" = %"iw_4.v12" +p #24;
    %"chk12" : A = (Check 0 4 Read 1) %"iw_4.v17";
    %"iw_4.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk12";
    %"chk13" : A = (Check 0 4 Write 1) %"v32";
    store Ww [%"chk13" + 0] <- %"iw_4.v18";
    %"v35" = %"v8" +p #40;
    %"iw_5.v10" = %"v2" +p #8;
    %"iw_5.v11" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_5.v12" = %"iw_5.v11" +p #56;
    %"iw_5.v17" = %"iw_5.v12" +p #32;
    %"chk15" : A = (Check 0 4 Read 1) %"iw_5.v17";
    %"iw_5.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk15";
    %"chk16" : A = (HalfCheck Lower 0 4 Write 1) %"chk13", %"v35";
    store Ww [%"chk16" + 0] <- %"iw_5.v18"
    => goto "L11";
  @"L11":
    %"v42" = %"v4" +p #12;
    %"v43" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v44" : W = Shl %"v43", #20;
    %"v45" : W = Shr %"v44", #31
    => br %"v45" ? "L38" : "L39";
  @"L38":
    %"v46" = %"v8" +p #56;
    %"chk18" : A = (Check 0 8 Read 8) %"v2";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"chk19" : A = (Check 0 8 Write 8) %"v46";
    store.ptr [%"chk19" + 0] <- %"v49"
    => goto "L40";
  @"L39":
    %"v50" = %"v8" +p #56;
    %"chk20" : A = (Check 0 8 Write 8) %"v50";
    store.ptr [%"chk20" + 0] <- #0
    => goto "L40";
  @"L40":
    %"v51" = %"v8" +p #48;
    %"chk21" : A = (Check 0 8 Write 8) %"v51";
    store.ptr [%"chk21" + 0] <- %"v0";
    %"v53" = %"v8" +p #64;
    %"iw_6.v12" = %"v53" +p #64;
    %"chk22" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"v8";
    store.ptr [%"chk22" + 0] <- %"v53";
    %"iw_6.iw_1.v11" = %"v8" +p #8;
    %"chk23" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"iw_6.iw_1.v11";
    store.ptr [%"chk23" + 0] <- %"v53";
    %"iw_6.iw_1.v14" = %"v8" +p #16;
    %"chk24" : A = (HalfCheck Lower 0 8 Write 8) %"chk21", %"iw_6.iw_1.v14";
    store.ptr [%"chk24" + 0] <- %"iw_6.v12";
    %"iw_6.iw_1.v17" = %"v8" +p #24;
    %"chk25" : A = (HalfCheck Lower 0 8 Write 1) %"chk21", %"iw_6.iw_1.v17";
    store Wl [%"chk25" + 0] <- #0;
    %"iw_6.iw_1.v19" = %"v8" +p #32;
    %"chk26" : A = (HalfCheck Lower 0 4 Write 1) %"chk21", %"iw_6.iw_1.v19";
    store Ww [%"chk26" + 0] <- #9;
    call void $"glibc_printf_fp#__printf_fp_buffer_1"(P %"v8", P %"v2", W #44, W #46, W #1, P %"v4", P %"v6");
    %"iw_7.v3" = %"v8" +p #32;
    %"chk27" : A = (Renew 0 4 Read 1) %"chk26", %"iw_7.v3";
    %"iw_7.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk27";
    %"iw_7.v5" : W = (Cmp Eq W) %"iw_7.v4", #0
    => br %"iw_7.v5" ? "L57" : "L59";
  @"L57":
    %"v62" = %"v8" +p #48;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk21", %"v62";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"iw_8.v3" = %"v63" +p #32;
    %"chk29" : A = (Check 0 4 Write 1) %"iw_8.v3";
    store Ww [%"chk29" + 0] <- #0
    => ret void;
  @"L59":
    call %"v65" : W = $"__printf_buffer_flush"(P %"v8")
    => ret void
} }.

Definition fn_glibc_printf_fp'23__ctype_b_loc'2egnu_inline : func :=
  ir_fn{ "local" "glibc_printf_fp#__ctype_b_loc.gnu_inline"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_B"
    => ret %"v0"
} }.

Definition fn_glibc_printf_fp'23__ctype_tolower_loc'2egnu_inline : func :=
  ir_fn{ "local" "glibc_printf_fp#__ctype_tolower_loc.gnu_inline"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_CTYPE_TOLOWER"
    => ret %"v0"
} }.

Definition fn_glibc_printf_fp'23__libc_use_alloca'2egnu_inline : func :=
  ir_fn{ "local" "glibc_printf_fp#__libc_use_alloca.gnu_inline"(L %"v0") -> (RClass W) {
  @"start":
    call %"v3" : W = $"__GI___libc_alloca_cutoff"(L %"v0");
    %"v4" : L = (Ext Sw) %"v3";
    %"v5" : W = (Cmp Ne L) %"v4", #0
    => br %"v5" ? "L7" : "L6";
  @"L6":
    %"v11" : W = (Cmp Ule L) %"v0", #4096
    => goto "L7";
  @"L7" [%"v15" : W = phi("start" => #1, "L6" => %"v11")]:
    => ret %"v15"
} }.

Definition fn_glibc_printf_fp'23__printf_buffer_mark_failed : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_mark_failed"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- #0
    => ret void
} }.

Definition fn_glibc_printf_fp'23__printf_buffer_pad : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_pad"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"v10" : W = (Cmp Sgt L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v12" : W = (Ext Sb) %"v2";
    call void $"__printf_buffer_pad_1"(P %"v0", W %"v12", L %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition fn_glibc_printf_fp'23__printf_buffer_putc : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_putc"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v11";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v13" : L = Ptoi %"v9";
    %"v14" : L = Ptoi %"v12";
    %"v15" : W = (Cmp Ne L) %"v13", %"v14"
    => br %"v15" ? "L4" : "L5";
  @"L4":
    %"v17" = %"v0" +p #8;
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v19" = %"v18" +p #1;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk3" + 0] <- %"v19";
    %"v20" : W = (Ext Sb) %"v2";
    %"chk4" : A = (Check 0 1 Write 1) %"v18";
    store Wb [%"chk4" + 0] <- %"v20"
    => goto "L6";
  @"L5":
    %"v22" : W = (Ext Sb) %"v2";
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v22")
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition fn_glibc_printf_fp'23__printf_buffer_puts : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_puts"(P %"v0", P %"v2") -> RVoid {
  @"start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v2")
    => ret void
} }.

Definition fn_glibc_printf_fp'23__printf_fp_buffer_1 : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_fp_buffer_1"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8", P %"v10", P %"v12") -> RVoid blocks (fn_glibc_printf_fp'23__printf_fp_buffer_1'blocks1 ++ fn_glibc_printf_fp'23__printf_fp_buffer_1'blocks2) }.

Definition fn_glibc_printf_fp'23get_rounding_mode : func :=
  ir_fn{ "local" "glibc_printf_fp#get_rounding_mode"() -> (RClass W) {
  @"start":
    call %"v7" : W = $"zmath_getcw"();
    %"v8" : W = (Ext Uh) %"v7";
    %"v11" : W = And %"v8", #3072;
    %"v19" : W = (Cmp Eq W) %"v11", #1024
    => br %"v19" ? "L14" : "L20";
  @"L14":
    => ret #1024;
  @"L15":
    => ret #0;
  @"L16":
    => ret #3072;
  @"L17":
    => ret #2048;
  @"L18":
    call void $"__GI_abort"()
    => ret #0;
  @"L20":
    %"v21" : W = (Cmp Eq W) %"v11", #0
    => br %"v21" ? poll "L15" : "L22";
  @"L22":
    %"v23" : W = (Cmp Eq W) %"v11", #3072
    => br %"v23" ? poll "L16" : "L24";
  @"L24":
    %"v25" : W = (Cmp Eq W) %"v11", #2048
    => br %"v25" ? poll "L17" : poll "L18"
} }.

Definition fn_glibc_printf_fp'23hack_digit : func :=
  ir_fn{ "local" "glibc_printf_fp#hack_digit"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = (Cmp Ne W) %"v7", #0
    => br %"v8" ? "L9" : "L10";
  @"L9":
    %"v12" = %"v0" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v12";
    %"v13" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v14" : W = (Cmp Eq W) %"v13", #102
    => goto "L10";
  @"L10" [%"v16" : W = phi("start" => #0, "L9" => %"v14")]:
    => br %"v16" ? "L17" : "L18";
  @"L17":
    %"v20" = %"v0" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v20";
    %"v21" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v22" : W = Sub %"v21", #1;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk2", %"v20";
    store Ww [%"chk3" + 0] <- %"v22";
    %"v23" : W = (Cmp Sgt W) %"v21", #0
    => goto "L18";
  @"L18" [%"v25" : W = phi("L10" => #0, "L17" => %"v23")]:
    => br %"v25" ? "L5" : "L4";
  @"L4":
    %"v30" = %"v0" +p #40;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v30";
    %"v31" : L = (RawLoad LdL 0) %"chk4";
    %"v32" : W = (Cmp Eq L) %"v31", #0
    => br %"v32" ? "L26" : "L27";
  @"L26":
    %"v34" = %"v0" +p #16;
    %"chk5" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v34";
    %"v35" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v37" = %"v0" +p #24;
    %"v38" : L = (RawLoad LdL 8) %"chk5";
    %"v39" : L = Sub %"v38", #1;
    %"v40" : L = Shl %"v39", #3;
    %"v41" = %"v35" +p %"v40";
    %"chk7" : A = (Check 0 8 Read 1) %"v41";
    %"v42" : L = (RawLoad LdL 0) %"chk7";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v48" : L = (RawLoad LdL 8) %"chk5";
    %"v49" : L = Sub %"v48", #1;
    %"v50" : L = Shl %"v49", #3;
    %"v51" = %"v45" +p %"v50";
    %"v54" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v60" : L = (RawLoad LdL 8) %"chk5";
    %"v61" : L = Sub %"v60", #1;
    call %"v62" : L = $"__mpn_mul_1"(P %"v54", P %"v57", L %"v61", L #10);
    %"chk13" : A = (Check 0 8 Write 1) %"v51";
    store Wl [%"chk13" + 0] <- %"v62"
    => goto "L5";
  @"L27":
    %"v67" = %"v0" +p #24;
    %"v68" : L = (RawLoad LdL (-16)) %"chk4";
    %"v70" = %"v0" +p #40;
    %"v71" : L = (RawLoad LdL 0) %"chk4";
    %"v72" : W = (Cmp Slt L) %"v68", %"v71"
    => br %"v72" ? "L65" : "L64";
  @"L64":
    %"v74" = %"v0" +p #48;
    %"chk16" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v74";
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"v77" = %"v0" +p #16;
    %"v78" : P = (RawLoadPointer (-32) load_effects) %"chk16";
    %"v80" = %"v0" +p #24;
    %"v81" : L = (RawLoad LdL (-16)) %"chk4";
    %"v83" = %"v0" +p #32;
    %"v84" : P = (RawLoadPointer (-16) load_effects) %"chk16";
    %"v86" = %"v0" +p #40;
    %"v87" : L = (RawLoad LdL 0) %"chk4";
    call %"v88" : L = $"__mpn_divrem"(P %"v75", L #0, P %"v78", L %"v81", P %"v84", L %"v87");
    %"chk21" : A = (Renew 0 8 Read 8) %"chk16", %"v74";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk22" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v80";
    %"v94" : L = (RawLoad LdL 0) %"chk22";
    %"v97" : L = (RawLoad LdL (-8)) %"chk21";
    %"v98" : L = Sub %"v94", %"v97";
    %"v99" : L = Shl %"v98", #3;
    %"v100" = %"v91" +p %"v99";
    %"chk24" : A = (Check 0 8 Write 1) %"v100";
    store Wl [%"chk24" + 0] <- %"v88";
    %"v104" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"chk26" : A = (Check 0 8 Read 1) %"v104";
    %"v106" : L = (RawLoad LdL 0) %"chk26";
    %"v111" : L = (RawLoad LdL (-8)) %"chk21";
    %"chk28" : A = (Renew 0 8 Write 1) %"chk22", %"v80";
    store Wl [%"chk28" + 0] <- %"v111"
    => goto "L112";
  @"L112":
    %"v116" = %"v0" +p #24;
    %"chk29" : A = (Renew 0 8 Read 1) %"chk22", %"v116";
    %"v117" : L = (RawLoad LdL 0) %"chk29";
    %"v118" : W = (Cmp Ne L) %"v117", #0
    => br %"v118" ? "L119" : "L120";
  @"L119":
    %"v122" = %"v0" +p #16;
    %"chk30" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v122";
    %"v123" : P = (RawLoadPointer 0 load_effects) %"chk30";
    %"v125" = %"v0" +p #24;
    %"v126" : L = (RawLoad LdL 0) %"chk29";
    %"v127" : L = Sub %"v126", #1;
    %"v128" : L = Shl %"v127", #3;
    %"v129" = %"v123" +p %"v128";
    %"chk32" : A = (Check 0 8 Read 1) %"v129";
    %"v130" : L = (RawLoad LdL 0) %"chk32";
    %"v131" : W = (Cmp Eq L) %"v130", #0
    => goto "L120";
  @"L120" [%"v133" : W = phi("L112" => #0, "L119" => %"v131")]:
    => br %"v133" ? "L113" : "L114";
  @"L113":
    %"v135" = %"v0" +p #24;
    %"v136" : L = (RawLoad LdL 0) %"chk29";
    %"v137" : L = Sub %"v136", #1;
    %"chk34" : A = (Renew 0 8 Write 1) %"chk22", %"v135";
    store Wl [%"chk34" + 0] <- %"v137"
    => goto poll "L112";
  @"L114":
    %"v142" = %"v0" +p #24;
    %"v143" : L = (RawLoad LdL 0) %"chk29";
    %"v144" : W = (Cmp Eq L) %"v143", #0
    => br %"v144" ? "L138" : "L65";
  @"L138":
    %"v146" = %"v0" +p #24;
    %"chk36" : A = (Renew 0 8 Write 1) %"chk22", %"v146";
    store Wl [%"chk36" + 0] <- #1;
    %"v148" : L = Add %"v106", #48;
    %"v149" : W = (Ext Sb) %"v148"
    => ret %"v149";
  @"L65" [%"pr.3" : L = phi("L27" => #0, "L114" => %"v106")]:
    %"v153" = %"v0" +p #16;
    %"chk37" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v153";
    %"v154" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v157" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"v159" = %"v0" +p #24;
    %"chk39" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v159";
    %"v160" : L = (RawLoad LdL 0) %"chk39";
    call %"v161" : L = $"__mpn_mul_1"(P %"v154", P %"v157", L %"v160", L #10);
    %"v166" : W = (Cmp Ne L) %"v161", #0
    => br %"v166" ? "L162" : "L5";
  @"L162":
    %"v168" = %"v0" +p #16;
    %"chk40" : A = (Renew 0 8 Read 8) %"chk37", %"v168";
    %"v169" : P = (RawLoadPointer 0 load_effects) %"chk40";
    %"v171" = %"v0" +p #24;
    %"chk41" : A = (Renew 0 8 Read 1) %"chk39", %"v171";
    %"v172" : L = (RawLoad LdL 0) %"chk41";
    %"v173" : L = Add %"v172", #1;
    %"chk42" : A = (Renew 0 8 Write 1) %"chk39", %"v171";
    store Wl [%"chk42" + 0] <- %"v173";
    %"v174" : L = Shl %"v172", #3;
    %"v175" = %"v169" +p %"v174";
    %"chk43" : A = (Check 0 8 Write 1) %"v175";
    store Wl [%"chk43" + 0] <- %"v161"
    => goto "L5";
  @"L5" [%"pr.2" : L = phi("L18" => #0, "L26" => %"v42", "L162" => %"pr.3", "L65" => %"pr.3")]:
    %"v178" : L = Add %"pr.2", #48;
    %"v179" : W = (Ext Sb) %"v178"
    => ret %"v179"
} }.

Definition fn_glibc_printf_fp'23round_away : func :=
  ir_fn{ "local" "glibc_printf_fp#round_away"(W %"v0", W %"v2", W %"v4", W %"v6", W %"v8") -> (RClass W) {
  @"start":
    %"v56" : W = (Cmp Eq W) %"v8", #1024
    => br %"v56" ? "L13" : "L57";
  @"L13":
    %"v14" : W = (Ext Ub) %"v0"
    => br %"v14" ? "L15" : "L16";
  @"L15":
    %"v17" : W = (Ext Ub) %"v4"
    => br %"v17" ? "L16" : "L18";
  @"L18":
    %"v20" : W = (Ext Ub) %"v6";
    %"v21" : W = (Cmp Ne W) %"v20", #0
    => goto "L16";
  @"L16" [%"v24" : W = phi("L13" => #0, "L15" => #1, "L18" => %"v21")]:
    => ret %"v24";
  @"L26":
    %"v27" : W = (Ext Ub) %"v4"
    => br %"v27" ? "L28" : "L29";
  @"L28":
    %"v30" : W = (Ext Ub) %"v2"
    => br %"v30" ? "L29" : "L31";
  @"L31":
    %"v33" : W = (Ext Ub) %"v6";
    %"v34" : W = (Cmp Ne W) %"v33", #0
    => goto "L29";
  @"L29" [%"v37" : W = phi("L26" => #0, "L28" => #1, "L31" => %"v34")]:
    => ret %"v37";
  @"L39":
    => ret #0;
  @"L41":
    %"v42" : W = (Ext Ub) %"v0";
    %"v43" : W = (Cmp Eq W) %"v42", #0
    => br %"v43" ? "L44" : "L45";
  @"L44":
    %"v46" : W = (Ext Ub) %"v4"
    => br %"v46" ? "L45" : "L47";
  @"L47":
    %"v49" : W = (Ext Ub) %"v6";
    %"v50" : W = (Cmp Ne W) %"v49", #0
    => goto "L45";
  @"L45" [%"v53" : W = phi("L41" => #0, "L44" => #1, "L47" => %"v50")]:
    => ret %"v53";
  @"L55":
    call void $"__GI_abort"()
    => ret #0;
  @"L57":
    %"v58" : W = (Cmp Eq W) %"v8", #0
    => br %"v58" ? poll "L26" : "L59";
  @"L59":
    %"v60" : W = (Cmp Eq W) %"v8", #3072
    => br %"v60" ? poll "L39" : "L61";
  @"L61":
    %"v62" : W = (Cmp Eq W) %"v8", #2048
    => br %"v62" ? poll "L41" : poll "L55"
} }.

Definition item_glibc_printf_fp'23str'2e295 : item :=
  (IData (a "glibc_printf_fp#str.295") (LRo (a "local")) 1 [(Item Wb 78); (Item Wb 65); (Item Wb 78); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e296 : item :=
  (IData (a "glibc_printf_fp#str.296") (LRo (a "local")) 1 [(Item Wb 110); (Item Wb 97); (Item Wb 110); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e297 : item :=
  (IData (a "glibc_printf_fp#str.297") (LRo (a "local")) 1 [(Item Wb 73); (Item Wb 78); (Item Wb 70); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e298 : item :=
  (IData (a "glibc_printf_fp#str.298") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 102); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e301 : item :=
  (IData (a "glibc_printf_fp#str.301") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 32); (Item Wb 62); (Item Wb 32); (Item Wb 38); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 105); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 49); (Item Wb 48); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e302 : item :=
  (IData (a "glibc_printf_fp#str.302") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e303 : item :=
  (IData (a "glibc_printf_fp#str.303") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 49); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e304 : item :=
  (IData (a "glibc_printf_fp#str.304") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 40); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 50); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 41); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e305 : item :=
  (IData (a "glibc_printf_fp#str.305") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 32); (Item Wb 33); (Item Wb 61); (Item Wb 32); (Item Wb 38); (Item Wb 95); (Item Wb 102); (Item Wb 112); (Item Wb 105); (Item Wb 111); (Item Wb 99); (Item Wb 111); (Item Wb 110); (Item Wb 115); (Item Wb 116); (Item Wb 95); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 49); (Item Wb 48); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e306 : item :=
  (IData (a "glibc_printf_fp#str.306") (LRo (a "local")) 1 [(Item Wb 105); (Item Wb 110); (Item Wb 99); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 112); (Item Wb 111); (Item Wb 119); (Item Wb 101); (Item Wb 114); (Item Wb 115); (Item Wb 45); (Item Wb 62); (Item Wb 112); (Item Wb 95); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e307 : item :=
  (IData (a "glibc_printf_fp#str.307") (LRo (a "local")) 1 [(Item Wb 99); (Item Wb 121); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 116); (Item Wb 109); (Item Wb 112); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 116); (Item Wb 109); (Item Wb 112); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 50); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e308 : item :=
  (IData (a "glibc_printf_fp#str.308") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 91); (Item Wb 112); (Item Wb 46); (Item Wb 102); (Item Wb 114); (Item Wb 97); (Item Wb 99); (Item Wb 115); (Item Wb 105); (Item Wb 122); (Item Wb 101); (Item Wb 32); (Item Wb 45); (Item Wb 32); (Item Wb 49); (Item Wb 93); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 49); (Item Wb 48); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e309 : item :=
  (IData (a "glibc_printf_fp#str.309") (LRo (a "local")) 1 (app [(Item Wb 48); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 51); (Item Wb 32); (Item Wb 38); (Item Wb 38); (Item Wb 32); (Item Wb 112); (Item Wb 46)] [(Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 111); (Item Wb 110); (Item Wb 101); (Item Wb 110); (Item Wb 116); (Item Wb 32); (Item Wb 43); (Item Wb 32); (Item Wb 116); (Item Wb 111); (Item Wb 95); (Item Wb 115); (Item Wb 104); (Item Wb 105); (Item Wb 102); (Item Wb 116); (Item Wb 32); (Item Wb 60); (Item Wb 32); (Item Wb 66); (Item Wb 73); (Item Wb 84); (Item Wb 83); (Item Wb 95); (Item Wb 80); (Item Wb 69); (Item Wb 82); (Item Wb 95); (Item Wb 77); (Item Wb 80); (Item Wb 95); (Item Wb 76); (Item Wb 73); (Item Wb 77); (Item Wb 66); (Item Wb 0)])).

Definition item_glibc_printf_fp'23str'2e310 : item :=
  (IData (a "glibc_printf_fp#str.310") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 46); (Item Wb 101); (Item Wb 120); (Item Wb 112); (Item Wb 115); (Item Wb 105); (Item Wb 103); (Item Wb 110); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 48); (Item Wb 32); (Item Wb 124); (Item Wb 124); (Item Wb 32); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 100); (Item Wb 105); (Item Wb 103); (Item Wb 95); (Item Wb 109); (Item Wb 97); (Item Wb 120); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e311 : item :=
  (IData (a "glibc_printf_fp#str.311") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 99); (Item Wb 112); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 119); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 112); (Item Wb 32); (Item Wb 43); (Item Wb 32); (Item Wb 49); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e312 : item :=
  (IData (a "glibc_printf_fp#str.312") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 115); (Item Wb 116); (Item Wb 97); (Item Wb 114); (Item Wb 116); (Item Wb 112); (Item Wb 91); (Item Wb 48); (Item Wb 93); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 39); (Item Wb 49); (Item Wb 39); (Item Wb 0)]).

Definition item_glibc_printf_fp'23str'2e313 : item :=
  (IData (a "glibc_printf_fp#str.313") (LRo (a "local")) 1 [(Item Wb 48); (Item Wb 46); (Item Wb 48); (Item Wb 48); (Item Wb 48); (Item Wb 49); (Item Wb 0)]).
