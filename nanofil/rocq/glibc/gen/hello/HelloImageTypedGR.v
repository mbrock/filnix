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

Definition hello_image_fn___grouping_iterator_init_none : func :=
  ir_fn{ "export" "__grouping_iterator_init_none"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    call %"v5" : P = $"__GI_memset"(P %"v0", W #0, L #24);
    %"chk0" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk0" + 0] <- %"v2";
    %"v9" = %"v0" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v9";
    store Ww [%"chk1" + 0] <- %"v2"
    => ret #0
} }.

Definition hello_image_fn___grouping_iterator_init : func :=
  ir_fn{ "export" "__grouping_iterator_init"(P %"v0", W %"v2", P %"v4", W %"v6") -> (RClass W) {
  @"start":
    %"v12" : W = (Cmp Ule W) %"v6", #1
    => br %"v12" ? "L8" : "iw_1.start";
  @"L8":
    call %"v15" : W = $"__grouping_iterator_init_none"(P %"v0", W %"v6");
    %"v16" : W = (Ext Ub) %"v15"
    => ret %"v16";
  @"iw_1.start":
    %"iw_1.v10" : W = (Cmp Eq W) %"v2", #4
    => br %"iw_1.v10" ? "iw_1.L8" : "iw_1.L7";
  @"iw_1.L7":
    => goto "iw_1.L8";
  @"iw_1.L8" [%"iw_1.v11" : W = phi("iw_1.L7" => #65538, "iw_1.start" => #262148)]:
    %"iw_1.iw_1.v8" : L = (Ext Sw) %"v2";
    %"iw_1.iw_1.v9" : L = Shl %"iw_1.iw_1.v8", #3;
    %"iw_1.iw_1.v10" = %"v4" +p %"iw_1.iw_1.v9";
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v10";
    %"iw_1.iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.iw_1.v12" = %"iw_1.iw_1.v11" +p #56;
    %"iw_1.iw_1.v14" : W = And %"iw_1.v11", #65535;
    %"iw_1.iw_1.v15" : L = (Ext Sw) %"iw_1.iw_1.v14";
    %"iw_1.iw_1.v16" : L = Shl %"iw_1.iw_1.v15", #3;
    %"iw_1.iw_1.v17" = %"iw_1.iw_1.v12" +p %"iw_1.iw_1.v16";
    %"chk1" : A = (Check 0 8 Read 8) %"iw_1.iw_1.v17";
    %"iw_1.iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (Check 0 1 Read 1) %"iw_1.iw_1.v18";
    %"iw_2.v10" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_2.v11" : W = (Cmp Eq W) %"iw_2.v10", #127
    => br %"iw_2.v11" ? "iw_2.L13" : "iw_2.L12";
  @"iw_2.L12":
    %"iw_2.v15" : W = (RawLoad (LdNarrow Sb) 0) %"chk2";
    %"iw_2.v16" : W = (Cmp Sle W) %"iw_2.v15", #0
    => goto "iw_2.L13";
  @"iw_2.L13" [%"iw_2.v18" : W = phi("iw_1.L8" => #1, "iw_2.L12" => %"iw_2.v16")]:
    => br %"iw_2.v18" ? "iw_2.L6" : "iw_2.L28";
  @"iw_2.L6":
    call %"iw_2.v21" : W = $"__grouping_iterator_init_none"(P %"v0", W %"v6");
    %"iw_2.v22" : W = (Ext Ub) %"iw_2.v21"
    => goto "iw_2.join";
  @"iw_2.L28" [%"iw_2.pr.7" : W = phi("iw_2.L13" => #0, "iw_2.L51" => %"iw_2.v44"); %"iw_2.pr.5" : W = phi("iw_2.L13" => #0, "iw_2.L51" => %"iw_2.v34"); %"iw_2.pr.3" : W = phi("iw_2.L13" => %"v6", "iw_2.L51" => %"iw_2.v49"); %"iw_2.pr.1" : P = phi("iw_2.L13" => %"iw_1.iw_1.v18", "iw_2.L51" => %"iw_2.v47")]:
    %"chk4" : A = (Check 0 1 Read 1) %"iw_2.pr.1";
    %"iw_2.v33" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v34" : W = Add %"iw_2.pr.5", %"iw_2.v33";
    %"iw_2.v40" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v41" : W = (Cmp Ule W) %"iw_2.pr.3", %"iw_2.v40"
    => br %"iw_2.v41" ? "iw_2.L30" : "iw_2.L37";
  @"iw_2.L37":
    %"iw_2.v44" : W = Add %"iw_2.pr.7", #1;
    %"iw_2.v47" = %"iw_2.pr.1" +p #1;
    %"iw_2.v48" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v49" : W = Sub %"iw_2.pr.3", %"iw_2.v48";
    %"chk7" : A = (HalfCheck Upper 0 1 Read 1) %"chk4", %"iw_2.v47";
    %"iw_2.v54" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v55" : W = (Cmp Eq W) %"iw_2.v54", #127
    => br %"iw_2.v55" ? "iw_2.L57" : "iw_2.L56";
  @"iw_2.L56":
    %"iw_2.v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v60" : W = (Cmp Slt W) %"iw_2.v59", #0
    => goto "iw_2.L57";
  @"iw_2.L57" [%"iw_2.v62" : W = phi("iw_2.L37" => #1, "iw_2.L56" => %"iw_2.v60")]:
    => br %"iw_2.v62" ? "iw_2.L30" : "iw_2.L51";
  @"iw_2.L51":
    %"iw_2.v68" : W = (RawLoad (LdNarrow Sb) 0) %"chk7";
    %"iw_2.v69" : W = (Cmp Eq W) %"iw_2.v68", #0
    => br %"iw_2.v69" ? "iw_2.L64" : poll "iw_2.L28";
  @"iw_2.L64":
    (Flight (a "iw_2.v71") Sub [(FAddress (t "iw_2.v47")); (FValue (Const 1))] (LowerOf (t "iw_2.v47")));
    %"iw_2.v74" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v75" : W = Sub %"iw_2.v34", %"iw_2.v74";
    %"iw_2.v78" : W = Sub %"iw_2.v49", #1;
    %"iw_2.v80" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v81" : W = Udiv %"iw_2.v78", %"iw_2.v80";
    %"iw_2.v84" : W = Add %"iw_2.v44", %"iw_2.v81";
    %"iw_2.v88" : W = (RawLoad (LdNarrow Sb) 0) %"chk4";
    %"iw_2.v89" : W = Mul %"iw_2.v81", %"iw_2.v88";
    %"iw_2.v90" : W = Sub %"iw_2.v49", %"iw_2.v89"
    => goto "iw_2.L30";
  @"iw_2.L30" [%"iw_2.pr.8" : W = phi("iw_2.L64" => %"iw_2.v84", "iw_2.L28" => %"iw_2.pr.7", "iw_2.L57" => %"iw_2.v44"); %"iw_2.pr.6" : W = phi("iw_2.L64" => %"iw_2.v75", "iw_2.L28" => %"iw_2.v34", "iw_2.L57" => %"iw_2.v34"); %"iw_2.pr.4" : W = phi("iw_2.L64" => %"iw_2.v90", "iw_2.L28" => %"iw_2.pr.3", "iw_2.L57" => %"iw_2.v49"); %"iw_2.pr.2" : P = phi("iw_2.L64" => %"iw_2.v71", "iw_2.L28" => %"iw_2.pr.1", "iw_2.L57" => %"iw_2.v47")]:
    %"chk13" : A = (Check 0 4 Write 1) %"v0";
    store Ww [%"chk13" + 0] <- %"iw_2.pr.4";
    %"iw_2.v95" = %"v0" +p #4;
    %"chk14" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v95";
    store Ww [%"chk14" + 0] <- %"v6";
    %"iw_2.v98" = %"v0" +p #8;
    %"chk15" : A = (HalfCheck Upper 0 8 Write 8) %"chk13", %"iw_2.v98";
    store.ptr [%"chk15" + 0] <- %"iw_2.pr.2";
    %"iw_2.v101" = %"v0" +p #16;
    %"chk16" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v101";
    store Ww [%"chk16" + 0] <- %"iw_2.pr.6";
    %"iw_2.v104" = %"v0" +p #20;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk13", %"iw_2.v104";
    store Ww [%"chk17" + 0] <- %"iw_2.pr.8";
    %"iw_2.v108" : W = (RawLoad (LdNarrow Uw) 0) %"chk17";
    %"iw_2.v109" : W = (Cmp Ugt W) %"iw_2.v108", #0
    => goto "iw_2.join";
  @"iw_2.join" [%"v23" : W = phi("iw_2.L6" => %"iw_2.v22", "iw_2.L30" => %"iw_2.v109")]:
    %"v24" : W = (Ext Ub) %"v23"
    => ret %"v24"
} }.

Definition hello_image_fn___grouping_iterator_next : func :=
  ir_fn{ "export" "__grouping_iterator_next"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #4;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v8" : W = (Cmp Ugt W) %"v7", #0
    => br %"v8" ? "L4" : "L3";
  @"L3":
    %"v9" : P = Copy $"glibc_grouping_iterator#str.41";
    %"v10" : P = Copy $"glibc_grouping_iterator#str.42";
    %"v11" : P = Copy $"glibc_grouping_iterator#str.43";
    call void $"__libc_assert_fail"(P %"v9", P %"v10", W #111, P %"v11")
    => goto "L4";
  @"L4":
    %"v13" = %"v0" +p #4;
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v13";
    %"v14" : W = (RawLoad (LdNarrow Uw) 0) %"chk1";
    %"v15" : W = Sub %"v14", #1;
    %"chk2" : A = (Renew 0 4 Write 1) %"chk0", %"v13";
    store Ww [%"chk2" + 0] <- %"v15";
    %"chk3" : A = (HalfCheck Lower 0 4 Read 1) %"chk0", %"v0";
    %"v20" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v21" : W = (Cmp Ugt W) %"v20", #0
    => br %"v21" ? "L16" : "L18";
  @"L16":
    %"v23" : W = (RawLoad (LdNarrow Uw) 0) %"chk3";
    %"v24" : W = Sub %"v23", #1;
    store Ww [%"chk3" + 0] <- %"v24"
    => ret #0;
  @"L18":
    %"v31" = %"v0" +p #4;
    %"v32" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v34" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v34";
    %"v35" : W = (RawLoad (LdNarrow Uw) 0) %"chk7";
    %"v36" : W = (Cmp Ult W) %"v32", %"v35"
    => br %"v36" ? "L27" : "L29";
  @"L27":
    %"v38" = %"v0" +p #8;
    %"chk8" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v38";
    %"v39" : P = (RawLoadPointer 0 load_effects) %"chk8";
    (Flight (a "v40") Sub [(FAddress (t "v39")); (FValue (Const 1))] (LowerOf (t "v39")));
    %"chk9" : A = (Renew 0 8 Write 8) %"chk8", %"v38";
    store.ptr [%"chk9" + 0] <- %"v40"
    => goto "L29";
  @"L29":
    %"v43" = %"v0" +p #8;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (Check 0 1 Read 1) %"v44";
    %"v45" : W = (RawLoad (LdNarrow Sb) 0) %"chk11";
    %"v46" : W = Sub %"v45", #1;
    %"chk12" : A = (Renew 0 4 Write 1) %"chk3", %"v0";
    store Ww [%"chk12" + 0] <- %"v46"
    => ret #1
} }.

Definition hello_image_fn_glibc_vfprintf_internal'23group_number : func :=
  ir_fn{ "local" "glibc_vfprintf_internal#group_number"(P %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W %"v10") -> RVoid {
  @"start":
    %"v15" : W = (Ext Ub) %"v10";
    %"v16" : W = (Cmp Eq W) %"v15", #0
    => br %"v16" ? "L19" : "L43";
  @"L19" [%"pr.1" : P = phi("L21" => %"v40", "start" => %"v4")]:
    %"v25" : L = Ptoi %"pr.1";
    %"v26" : L = Ptoi %"v6";
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => br %"v27" ? "L20" : "L14";
  @"L20":
    call %"v32" : W = $"__grouping_iterator_next"(P %"v2");
    %"v33" : W = (Ext Ub) %"v32"
    => br %"v33" ? "iw_1.start" : "L30";
  @"iw_1.start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v8")
    => goto "L30";
  @"L30":
    %"chk0" : A = (Check 0 1 Read 1) %"pr.1";
    %"v38" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"iw_2.v8" = %"v0" +p #8;
    %"chk1" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_2.v11" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk1", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v0" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_2.v19" = %"iw_2.v18" +p #1;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"iw_2.v17";
    store.ptr [%"chk4" + 0] <- %"iw_2.v19";
    %"chk5" : A = (Check 0 1 Write 1) %"iw_2.v18";
    store Wb [%"chk5" + 0] <- %"v38"
    => goto "L21";
  @"iw_2.L5":
    call void $"__printf_buffer_putc_1"(P %"v0", W %"v38")
    => goto "L21";
  @"L21":
    %"v40" = %"pr.1" +p #1
    => goto poll "L19";
  @"L43" [%"pr.2" : P = phi("L54" => %"v78", "start" => %"v4")]:
    %"v49" : L = Ptoi %"pr.2";
    %"v50" : L = Ptoi %"v6";
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L44" : "L14";
  @"L44":
    call %"v56" : W = $"__grouping_iterator_next"(P %"v2");
    %"v57" : W = (Ext Ub) %"v56"
    => br %"v57" ? "iw_3.start" : "L54";
  @"iw_3.start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v8")
    => goto "L54";
  @"L54":
    %"chk6" : A = (Check 0 1 Read 1) %"pr.2";
    %"v62" : W = (RawLoad (LdNarrow Sb) 0) %"chk6";
    %"v63" : W = Sub %"v62", #48;
    %"v65" : P = Copy $"__libc_tsd_LOCALE";
    %"chk7" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"v66";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v69" = %"v68" +p #56;
    %"v71" : W = Add %"v63", #41;
    %"v72" : W = And %"v71", #65535;
    %"v73" : L = (Ext Sw) %"v72";
    %"v74" : L = Shl %"v73", #3;
    %"v75" = %"v69" +p %"v74";
    %"chk9" : A = (Check 0 8 Read 8) %"v75";
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk9";
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v76");
    %"v78" = %"pr.2" +p #1
    => goto poll "L43";
  @"L14":
    => ret void
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23group_number : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#group_number"(P %"v0", P %"v2", P %"v4", P %"v6", W %"v8", W %"v10") -> RVoid {
  @"start":
    %"v15" : W = (Ext Ub) %"v10";
    %"v16" : W = (Cmp Eq W) %"v15", #0
    => br %"v16" ? "L19" : "L43";
  @"L19" [%"pr.1" : P = phi("L21" => %"v40", "start" => %"v4")]:
    %"v25" : L = Ptoi %"pr.1";
    %"v26" : L = Ptoi %"v6";
    %"v27" : W = (Cmp Ne L) %"v25", %"v26"
    => br %"v27" ? "L20" : "L14";
  @"L20":
    call %"v32" : W = $"__grouping_iterator_next"(P %"v2");
    %"v33" : W = (Ext Ub) %"v32"
    => br %"v33" ? "iw_1.start" : "L30";
  @"iw_1.start":
    %"iw_1.v8" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v8";
    %"iw_1.v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v11" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v13" : L = Ptoi %"iw_1.v9";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Ne L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L5";
  @"iw_1.L4":
    %"iw_1.v17" = %"v0" +p #8;
    %"iw_1.v18" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v19" = %"iw_1.v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"iw_1.v17";
    store.ptr [%"chk3" + 0] <- %"iw_1.v19";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_1.v18";
    store Ww [%"chk4" + 0] <- %"v8"
    => goto "L30";
  @"iw_1.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v8")
    => goto "L30";
  @"L30":
    %"chk5" : A = (Check 0 4 Read 1) %"pr.1";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk5";
    %"iw_2.v8" = %"v0" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v11" = %"v0" +p #16;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk6", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v0" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_2.v19" = %"iw_2.v18" +p #4;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk6", %"iw_2.v17";
    store.ptr [%"chk9" + 0] <- %"iw_2.v19";
    %"chk10" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk10" + 0] <- %"v38"
    => goto "L21";
  @"iw_2.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v38")
    => goto "L21";
  @"L21":
    %"v40" = %"pr.1" +p #4
    => goto poll "L19";
  @"L43" [%"pr.2" : P = phi("L45" => %"v78", "start" => %"v4")]:
    %"v49" : L = Ptoi %"pr.2";
    %"v50" : L = Ptoi %"v6";
    %"v51" : W = (Cmp Ne L) %"v49", %"v50"
    => br %"v51" ? "L44" : "L14";
  @"L44":
    call %"v56" : W = $"__grouping_iterator_next"(P %"v2");
    %"v57" : W = (Ext Ub) %"v56"
    => br %"v57" ? "iw_3.start" : "L54";
  @"iw_3.start":
    %"iw_3.v8" = %"v0" +p #8;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_3.v8";
    %"iw_3.v9" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_3.v11" = %"v0" +p #16;
    %"chk12" : A = (HalfCheck Upper 0 8 Read 8) %"chk11", %"iw_3.v11";
    %"iw_3.v12" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_3.v13" : L = Ptoi %"iw_3.v9";
    %"iw_3.v14" : L = Ptoi %"iw_3.v12";
    %"iw_3.v15" : W = (Cmp Ne L) %"iw_3.v13", %"iw_3.v14"
    => br %"iw_3.v15" ? "iw_3.L4" : "iw_3.L5";
  @"iw_3.L4":
    %"iw_3.v17" = %"v0" +p #8;
    %"iw_3.v18" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_3.v19" = %"iw_3.v18" +p #4;
    %"chk14" : A = (Renew 0 8 Write 8) %"chk11", %"iw_3.v17";
    store.ptr [%"chk14" + 0] <- %"iw_3.v19";
    %"chk15" : A = (Check 0 4 Write 1) %"iw_3.v18";
    store Ww [%"chk15" + 0] <- %"v8"
    => goto "L54";
  @"iw_3.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v8")
    => goto "L54";
  @"L54":
    %"chk16" : A = (Check 0 4 Read 1) %"pr.2";
    %"v62" : W = (RawLoad (LdNarrow Sw) 0) %"chk16";
    %"v63" : W = Sub %"v62", #48;
    %"v65" : P = Copy $"__libc_tsd_LOCALE";
    %"chk17" : A = (Check 0 8 Read 8) %"v65";
    %"v66" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Check 0 8 Read 8) %"v66";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk18";
    %"v69" = %"v68" +p #56;
    %"v71" : W = Add %"v63", #51;
    %"v72" : W = And %"v71", #65535;
    %"v73" : L = (Ext Sw) %"v72";
    %"v74" : L = Shl %"v73", #3;
    %"v75" = %"v69" +p %"v74";
    %"chk19" : A = (Check 0 4 Read 1) %"v75";
    %"v76" : W = (RawLoad (LdNarrow Uw) 0) %"chk19";
    %"iw_4.v8" = %"v0" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_4.v8";
    %"iw_4.v9" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_4.v11" = %"v0" +p #16;
    %"chk21" : A = (HalfCheck Upper 0 8 Read 8) %"chk20", %"iw_4.v11";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_4.v13" : L = Ptoi %"iw_4.v9";
    %"iw_4.v14" : L = Ptoi %"iw_4.v12";
    %"iw_4.v15" : W = (Cmp Ne L) %"iw_4.v13", %"iw_4.v14"
    => br %"iw_4.v15" ? "iw_4.L4" : "iw_4.L5";
  @"iw_4.L4":
    %"iw_4.v17" = %"v0" +p #8;
    %"iw_4.v18" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"iw_4.v19" = %"iw_4.v18" +p #4;
    %"chk23" : A = (Renew 0 8 Write 8) %"chk20", %"iw_4.v17";
    store.ptr [%"chk23" + 0] <- %"iw_4.v19";
    %"chk24" : A = (Check 0 4 Write 1) %"iw_4.v18";
    store Ww [%"chk24" + 0] <- %"v76"
    => goto "L45";
  @"iw_4.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v76")
    => goto "L45";
  @"L45":
    %"v78" = %"pr.2" +p #4
    => goto poll "L43";
  @"L14":
    => ret void
} }.
