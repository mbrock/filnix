(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedPRBlocks1315x1 HelloImageTypedPRBlocks1315x2 IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___printf_buffer_flush : func :=
  ir_fn{ "export" "__printf_buffer_flush"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "iw_2.start";
  @"L2":
    => ret #0;
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"iw_2.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_2.v30" : W = (Cmp Ult W) %"iw_2.v4", #6
    => br %"iw_2.v30" ? "iw_2.L31" : "iw_2.L32";
  @"iw_2.L9":
    call void $"__printf_buffer_flush_snprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L11":
    call void $"__GI___chk_fail"()
    => goto "iw_2.L6";
  @"iw_2.L12":
    call void $"__printf_buffer_flush_to_file"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L14":
    call void $"__printf_buffer_flush_asprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L16":
    call void $"__printf_buffer_flush_dprintf"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L18":
    %"iw_2.v19" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Write 1) %"iw_2.v19";
    store Ww [%"chk2" + 0] <- #7;
    %"iw_2.iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => goto "iw_3.start";
  @"iw_2.L21":
    call void $"__printf_buffer_flush_fp"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L23":
    call void $"__printf_buffer_flush_fp_to_wide"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L25":
    call void $"__printf_buffer_flush_fphex_to_wide"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L27":
    call void $"__printf_buffer_flush_obstack"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L31":
    %"iw_2.v33" : W = (Cmp Ult W) %"iw_2.v4", #3
    => br %"iw_2.v33" ? "iw_2.L34" : "iw_2.L35";
  @"iw_2.L34":
    %"iw_2.v36" : W = (Cmp Eq W) %"iw_2.v4", #0
    => br %"iw_2.v36" ? "iw_3.start" : "iw_2.L37";
  @"iw_2.L37":
    %"iw_2.v38" : W = (Cmp Eq W) %"iw_2.v4", #1
    => br %"iw_2.v38" ? "iw_3.start" : "iw_2.L39";
  @"iw_2.L39":
    %"iw_2.v40" : W = (Cmp Eq W) %"iw_2.v4", #2
    => br %"iw_2.v40" ? poll "iw_2.L9" : "iw_2.L6";
  @"iw_2.L35":
    %"iw_2.v42" : W = (Cmp Eq W) %"iw_2.v4", #3
    => br %"iw_2.v42" ? poll "iw_2.L11" : "iw_2.L43";
  @"iw_2.L43":
    %"iw_2.v44" : W = (Cmp Eq W) %"iw_2.v4", #4
    => br %"iw_2.v44" ? poll "iw_2.L12" : "iw_2.L45";
  @"iw_2.L45":
    %"iw_2.v46" : W = (Cmp Eq W) %"iw_2.v4", #5
    => br %"iw_2.v46" ? poll "iw_2.L14" : "iw_2.L6";
  @"iw_2.L32":
    %"iw_2.v48" : W = (Cmp Ult W) %"iw_2.v4", #9
    => br %"iw_2.v48" ? "iw_2.L49" : "iw_2.L50";
  @"iw_2.L49":
    %"iw_2.v51" : W = (Cmp Eq W) %"iw_2.v4", #6
    => br %"iw_2.v51" ? poll "iw_2.L16" : "iw_2.L52";
  @"iw_2.L52":
    %"iw_2.v53" : W = (Cmp Eq W) %"iw_2.v4", #7
    => br %"iw_2.v53" ? poll "iw_2.L18" : "iw_2.L54";
  @"iw_2.L54":
    %"iw_2.v55" : W = (Cmp Eq W) %"iw_2.v4", #8
    => br %"iw_2.v55" ? poll "iw_2.L21" : "iw_2.L6";
  @"iw_2.L50":
    %"iw_2.v57" : W = (Cmp Eq W) %"iw_2.v4", #9
    => br %"iw_2.v57" ? poll "iw_2.L23" : "iw_2.L58";
  @"iw_2.L58":
    %"iw_2.v59" : W = (Cmp Eq W) %"iw_2.v4", #10
    => br %"iw_2.v59" ? poll "iw_2.L25" : "iw_2.L60";
  @"iw_2.L60":
    %"iw_2.v61" : W = (Cmp Eq W) %"iw_2.v4", #11
    => br %"iw_2.v61" ? poll "iw_2.L27" : "iw_2.L6";
  @"iw_2.L6":
    => unreachable;
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk4" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk4";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L13" : "L15";
  @"L13":
    => ret #0;
  @"L15":
    %"v25" = %"v0" +p #8;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 8 load_effects) %"chk5";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_printf_buffer_flush#str.39";
    %"v34" : P = Copy $"glibc_printf_buffer_flush#str.40";
    %"v35" : P = Copy $"glibc_printf_buffer_flush#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #70, P %"v35")
    => goto "L23";
  @"L23":
    => ret #1
} }.

Definition hello_image_fn___printf_buffer_pad_1 : func :=
  ir_fn{ "export" "__printf_buffer_pad_1"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.1" : L = phi("L66" => %"v84", "start" => %"v4")]:
    %"v22" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v25" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v27" : L = Ptoi %"v23";
    %"v28" : L = Ptoi %"v26";
    %"v29" : W = (Cmp Eq L) %"v27", %"v28"
    => br %"v29" ? "L30" : "L31";
  @"L30":
    call %"v33" : W = $"__printf_buffer_flush"(P %"v0");
    %"v34" : W = (Ext Ub) %"v33";
    %"v35" : W = (Cmp Eq W) %"v34", #0
    => goto "L31";
  @"L31" [%"v37" : W = phi("L15" => #0, "L30" => %"v35")]:
    => br %"v37" ? "L18" : "L20";
  @"L18":
    => ret void;
  @"L20":
    %"v43" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v43";
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v46" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v48" : L = Ptoi %"v44";
    %"v49" : L = Ptoi %"v47";
    %"v50" : W = (Cmp Ne L) %"v48", %"v49"
    => br %"v50" ? "L41" : "L40";
  @"L40":
    %"v51" : P = Copy $"glibc_printf_buffer_pad_1#str.41";
    %"v52" : P = Copy $"glibc_printf_buffer_pad_1#str.42";
    %"v53" : P = Copy $"glibc_printf_buffer_pad_1#str.43";
    call void $"__libc_assert_fail"(P %"v51", P %"v52", W #35, P %"v53")
    => goto "L41";
  @"L41":
    %"v56" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v56";
    %"v57" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v59" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v59";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" : L = Ptoi %"v57";
    %"v62" : L = Ptoi %"v60";
    %"v63" : L = Sub %"v61", %"v62";
    %"v69" : W = (Cmp Ugt L) %"v63", %"pr.1"
    => br %"v69" ? "L66" : "L65";
  @"L65":
    => goto "L66";
  @"L66" [%"pr.2" : L = phi("L65" => %"v63", "L41" => %"pr.1")]:
    %"v72" = %"v0" +p #8;
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v74" : W = (Ext Sb) %"v2";
    call %"v76" : P = $"__GI_memset"(P %"v73", W %"v74", L %"pr.2");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v72";
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v81" = %"v79" +p %"pr.2";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v72";
    store.ptr [%"chk9" + 0] <- %"v81";
    %"v84" : L = Sub %"pr.1", %"pr.2";
    %"v86" : W = (Cmp Ugt L) %"v84", #0
    => br %"v86" ? poll "L15" : "L17";
  @"L17":
    => ret void
} }.

Definition hello_image_fn___printf_buffer_putc_1 : func :=
  ir_fn{ "export" "__printf_buffer_putc_1"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L13" : "L12";
  @"L12":
    call %"v15" : W = $"__printf_buffer_flush"(P %"v0");
    %"v16" : W = (Ext Ub) %"v15";
    %"v17" : W = (Cmp Eq W) %"v16", #0
    => goto "L13";
  @"L13" [%"v19" : W = phi("start" => #1, "L12" => %"v17")]:
    => br %"v19" ? "L4" : "L6";
  @"L4":
    => ret void;
  @"L6":
    %"v25" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v28" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ult L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_printf_buffer_putc_1#str.39";
    %"v34" : P = Copy $"glibc_printf_buffer_putc_1#str.40";
    %"v35" : P = Copy $"glibc_printf_buffer_putc_1#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #27, P %"v35")
    => goto "L23";
  @"L23":
    %"v37" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v39" = %"v38" +p #1;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"v37";
    store.ptr [%"chk4" + 0] <- %"v39";
    %"v40" : W = (Ext Sb) %"v2";
    %"chk5" : A = (Check 0 1 Write 1) %"v38";
    store Wb [%"chk5" + 0] <- %"v40"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_to_file_switch : func :=
  ir_fn{ "export" "__printf_buffer_to_file_switch"(P %"v0") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v8" = %"v7" +p #40;
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v13" = %"v12" +p #48;
    %"chk3" : A = (Check 0 8 Read 8) %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v15" : L = Ptoi %"v9";
    %"v16" : L = Ptoi %"v14";
    %"v17" : W = (Cmp Ult L) %"v15", %"v16"
    => br %"v17" ? "L2" : "L3";
  @"L2":
    %"v19" = %"v0" +p #8;
    %"v21" = %"v0" +p #40;
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v23" = %"v22" +p #40;
    %"chk5" : A = (Check 0 8 Read 8) %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v19";
    store.ptr [%"chk6" + 0] <- %"v24";
    %"v26" = %"v0" +p #16;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk0", %"v21";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v30" = %"v29" +p #48;
    %"chk8" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v26";
    store.ptr [%"chk9" + 0] <- %"v31"
    => goto "L4";
  @"L3":
    %"v33" = %"v0" +p #8;
    %"v35" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v33";
    store.ptr [%"chk10" + 0] <- %"v35";
    %"v37" = %"v0" +p #16;
    %"v43" = %"v35" +p #128;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v37";
    store.ptr [%"chk11" + 0] <- %"v43"
    => goto "L4";
  @"L4":
    %"v46" = %"v0" +p #8;
    %"chk12" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v46";
    %"v47" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk13" + 0] <- %"v47"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_flush_to_file : func :=
  ir_fn{ "export" "__printf_buffer_flush_to_file"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 1) %"v3";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"v6" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v10" : L = Ptoi %"v7";
    %"v11" : L = Ptoi %"v9";
    %"v12" : L = Sub %"v10", %"v11";
    %"v13" : L = Add %"v4", %"v12";
    %"chk3" : A = (Renew 0 8 Write 1) %"chk0", %"v3";
    store Wl [%"chk3" + 0] <- %"v13";
    %"v18" = %"v0" +p #16;
    %"v19" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v21" = %"v0" +p #48;
    %"v25" = %"v21" +p #128;
    %"v26" : L = Ptoi %"v19";
    %"v27" : L = Ptoi %"v25";
    %"v28" : W = (Cmp Eq L) %"v26", %"v27"
    => br %"v28" ? "L14" : "L15";
  @"L14":
    %"v31" = %"v0" +p #8;
    %"v32" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v34" = %"v0" +p #48;
    %"v35" : L = Ptoi %"v32";
    %"v36" : L = Ptoi %"v34";
    %"v37" : L = Sub %"v35", %"v36";
    %"v42" = %"v0" +p #40;
    %"chk6" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v42";
    %"v43" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v44" = %"v43" +p #216;
    %"chk7" : A = (Check 0 8 Read 8) %"v44";
    %"v45" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v4" : L = Ptoi %"v45";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v47" = %"v45" +p #56;
    %"chk8" : A = (Check 0 8 Read 8) %"v47";
    %"v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v50" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk6", %"v50";
    %"v51" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"v53" = %"v0" +p #48;
    %"chk10" : F = CheckFunction %"v48";
    rawcall %"v55" : L = %"chk10"(P %"v51", P %"v53", L %"v37");
    %"v57" : W = (Cmp Ne L) %"v55", %"v37"
    => br %"v57" ? "iw_2.start" : "L40";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk11" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk11" + 0] <- #0
    => ret void;
  @"L40":
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => ret void;
  @"L15":
    %"v66" = %"v0" +p #16;
    %"v67" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v69" = %"v0" +p #48;
    %"v70" = %"v69" +p #1;
    %"v71" : L = Ptoi %"v67";
    %"v72" : L = Ptoi %"v70";
    %"v73" : W = (Cmp Eq L) %"v71", %"v72"
    => br %"v73" ? "L62" : "L16";
  @"L62":
    %"v78" = %"v0" +p #8;
    %"v79" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v81" = %"v0" +p #16;
    %"v82" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v83" : L = Ptoi %"v79";
    %"v84" : L = Ptoi %"v82";
    %"v85" : W = (Cmp Eq L) %"v83", %"v84"
    => br %"v85" ? "L74" : "L76";
  @"L74":
    %"v90" = %"v0" +p #40;
    %"chk15" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v90";
    %"v91" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v93" = %"v0" +p #48;
    %"chk16" : A = (HalfCheck Upper 0 1 Read 1) %"chk0", %"v93";
    %"v94" : W = (RawLoad (LdNarrow Sb) 0) %"chk16";
    %"v95" : W = (Ext Ub) %"v94";
    call %"v96" : W = $"__GI___overflow"(P %"v91", W %"v95");
    %"v98" : W = (Cmp Eq W) %"v96", #4294967295
    => br %"v98" ? "iw_3.start" : "L88";
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk17" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_3.v3";
    store Ww [%"chk17" + 0] <- #0
    => ret void;
  @"L88":
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => goto "L76";
  @"L76":
    => ret void;
  @"L16":
    %"v107" = %"v0" +p #16;
    %"v108" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v110" = %"v0" +p #40;
    %"chk19" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v110";
    %"v111" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"v112" = %"v111" +p #48;
    %"chk20" : A = (Check 0 8 Read 8) %"v112";
    %"v113" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"v114" : L = Ptoi %"v108";
    %"v115" : L = Ptoi %"v113";
    %"v116" : W = (Cmp Eq L) %"v114", %"v115"
    => br %"v116" ? "L105" : "L104";
  @"L104":
    %"v117" : P = Copy $"glibc_printf_buffer_to_file#str.266";
    %"v118" : P = Copy $"glibc_printf_buffer_to_file#str.267";
    %"v119" : P = Copy $"glibc_printf_buffer_to_file#str.268";
    call void $"__libc_assert_fail"(P %"v117", P %"v118", W #86, P %"v119")
    => goto "L105";
  @"L105":
    %"v121" = %"v0" +p #40;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk19", %"v121";
    %"v122" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v123" = %"v122" +p #40;
    %"v125" = %"v0" +p #8;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"v125";
    %"v126" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"chk23" : A = (Check 0 8 Write 8) %"v123";
    store.ptr [%"chk23" + 0] <- %"v126";
    %"chk24" : A = (Renew 0 8 Read 8) %"chk1", %"v125";
    %"v132" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v134" = %"v0" +p #16;
    %"chk25" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v134";
    %"v135" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"v136" : L = Ptoi %"v132";
    %"v137" : L = Ptoi %"v135";
    %"v138" : W = (Cmp Eq L) %"v136", %"v137"
    => br %"v138" ? "L127" : "L129";
  @"L127":
    %"v140" = %"v0" +p #8;
    %"v142" = %"v0" +p #48;
    %"chk26" : A = (Renew 0 8 Write 8) %"chk1", %"v140";
    store.ptr [%"chk26" + 0] <- %"v142";
    %"v144" = %"v0" +p #16;
    %"v147" = %"v142" +p #1;
    %"chk27" : A = (Renew 0 8 Write 8) %"chk25", %"v144";
    store.ptr [%"chk27" + 0] <- %"v147"
    => goto "L129";
  @"L129":
    %"v150" = %"v0" +p #8;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk1", %"v150";
    %"v151" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk29" + 0] <- %"v151"
    => ret void
} }.

Definition hello_image_fn___printf_buffer_to_file_init : func :=
  ir_fn{ "export" "__printf_buffer_to_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #48;
    %"iw_1.v12" = %"v6" +p #128;
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v6";
    %"iw_1.iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"iw_1.iw_1.v14" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #4;
    %"v11" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk5" + 0] <- %"v2";
    call void $"__printf_buffer_to_file_switch"(P %"v0")
    => ret void
} }.

Definition hello_image_fn___printf_buffer_to_file_done : func :=
  ir_fn{ "export" "__printf_buffer_to_file_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    call void $"__printf_buffer_flush_to_file"(P %"v0");
    call %"v12" : W = $"__printf_buffer_done"(P %"v0")
    => ret %"v12"
} }.

Definition hello_image_fn___printf_buffer_write : func :=
  ir_fn{ "export" "__printf_buffer_write"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.2" : L = phi("L68" => %"v89", "start" => %"v4"); %"pr.1" : P = phi("L68" => %"v86", "start" => %"v2")]:
    %"v19" : W = (Cmp Ugt L) %"pr.2", #0
    => br %"v19" ? "L16" : "L17";
  @"L16":
    %"v24" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v27" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v27";
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v29" : L = Ptoi %"v25";
    %"v30" : L = Ptoi %"v28";
    %"v31" : W = (Cmp Eq L) %"v29", %"v30"
    => br %"v31" ? "L32" : "L33";
  @"L32":
    call %"v35" : W = $"__printf_buffer_flush"(P %"v0");
    %"v36" : W = (Ext Ub) %"v35";
    %"v37" : W = (Cmp Eq W) %"v36", #0
    => goto "L33";
  @"L33" [%"v39" : W = phi("L16" => #0, "L32" => %"v37")]:
    => br %"v39" ? "L20" : "L22";
  @"L20":
    => ret void;
  @"L22":
    %"v45" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v45";
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v48" = %"v0" +p #16;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk2", %"v48";
    %"v49" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v50" : L = Ptoi %"v46";
    %"v51" : L = Ptoi %"v49";
    %"v52" : W = (Cmp Ne L) %"v50", %"v51"
    => br %"v52" ? "L43" : "L42";
  @"L42":
    %"v53" : P = Copy $"glibc_printf_buffer_write#str.41";
    %"v54" : P = Copy $"glibc_printf_buffer_write#str.42";
    %"v55" : P = Copy $"glibc_printf_buffer_write#str.43";
    call void $"__libc_assert_fail"(P %"v53", P %"v54", W #35, P %"v55")
    => goto "L43";
  @"L43":
    %"v58" = %"v0" +p #16;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"v58";
    %"v59" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v61" = %"v0" +p #8;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk1", %"v61";
    %"v62" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v63" : L = Ptoi %"v59";
    %"v64" : L = Ptoi %"v62";
    %"v65" : L = Sub %"v63", %"v64";
    %"v71" : W = (Cmp Ugt L) %"v65", %"pr.2"
    => br %"v71" ? "L68" : "L67";
  @"L67":
    => goto "L68";
  @"L68" [%"pr.3" : L = phi("L67" => %"v65", "L43" => %"pr.2")]:
    %"v74" = %"v0" +p #8;
    %"v75" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v78" : P = $"__GI_memcpy"(P %"v75", P %"pr.1", L %"pr.3");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v74";
    %"v81" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v83" = %"v81" +p %"pr.3";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v74";
    store.ptr [%"chk9" + 0] <- %"v83";
    %"v86" = %"pr.1" +p %"pr.3";
    %"v89" : L = Sub %"pr.2", %"pr.3"
    => goto poll "L15";
  @"L17":
    => ret void
} }.

Definition hello_image_fn_glibc_printf_fp'23__printf_fp_buffer_1 : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_fp_buffer_1"(P %"v0", P %"v2", W %"v4", W %"v6", W %"v8", P %"v10", P %"v12") -> RVoid blocks (hello_image_fn_glibc_printf_fp'23__printf_fp_buffer_1'blocks1 ++ hello_image_fn_glibc_printf_fp'23__printf_fp_buffer_1'blocks2) }.

Definition hello_image_fn___printf_buffer_flush_fp : func :=
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

Definition hello_image_fn___printf_fp_l_buffer : func :=
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

Definition hello_image_fn___printf_buffer_flush_fp_to_wide : func :=
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

Definition hello_image_fn_glibc_printf_fp'23__printf_buffer_mark_failed : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_mark_failed"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn_glibc_printf_fp'23__printf_buffer_pad : func :=
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

Definition hello_image_fn_glibc_printf_fp'23__printf_buffer_putc : func :=
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

Definition hello_image_fn_glibc_printf_fp'23__printf_buffer_puts : func :=
  ir_fn{ "local" "glibc_printf_fp#__printf_buffer_puts"(P %"v0", P %"v2") -> RVoid {
  @"start":
    call void $"__printf_buffer_puts_1"(P %"v0", P %"v2")
    => ret void
} }.
