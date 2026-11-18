(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedWPBlocks1403x1 HelloImageTypedWPBlocks1403x2 IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___wprintf : func :=
  ir_fn{ "export" "__wprintf"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk0" + 0] <- %"va_args";
    %"v4" : P = Copy $"stdout";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v7" : W = $"__vfwprintf_internal"(P %"v5", P %"v0", P %"v2", W #0)
    => ret %"v7"
} }.

Definition hello_image_fn___wprintf_fp_l_buffer : func :=
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

Definition hello_image_fn___wprintf_fphex_l_buffer : func :=
  ir_fn{ "export" "__wprintf_fphex_l_buffer"(P %"v0", P %"v2", P %"v4", P %"v6") -> RVoid {
  @"start":
    %"v8" : P = (Alloc 8) #120;
    %"v9" = %"v8" +p #56;
    %"iw_1.v12" = %"v9" +p #64;
    %"chk0" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk0" + 0] <- %"v9";
    %"iw_1.iw_1.v11" = %"v8" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v9";
    %"iw_1.iw_1.v14" = %"v8" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v8" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v8" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #10;
    %"v10" = %"v8" +p #40;
    %"iw_2.v10" = %"v2" +p #8;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_2.v10";
    %"iw_2.v11" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_2.v12" = %"iw_2.v11" +p #56;
    %"iw_2.v17" = %"iw_2.v12" +p #24;
    %"chk6" : A = (Check 0 4 Read 1) %"iw_2.v17";
    %"iw_2.v18" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"chk7" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v10";
    store Ww [%"chk7" + 0] <- %"iw_2.v18";
    %"v13" = %"v8" +p #48;
    %"chk8" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk8" + 0] <- %"v0";
    %"v15" : P = Copy $"glibc_printf_fphex#str.295";
    call void $"glibc_printf_fphex#__printf_fphex_buffer"(P %"v8", P %"v15", P %"v4", P %"v6");
    %"iw_3.v3" = %"v8" +p #32;
    %"chk9" : A = (Renew 0 4 Read 1) %"chk4", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk9";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L18" : "L20";
  @"L18":
    %"v23" = %"v8" +p #48;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk8", %"v23";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_4.v3" = %"v24" +p #32;
    %"chk11" : A = (Check 0 4 Write 1) %"iw_4.v3";
    store Ww [%"chk11" + 0] <- #0
    => ret void;
  @"L20":
    call void $"__printf_buffer_flush_fphex_to_wide"(P %"v8")
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer : func :=
  ir_fn{ "export" "__wprintf_buffer"(P %"v0", P %"v2", P %"v4", W %"v6") -> RVoid blocks (hello_image_fn___wprintf_buffer'blocks1 ++ hello_image_fn___wprintf_buffer'blocks2) }.

Definition hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_has_failed : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_has_failed"(P %"v0") -> (RClass W) {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"v3";
    %"v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"v5" : W = (Cmp Eq W) %"v4", #0
    => ret %"v5"
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_mark_failed : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_mark_failed"(P %"v0") -> RVoid {
  @"start":
    %"v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Write 1) %"v3";
    store Ww [%"chk0" + 0] <- #0
    => ret void
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_pad : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_pad"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"v10" : W = (Cmp Sgt L) %"v4", #0
    => br %"v10" ? "L6" : "L8";
  @"L6":
    %"v12" : W = (Ext Sb) %"v2";
    call void $"__wprintf_buffer_pad_1"(P %"v0", W %"v12", L %"v4")
    => goto "L8";
  @"L8":
    => ret void
} }.

Definition hello_image_fn_glibc_vfwprintf_internal'23__wprintf_buffer_putc : func :=
  ir_fn{ "local" "glibc_vfwprintf_internal#__wprintf_buffer_putc"(P %"v0", W %"v2") -> RVoid {
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
    %"v19" = %"v18" +p #4;
    %"chk3" : A = (Renew 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk3" + 0] <- %"v19";
    %"chk4" : A = (Check 0 4 Write 1) %"v18";
    store Ww [%"chk4" + 0] <- %"v2"
    => goto "L6";
  @"L5":
    call void $"__wprintf_buffer_putc_1"(P %"v0", W %"v2")
    => goto "L6";
  @"L6":
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_as_file_overflow : func :=
  ir_fn{ "export" "__wprintf_buffer_as_file_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"iw_1.v6" = %"v0" +p #224;
    %"iw_1.v7" = %"iw_1.v6" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" = %"v0" +p #456;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" = %"iw_1.v11" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v12";
    %"iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v14" : L = Ptoi %"iw_1.v8";
    %"iw_1.v15" : L = Ptoi %"iw_1.v13";
    %"iw_1.v16" : W = (Cmp Uge L) %"iw_1.v14", %"iw_1.v15"
    => br %"iw_1.v16" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v17" : P = Copy $"glibc_wprintf_buffer_as_file#str.266";
    %"iw_1.v18" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v19" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v17", P %"iw_1.v18", W #30, P %"iw_1.v19")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v24" = %"v0" +p #224;
    %"iw_1.v25" = %"iw_1.v24" +p #32;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v25";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v28" = %"v0" +p #456;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v30" = %"iw_1.v29" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v30";
    %"iw_1.v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v32" : L = Ptoi %"iw_1.v26";
    %"iw_1.v33" : L = Ptoi %"iw_1.v31";
    %"iw_1.v34" : W = (Cmp Ule L) %"iw_1.v32", %"iw_1.v33"
    => br %"iw_1.v34" ? "iw_1.L22" : "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v35" : P = Copy $"glibc_wprintf_buffer_as_file#str.269";
    %"iw_1.v36" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v37" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v35", P %"iw_1.v36", W #31, P %"iw_1.v37")
    => goto "iw_1.L22";
  @"iw_1.L22":
    %"iw_1.v42" = %"v0" +p #224;
    %"iw_1.v43" = %"iw_1.v42" +p #24;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v46" = %"v0" +p #456;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v46";
    %"iw_1.v47" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v47";
    %"iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v49" : L = Ptoi %"iw_1.v44";
    %"iw_1.v50" : L = Ptoi %"iw_1.v48";
    %"iw_1.v51" : W = (Cmp Eq L) %"iw_1.v49", %"iw_1.v50"
    => br %"iw_1.v51" ? "iw_1.L40" : "iw_1.L39";
  @"iw_1.L39":
    %"iw_1.v52" : P = Copy $"glibc_wprintf_buffer_as_file#str.270";
    %"iw_1.v53" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v54" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v52", P %"iw_1.v53", W #32, P %"iw_1.v54")
    => goto "iw_1.L40";
  @"iw_1.L40":
    %"iw_1.v59" = %"v0" +p #224;
    %"iw_1.v60" = %"iw_1.v59" +p #40;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v60";
    %"iw_1.v61" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v63" = %"v0" +p #456;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v63";
    %"iw_1.v64" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v65" = %"iw_1.v64" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v65";
    %"iw_1.v66" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v67" : L = Ptoi %"iw_1.v61";
    %"iw_1.v68" : L = Ptoi %"iw_1.v66";
    %"iw_1.v69" : W = (Cmp Eq L) %"iw_1.v67", %"iw_1.v68"
    => br %"iw_1.v69" ? "iw_1.L57" : "iw_1.L56";
  @"iw_1.L56":
    %"iw_1.v70" : P = Copy $"glibc_wprintf_buffer_as_file#str.271";
    %"iw_1.v71" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v72" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v70", P %"iw_1.v71", W #33, P %"iw_1.v72")
    => goto "iw_1.L57";
  @"iw_1.L57":
    %"iw_1.v74" = %"v0" +p #456;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v76" = %"iw_1.v75" +p #8;
    %"iw_1.v78" = %"v0" +p #224;
    %"iw_1.v79" = %"iw_1.v78" +p #32;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v76";
    store.ptr [%"chk14" + 0] <- %"iw_1.v80";
    %"v11" : W = (Cmp Ne W) %"v2", #4294967295
    => br %"v11" ? "L7" : "L9";
  @"L7":
    %"v13" = %"v0" +p #456;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v13";
    %"v14" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"iw_2.v8" = %"v14" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v11" = %"v14" +p #16;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v14" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v19" = %"iw_2.v18" +p #4;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk16", %"iw_2.v17";
    store.ptr [%"chk19" + 0] <- %"iw_2.v19";
    %"chk20" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk20" + 0] <- %"v2"
    => goto "L9";
  @"iw_2.L5":
    call void $"__wprintf_buffer_putc_1"(P %"v14", W %"v2")
    => goto "L9";
  @"L9" [%"pr.1" : W = phi("iw_2.L4" => %"v2", "iw_2.L5" => %"v2", "iw_1.L57" => #0)]:
    %"v20" = %"v0" +p #456;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk1", %"v20";
    %"v21" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_3.v3" = %"v21" +p #32;
    %"chk22" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v24" : W = (Cmp Ne W) %"iw_3.v4", #0
    => br %"v24" ? "L25" : "L26";
  @"L25":
    %"v28" = %"v0" +p #456;
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v30" = %"v29" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v30";
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v34" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v35" = %"v34" +p #16;
    %"chk26" : A = (Check 0 8 Read 8) %"v35";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v37" : L = Ptoi %"v31";
    %"v38" : L = Ptoi %"v36";
    %"v39" : W = (Cmp Eq L) %"v37", %"v38"
    => goto "L26";
  @"L26" [%"v41" : W = phi("L9" => #0, "L25" => %"v39")]:
    => br %"v41" ? "L16" : "iw_4.start";
  @"L16":
    %"v43" = %"v0" +p #456;
    %"v44" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v45" : W = $"__wprintf_buffer_flush"(P %"v44")
    => goto "iw_4.start";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #224;
    %"iw_4.v4" = %"iw_4.v3" +p #24;
    %"iw_4.v6" = %"v0" +p #456;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v6";
    %"iw_4.v7" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Check 0 8 Read 8) %"iw_4.v7";
    %"iw_4.v8" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk6", %"iw_4.v4";
    store.ptr [%"chk30" + 0] <- %"iw_4.v8";
    %"iw_4.v11" = %"iw_4.v3" +p #32;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v6";
    %"iw_4.v14" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_4.v15" = %"iw_4.v14" +p #8;
    %"chk32" : A = (Check 0 8 Read 8) %"iw_4.v15";
    %"iw_4.v16" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v11";
    store.ptr [%"chk33" + 0] <- %"iw_4.v16";
    %"iw_4.v19" = %"iw_4.v3" +p #40;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v6";
    %"iw_4.v22" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_4.v23" = %"iw_4.v22" +p #16;
    %"chk35" : A = (Check 0 8 Read 8) %"iw_4.v23";
    %"iw_4.v24" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Write 8) %"chk9", %"iw_4.v19";
    store.ptr [%"chk36" + 0] <- %"iw_4.v24";
    %"v52" = %"v0" +p #456;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"v52";
    %"v53" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_5.v3" = %"v53" +p #32;
    %"chk38" : A = (Check 0 4 Read 1) %"iw_5.v3";
    %"iw_5.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    %"v56" : W = (Cmp Ne W) %"iw_5.v4", #0
    => br %"v56" ? "L48" : "L49";
  @"L48":
    %"v58" : W = (Ext Ub) %"pr.1"
    => ret %"v58";
  @"L49":
    => ret #4294967295
} }.

Definition hello_image_fn___wprintf_buffer_as_file_xsputn : func :=
  ir_fn{ "export" "__wprintf_buffer_as_file_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"iw_1.v6" = %"v0" +p #224;
    %"iw_1.v7" = %"iw_1.v6" +p #32;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v10" = %"v0" +p #456;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v12" = %"iw_1.v11" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v12";
    %"iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v14" : L = Ptoi %"iw_1.v8";
    %"iw_1.v15" : L = Ptoi %"iw_1.v13";
    %"iw_1.v16" : W = (Cmp Uge L) %"iw_1.v14", %"iw_1.v15"
    => br %"iw_1.v16" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v17" : P = Copy $"glibc_wprintf_buffer_as_file#str.266";
    %"iw_1.v18" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v19" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v17", P %"iw_1.v18", W #30, P %"iw_1.v19")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v24" = %"v0" +p #224;
    %"iw_1.v25" = %"iw_1.v24" +p #32;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v25";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v28" = %"v0" +p #456;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v30" = %"iw_1.v29" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v30";
    %"iw_1.v31" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v32" : L = Ptoi %"iw_1.v26";
    %"iw_1.v33" : L = Ptoi %"iw_1.v31";
    %"iw_1.v34" : W = (Cmp Ule L) %"iw_1.v32", %"iw_1.v33"
    => br %"iw_1.v34" ? "iw_1.L22" : "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v35" : P = Copy $"glibc_wprintf_buffer_as_file#str.269";
    %"iw_1.v36" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v37" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v35", P %"iw_1.v36", W #31, P %"iw_1.v37")
    => goto "iw_1.L22";
  @"iw_1.L22":
    %"iw_1.v42" = %"v0" +p #224;
    %"iw_1.v43" = %"iw_1.v42" +p #24;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v46" = %"v0" +p #456;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v46";
    %"iw_1.v47" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v47";
    %"iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v49" : L = Ptoi %"iw_1.v44";
    %"iw_1.v50" : L = Ptoi %"iw_1.v48";
    %"iw_1.v51" : W = (Cmp Eq L) %"iw_1.v49", %"iw_1.v50"
    => br %"iw_1.v51" ? "iw_1.L40" : "iw_1.L39";
  @"iw_1.L39":
    %"iw_1.v52" : P = Copy $"glibc_wprintf_buffer_as_file#str.270";
    %"iw_1.v53" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v54" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v52", P %"iw_1.v53", W #32, P %"iw_1.v54")
    => goto "iw_1.L40";
  @"iw_1.L40":
    %"iw_1.v59" = %"v0" +p #224;
    %"iw_1.v60" = %"iw_1.v59" +p #40;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v60";
    %"iw_1.v61" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v63" = %"v0" +p #456;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v63";
    %"iw_1.v64" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v65" = %"iw_1.v64" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v65";
    %"iw_1.v66" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v67" : L = Ptoi %"iw_1.v61";
    %"iw_1.v68" : L = Ptoi %"iw_1.v66";
    %"iw_1.v69" : W = (Cmp Eq L) %"iw_1.v67", %"iw_1.v68"
    => br %"iw_1.v69" ? "iw_1.L57" : "iw_1.L56";
  @"iw_1.L56":
    %"iw_1.v70" : P = Copy $"glibc_wprintf_buffer_as_file#str.271";
    %"iw_1.v71" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v72" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v70", P %"iw_1.v71", W #33, P %"iw_1.v72")
    => goto "iw_1.L57";
  @"iw_1.L57":
    %"iw_1.v74" = %"v0" +p #456;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v76" = %"iw_1.v75" +p #8;
    %"iw_1.v78" = %"v0" +p #224;
    %"iw_1.v79" = %"iw_1.v78" +p #32;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v76";
    store.ptr [%"chk14" + 0] <- %"iw_1.v80";
    %"v10" = %"v0" +p #456;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call void $"__wprintf_buffer_write"(P %"v11", P %"v2", L %"v4");
    %"iw_2.v3" = %"v0" +p #224;
    %"iw_2.v4" = %"iw_2.v3" +p #24;
    %"iw_2.v6" = %"v0" +p #456;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v6";
    %"iw_2.v7" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 8) %"iw_2.v7";
    %"iw_2.v8" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk6", %"iw_2.v4";
    store.ptr [%"chk18" + 0] <- %"iw_2.v8";
    %"iw_2.v11" = %"iw_2.v3" +p #32;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v6";
    %"iw_2.v14" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_2.v15" = %"iw_2.v14" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_2.v15";
    %"iw_2.v16" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v11";
    store.ptr [%"chk21" + 0] <- %"iw_2.v16";
    %"iw_2.v19" = %"iw_2.v3" +p #40;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v6";
    %"iw_2.v22" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_2.v23" = %"iw_2.v22" +p #16;
    %"chk23" : A = (Check 0 8 Read 8) %"iw_2.v23";
    %"iw_2.v24" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk9", %"iw_2.v19";
    store.ptr [%"chk24" + 0] <- %"iw_2.v24";
    %"v19" = %"v0" +p #456;
    %"chk25" : A = (Renew 0 8 Read 8) %"chk1", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk25";
    %"iw_3.v3" = %"v20" +p #32;
    %"chk26" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk26";
    %"v23" : W = (Cmp Ne W) %"iw_3.v4", #0
    => br %"v23" ? "L15" : "L16";
  @"L15":
    => ret %"v4";
  @"L16":
    => ret #0
} }.

Definition hello_image_fn___wprintf_buffer_as_file_init : func :=
  ir_fn{ "export" "__wprintf_buffer_as_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v5" = %"v0" +p #136;
    %"chk0" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk0" + 0] <- #0;
    %"v8" = %"v0" +p #224;
    %"v9" : P = Copy $"__io_vtables";
    %"v10" = %"v9" +p #2184;
    call void $"_IO_no_init"(P %"v0", W #32768, W #0, P %"v8", P %"v10");
    call %"v53" : W = $"_IO_fwide"(P %"v0", W #1);
    %"v56" = %"v0" +p #456;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v56";
    store.ptr [%"chk1" + 0] <- %"v2";
    %"iw_1.v3" = %"v0" +p #224;
    %"iw_1.v4" = %"iw_1.v3" +p #24;
    %"iw_1.v6" = %"v0" +p #456;
    %"chk2" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v4";
    store.ptr [%"chk4" + 0] <- %"iw_1.v8";
    %"iw_1.v11" = %"iw_1.v3" +p #32;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v6";
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v15" = %"iw_1.v14" +p #8;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v15";
    %"iw_1.v16" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"chk7" : A = (HalfCheck Upper 0 8 Write 8) %"chk4", %"iw_1.v11";
    store.ptr [%"chk7" + 0] <- %"iw_1.v16";
    %"iw_1.v19" = %"iw_1.v3" +p #40;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v6";
    %"iw_1.v22" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v23" = %"iw_1.v22" +p #16;
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"chk10" : A = (HalfCheck Upper 0 8 Write 8) %"chk4", %"iw_1.v19";
    store.ptr [%"chk10" + 0] <- %"iw_1.v24";
    %"v60" = %"v0" +p #24;
    %"v62" = %"v0" +p #32;
    %"chk11" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v62";
    %"v63" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"chk12" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v60";
    store.ptr [%"chk12" + 0] <- %"v63";
    %"v65" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk11", %"v62";
    %"v68" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v65";
    store.ptr [%"chk14" + 0] <- %"v68";
    %"v70" = %"v0" +p #16;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk11", %"v62";
    %"v73" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"chk16" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v70";
    store.ptr [%"chk16" + 0] <- %"v73"
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_as_file_terminate : func :=
  ir_fn{ "export" "__wprintf_buffer_as_file_terminate"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #32
    => br %"v7" ? "L2" : "iw_1.start";
  @"L2":
    => ret #0;
  @"iw_1.start":
    %"iw_1.v6" = %"v0" +p #224;
    %"iw_1.v7" = %"iw_1.v6" +p #32;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v7";
    %"iw_1.v8" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v10" = %"v0" +p #456;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v10";
    %"iw_1.v11" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v12" = %"iw_1.v11" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v12";
    %"iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v14" : L = Ptoi %"iw_1.v8";
    %"iw_1.v15" : L = Ptoi %"iw_1.v13";
    %"iw_1.v16" : W = (Cmp Uge L) %"iw_1.v14", %"iw_1.v15"
    => br %"iw_1.v16" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v17" : P = Copy $"glibc_wprintf_buffer_as_file#str.266";
    %"iw_1.v18" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v19" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v17", P %"iw_1.v18", W #30, P %"iw_1.v19")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v24" = %"v0" +p #224;
    %"iw_1.v25" = %"iw_1.v24" +p #32;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v25";
    %"iw_1.v26" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v28" = %"v0" +p #456;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v30" = %"iw_1.v29" +p #16;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v30";
    %"iw_1.v31" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v32" : L = Ptoi %"iw_1.v26";
    %"iw_1.v33" : L = Ptoi %"iw_1.v31";
    %"iw_1.v34" : W = (Cmp Ule L) %"iw_1.v32", %"iw_1.v33"
    => br %"iw_1.v34" ? "iw_1.L22" : "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v35" : P = Copy $"glibc_wprintf_buffer_as_file#str.269";
    %"iw_1.v36" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v37" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v35", P %"iw_1.v36", W #31, P %"iw_1.v37")
    => goto "iw_1.L22";
  @"iw_1.L22":
    %"iw_1.v42" = %"v0" +p #224;
    %"iw_1.v43" = %"iw_1.v42" +p #24;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v46" = %"v0" +p #456;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v46";
    %"iw_1.v47" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v47";
    %"iw_1.v48" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v49" : L = Ptoi %"iw_1.v44";
    %"iw_1.v50" : L = Ptoi %"iw_1.v48";
    %"iw_1.v51" : W = (Cmp Eq L) %"iw_1.v49", %"iw_1.v50"
    => br %"iw_1.v51" ? "iw_1.L40" : "iw_1.L39";
  @"iw_1.L39":
    %"iw_1.v52" : P = Copy $"glibc_wprintf_buffer_as_file#str.270";
    %"iw_1.v53" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v54" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v52", P %"iw_1.v53", W #32, P %"iw_1.v54")
    => goto "iw_1.L40";
  @"iw_1.L40":
    %"iw_1.v59" = %"v0" +p #224;
    %"iw_1.v60" = %"iw_1.v59" +p #40;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v60";
    %"iw_1.v61" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v63" = %"v0" +p #456;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v63";
    %"iw_1.v64" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v65" = %"iw_1.v64" +p #16;
    %"chk12" : A = (Check 0 8 Read 8) %"iw_1.v65";
    %"iw_1.v66" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v67" : L = Ptoi %"iw_1.v61";
    %"iw_1.v68" : L = Ptoi %"iw_1.v66";
    %"iw_1.v69" : W = (Cmp Eq L) %"iw_1.v67", %"iw_1.v68"
    => br %"iw_1.v69" ? "iw_1.L57" : "iw_1.L56";
  @"iw_1.L56":
    %"iw_1.v70" : P = Copy $"glibc_wprintf_buffer_as_file#str.271";
    %"iw_1.v71" : P = Copy $"glibc_wprintf_buffer_as_file#str.267";
    %"iw_1.v72" : P = Copy $"glibc_wprintf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v70", P %"iw_1.v71", W #33, P %"iw_1.v72")
    => goto "iw_1.L57";
  @"iw_1.L57":
    %"iw_1.v74" = %"v0" +p #456;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v76" = %"iw_1.v75" +p #8;
    %"iw_1.v78" = %"v0" +p #224;
    %"iw_1.v79" = %"iw_1.v78" +p #32;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v79";
    %"iw_1.v80" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"iw_1.v76";
    store.ptr [%"chk15" + 0] <- %"iw_1.v80"
    => ret #1
} }.

Definition hello_image_fn___wprintf_buffer_done : func :=
  ir_fn{ "export" "__wprintf_buffer_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    %"v12" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v16" : L = Ptoi %"v13";
    %"v17" : L = Ptoi %"v15";
    %"v18" : L = Sub %"v16", %"v17";
    %"v19" : L = Div %"v18", #4;
    %"v25" = %"v0" +p #24;
    %"v26" : L = (RawLoad LdL (-8)) %"chk0";
    %"v28" : L = Add %"v26", %"v19";
    %"v29" : W = (Cmp Ult L) %"v28", %"v26";
    %"v30" : L = (Ext Uw) %"v29";
    %"v33" : L = (Ext Sw) %"v28";
    %"v34" : L = Sar %"v33", #63;
    %"v35" : W = (Cmp Ne L) %"v28", %"v33";
    %"v36" : W = (Cmp Ne L) %"v30", %"v34";
    %"v37" : W = Or %"v35", %"v36"
    => br %"v37" ? "L21" : "L22";
  @"L21":
    %"v38" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v38";
    store Ww [%"chk4" + 0] <- #75
    => ret #4294967295;
  @"L22":
    %"v41" : W = Copy %"v28"
    => ret %"v41"
} }.

Definition hello_image_fn___wprintf_buffer_flush : func :=
  ir_fn{ "export" "__wprintf_buffer_flush"(P %"v0") -> (RClass W) {
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
    %"iw_2.v21" : W = (Cmp Eq W) %"iw_2.v4", #0
    => br %"iw_2.v21" ? "iw_3.start" : "iw_2.L22";
  @"iw_2.L8":
    call void $"__wprintf_buffer_flush_to_file"(P %"v0")
    => goto "iw_3.start";
  @"iw_2.L10":
    %"iw_2.v12" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_2.v12";
    %"iw_2.v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_2.v17" = %"iw_2.v13" +p #18446744073709551612;
    %"chk3" : A = (Check 0 4 Write 1) %"iw_2.v17";
    store Ww [%"chk3" + 0] <- #0;
    %"iw_2.v18" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"iw_2.v18";
    store Ww [%"chk4" + 0] <- #7;
    %"iw_2.iw_1.v3" = %"v0" +p #32;
    %"chk5" : A = (Renew 0 4 Write 1) %"chk0", %"iw_2.iw_1.v3";
    store Ww [%"chk5" + 0] <- #0
    => goto "iw_3.start";
  @"iw_2.L22":
    %"iw_2.v23" : W = (Cmp Eq W) %"iw_2.v4", #2
    => br %"iw_2.v23" ? poll "iw_2.L8" : "iw_2.L24";
  @"iw_2.L24":
    %"iw_2.v25" : W = (Cmp Eq W) %"iw_2.v4", #1
    => br %"iw_2.v25" ? poll "iw_2.L10" : "iw_2.L6";
  @"iw_2.L6":
    => unreachable;
  @"iw_3.start":
    %"iw_3.v3" = %"v0" +p #32;
    %"chk6" : A = (Renew 0 4 Read 1) %"chk0", %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk6";
    %"iw_3.v5" : W = (Cmp Eq W) %"iw_3.v4", #0
    => br %"iw_3.v5" ? "L13" : "L15";
  @"L13":
    => ret #0;
  @"L15":
    %"v25" = %"v0" +p #8;
    %"chk7" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"v28" = %"v0" +p #16;
    %"v29" : P = (RawLoadPointer 8 load_effects) %"chk7";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : W = (Cmp Ne L) %"v30", %"v31"
    => br %"v32" ? "L23" : "L22";
  @"L22":
    %"v33" : P = Copy $"glibc_wprintf_buffer_flush#str.39";
    %"v34" : P = Copy $"glibc_wprintf_buffer_flush#str.40";
    %"v35" : P = Copy $"glibc_wprintf_buffer_flush#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #70, P %"v35")
    => goto "L23";
  @"L23":
    => ret #1
} }.

Definition hello_image_fn___wprintf_buffer_pad_1 : func :=
  ir_fn{ "export" "__wprintf_buffer_pad_1"(P %"v0", W %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.1" : L = phi("L67" => %"v86", "start" => %"v4")]:
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
    call %"v33" : W = $"__wprintf_buffer_flush"(P %"v0");
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
    %"v51" : P = Copy $"glibc_wprintf_buffer_pad_1#str.41";
    %"v52" : P = Copy $"glibc_wprintf_buffer_pad_1#str.42";
    %"v53" : P = Copy $"glibc_wprintf_buffer_pad_1#str.43";
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
    %"v64" : L = Div %"v63", #4;
    %"v70" : W = (Cmp Ugt L) %"v64", %"pr.1"
    => br %"v70" ? "L67" : "L66";
  @"L66":
    => goto "L67";
  @"L67" [%"pr.2" : L = phi("L66" => %"v64", "L41" => %"pr.1")]:
    %"v73" = %"v0" +p #8;
    %"v74" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v77" : P = $"__GI___wmemset"(P %"v74", W %"v2", L %"pr.2");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v73";
    %"v80" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v82" : L = Shl %"pr.2", #2;
    %"v83" = %"v80" +p %"v82";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v73";
    store.ptr [%"chk9" + 0] <- %"v83";
    %"v86" : L = Sub %"pr.1", %"pr.2";
    %"v88" : W = (Cmp Ugt L) %"v86", #0
    => br %"v88" ? poll "L15" : "L17";
  @"L17":
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_putc_1 : func :=
  ir_fn{ "export" "__wprintf_buffer_putc_1"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L13" : "L12";
  @"L12":
    call %"v15" : W = $"__wprintf_buffer_flush"(P %"v0");
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
    %"v33" : P = Copy $"glibc_wprintf_buffer_putc_1#str.39";
    %"v34" : P = Copy $"glibc_wprintf_buffer_putc_1#str.40";
    %"v35" : P = Copy $"glibc_wprintf_buffer_putc_1#str.41";
    call void $"__libc_assert_fail"(P %"v33", P %"v34", W #27, P %"v35")
    => goto "L23";
  @"L23":
    %"v37" = %"v0" +p #8;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk1", %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v39" = %"v38" +p #4;
    %"chk4" : A = (Renew 0 8 Write 8) %"chk1", %"v37";
    store.ptr [%"chk4" + 0] <- %"v39";
    %"chk5" : A = (Check 0 4 Write 1) %"v38";
    store Ww [%"chk5" + 0] <- %"v2"
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_flush_to_file : func :=
  ir_fn{ "export" "__wprintf_buffer_flush_to_file"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v7" = %"v0" +p #48;
    %"v8" : L = Ptoi %"v5";
    %"v9" : L = Ptoi %"v7";
    %"v10" : L = Sub %"v8", %"v9";
    %"v11" : L = Div %"v10", #4;
    %"v16" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v18" = %"v17" +p #216;
    %"chk2" : A = (Check 0 8 Read 8) %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v4" : L = Ptoi %"v19";
    %"iw_1.v7" : P = Copy $"__io_vtables";
    %"iw_1.v8" : L = Ptoi %"iw_1.v7";
    %"iw_1.v9" : L = Sub %"iw_1.v4", %"iw_1.v8";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v9", #2352
    => br %"iw_1.v15" ? "iw_1.L10" : "iw_1.join";
  @"iw_1.L10":
    call void $"_IO_vtable_check"()
    => goto "iw_1.join";
  @"iw_1.join":
    %"v21" = %"v19" +p #56;
    %"chk3" : A = (Check 0 8 Read 8) %"v21";
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"v24" = %"v0" +p #40;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"v24";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v27" = %"v0" +p #48;
    %"chk5" : F = CheckFunction %"v22";
    rawcall %"v29" : L = %"chk5"(P %"v25", P %"v27", L %"v11");
    %"v31" : W = (Cmp Ne L) %"v29", %"v11"
    => br %"v31" ? "iw_2.start" : "L14";
  @"iw_2.start":
    %"iw_2.v3" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_2.v3";
    store Ww [%"chk6" + 0] <- #0
    => ret void;
  @"L14":
    %"v35" = %"v0" +p #24;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v35";
    %"v36" : L = (RawLoad LdL 0) %"chk7";
    %"v38" : L = Add %"v36", %"v11";
    %"chk8" : A = (Renew 0 8 Write 1) %"chk7", %"v35";
    store Wl [%"chk8" + 0] <- %"v38";
    %"v40" = %"v0" +p #8;
    %"v42" = %"v0" +p #48;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk0", %"v40";
    store.ptr [%"chk9" + 0] <- %"v42"
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_to_file_init : func :=
  ir_fn{ "export" "__wprintf_buffer_to_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v6" = %"v0" +p #48;
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v6";
    %"iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v6";
    %"iw_1.v14" = %"v0" +p #16;
    %"iw_1.v18" = %"v6" +p #512;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v18";
    %"iw_1.v20" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.v20";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.v22" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v22";
    store Ww [%"chk4" + 0] <- #2;
    %"v11" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk5" + 0] <- %"v2"
    => ret void
} }.

Definition hello_image_fn___wprintf_buffer_to_file_done : func :=
  ir_fn{ "export" "__wprintf_buffer_to_file_done"(P %"v0") -> (RClass W) {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L2" : "L4";
  @"L2":
    => ret #4294967295;
  @"L4":
    call void $"__wprintf_buffer_flush_to_file"(P %"v0");
    call %"v12" : W = $"__wprintf_buffer_done"(P %"v0")
    => ret %"v12"
} }.

Definition hello_image_fn___wprintf_buffer_write : func :=
  ir_fn{ "export" "__wprintf_buffer_write"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk0" : A = (Check 0 4 Read 1) %"iw_1.v3";
    %"iw_1.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk0";
    %"iw_1.v5" : W = (Cmp Eq W) %"iw_1.v4", #0
    => br %"iw_1.v5" ? "L6" : "L15";
  @"L6":
    => ret void;
  @"L15" [%"pr.2" : L = phi("L69" => %"v92", "start" => %"v4"); %"pr.1" : P = phi("L69" => %"v89", "start" => %"v2")]:
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
    call %"v35" : W = $"__wprintf_buffer_flush"(P %"v0");
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
    %"v53" : P = Copy $"glibc_wprintf_buffer_write#str.41";
    %"v54" : P = Copy $"glibc_wprintf_buffer_write#str.42";
    %"v55" : P = Copy $"glibc_wprintf_buffer_write#str.43";
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
    %"v66" : L = Div %"v65", #4;
    %"v72" : W = (Cmp Ugt L) %"v66", %"pr.2"
    => br %"v72" ? "L69" : "L68";
  @"L68":
    => goto "L69";
  @"L69" [%"pr.3" : L = phi("L68" => %"v66", "L43" => %"pr.2")]:
    %"v75" = %"v0" +p #8;
    %"v76" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call %"v79" : P = $"__wmemcpy"(P %"v76", P %"pr.1", L %"pr.3");
    %"chk8" : A = (Renew 0 8 Read 8) %"chk1", %"v75";
    %"v82" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"v84" : L = Shl %"pr.3", #2;
    %"v85" = %"v82" +p %"v84";
    %"chk9" : A = (Renew 0 8 Write 8) %"chk1", %"v75";
    store.ptr [%"chk9" + 0] <- %"v85";
    %"v89" = %"pr.1" +p %"v84";
    %"v92" : L = Sub %"pr.2", %"pr.3"
    => goto poll "L15";
  @"L17":
    => ret void
} }.

Definition hello_image_fn___wprintf_function_invoke : func :=
  ir_fn{ "export" "__wprintf_function_invoke"(P %"v0", P %"v2", P %"v4", L %"v6", P %"v8") -> (RClass W) {
  @"start":
    %"v10" : P = (Alloc 8) #32;
    %"v52" : P = (Alloc 8) #464;
    %"v19" : W = (Cmp Ule L) %"v6", #4
    => br %"v19" ? "L14" : "L13";
  @"L13":
    call %"v21" : P = $"calloc"(L %"v6", L #8);
    %"v26" : L = Ptoi %"v21";
    %"v27" : L = Ptoi #0;
    %"v28" : W = (Cmp Eq L) %"v26", %"v27"
    => br %"v28" ? "L22" : "L14";
  @"L22":
    => ret #4294967295;
  @"L14" [%"pr.1" : P = phi("start" => %"v10", "L13" => %"v21")]:
    => goto "L32";
  @"L32" [%"pr.2" : W = phi("L14" => #0, "L33" => %"v51")]:
    %"v38" : L = (Ext Uw) %"pr.2";
    %"v39" : W = (Cmp Ult L) %"v38", %"v6"
    => br %"v39" ? "L33" : "L35";
  @"L33":
    %"v43" : L = Shl %"v38", #3;
    %"v44" = %"pr.1" +p %"v43";
    %"v48" : L = Shl %"v38", #4;
    %"v49" = %"v4" +p %"v48";
    %"chk0" : A = (Check 0 8 Write 8) %"v44";
    store.ptr [%"chk0" + 0] <- %"v49";
    %"v51" : W = Add %"pr.2", #1
    => goto poll "L32";
  @"L35":
    call void $"__wprintf_buffer_as_file_init"(P %"v52", P %"v0");
    %"chk1" : F = CheckFunction %"v2";
    rawcall %"v59" : W = %"chk1"(P %"v52", P %"v8", P %"pr.1");
    call %"v63" : W = $"__wprintf_buffer_as_file_terminate"(P %"v52");
    %"v64" : W = (Ext Ub) %"v63";
    %"v65" : W = (Cmp Eq W) %"v64", #0
    => br %"v65" ? "L62" : "L61";
  @"L61":
    => goto "L62";
  @"L62" [%"pr.3" : W = phi("L61" => %"v59", "L35" => #4294967295)]:
    %"v71" : L = Ptoi %"pr.1";
    %"v72" : L = Ptoi %"v10";
    %"v73" : W = (Cmp Ne L) %"v71", %"v72"
    => br %"v73" ? "L67" : "L69";
  @"L67":
    call void $"free"(P %"pr.1")
    => goto "L69";
  @"L69":
    => ret %"pr.3"
} }.
