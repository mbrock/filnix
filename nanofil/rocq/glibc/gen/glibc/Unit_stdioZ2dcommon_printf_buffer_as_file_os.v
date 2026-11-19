(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_as_file.os` object.
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

Definition fn___printf_buffer_as_file_init : func :=
  ir_fn{ "export" "__printf_buffer_as_file_init"(P %"v0", P %"v2") -> RVoid {
  @"start":
    %"v5" = %"v0" +p #136;
    %"chk0" : A = (Check 0 8 Write 8) %"v5";
    store.ptr [%"chk0" + 0] <- #0;
    call void $"_IO_no_init"(P %"v0", W #32768, W #4294967295, P #0, P #0);
    %"v9" = %"v0" +p #216;
    %"v10" : P = Copy $"__io_vtables";
    %"v11" = %"v10" +p #2016;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v9";
    store.ptr [%"chk1" + 0] <- %"v11";
    %"v13" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v13";
    store.ptr [%"chk2" + 0] <- %"v2";
    %"iw_1.v3" = %"v0" +p #32;
    %"iw_1.v5" = %"v0" +p #224;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v6" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"chk5" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v3";
    store.ptr [%"chk5" + 0] <- %"iw_1.v7";
    %"iw_1.v9" = %"v0" +p #40;
    %"chk6" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v13" = %"iw_1.v12" +p #8;
    %"chk7" : A = (Check 0 8 Read 8) %"iw_1.v13";
    %"iw_1.v14" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v9";
    store.ptr [%"chk8" + 0] <- %"iw_1.v14";
    %"iw_1.v16" = %"v0" +p #48;
    %"chk9" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v5";
    %"iw_1.v19" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v20" = %"iw_1.v19" +p #16;
    %"chk10" : A = (Check 0 8 Read 8) %"iw_1.v20";
    %"iw_1.v21" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"iw_1.v16";
    store.ptr [%"chk11" + 0] <- %"iw_1.v21";
    %"v17" = %"v0" +p #24;
    %"v19" = %"v0" +p #32;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"chk13" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v17";
    store.ptr [%"chk13" + 0] <- %"v20";
    %"v22" = %"v0" +p #8;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v25" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v22";
    store.ptr [%"chk15" + 0] <- %"v25";
    %"v27" = %"v0" +p #16;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk5", %"v19";
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v27";
    store.ptr [%"chk17" + 0] <- %"v30"
    => ret void
} }.

Definition fn___printf_buffer_as_file_overflow : func :=
  ir_fn{ "export" "__printf_buffer_as_file_overflow"(P %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk14" + 0] <- %"iw_1.v75";
    %"v12" : W = (Cmp Ne W) %"v2", #4294967295
    => br %"v12" ? "L7" : "L9";
  @"L7":
    %"v14" = %"v0" +p #224;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v14";
    %"v15" : P = (RawLoadPointer 0 load_effects) %"chk15";
    %"v17" : W = (Ext Sb) %"v2";
    %"iw_2.v8" = %"v15" +p #8;
    %"chk16" : A = (Check 0 8 Read 8) %"iw_2.v8";
    %"iw_2.v9" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v11" = %"v15" +p #16;
    %"chk17" : A = (HalfCheck Upper 0 8 Read 8) %"chk16", %"iw_2.v11";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"iw_2.v13" : L = Ptoi %"iw_2.v9";
    %"iw_2.v14" : L = Ptoi %"iw_2.v12";
    %"iw_2.v15" : W = (Cmp Ne L) %"iw_2.v13", %"iw_2.v14"
    => br %"iw_2.v15" ? "iw_2.L4" : "iw_2.L5";
  @"iw_2.L4":
    %"iw_2.v17" = %"v15" +p #8;
    %"iw_2.v18" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"iw_2.v19" = %"iw_2.v18" +p #1;
    %"chk19" : A = (Renew 0 8 Write 8) %"chk16", %"iw_2.v17";
    store.ptr [%"chk19" + 0] <- %"iw_2.v19";
    %"chk20" : A = (Check 0 1 Write 1) %"iw_2.v18";
    store Wb [%"chk20" + 0] <- %"v17"
    => goto "L9";
  @"iw_2.L5":
    call void $"__printf_buffer_putc_1"(P %"v15", W %"v17")
    => goto "L9";
  @"L9":
    %"v22" = %"v0" +p #224;
    %"chk21" : A = (Renew 0 8 Read 8) %"chk1", %"v22";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"iw_3.v3" = %"v23" +p #32;
    %"chk22" : A = (Check 0 4 Read 1) %"iw_3.v3";
    %"iw_3.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk22";
    %"v26" : W = (Cmp Ne W) %"iw_3.v4", #0
    => br %"v26" ? "L27" : "L28";
  @"L27":
    %"v30" = %"v0" +p #224;
    %"v31" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v32" = %"v31" +p #8;
    %"chk24" : A = (Check 0 8 Read 8) %"v32";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk24";
    %"v36" : P = (RawLoadPointer 0 load_effects) %"chk21";
    %"v37" = %"v36" +p #16;
    %"chk26" : A = (Check 0 8 Read 8) %"v37";
    %"v38" : P = (RawLoadPointer 0 load_effects) %"chk26";
    %"v39" : L = Ptoi %"v33";
    %"v40" : L = Ptoi %"v38";
    %"v41" : W = (Cmp Eq L) %"v39", %"v40"
    => goto "L28";
  @"L28" [%"v43" : W = phi("L9" => #0, "L27" => %"v41")]:
    => br %"v43" ? "L18" : "iw_4.start";
  @"L18":
    %"v45" = %"v0" +p #224;
    %"v46" : P = (RawLoadPointer 0 load_effects) %"chk21";
    call %"v47" : W = $"__printf_buffer_flush"(P %"v46")
    => goto "iw_4.start";
  @"iw_4.start":
    %"iw_4.v3" = %"v0" +p #32;
    %"iw_4.v5" = %"v0" +p #224;
    %"chk28" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v6" : P = (RawLoadPointer 0 load_effects) %"chk28";
    %"chk29" : A = (Check 0 8 Read 8) %"iw_4.v6";
    %"iw_4.v7" : P = (RawLoadPointer 0 load_effects) %"chk29";
    %"chk30" : A = (Renew 0 8 Write 8) %"chk6", %"iw_4.v3";
    store.ptr [%"chk30" + 0] <- %"iw_4.v7";
    %"iw_4.v9" = %"v0" +p #40;
    %"chk31" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v12" : P = (RawLoadPointer 0 load_effects) %"chk31";
    %"iw_4.v13" = %"iw_4.v12" +p #8;
    %"chk32" : A = (Check 0 8 Read 8) %"iw_4.v13";
    %"iw_4.v14" : P = (RawLoadPointer 0 load_effects) %"chk32";
    %"chk33" : A = (Renew 0 8 Write 8) %"chk0", %"iw_4.v9";
    store.ptr [%"chk33" + 0] <- %"iw_4.v14";
    %"iw_4.v16" = %"v0" +p #48;
    %"chk34" : A = (Renew 0 8 Read 8) %"chk1", %"iw_4.v5";
    %"iw_4.v19" : P = (RawLoadPointer 0 load_effects) %"chk34";
    %"iw_4.v20" = %"iw_4.v19" +p #16;
    %"chk35" : A = (Check 0 8 Read 8) %"iw_4.v20";
    %"iw_4.v21" : P = (RawLoadPointer 0 load_effects) %"chk35";
    %"chk36" : A = (Renew 0 8 Write 8) %"chk9", %"iw_4.v16";
    store.ptr [%"chk36" + 0] <- %"iw_4.v21";
    %"v54" = %"v0" +p #224;
    %"chk37" : A = (Renew 0 8 Read 8) %"chk1", %"v54";
    %"v55" : P = (RawLoadPointer 0 load_effects) %"chk37";
    %"iw_5.v3" = %"v55" +p #32;
    %"chk38" : A = (Check 0 4 Read 1) %"iw_5.v3";
    %"iw_5.v4" : W = (RawLoad (LdNarrow Uw) 0) %"chk38";
    %"v58" : W = (Cmp Ne W) %"iw_5.v4", #0
    => br %"v58" ? "L50" : "L51";
  @"L50":
    %"v60" : W = (Ext Ub) %"v2"
    => ret %"v60";
  @"L51":
    => ret #4294967295
} }.

Definition fn___printf_buffer_as_file_terminate : func :=
  ir_fn{ "export" "__printf_buffer_as_file_terminate"(P %"v0") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = And %"v6", #32
    => br %"v7" ? "L2" : "iw_1.start";
  @"L2":
    => ret #0;
  @"iw_1.start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk2" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk3" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk6" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk7" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk8" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"chk9" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk10" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk11" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk12" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk2", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk14" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk14";
    %"chk15" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk15" + 0] <- %"iw_1.v75"
    => ret #1
} }.

Definition fn___printf_buffer_as_file_xsputn : func :=
  ir_fn{ "export" "__printf_buffer_as_file_xsputn"(P %"v0", P %"v2", L %"v4") -> (RClass L) {
  @"start":
    %"iw_1.v6" = %"v0" +p #40;
    %"chk0" : A = (Check 0 8 Read 8) %"iw_1.v6";
    %"iw_1.v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v9" = %"v0" +p #224;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v9";
    %"iw_1.v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"iw_1.v11" = %"iw_1.v10" +p #8;
    %"chk2" : A = (Check 0 8 Read 8) %"iw_1.v11";
    %"iw_1.v12" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"iw_1.v13" : L = Ptoi %"iw_1.v7";
    %"iw_1.v14" : L = Ptoi %"iw_1.v12";
    %"iw_1.v15" : W = (Cmp Uge L) %"iw_1.v13", %"iw_1.v14"
    => br %"iw_1.v15" ? "iw_1.L4" : "iw_1.L3";
  @"iw_1.L3":
    %"iw_1.v16" : P = Copy $"glibc_printf_buffer_as_file#str.266";
    %"iw_1.v17" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v18" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v16", P %"iw_1.v17", W #30, P %"iw_1.v18")
    => goto "iw_1.L4";
  @"iw_1.L4":
    %"iw_1.v23" = %"v0" +p #40;
    %"chk3" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v23";
    %"iw_1.v24" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"iw_1.v26" = %"v0" +p #224;
    %"chk4" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v26";
    %"iw_1.v27" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"iw_1.v28" = %"iw_1.v27" +p #16;
    %"chk5" : A = (Check 0 8 Read 8) %"iw_1.v28";
    %"iw_1.v29" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"iw_1.v30" : L = Ptoi %"iw_1.v24";
    %"iw_1.v31" : L = Ptoi %"iw_1.v29";
    %"iw_1.v32" : W = (Cmp Ule L) %"iw_1.v30", %"iw_1.v31"
    => br %"iw_1.v32" ? "iw_1.L21" : "iw_1.L20";
  @"iw_1.L20":
    %"iw_1.v33" : P = Copy $"glibc_printf_buffer_as_file#str.269";
    %"iw_1.v34" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v35" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v33", P %"iw_1.v34", W #31, P %"iw_1.v35")
    => goto "iw_1.L21";
  @"iw_1.L21":
    %"iw_1.v40" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"iw_1.v40";
    %"iw_1.v41" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_1.v43" = %"v0" +p #224;
    %"chk7" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v43";
    %"iw_1.v44" : P = (RawLoadPointer 0 load_effects) %"chk7";
    %"chk8" : A = (Check 0 8 Read 8) %"iw_1.v44";
    %"iw_1.v45" : P = (RawLoadPointer 0 load_effects) %"chk8";
    %"iw_1.v46" : L = Ptoi %"iw_1.v41";
    %"iw_1.v47" : L = Ptoi %"iw_1.v45";
    %"iw_1.v48" : W = (Cmp Eq L) %"iw_1.v46", %"iw_1.v47"
    => br %"iw_1.v48" ? "iw_1.L38" : "iw_1.L37";
  @"iw_1.L37":
    %"iw_1.v49" : P = Copy $"glibc_printf_buffer_as_file#str.270";
    %"iw_1.v50" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v51" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v49", P %"iw_1.v50", W #32, P %"iw_1.v51")
    => goto "iw_1.L38";
  @"iw_1.L38":
    %"iw_1.v56" = %"v0" +p #48;
    %"chk9" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"iw_1.v56";
    %"iw_1.v57" : P = (RawLoadPointer 0 load_effects) %"chk9";
    %"iw_1.v59" = %"v0" +p #224;
    %"chk10" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v59";
    %"iw_1.v60" : P = (RawLoadPointer 0 load_effects) %"chk10";
    %"iw_1.v61" = %"iw_1.v60" +p #16;
    %"chk11" : A = (Check 0 8 Read 8) %"iw_1.v61";
    %"iw_1.v62" : P = (RawLoadPointer 0 load_effects) %"chk11";
    %"iw_1.v63" : L = Ptoi %"iw_1.v57";
    %"iw_1.v64" : L = Ptoi %"iw_1.v62";
    %"iw_1.v65" : W = (Cmp Eq L) %"iw_1.v63", %"iw_1.v64"
    => br %"iw_1.v65" ? "iw_1.L54" : "iw_1.L53";
  @"iw_1.L53":
    %"iw_1.v66" : P = Copy $"glibc_printf_buffer_as_file#str.271";
    %"iw_1.v67" : P = Copy $"glibc_printf_buffer_as_file#str.267";
    %"iw_1.v68" : P = Copy $"glibc_printf_buffer_as_file#str.268";
    call void $"__libc_assert_fail"(P %"iw_1.v66", P %"iw_1.v67", W #33, P %"iw_1.v68")
    => goto "iw_1.L54";
  @"iw_1.L54":
    %"iw_1.v70" = %"v0" +p #224;
    %"chk12" : A = (Renew 0 8 Read 8) %"chk1", %"iw_1.v70";
    %"iw_1.v71" : P = (RawLoadPointer 0 load_effects) %"chk12";
    %"iw_1.v72" = %"iw_1.v71" +p #8;
    %"iw_1.v74" = %"v0" +p #40;
    %"chk13" : A = (Renew 0 8 Read 8) %"chk0", %"iw_1.v74";
    %"iw_1.v75" : P = (RawLoadPointer 0 load_effects) %"chk13";
    %"chk14" : A = (Check 0 8 Write 8) %"iw_1.v72";
    store.ptr [%"chk14" + 0] <- %"iw_1.v75";
    %"v10" = %"v0" +p #224;
    %"chk15" : A = (Renew 0 8 Read 8) %"chk1", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk15";
    call void $"__printf_buffer_write"(P %"v11", P %"v2", L %"v4");
    %"iw_2.v3" = %"v0" +p #32;
    %"iw_2.v5" = %"v0" +p #224;
    %"chk16" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v6" : P = (RawLoadPointer 0 load_effects) %"chk16";
    %"chk17" : A = (Check 0 8 Read 8) %"iw_2.v6";
    %"iw_2.v7" : P = (RawLoadPointer 0 load_effects) %"chk17";
    %"chk18" : A = (Renew 0 8 Write 8) %"chk6", %"iw_2.v3";
    store.ptr [%"chk18" + 0] <- %"iw_2.v7";
    %"iw_2.v9" = %"v0" +p #40;
    %"chk19" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v12" : P = (RawLoadPointer 0 load_effects) %"chk19";
    %"iw_2.v13" = %"iw_2.v12" +p #8;
    %"chk20" : A = (Check 0 8 Read 8) %"iw_2.v13";
    %"iw_2.v14" : P = (RawLoadPointer 0 load_effects) %"chk20";
    %"chk21" : A = (Renew 0 8 Write 8) %"chk0", %"iw_2.v9";
    store.ptr [%"chk21" + 0] <- %"iw_2.v14";
    %"iw_2.v16" = %"v0" +p #48;
    %"chk22" : A = (Renew 0 8 Read 8) %"chk1", %"iw_2.v5";
    %"iw_2.v19" : P = (RawLoadPointer 0 load_effects) %"chk22";
    %"iw_2.v20" = %"iw_2.v19" +p #16;
    %"chk23" : A = (Check 0 8 Read 8) %"iw_2.v20";
    %"iw_2.v21" : P = (RawLoadPointer 0 load_effects) %"chk23";
    %"chk24" : A = (Renew 0 8 Write 8) %"chk9", %"iw_2.v16";
    store.ptr [%"chk24" + 0] <- %"iw_2.v21";
    %"v19" = %"v0" +p #224;
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

Definition item_glibc_printf_buffer_as_file'23str'2e266 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_printf_buffer_as_file'23str'2e267 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.267") (LRo (a "local")) 1 [(Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_printf_buffer_as_file'23str'2e268 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_printf_buffer_as_file'23str'2e269 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.269") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_printf_buffer_as_file'23str'2e270 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.270") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_printf_buffer_as_file'23str'2e271 : item :=
  (IData (a "glibc_printf_buffer_as_file#str.271") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).
