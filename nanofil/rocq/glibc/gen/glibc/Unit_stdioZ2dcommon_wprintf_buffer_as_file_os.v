(** This file defines checked IR from glibc’s `stdio-common/wprintf_buffer_as_file.os` object.
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

Definition fn___wprintf_buffer_as_file_init : func :=
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

Definition fn___wprintf_buffer_as_file_overflow : func :=
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

Definition fn___wprintf_buffer_as_file_terminate : func :=
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

Definition fn___wprintf_buffer_as_file_xsputn : func :=
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

Definition item_glibc_wprintf_buffer_as_file'23str'2e266 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.266") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 62); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_as_file'23str'2e267 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.267") (LRo (a "local")) 1 [(Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 46); (Item Wb 99); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_as_file'23str'2e268 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.268") (LRo (a "local")) 1 [(Item Wb 95); (Item Wb 95); (Item Wb 119); (Item Wb 112); (Item Wb 114); (Item Wb 105); (Item Wb 110); (Item Wb 116); (Item Wb 102); (Item Wb 95); (Item Wb 98); (Item Wb 117); (Item Wb 102); (Item Wb 102); (Item Wb 101); (Item Wb 114); (Item Wb 95); (Item Wb 97); (Item Wb 115); (Item Wb 95); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 95); (Item Wb 99); (Item Wb 111); (Item Wb 109); (Item Wb 109); (Item Wb 105); (Item Wb 116); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_as_file'23str'2e269 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.269") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 112); (Item Wb 116); (Item Wb 114); (Item Wb 32); (Item Wb 60); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_as_file'23str'2e270 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.270") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 98); (Item Wb 97); (Item Wb 115); (Item Wb 101); (Item Wb 0)]).

Definition item_glibc_wprintf_buffer_as_file'23str'2e271 : item :=
  (IData (a "glibc_wprintf_buffer_as_file#str.271") (LRo (a "local")) 1 [(Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 105); (Item Wb 100); (Item Wb 101); (Item Wb 95); (Item Wb 115); (Item Wb 116); (Item Wb 114); (Item Wb 101); (Item Wb 97); (Item Wb 109); (Item Wb 46); (Item Wb 95); (Item Wb 73); (Item Wb 79); (Item Wb 95); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 32); (Item Wb 61); (Item Wb 61); (Item Wb 32); (Item Wb 102); (Item Wb 105); (Item Wb 108); (Item Wb 101); (Item Wb 45); (Item Wb 62); (Item Wb 110); (Item Wb 101); (Item Wb 120); (Item Wb 116); (Item Wb 45); (Item Wb 62); (Item Wb 119); (Item Wb 114); (Item Wb 105); (Item Wb 116); (Item Wb 101); (Item Wb 95); (Item Wb 101); (Item Wb 110); (Item Wb 100); (Item Wb 0)]).
