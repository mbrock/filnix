(** This file defines checked IR from glibc’s `libio/vsnprintf.os` object.
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

Definition fn___printf_buffer_flush_snprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_snprintf"(P %"v0") -> RVoid {
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
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v20" = %"v0" +p #40;
    %"v21" : L = Ptoi %"v18";
    %"v22" : L = Ptoi %"v20";
    %"v23" : W = (Cmp Ne L) %"v21", %"v22"
    => br %"v23" ? "L14" : "L16";
  @"L14":
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v30" = %"v0" +p #16;
    %"v31" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v32" : L = Ptoi %"v28";
    %"v33" : L = Ptoi %"v31";
    %"v34" : W = (Cmp Ne L) %"v32", %"v33"
    => br %"v34" ? "L24" : "L26";
  @"L24":
    %"v36" = %"v0" +p #16;
    %"v37" : P = (RawLoadPointer 8 load_effects) %"chk1";
    %"v40" = %"v37" +p #18446744073709551615;
    %"chk8" : A = (Check 0 1 Write 1) %"v40";
    store Wb [%"chk8" + 0] <- #0
    => goto "L26";
  @"L26":
    %"v43" = %"v0" +p #40;
    %"chk9" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk9" + 0] <- %"v43";
    %"v45" = %"v0" +p #8;
    %"chk10" : A = (Renew 0 8 Write 8) %"chk1", %"v45";
    store.ptr [%"chk10" + 0] <- %"v43";
    %"v49" = %"v0" +p #16;
    %"v55" = %"v43" +p #128;
    %"chk11" : A = (HalfCheck Lower 0 8 Write 8) %"chk0", %"v49";
    store.ptr [%"chk11" + 0] <- %"v55"
    => goto "L16";
  @"L16":
    %"v58" = %"v0" +p #40;
    %"chk12" : A = (Renew 0 8 Write 8) %"chk2", %"v0";
    store.ptr [%"chk12" + 0] <- %"v58";
    %"v60" = %"v0" +p #8;
    %"chk13" : A = (Renew 0 8 Write 8) %"chk1", %"v60";
    store.ptr [%"chk13" + 0] <- %"v58"
    => ret void
} }.

Definition fn___printf_buffer_snprintf_done : func :=
  ir_fn{ "export" "__printf_buffer_snprintf_done"(P %"v0") -> (RClass W) {
  @"start":
    %"v6" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v6";
    %"v7" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v9" = %"v0" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Read 8) %"chk0", %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v11" : L = Ptoi %"v7";
    %"v12" : L = Ptoi %"v10";
    %"v13" : W = (Cmp Ult L) %"v11", %"v12"
    => br %"v13" ? "L2" : "L3";
  @"L2":
    %"v15" = %"v0" +p #8;
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk3" : A = (Check 0 1 Write 1) %"v16";
    store Wb [%"chk3" + 0] <- #0
    => goto "L4";
  @"L3":
    %"v21" = %"v0" +p #8;
    %"v22" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v24" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v25" : L = Ptoi %"v22";
    %"v26" : L = Ptoi %"v24";
    %"v27" : W = (Cmp Ugt L) %"v25", %"v26"
    => br %"v27" ? "L17" : "L4";
  @"L17":
    %"v29" = %"v0" +p #8;
    %"v30" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v33" = %"v30" +p #18446744073709551615;
    %"chk7" : A = (Check 0 1 Write 1) %"v33";
    store Wb [%"chk7" + 0] <- #0
    => goto "L4";
  @"L4":
    call %"v35" : W = $"__printf_buffer_done"(P %"v0")
    => ret %"v35"
} }.

Definition fn___printf_buffer_snprintf_init : func :=
  ir_fn{ "export" "__printf_buffer_snprintf_init"(P %"v0", P %"v2", L %"v4") -> RVoid {
  @"start":
    %"iw_1.v12" = %"v2" +p %"v4";
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"iw_1.iw_1.v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v11";
    store.ptr [%"chk1" + 0] <- %"v2";
    %"iw_1.iw_1.v14" = %"v0" +p #16;
    %"chk2" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.iw_1.v14";
    store.ptr [%"chk2" + 0] <- %"iw_1.v12";
    %"iw_1.iw_1.v17" = %"v0" +p #24;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_1.iw_1.v17";
    store Wl [%"chk3" + 0] <- #0;
    %"iw_1.iw_1.v19" = %"v0" +p #32;
    %"chk4" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.iw_1.v19";
    store Ww [%"chk4" + 0] <- #2;
    %"v13" : W = (Cmp Ugt L) %"v4", #0
    => br %"v13" ? "L9" : "L11";
  @"L9":
    %"chk5" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk5" + 0] <- #0
    => goto "L11";
  @"L11":
    => ret void
} }.

Definition fn___vsnprintf_internal : func :=
  ir_fn{ "export" "__vsnprintf_internal"(P %"v0", L %"v2", P %"v4", P %"v6", W %"v8") -> (RClass W) {
  @"start":
    %"v10" : P = (Alloc 8) #168;
    call void $"__printf_buffer_snprintf_init"(P %"v10", P %"v0", L %"v2");
    call void $"__printf_buffer"(P %"v10", P %"v4", P %"v6", W %"v8");
    call %"v16" : W = $"__printf_buffer_snprintf_done"(P %"v10")
    => ret %"v16"
} }.
