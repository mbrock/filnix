(** This file defines checked IR from glibc’s `stdio-common/wprintf_buffer_done.os` object.
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

Definition fn___wprintf_buffer_done : func :=
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
