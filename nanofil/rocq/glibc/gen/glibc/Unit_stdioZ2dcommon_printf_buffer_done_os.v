(** This file defines checked IR from glibc’s `stdio-common/printf_buffer_done.os` object.
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

Definition fn___printf_buffer_done : func :=
  ir_fn{ "export" "__printf_buffer_done"(P %"v0") -> (RClass W) {
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
    %"v24" = %"v0" +p #24;
    %"v25" : L = (RawLoad LdL (-8)) %"chk0";
    %"v27" : L = Add %"v25", %"v18";
    %"v28" : W = (Cmp Ult L) %"v27", %"v25";
    %"v29" : L = (Ext Uw) %"v28";
    %"v32" : L = (Ext Sw) %"v27";
    %"v33" : L = Sar %"v32", #63;
    %"v34" : W = (Cmp Ne L) %"v27", %"v32";
    %"v35" : W = (Cmp Ne L) %"v29", %"v33";
    %"v36" : W = Or %"v34", %"v35"
    => br %"v36" ? "L20" : "L21";
  @"L20":
    %"v37" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v37";
    store Ww [%"chk4" + 0] <- #75
    => ret #4294967295;
  @"L21":
    %"v40" : W = Copy %"v27"
    => ret %"v40"
} }.
