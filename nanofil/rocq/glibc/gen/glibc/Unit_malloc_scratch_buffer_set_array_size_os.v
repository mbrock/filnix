(** This file defines checked IR from glibc’s `malloc/scratch_buffer_set_array_size.os` object.
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

Definition fn___GI___libc_scratch_buffer_set_array_size : func :=
  ir_fn{ "export" "__GI___libc_scratch_buffer_set_array_size"(P %"v0", L %"v2", L %"v4") -> (RClass W) {
  @"start":
    %"v9" : L = Mul %"v2", %"v4";
    %"v15" : L = Or %"v2", %"v4";
    %"v18" : L = Shr %"v15", #32;
    %"v19" : W = (Cmp Ne L) %"v18", #0
    => br %"v19" ? "L20" : "L21";
  @"L20":
    %"v23" : W = (Cmp Ne L) %"v2", #0
    => goto "L21";
  @"L21" [%"v25" : W = phi("start" => #0, "L20" => %"v23")]:
    => br %"v25" ? "L26" : "L27";
  @"L26":
    %"v31" : L = Udiv %"v9", %"v2";
    %"v32" : W = (Cmp Ne L) %"v4", %"v31"
    => goto "L27";
  @"L27" [%"v34" : W = phi("L21" => #0, "L26" => %"v32")]:
    => br %"v34" ? "iw_1.start" : "L12";
  @"iw_1.start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"iw_1.v6" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"iw_1.v8" = %"v0" +p #16;
    %"iw_1.v9" : L = Ptoi %"iw_1.v6";
    %"iw_1.v10" : L = Ptoi %"iw_1.v8";
    %"iw_1.v11" : W = (Cmp Ne L) %"iw_1.v9", %"iw_1.v10"
    => br %"iw_1.v11" ? "iw_1.L2" : "iw_2.start";
  @"iw_1.L2":
    %"iw_1.v13" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"free"(P %"iw_1.v13")
    => goto "iw_2.start";
  @"iw_2.start":
    %"iw_2.v4" = %"v0" +p #16;
    %"chk2" : A = (Renew 0 8 Write 8) %"chk0", %"v0";
    store.ptr [%"chk2" + 0] <- %"iw_2.v4";
    %"iw_2.v6" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Upper 0 8 Write 1) %"chk0", %"iw_2.v6";
    store Wl [%"chk3" + 0] <- #1024;
    %"v37" : P = Copy $"__libc_errno";
    %"chk4" : A = (Check 0 4 Write 1) %"v37";
    store Ww [%"chk4" + 0] <- #12
    => ret #0;
  @"L12":
    %"v45" = %"v0" +p #8;
    %"chk5" : A = (Check 0 8 Read 1) %"v45";
    %"v46" : L = (RawLoad LdL 0) %"chk5";
    %"v47" : W = (Cmp Ule L) %"v9", %"v46"
    => br %"v47" ? "L40" : "iw_3.start";
  @"L40":
    => ret #1;
  @"iw_3.start":
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk5", %"v0";
    %"iw_3.v6" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"iw_3.v8" = %"v0" +p #16;
    %"iw_3.v9" : L = Ptoi %"iw_3.v6";
    %"iw_3.v10" : L = Ptoi %"iw_3.v8";
    %"iw_3.v11" : W = (Cmp Ne L) %"iw_3.v9", %"iw_3.v10"
    => br %"iw_3.v11" ? "iw_3.L2" : "iw_3.join";
  @"iw_3.L2":
    %"iw_3.v13" : P = (RawLoadPointer 0 load_effects) %"chk6";
    call void $"free"(P %"iw_3.v13")
    => goto "iw_3.join";
  @"iw_3.join":
    call %"v53" : P = $"malloc"(L %"v9");
    %"v58" : L = Ptoi %"v53";
    %"v59" : L = Ptoi #0;
    %"v60" : W = (Cmp Eq L) %"v58", %"v59"
    => br %"v60" ? "iw_4.start" : "L56";
  @"iw_4.start":
    %"iw_4.v4" = %"v0" +p #16;
    %"chk8" : A = (Renew 0 8 Write 8) %"chk6", %"v0";
    store.ptr [%"chk8" + 0] <- %"iw_4.v4";
    %"iw_4.v6" = %"v0" +p #8;
    %"chk9" : A = (Renew 0 8 Write 1) %"chk5", %"iw_4.v6";
    store Wl [%"chk9" + 0] <- #1024
    => ret #0;
  @"L56":
    %"chk10" : A = (Renew 0 8 Write 8) %"chk6", %"v0";
    store.ptr [%"chk10" + 0] <- %"v53";
    %"v67" = %"v0" +p #8;
    %"chk11" : A = (Renew 0 8 Write 1) %"chk5", %"v67";
    store Wl [%"chk11" + 0] <- %"v9"
    => ret #1
} }.
