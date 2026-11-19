(** This file defines checked IR from glibc’s `libio/iovdprintf.os` object.
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

Definition fn___printf_buffer_flush_dprintf : func :=
  ir_fn{ "export" "__printf_buffer_flush_dprintf"(P %"v0") -> RVoid {
  @"start":
    %"v4" = %"v0" +p #44;
    %"v7" = %"v0" +p #8;
    %"chk0" : A = (Check 0 8 Read 8) %"v7";
    %"v8" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L9";
  @"L9" [%"pr.1" : P = phi("L45" => %"v52", "start" => %"v4")]:
    %"v14" : L = Ptoi %"pr.1";
    %"v15" : L = Ptoi %"v8";
    %"v16" : W = (Cmp Ult L) %"v14", %"v15"
    => br %"v16" ? "L19" : "L11";
  @"L19":
    %"v23" = %"v0" +p #40;
    %"chk1" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v23";
    %"v24" : W = (RawLoad (LdNarrow Sw) 0) %"chk1";
    %"v30" : L = Sub %"v15", %"v14";
    call %"v31" : L = $"__GI_write"(W %"v24", P %"pr.1", L %"v30");
    %"v34" : W = (Cmp Eq L) %"v31", #18446744073709551615
    => br %"v34" ? "L35" : "L36";
  @"L35":
    %"v37" : P = Copy $"__libc_errno";
    %"chk2" : A = (Check 0 4 Read 1) %"v37";
    %"v38" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v39" : W = (Cmp Eq W) %"v38", #4
    => goto "L36";
  @"L36" [%"v41" : W = phi("L19" => #0, "L35" => %"v39")]:
    => br %"v41" ? poll "L19" : "L21";
  @"L21":
    %"v47" : W = (Cmp Slt L) %"v31", #0
    => br %"v47" ? "iw_1.start" : "L45";
  @"iw_1.start":
    %"iw_1.v3" = %"v0" +p #32;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"iw_1.v3";
    store Ww [%"chk3" + 0] <- #0
    => ret void;
  @"L45":
    %"v52" = %"pr.1" +p %"v31"
    => goto poll "L9";
  @"L11":
    %"v54" = %"v0" +p #24;
    %"chk4" : A = (HalfCheck Upper 0 8 Read 1) %"chk0", %"v54";
    %"v55" : L = (RawLoad LdL 0) %"chk4";
    %"v57" = %"v0" +p #8;
    %"chk5" : A = (Renew 0 8 Read 8) %"chk0", %"v57";
    %"v58" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v60" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v61" : L = Ptoi %"v58";
    %"v62" : L = Ptoi %"v60";
    %"v63" : L = Sub %"v61", %"v62";
    %"v64" : L = Add %"v55", %"v63";
    %"chk7" : A = (Renew 0 8 Write 1) %"chk4", %"v54";
    store Wl [%"chk7" + 0] <- %"v64";
    %"v68" = %"v0" +p #44;
    %"chk8" : A = (Renew 0 8 Write 8) %"chk0", %"v57";
    store.ptr [%"chk8" + 0] <- %"v68"
    => ret void
} }.
