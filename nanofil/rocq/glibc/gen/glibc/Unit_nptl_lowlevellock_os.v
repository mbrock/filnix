(** This file defines checked IR from glibc’s `nptl/lowlevellock.os` object.
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

Definition fn___GI___lll_lock_wait_private : func :=
  ir_fn{ "export" "__GI___lll_lock_wait_private"(P %"v0") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 4 Read 1) %"v0";
    %"v6" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v7" : W = (Cmp Eq W) %"v6", #2
    => br %"v7" ? "iw_1.L29" : "L10";
  @"L10":
    %"chk1" : A = (Renew 0 4 Read 1) %"chk0", %"v0";
    %"v14" : W = (RawLoad (LdNarrow Sw) 0) %"chk1"
    => goto "L15";
  @"L15" [%"v17" : W = phi("L10" => %"v14", "L15" => %"v18")]:
    %"chk2" : A = (HalfCheck Lower 0 4 Write 4) %"chk0", %"v0";
    %"v18" : W = (RawCas (CasNarrow Sw) 0) %"chk2", %"v17", #2;
    %"v19" : W = (Cmp Eq W) %"v18", %"v17"
    => br %"v19" ? "L16" : poll "L15";
  @"L16":
    %"v20" : W = (Cmp Ne W) %"v17", #0
    => br %"v20" ? "iw_1.L29" : "L12";
  @"iw_1.L29":
    call void $"zsys_futex_wait"(P %"v0", W #2, W #1)
    => goto poll "L10";
  @"L12":
    => ret void
} }.

Definition fn___GI___lll_lock_wake_private : func :=
  ir_fn{ "export" "__GI___lll_lock_wake_private"(P %"v0") -> RVoid {
  @"start":
    call void $"zsys_futex_wake"(P %"v0", W #1, W #1)
    => ret void
} }.
