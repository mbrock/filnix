(** This file defines checked IR from glibc’s `libio/__fpending.os` object.
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

Definition fn___fpending : func :=
  ir_fn{ "export" "__fpending"(P %"v0") -> (RClass L) {
  @"start":
    %"v6" = %"v0" +p #192;
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"v8" : W = (Cmp Sgt W) %"v7", #0
    => br %"v8" ? "L2" : "L3";
  @"L2":
    %"v10" = %"v0" +p #160;
    %"chk1" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v12" = %"v11" +p #32;
    %"chk2" : A = (Check 0 8 Read 8) %"v12";
    %"v13" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v17" = %"v16" +p #24;
    %"chk4" : A = (Check 0 8 Read 8) %"v17";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk4";
    %"v19" : L = Ptoi %"v13";
    %"v20" : L = Ptoi %"v18";
    %"v21" : L = Sub %"v19", %"v20";
    %"v22" : L = Div %"v21", #4
    => ret %"v22";
  @"L3":
    %"v25" = %"v0" +p #40;
    %"chk5" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v25";
    %"v26" : P = (RawLoadPointer 0 load_effects) %"chk5";
    %"v28" = %"v0" +p #32;
    %"chk6" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v28";
    %"v29" : P = (RawLoadPointer 0 load_effects) %"chk6";
    %"v30" : L = Ptoi %"v26";
    %"v31" : L = Ptoi %"v29";
    %"v32" : L = Sub %"v30", %"v31"
    => ret %"v32"
} }.
