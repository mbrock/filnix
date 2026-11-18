(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRNotation.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn___GI___tfind : func :=
  ir_fn{ "export" "__GI___tfind"(P %"v0", P %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v13" : L = Ptoi %"v2";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L11";
  @"L9":
    => ret #0;
  @"L11":
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v18" : P = (RawLoadPointer 0 load_effects) %"chk0"
    => goto "L19";
  @"L19" [%"pr.1" : P = phi("L11" => %"v2", "L42" => %"v48", "L43" => %"v50")]:
    %"chk1" : A = (Check 0 8 Read 8) %"pr.1";
    %"v23" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v24" : L = Ptoi %"v23";
    %"v26" : W = (Cmp Ne L) %"v24", %"v14"
    => br %"v26" ? "L20" : "L21";
  @"L20":
    %"v28" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"chk3" : A = (Check 0 8 Read 8) %"v28";
    %"v33" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v4";
    rawcall %"v34" : W = %"chk4"(P %"v0", P %"v33");
    %"v39" : W = (Cmp Eq W) %"v34", #0
    => br %"v39" ? "L35" : "L37";
  @"L35":
    => ret %"v28";
  @"L37":
    %"v46" : W = (Cmp Slt W) %"v34", #0
    => br %"v46" ? "L42" : "L43";
  @"L42":
    %"v48" = %"v28" +p #8
    => goto poll "L19";
  @"L43":
    %"v50" = %"v28" +p #16
    => goto poll "L19";
  @"L21":
    => ret #0
} }.
