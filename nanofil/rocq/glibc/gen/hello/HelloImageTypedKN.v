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

Definition hello_image_fn_glibc_gconv_dl'23known_compare : func :=
  ir_fn{ "local" "glibc_gconv_dl#known_compare"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v2";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v12" : W = $"__GI_strcmp"(P %"v9", P %"v11")
    => ret %"v12"
} }.
