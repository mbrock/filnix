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

Definition hello_image_fn___current_locale_name : func :=
  ir_fn{ "export" "__current_locale_name"(W %"v0") -> (RClass P) {
  @"start":
    %"v2" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v2";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"v4" = %"v3" +p #128;
    %"v6" : L = (Ext Sw) %"v0";
    %"v7" : L = Shl %"v6", #3;
    %"v8" = %"v4" +p %"v7";
    %"chk1" : A = (Check 0 8 Read 8) %"v8";
    %"v9" : P = (RawLoadPointer 0 load_effects) %"chk1"
    => ret %"v9"
} }.
