(** This file defines checked IR from glibc’s `stdlib/strtoul.os` object.
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

Definition fn___GI___isoc23_strtoul : func :=
  ir_fn{ "export" "__GI___isoc23_strtoul"(P %"v0", P %"v2", W %"v4") -> (RClass L) {
  @"start":
    %"v10" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v10";
    %"v11" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v12" : L = $"__GI_____strtoul_l_internal"(P %"v0", P %"v2", W %"v4", W #0, W #1, P %"v11")
    => ret %"v12"
} }.
