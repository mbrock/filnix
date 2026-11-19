(** This file defines checked IR from glibc’s `locale/mb_cur_max.os` object.
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

Definition fn___ctype_get_mb_cur_max : func :=
  ir_fn{ "weak" "__ctype_get_mb_cur_max"() -> (RClass L) {
  @"start":
    %"v0" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v1" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Read 8) %"v1";
    %"v3" : P = (RawLoadPointer 0 load_effects) %"chk1";
    %"v4" = %"v3" +p #56;
    %"v8" = %"v4" +p #104;
    %"chk2" : A = (Check 0 4 Read 1) %"v8";
    %"v9" : W = (RawLoad (LdNarrow Uw) 0) %"chk2";
    %"v10" : L = (Ext Uw) %"v9"
    => ret %"v10"
} }.
