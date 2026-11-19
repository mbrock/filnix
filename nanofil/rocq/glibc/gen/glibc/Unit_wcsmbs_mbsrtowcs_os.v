(** This file defines checked IR from glibc’s `wcsmbs/mbsrtowcs.os` object.
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

Definition fn___mbsrtowcs : func :=
  ir_fn{ "export" "__mbsrtowcs"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : W = (Cmp Ne L) %"v12", #0
    => br %"v13" ? "L16" : "L15";
  @"L15":
    %"v17" : P = Copy $"glibc_mbsrtowcs#state"
    => goto "L16";
  @"L16" [%"v18" : P = phi("L15" => %"v17", "start" => %"v6")]:
    %"v19" : P = Copy $"__libc_tsd_LOCALE";
    %"chk0" : A = (Check 0 8 Read 8) %"v19";
    %"v20" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v21" : L = $"__mbsrtowcs_l"(P %"v0", P %"v2", L %"v4", P %"v18", P %"v20")
    => ret %"v21"
} }.

Definition item_glibc_mbsrtowcs'23state : item :=
  (IData (a "glibc_mbsrtowcs#state") LLocal 4 [(Zero 8)]).
