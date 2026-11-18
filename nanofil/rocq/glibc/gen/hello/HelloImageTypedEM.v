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

Definition hello_image_fn_emit_bug_reporting_address : func :=
  ir_fn{ "export" "emit_bug_reporting_address"() -> RVoid {
  @"start":
    %"v0" : P = Copy $"version-etc#str.45";
    %"v1" : P = Copy $"stdout";
    %"chk0" : A = (Check 0 8 Read 8) %"v1";
    %"v2" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call %"v3" : W = $"fputs"(P %"v0", P %"v2");
    %"v4" : P = Copy $"version-etc#str.43";
    %"v5" : P = Copy $"version-etc#str.58";
    %"v6" : P = Copy $"version-etc#str.59";
    call %"v7" : W = $"printf"(P %"v5", P %"v6");
    %"v8" : P = Copy $"version-etc#str.43";
    %"v9" : P = Copy $"version-etc#str.60";
    %"v10" : P = Copy $"version-etc#str.61";
    %"v11" : P = Copy $"version-etc#str.62";
    call %"v12" : W = $"printf"(P %"v9", P %"v10", P %"v11");
    %"v13" : P = Copy $"version-etc#str.43";
    %"v14" : P = Copy $"version-etc#str.63";
    %"v15" : P = Copy $"version-etc#str.64";
    call %"v16" : W = $"printf"(P %"v14", P %"v15")
    => ret void
} }.
