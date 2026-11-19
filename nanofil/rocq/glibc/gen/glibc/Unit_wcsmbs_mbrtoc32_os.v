(** This file defines checked IR from glibc’s `wcsmbs/mbrtoc32.os` object.
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

Definition item_glibc_mbrtoc32'23state : item :=
  (IData (a "glibc_mbrtoc32#state") LLocal 4 [(Zero 8)]).

Definition fn_mbrtoc32 : func :=
  ir_fn{ "export" "mbrtoc32"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v6";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"glibc_mbrtoc32#state"
    => goto "L10";
  @"L10" [%"pr.1" : P = phi("L8" => %"v15", "start" => %"v6")]:
    call %"v20" : L = $"__GI_mbrtowc"(P %"v0", P %"v2", L %"v4", P %"pr.1")
    => ret %"v20"
} }.
