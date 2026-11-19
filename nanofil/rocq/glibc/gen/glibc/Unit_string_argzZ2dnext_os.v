(** This file defines checked IR from glibc’s `string/argz-next.os` object.
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

Definition fn___GI___argz_next : func :=
  ir_fn{ "export" "__GI___argz_next"(P %"v0", L %"v2", P %"v4") -> (RClass P) {
  @"start":
    %"v10" : L = Ptoi %"v4";
    %"v11" : W = (Cmp Ne L) %"v10", #0
    => br %"v11" ? "L6" : "L7";
  @"L6":
    %"v18" = %"v0" +p %"v2";
    %"v20" : L = Ptoi %"v18";
    %"v21" : W = (Cmp Ult L) %"v10", %"v20"
    => br %"v21" ? "L12" : "L14";
  @"L12":
    call %"v23" : P = $"__GI_strchr"(P %"v4", W #0);
    %"v24" = %"v23" +p #1
    => goto "L14";
  @"L14" [%"pr.1" : P = phi("L12" => %"v24", "L6" => %"v4")]:
    %"v32" : L = Ptoi %"pr.1";
    %"v34" : W = (Cmp Uge L) %"v32", %"v20"
    => br %"v34" ? "L27" : "L26";
  @"L26":
    => goto "L27";
  @"L27" [%"v36" : P = phi("L26" => %"pr.1", "L14" => #0)]:
    => ret %"v36";
  @"L7":
    %"v42" : W = (Cmp Ugt L) %"v2", #0
    => br %"v42" ? "L38" : "L39";
  @"L38":
    => ret %"v0";
  @"L39":
    => ret #0
} }.
