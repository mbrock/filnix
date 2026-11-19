(** This file defines checked IR from the `setlocale_null-unlocked` object of HelloImage.
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

Definition fn_setlocale_null_r_unlocked : func :=
  ir_fn{ "export" "setlocale_null_r_unlocked"(W %"v0", P %"v2", L %"v4") -> (RClass W) {
  @"start":
    call %"v8" : P = $"setlocale_null_unlocked"(W %"v0");
    %"v13" : L = Ptoi %"v8";
    %"v14" : L = Ptoi #0;
    %"v15" : W = (Cmp Eq L) %"v13", %"v14"
    => br %"v15" ? "L9" : "L10";
  @"L9":
    %"v20" : W = (Cmp Ugt L) %"v4", #0
    => br %"v20" ? "L16" : "L18";
  @"L16":
    %"chk0" : A = (Check 0 1 Write 1) %"v2";
    store Wb [%"chk0" + 0] <- #0
    => goto "L18";
  @"L18":
    => ret #22;
  @"L10":
    call %"v26" : L = $"strlen"(P %"v8");
    %"v32" : W = (Cmp Ult L) %"v26", %"v4"
    => br %"v32" ? "L27" : "L28";
  @"L27":
    %"v36" : L = Add %"v26", #1;
    call %"v37" : P = $"memcpy"(P %"v2", P %"v8", L %"v36")
    => ret #0;
  @"L28":
    %"v43" : W = (Cmp Ugt L) %"v4", #0
    => br %"v43" ? "L39" : "L41";
  @"L39":
    %"v47" : L = Sub %"v4", #1;
    call %"v48" : P = $"memcpy"(P %"v2", P %"v8", L %"v47");
    %"v52" = %"v2" +p %"v47";
    %"chk1" : A = (Check 0 1 Write 1) %"v52";
    store Wb [%"chk1" + 0] <- #0
    => goto "L41";
  @"L41":
    => ret #34
} }.

Definition fn_setlocale_null_unlocked : func :=
  ir_fn{ "export" "setlocale_null_unlocked"(W %"v0") -> (RClass P) {
  @"start":
    call %"v4" : P = $"setlocale"(W %"v0", P #0)
    => ret %"v4"
} }.
