(** This file defines checked IR from the `mbrtoc32` object of HelloImage.
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

Definition item_mbrtoc32'23internal_state : item :=
  (IData (a "mbrtoc32#internal_state") LLocal 4 [(Zero 8)]).

Definition item_mbrtoc32'23str'2e36 : item :=
  (IData (a "mbrtoc32#str.36") (LRo (a "local")) 1 [(Item Wb 0)]).

Definition fn_rpl_mbrtoc32 : func :=
  ir_fn{ "export" "rpl_mbrtoc32"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v12" : L = Ptoi %"v2";
    %"v13" : L = Ptoi #0;
    %"v14" : W = (Cmp Eq L) %"v12", %"v13"
    => br %"v14" ? "L8" : "L10";
  @"L8":
    %"v15" : P = Copy $"mbrtoc32#str.36"
    => goto "L10";
  @"L10" [%"pr.3" : L = phi("L8" => #1, "start" => %"v4"); %"pr.2" : P = phi("L8" => %"v15", "start" => %"v2"); %"pr.1" : P = phi("L8" => #0, "start" => %"v0")]:
    %"v20" : L = Ptoi %"v6";
    %"v22" : W = (Cmp Eq L) %"v20", %"v13"
    => br %"v22" ? "L16" : "L18";
  @"L16":
    %"v23" : P = Copy $"mbrtoc32#internal_state"
    => goto "L18";
  @"L18" [%"pr.4" : P = phi("L16" => %"v23", "L10" => %"v6")]:
    call %"v29" : L = $"mbrtoc32"(P %"pr.1", P %"pr.2", L %"pr.3", P %"pr.4");
    %"v36" : W = (Cmp Uge L) %"v29", #18446744073709551614
    => br %"v36" ? "L37" : "L38";
  @"L37":
    %"v40" : W = (Cmp Ne L) %"pr.3", #0
    => goto "L38";
  @"L38" [%"v42" : W = phi("L18" => #0, "L37" => %"v40")]:
    => br %"v42" ? "L43" : "L44";
  @"L43":
    call %"v45" : W = $"hard_locale"(W #0);
    %"v46" : W = (Ext Ub) %"v45";
    %"v47" : W = (Cmp Eq W) %"v46", #0
    => goto "L44";
  @"L44" [%"v49" : W = phi("L38" => #0, "L43" => %"v47")]:
    => br %"v49" ? "L30" : "L32";
  @"L30":
    %"v54" : L = Ptoi %"pr.1";
    %"v56" : W = (Cmp Ne L) %"v54", %"v13"
    => br %"v56" ? "L50" : "L52";
  @"L50":
    %"chk0" : A = (Check 0 1 Read 1) %"pr.2";
    %"v59" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v60" : W = (Ext Ub) %"v59";
    %"chk1" : A = (Check 0 4 Write 1) %"pr.1";
    store Ww [%"chk1" + 0] <- %"v60"
    => goto "L52";
  @"L52":
    => ret #1;
  @"L32":
    => ret %"v29"
} }.
