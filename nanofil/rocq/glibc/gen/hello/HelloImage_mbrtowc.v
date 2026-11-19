(** This file defines checked IR from the `mbrtowc` object of HelloImage.
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

Definition fn_rpl_mbrtowc : func :=
  ir_fn{ "export" "rpl_mbrtowc"(P %"v0", P %"v2", L %"v4", P %"v6") -> (RClass L) {
  @"start":
    %"v8" : P = (Alloc 4) #4;
    %"v13" : L = Ptoi %"v0";
    %"v15" : W = (Cmp Eq L) %"v13", #0
    => br %"v15" ? "L11" : "L10";
  @"L10":
    => goto "L11";
  @"L11" [%"pr.1" : P = phi("L10" => %"v0", "start" => %"v8")]:
    call %"v21" : L = $"mbrtowc"(P %"pr.1", P %"v2", L %"v4", P %"v6");
    %"v28" : W = (Cmp Uge L) %"v21", #18446744073709551614
    => br %"v28" ? "L29" : "L30";
  @"L29":
    %"v32" : W = (Cmp Ne L) %"v4", #0
    => goto "L30";
  @"L30" [%"v34" : W = phi("L11" => #0, "L29" => %"v32")]:
    => br %"v34" ? "L35" : "L36";
  @"L35":
    call %"v37" : W = $"hard_locale"(W #0);
    %"v38" : W = (Ext Ub) %"v37";
    %"v39" : W = (Cmp Eq W) %"v38", #0
    => goto "L36";
  @"L36" [%"v41" : W = phi("L30" => #0, "L35" => %"v39")]:
    => br %"v41" ? "L22" : "L24";
  @"L22":
    %"chk0" : A = (Check 0 1 Read 1) %"v2";
    %"v44" : W = (RawLoad (LdNarrow Sb) 0) %"chk0";
    %"v45" : W = (Ext Ub) %"v44";
    %"chk1" : A = (Check 0 4 Write 1) %"pr.1";
    store Ww [%"chk1" + 0] <- %"v45"
    => ret #1;
  @"L24":
    => ret %"v21"
} }.
