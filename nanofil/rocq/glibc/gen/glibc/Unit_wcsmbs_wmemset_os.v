(** This file defines checked IR from glibc’s `wcsmbs/wmemset.os` object.
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

Definition fn___GI___wmemset : func :=
  ir_fn{ "export" "__GI___wmemset"(P %"v0", W %"v2", L %"v4") -> (RClass P) {
  @"start":
    => goto "L8";
  @"L8" [%"pr.2" : P = phi("L9" => %"v26", "start" => %"v0"); %"pr.1" : L = phi("L9" => %"v28", "start" => %"v4")]:
    %"v12" : W = (Cmp Uge L) %"pr.1", #4
    => br %"v12" ? "L9" : "L10";
  @"L9":
    %"chk0" : A = (Check 0 4 Write 1) %"pr.2";
    store Ww [%"chk0" + 0] <- %"v2";
    %"v17" = %"pr.2" +p #4;
    %"chk1" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v17";
    store Ww [%"chk1" + 0] <- %"v2";
    %"v20" = %"pr.2" +p #8;
    %"chk2" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v20";
    store Ww [%"chk2" + 0] <- %"v2";
    %"v23" = %"pr.2" +p #12;
    %"chk3" : A = (HalfCheck Upper 0 4 Write 1) %"chk0", %"v23";
    store Ww [%"chk3" + 0] <- %"v2";
    %"v26" = %"pr.2" +p #16;
    %"v28" : L = Sub %"pr.1", #4
    => goto poll "L8";
  @"L10":
    %"v33" : W = (Cmp Ugt L) %"pr.1", #0
    => br %"v33" ? "L29" : "L31";
  @"L29":
    %"chk4" : A = (Check 0 4 Write 1) %"pr.2";
    store Ww [%"chk4" + 0] <- %"v2";
    %"v41" : W = (Cmp Ugt L) %"pr.1", #1
    => br %"v41" ? "L37" : "L31";
  @"L37":
    %"v43" = %"pr.2" +p #4;
    %"chk5" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v43";
    store Ww [%"chk5" + 0] <- %"v2";
    %"v49" : W = (Cmp Ugt L) %"pr.1", #2
    => br %"v49" ? "L45" : "L31";
  @"L45":
    %"v51" = %"pr.2" +p #8;
    %"chk6" : A = (HalfCheck Upper 0 4 Write 1) %"chk4", %"v51";
    store Ww [%"chk6" + 0] <- %"v2"
    => goto "L31";
  @"L31":
    => ret %"v0"
} }.
