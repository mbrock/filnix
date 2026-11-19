(** This file defines checked IR from glibc’s `nptl/cleanup_compat.os` object.
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

Definition fn___GI___pthread_cleanup_pop : func :=
  ir_fn{ "export" "__GI___pthread_cleanup_pop"(P %"v0", W %"v2") -> RVoid {
  @"start":
    call %"v5" : P = $"zthread_self_cookie"();
    %"v7" = %"v5" +p #776;
    %"v9" = %"v0" +p #24;
    %"chk0" : A = (Check 0 8 Read 8) %"v9";
    %"v10" : P = (RawLoadPointer 0 load_effects) %"chk0";
    %"chk1" : A = (Check 0 8 Write 8) %"v7";
    store.ptr [%"chk1" + 0] <- %"v10"
    => br %"v2" ? "L11" : "L13";
  @"L11":
    %"chk2" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v0";
    %"v16" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"v18" = %"v0" +p #8;
    %"chk3" : A = (HalfCheck Lower 0 8 Read 8) %"chk0", %"v18";
    %"v19" : P = (RawLoadPointer 0 load_effects) %"chk3";
    %"chk4" : F = CheckFunction %"v16";
    rawcall void %"chk4"(P %"v19")
    => goto "L13";
  @"L13":
    => ret void
} }.

Definition fn___GI___pthread_cleanup_push : func :=
  ir_fn{ "export" "__GI___pthread_cleanup_push"(P %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    call %"v7" : P = $"zthread_self_cookie"();
    %"chk0" : A = (Check 0 8 Write 8) %"v0";
    store.ptr [%"chk0" + 0] <- %"v2";
    %"v11" = %"v0" +p #8;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v11";
    store.ptr [%"chk1" + 0] <- %"v4";
    %"v14" = %"v0" +p #24;
    %"v16" = %"v7" +p #776;
    %"chk2" : A = (Check 0 8 Read 8) %"v16";
    %"v17" : P = (RawLoadPointer 0 load_effects) %"chk2";
    %"chk3" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"v14";
    store.ptr [%"chk3" + 0] <- %"v17";
    %"chk4" : A = (Renew 0 8 Write 8) %"chk2", %"v16";
    store.ptr [%"chk4" + 0] <- %"v0"
    => ret void
} }.
