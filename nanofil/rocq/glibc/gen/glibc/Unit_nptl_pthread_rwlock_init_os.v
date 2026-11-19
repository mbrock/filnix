(** This file defines checked IR from glibc’s `nptl/pthread_rwlock_init.os` object.
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

Definition item___GI___pthread_rwlock_init : item :=
  (IAlias (a "__GI___pthread_rwlock_init") (a "export") (a "___pthread_rwlock_init")).

Definition fn____pthread_rwlock_init : func :=
  ir_fn{ "export" "___pthread_rwlock_init"(P %"v0", P %"v2") -> (RClass W) {
  @"start":
    %"v6" : L = Ptoi %"v2";
    %"v7" : W = (Cmp Ne L) %"v6", #0
    => br %"v7" ? "L10" : "L9";
  @"L9":
    %"v11" : P = Copy $"glibc_pthread_rwlock_init#default_rwlockattr"
    => goto "L10";
  @"L10" [%"v12" : P = phi("L9" => %"v11", "start" => %"v2")]:
    call %"v14" : P = $"__GI_memset"(P %"v0", W #0, L #56);
    %"v16" = %"v0" +p #48;
    %"chk0" : A = (Check 0 4 Read 1) %"v12";
    %"v18" : W = (RawLoad (LdNarrow Sw) 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v16";
    store Ww [%"chk1" + 0] <- %"v18";
    %"v20" = %"v0" +p #28;
    %"v22" = %"v12" +p #4;
    %"chk2" : A = (HalfCheck Upper 0 4 Read 1) %"chk0", %"v22";
    %"v23" : W = (RawLoad (LdNarrow Sw) 0) %"chk2";
    %"v24" : W = (Cmp Ne W) %"v23", #0;
    %"chk3" : A = (HalfCheck Lower 0 4 Write 1) %"chk1", %"v20";
    store Ww [%"chk3" + 0] <- %"v24"
    => ret #0
} }.

Definition item_glibc_pthread_rwlock_init'23default_rwlockattr : item :=
  (IData (a "glibc_pthread_rwlock_init#default_rwlockattr") (LRo (a "local")) 4 [(Item Ww 0); (Item Ww 0)]).
