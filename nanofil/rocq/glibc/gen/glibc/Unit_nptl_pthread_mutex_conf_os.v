(** This file defines checked IR from glibc’s `nptl/pthread_mutex_conf.os` object.
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

Definition item___GI___mutex_aconf : item :=
  (IData (a "__GI___mutex_aconf") LExport 4 [(Item Ww 100)]).

Definition fn___pthread_tunables_init : func :=
  ir_fn{ "export" "__pthread_tunables_init"() -> RVoid {
  @"start":
    %"v1" : P = (Alloc 4) #4;
    %"v3" : P = Copy $"glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count";
    call void $"__tunable_get_val"(W #27, P %"v1", P %"v3");
    %"chk0" : A = (Check 0 4 Read 1) %"v1";
    %"v4" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret void
} }.

Definition fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count : func :=
  ir_fn{ "local" "glibc_pthread_mutex_conf#_dl_tunable_set_mutex_spin_count"(P %"v0") -> RVoid {
  @"start":
    %"v2" : P = Copy $"__GI___mutex_aconf";
    %"chk0" : A = (Check 0 8 Read 1) %"v0";
    %"v4" : L = (RawLoad LdL 0) %"chk0";
    %"chk1" : A = (Check 0 4 Write 1) %"v2";
    store Ww [%"chk1" + 0] <- %"v4"
    => ret void
} }.
