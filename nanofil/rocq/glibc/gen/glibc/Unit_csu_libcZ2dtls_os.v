(** This file defines checked IR from glibc’s `csu/libc-tls.os` object.
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

Definition fn___libc_setup_tls : func :=
  ir_fn{ "export" "__libc_setup_tls"() -> RVoid {
  @"start":
    %"v1" : P = (Alloc 16) #2496;
    %"chk0" : A = (Check 0 8 Write 8) %"v1";
    store.ptr [%"chk0" + 0] <- %"v1";
    %"iw_1.v12" = %"v1" +p #16;
    %"chk1" : A = (HalfCheck Upper 0 8 Write 8) %"chk0", %"iw_1.v12";
    store.ptr [%"chk1" + 0] <- %"v1";
    call void $"zthread_set_self_cookie"(P %"v1");
    call void $"__tls_init_tp"()
    => ret void
} }.
