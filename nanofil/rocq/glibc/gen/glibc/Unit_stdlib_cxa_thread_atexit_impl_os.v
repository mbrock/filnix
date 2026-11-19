(** This file defines checked IR from glibc’s `stdlib/cxa_thread_atexit_impl.os` object.
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

Definition fn___GI___call_tls_dtors : func :=
  ir_fn{ "export" "__GI___call_tls_dtors"() -> RVoid {
  @"start":
    => ret void
} }.
