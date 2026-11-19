(** This file defines checked IR from glibc’s `posix/_exit.os` object.
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

Definition fn___GI__exit : func :=
  ir_fn{ "export" "__GI__exit"(W %"v0") -> RVoid {
  @"start":
    call void $"zsys_exit_hard"(W %"v0")
    => ret void
} }.

Definition item__exit : item :=
  (IAlias (a "_exit") (a "export") (a "__GI__exit")).
