(** This file defines checked IR from glibc’s `csu/errno-loc.os` object.
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

Definition fn___GI___errno_location : func :=
  ir_fn{ "export" "__GI___errno_location"() -> (RClass P) {
  @"start":
    %"v0" : P = Copy $"__libc_errno"
    => ret %"v0"
} }.

Definition item___errno_location : item :=
  (IAlias (a "__errno_location") (a "export") (a "__GI___errno_location")).
