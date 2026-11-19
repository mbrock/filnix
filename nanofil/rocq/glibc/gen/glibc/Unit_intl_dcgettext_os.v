(** This file defines checked IR from glibc’s `intl/dcgettext.os` object.
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

Definition fn___GI___dcgettext : func :=
  ir_fn{ "export" "__GI___dcgettext"(P %"v0", P %"v2", W %"v4") -> (RClass P) {
  @"start":
    call %"v9" : P = $"__dcigettext"(P %"v0", P %"v2", P #0, W #0, L #0, W %"v4")
    => ret %"v9"
} }.
