(** This file defines checked IR from glibc’s `posix/getopt1.os` object.
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

Definition fn_getopt_long : func :=
  ir_fn{ "export" "getopt_long"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8") -> (RClass W) {
  @"start":
    call %"v15" : W = $"_getopt_internal"(W %"v0", P %"v2", P %"v4", P %"v6", P %"v8", W #0, W #0)
    => ret %"v15"
} }.
