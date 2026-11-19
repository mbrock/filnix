(** This file defines checked IR from glibc’s `io/fcntl_nocancel.os` object.
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

Definition fn___GI___fcntl64_nocancel : func :=
  ir_fn{ "export" "__GI___fcntl64_nocancel"(W %"v0", W %"v2") -> (RClass W) {
  @"start":
    %"va_args" : P = VaArgs #16;
    %"v4" : P = Copy $"zsys_fcntl";
    %"v5" : P = VaArgs #0;
    call %"v6" : P = $"zcall"(P %"v4", P %"v5");
    %"chk0" : A = (Check 0 4 Read 1) %"v6";
    %"v7" : W = (RawLoad (LdNarrow Sw) 0) %"chk0"
    => ret %"v7"
} }.
