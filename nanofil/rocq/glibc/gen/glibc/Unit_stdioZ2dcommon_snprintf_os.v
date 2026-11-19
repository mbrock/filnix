(** This file defines checked IR from glibc’s `stdio-common/snprintf.os` object.
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

Definition fn___GI___snprintf : func :=
  ir_fn{ "export" "__GI___snprintf"(P %"v0", L %"v2", P %"v4") -> (RClass W) {
  @"start":
    %"v6" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #24;
    %"chk0" : A = (Check 0 8 Write 8) %"v6";
    store.ptr [%"chk0" + 0] <- %"va_args";
    call %"v11" : W = $"__vsnprintf_internal"(P %"v0", L %"v2", P %"v4", P %"v6", W #0)
    => ret %"v11"
} }.
