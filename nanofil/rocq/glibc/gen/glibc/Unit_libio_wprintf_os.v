(** This file defines checked IR from glibc’s `libio/wprintf.os` object.
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

Definition fn___wprintf : func :=
  ir_fn{ "export" "__wprintf"(P %"v0") -> (RClass W) {
  @"start":
    %"v2" : P = (Alloc 8) #24;
    %"va_args" : P = VaArgs #8;
    %"chk0" : A = (Check 0 8 Write 8) %"v2";
    store.ptr [%"chk0" + 0] <- %"va_args";
    %"v4" : P = Copy $"stdout";
    %"chk1" : A = (Check 0 8 Read 8) %"v4";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk1";
    call %"v7" : W = $"__vfwprintf_internal"(P %"v5", P %"v0", P %"v2", W #0)
    => ret %"v7"
} }.

Definition item_wprintf : item :=
  (IAlias (a "wprintf") (a "export") (a "__wprintf")).
