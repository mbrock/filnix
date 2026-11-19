(** This file defines checked IR from glibc’s `setjmp/longjmp.os` object.
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

Definition item___libc_longjmp : item :=
  (IAlias (a "__libc_longjmp") (a "export") (a "__libc_siglongjmp")).

Definition fn___libc_siglongjmp : func :=
  ir_fn{ "export" "__libc_siglongjmp"(P %"v0", W %"v2") -> RVoid {
  @"start":
    %"chk0" : A = (Check 0 8 Read 8) %"v0";
    %"v5" : P = (RawLoadPointer 0 load_effects) %"chk0";
    call void $"zlongjmp"(P %"v5", W %"v2")
    => ret void
} }.
