(** This file defines checked IR from glibc’s `csu/init-first.os` object.
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

Definition item___libc_argc : item :=
  (IData (a "__libc_argc") LExport 4 [(Zero 4)]).

Definition item___libc_argv : item :=
  (IData (a "__libc_argv") LExport 8 [(Zero 8)]).

Definition item___nanofil_ctor__init_first : item :=
  (IData (a "__nanofil_ctor__init_first") (LInit (a "ctor") (a "none")) 8 [(Sym (a "glibc_init_first#_init_first") 0)]).

Definition fn_glibc_init_first'23_init_first : func :=
  ir_fn{ "local" "glibc_init_first#_init_first"(W %"v0", P %"v2", P %"v4") -> RVoid {
  @"start":
    %"v6" : P = Copy $"__libc_argc";
    %"chk0" : A = (Check 0 4 Write 1) %"v6";
    store Ww [%"chk0" + 0] <- %"v0";
    %"v8" : P = Copy $"__libc_argv";
    %"chk1" : A = (Check 0 8 Write 8) %"v8";
    store.ptr [%"chk1" + 0] <- %"v2";
    %"v10" : P = Copy $"__environ";
    %"chk2" : A = (Check 0 8 Write 8) %"v10";
    store.ptr [%"chk2" + 0] <- %"v4";
    call void $"__init_misc"(W %"v0", P %"v2", P %"v4")
    => ret void
} }.
