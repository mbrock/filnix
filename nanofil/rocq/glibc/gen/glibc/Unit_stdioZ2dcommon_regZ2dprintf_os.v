(** This file defines checked IR from glibc’s `stdio-common/reg-printf.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___printf_arginfo_table : item :=
  (IData (a "__printf_arginfo_table") LExport 8 [(Zero 8)]).

Definition item___printf_function_table : item :=
  (IData (a "__printf_function_table") LExport 8 [(Zero 8)]).
