(** This file defines checked IR from glibc’s `libio/stdio.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_stderr : item :=
  (IData (a "stderr") LExport 8 [(Sym (a "_IO_2_1_stderr_") 0)]).

Definition item_stdout : item :=
  (IData (a "stdout") LExport 8 [(Sym (a "_IO_2_1_stdout_") 0)]).
