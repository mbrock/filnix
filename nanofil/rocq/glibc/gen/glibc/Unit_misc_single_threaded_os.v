(** This file defines checked IR from glibc’s `misc/single_threaded.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___libc_single_threaded : item :=
  (IData (a "__libc_single_threaded") LExport 1 [(Zero 1)]).

Definition item___libc_single_threaded_internal : item :=
  (IAlias (a "__libc_single_threaded_internal") (a "export") (a "__libc_single_threaded")).
