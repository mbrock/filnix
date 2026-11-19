(** This file defines checked IR from glibc’s `nptl/nptl_nthreads.os` object.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item___GI___nptl_nthreads : item :=
  (IData (a "__GI___nptl_nthreads") LExport 4 [(Item Ww 1)]).
