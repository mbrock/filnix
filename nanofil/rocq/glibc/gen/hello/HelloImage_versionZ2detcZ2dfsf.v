(** This file defines checked IR from the `version-etc-fsf` object of HelloImage.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import IRBytes.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition item_version_etc_copyright : item :=
  (IData (a "version_etc_copyright") (LRo (a "export")) 1 ["Copyright %s %d Free Software Foundation, Inc."%irbytes; (Zero 1)]).
