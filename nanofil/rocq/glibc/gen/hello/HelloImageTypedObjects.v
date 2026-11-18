(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Export HelloImageTypedObjects01 HelloImageTypedObjects02 HelloImageTypedObjects03 HelloImageTypedObjects04 HelloImageTypedObjects05 HelloImageTypedObjects06 HelloImageTypedObjects07 HelloImageTypedObjects08 HelloImageTypedObjects09 HelloImageTypedObjects10 HelloImageTypedObjects11 HelloImageTypedObjects12 HelloImageTypedObjects13.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
