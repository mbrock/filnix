(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Export HelloImageTypedIO01 HelloImageTypedIO02 HelloImageTypedIO03 HelloImageTypedIO04 HelloImageTypedIO05 HelloImageTypedIO06 HelloImageTypedIO07 HelloImageTypedIO08 HelloImageTypedIO09 HelloImageTypedIO10 HelloImageTypedIO11 HelloImageTypedIO12.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
