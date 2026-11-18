(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Export HelloImageTypedGC01 HelloImageTypedGC02 HelloImageTypedGC03 HelloImageTypedGC04 HelloImageTypedGC05 HelloImageTypedGC06 HelloImageTypedGC07 HelloImageTypedGC08 HelloImageTypedGC09 HelloImageTypedGC10 HelloImageTypedGC11 HelloImageTypedGC12 HelloImageTypedGC13.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
