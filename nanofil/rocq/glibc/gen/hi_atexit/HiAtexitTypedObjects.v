(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Export HiAtexitTypedObjects01 HiAtexitTypedObjects02 HiAtexitTypedObjects03 HiAtexitTypedObjects04 HiAtexitTypedObjects05 HiAtexitTypedObjects06.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
