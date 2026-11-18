(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Export HiAtexitTypedIO01 HiAtexitTypedIO02 HiAtexitTypedIO03 HiAtexitTypedIO04 HiAtexitTypedIO05 HiAtexitTypedIO06 HiAtexitTypedIO07 HiAtexitTypedIO08.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).
