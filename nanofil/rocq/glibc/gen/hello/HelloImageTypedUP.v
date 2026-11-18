(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageTypedUPBlocks1656x1 HelloImageTypedUPBlocks1656x2.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_fn_glibc_libc_start'23update_active : func :=
  mkFunc (a "glibc_libc_start#update_active") (a "local") RVoid [(P, (a "v0"))] (hello_image_fn_glibc_libc_start'23update_active'blocks1 ++ hello_image_fn_glibc_libc_start'23update_active'blocks2).
