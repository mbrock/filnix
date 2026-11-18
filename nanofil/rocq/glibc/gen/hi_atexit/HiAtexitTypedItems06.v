(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedObjects06.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_06 : module :=
  [hi_item_glibc_C_ctype'23str'2e278;
  hi_item_glibc_C_ctype'23str'2e279;
  hi_item_glibc_C_ctype'23str'2e280].
