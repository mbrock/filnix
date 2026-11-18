(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedItems01 HiAtexitTypedItems02 HiAtexitTypedItems03 HiAtexitTypedItems04 HiAtexitTypedItems05 HiAtexitTypedItems06.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).


Definition hi_decoded : module := hi_items_01 ++ hi_items_02 ++ hi_items_03 ++ hi_items_04 ++ hi_items_05 ++ hi_items_06.
