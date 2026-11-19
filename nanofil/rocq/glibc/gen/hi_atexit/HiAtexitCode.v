(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitCodeItems01 HiAtexitCodeItems02 HiAtexitCodeItems03 HiAtexitCodeItems04 HiAtexitCodeItems05 HiAtexitCodeItems06.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked : module := hi_linked_items_01 ++ hi_linked_items_02 ++ hi_linked_items_03 ++ hi_linked_items_04 ++ hi_linked_items_05 ++ hi_linked_items_06.
