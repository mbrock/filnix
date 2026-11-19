(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import ErrlistDataCodeItems01 ErrlistDataCodeItems02 ErrlistDataCodeItems03.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition errlistdata_module : module := errlistdata_module_items_01 ++ errlistdata_module_items_02 ++ errlistdata_module_items_03.
