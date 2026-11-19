(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_locale_CZ2dctype_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked_items_06 : module :=
  [Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e278;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e279;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e280].
