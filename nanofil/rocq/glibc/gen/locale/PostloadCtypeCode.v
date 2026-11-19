(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import PostloadCtype_roots Unit_locale_lcZ2dctype_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition postloadctype_module : module :=
  [PostloadCtype_roots.item_postloadctype_roots;
  IFunc Unit_locale_lcZ2dctype_os.fn__nl_postload_ctype].
