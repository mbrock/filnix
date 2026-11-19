(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Strcmp_roots Unit_string_strcmp_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition strcmp_module : module :=
  [Strcmp_roots.item_strcmp_roots;
  IFunc Unit_string_strcmp_os.fn___GI_strcmp;
  Unit_string_strcmp_os.item_strcmp].
