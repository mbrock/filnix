(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Strncmp_roots Unit_string_strncmp_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition strncmp_module : module :=
  [Strncmp_roots.item_strncmp_roots;
  IFunc Unit_string_strncmp_os.fn___GI_strncmp;
  Unit_string_strncmp_os.item_strncmp].
