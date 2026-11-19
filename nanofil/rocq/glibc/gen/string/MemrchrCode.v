(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Memrchr_roots Unit_string_memrchr_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition memrchr_module : module :=
  [Memrchr_roots.item_memrchr_roots;
  IFunc Unit_string_memrchr_os.fn___GI___memrchr;
  Unit_string_memrchr_os.item_memrchr].
