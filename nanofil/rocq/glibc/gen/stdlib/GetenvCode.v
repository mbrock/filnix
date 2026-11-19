(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Getenv_roots Unit_stdlib_getenv_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition getenv_module : module :=
  [Getenv_roots.item_getenv_roots;
  IFunc Unit_stdlib_getenv_os.fn___GI_getenv;
  Unit_stdlib_getenv_os.item_getenv].
