(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Fxprintf_roots Unit_stdioZ2dcommon_fxprintf_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition fxprintf_module : module :=
  [Fxprintf_roots.item_fxprintf_roots;
  IFunc Unit_stdioZ2dcommon_fxprintf_os.fn___fxprintf_nocancel].
