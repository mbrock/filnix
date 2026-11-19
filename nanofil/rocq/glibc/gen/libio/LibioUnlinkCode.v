(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_libio_fileops_os Unit_libio_genops_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition libiounlink_module : module :=
  [IFunc Unit_libio_fileops_os.fn__IO_new_file_finish;
  IFunc Unit_libio_genops_os.fn___GI__IO_un_link;
  IFunc Unit_libio_genops_os.fn___GI__IO_default_finish].
