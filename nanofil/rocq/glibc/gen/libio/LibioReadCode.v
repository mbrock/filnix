(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_libio___fpending_os Unit_libio_ferror_os Unit_libio_filedoalloc_os Unit_libio_fileops_os Unit_libio_genops_os Unit_misc_makedev_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition libioread_module : module :=
  [IFunc Unit_libio___fpending_os.fn___fpending;
  IFunc Unit_libio_ferror_os.fn__IO_ferror;
  IFunc Unit_libio_filedoalloc_os.fn___GI__IO_file_doallocate;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_stat;
  IFunc Unit_libio_fileops_os.fn___GI__IO_file_close;
  IFunc Unit_libio_fileops_os.fn__IO_new_file_write;
  IFunc Unit_libio_genops_os.fn___GI__IO_setb;
  IFunc Unit_libio_genops_os.fn___GI__IO_doallocbuf;
  IFunc Unit_misc_makedev_os.fn___gnu_dev_major].
