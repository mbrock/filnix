(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_io_close_nocancel_nostatus_os Unit_io_close_nocancel_os Unit_io_fstat64_os Unit_io_lseek64_os Unit_io_write_nocancel_os Unit_io_write_os Unit_nptl_libcZ2dcleanup_os Unit_posix__exit_os.
From Glibc Require Import Unit_termios_isatty_nostatus_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition sys_module : module :=
  [IFunc Unit_termios_isatty_nostatus_os.fn___isatty_nostatus;
  IFunc Unit_io_write_os.fn___GI___libc_write;
  IFunc Unit_io_lseek64_os.fn___lseek64;
  IFunc Unit_io_fstat64_os.fn___GI___fstat64;
  IFunc Unit_io_close_nocancel_os.fn___GI___close_nocancel;
  IFunc Unit_io_close_nocancel_nostatus_os.fn___GI___close_nocancel_nostatus;
  IFunc Unit_posix__exit_os.fn___GI__exit;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore;
  IFunc Unit_io_write_nocancel_os.fn___GI___write_nocancel].
