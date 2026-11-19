(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_flush_os Unit_stdioZ2dcommon_printf_buffer_write_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition printf_buffer_io_module : module :=
  [IFunc Unit_stdioZ2dcommon_printf_buffer_write_os.fn___printf_buffer_write;
  IFunc Unit_stdioZ2dcommon_printf_buffer_flush_os.fn___printf_buffer_flush].
