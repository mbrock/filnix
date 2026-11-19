(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_to_file_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition printf_buffer_file_module : module :=
  [IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_switch;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_flush_to_file;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_init;
  IFunc Unit_stdioZ2dcommon_printf_buffer_to_file_os.fn___printf_buffer_to_file_done].
