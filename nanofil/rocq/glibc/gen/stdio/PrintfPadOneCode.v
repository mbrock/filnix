(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import PrintfPadOne_roots Unit_stdioZ2dcommon_printf_buffer_pad_1_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition printfpadone_module : module :=
  [PrintfPadOne_roots.item_printfpadone_roots;
  IFunc Unit_stdioZ2dcommon_printf_buffer_pad_1_os.fn___printf_buffer_pad_1;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e41;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e42;
  Unit_stdioZ2dcommon_printf_buffer_pad_1_os.item_glibc_printf_buffer_pad_1'23str'2e43].
