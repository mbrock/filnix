(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_stdioZ2dcommon_printf_buffer_putc_1_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition printfputcone_module : module :=
  [(IData (a "printfputcone_roots") (LRo (a "export")) 8 [(Sym (a "__printf_buffer_putc_1") 0)]);
  IFunc Unit_stdioZ2dcommon_printf_buffer_putc_1_os.fn___printf_buffer_putc_1;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e39;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e40;
  Unit_stdioZ2dcommon_printf_buffer_putc_1_os.item_glibc_printf_buffer_putc_1'23str'2e41].
