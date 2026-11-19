(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_misc_error_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition error_module : module :=
  [(IData (a "error_roots") (LRo (a "export")) 8 [(Sym (a "error") 0)]);
  IFunc Unit_misc_error_os.fn___error_internal;
  IFunc Unit_misc_error_os.fn___error;
  Unit_misc_error_os.item_error;
  Unit_misc_error_os.item_error_message_count;
  Unit_misc_error_os.item_error_print_progname;
  Unit_misc_error_os.item_glibc_error'23str'2e252;
  Unit_misc_error_os.item_glibc_error'23str'2e253;
  Unit_misc_error_os.item_glibc_error'23str'2e254;
  Unit_misc_error_os.item_glibc_error'23str'2e255].
