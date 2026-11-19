(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_nptl_pthread_setcancelstate_os Unit_stdioZ2dcommon_printf_buffer_done_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition printf_state_module : module :=
  [IFunc Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate;
  IFunc Unit_stdioZ2dcommon_printf_buffer_done_os.fn___printf_buffer_done].
