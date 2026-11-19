(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Strchr_roots Unit_string_memchr_os Unit_string_strchr_os Unit_string_strchrnul_os Unit_string_strnlen_os Unit_string_strrchr_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition strchr_module : module :=
  [Strchr_roots.item_strchr_roots;
  IFunc Unit_string_strchr_os.fn___GI_strchr;
  Unit_string_strchr_os.item_strchr;
  IFunc Unit_string_strchrnul_os.fn___GI___strchrnul;
  Unit_string_strchrnul_os.item_strchrnul;
  IFunc Unit_string_strrchr_os.fn___GI_strrchr;
  Unit_string_strrchr_os.item_strrchr;
  IFunc Unit_string_memchr_os.fn___memchr;
  Unit_string_memchr_os.item___GI_memchr;
  Unit_string_memchr_os.item_memchr;
  IFunc Unit_string_strnlen_os.fn___GI___strnlen;
  Unit_string_strnlen_os.item_strnlen].
