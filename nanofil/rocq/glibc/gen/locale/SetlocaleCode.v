(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_locale_setlocale_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition setlocale_module : module :=
  [(IData (a "setlocale_roots") (LRo (a "export")) 8 [(Sym (a "__GI_setlocale") 0)]);
  IFunc Unit_locale_setlocale_os.fn_glibc_setlocale'23new_composite_name;
  IFunc Unit_locale_setlocale_os.fn___GI_setlocale;
  Unit_locale_setlocale_os.item___libc_setlocale_lock;
  Unit_locale_setlocale_os.item__nl_category_name_idxs;
  Unit_locale_setlocale_os.item__nl_category_name_sizes;
  Unit_locale_setlocale_os.item__nl_category_names;
  Unit_locale_setlocale_os.item_glibc_setlocale'23_nl_category_postload;
  Unit_locale_setlocale_os.item_glibc_setlocale'23str'2e234].
