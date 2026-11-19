(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Findlocale_roots Unit_locale_findlocale_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition findlocale_module : module :=
  [Findlocale_roots.item_findlocale_roots;
  IFunc Unit_locale_findlocale_os.fn__nl_find_locale;
  Unit_locale_findlocale_os.item__nl_default_locale_path;
  Unit_locale_findlocale_os.item_glibc_findlocale'23_nl_find_locale'2ecodeset_idx'2e245;
  Unit_locale_findlocale_os.item__nl_locale_file_list;
  Unit_locale_findlocale_os.item_glibc_findlocale'23valid_locale_name'2eslashdot'2e250;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e243;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e244;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e246;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e247;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e248;
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e249].
