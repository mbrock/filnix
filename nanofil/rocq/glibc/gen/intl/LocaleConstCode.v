(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_locale_C_name_os Unit_locale_setlocale_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition localeconst_module : module :=
  [(IData (a "localeconst_roots") (LRo (a "export")) 8 [(Sym (a "_nl_category_names") 0); (Sym (a "_nl_category_name_idxs") 0); (Sym (a "_nl_C_name") 0)]);
  Unit_locale_setlocale_os.item__nl_category_name_idxs;
  Unit_locale_setlocale_os.item__nl_category_names;
  Unit_locale_C_name_os.item__nl_C_name].
