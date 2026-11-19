(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_locale_SYS_libc_os Unit_string__strerror_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition strerror_module : module :=
  [(IData (a "strerror_roots") (LRo (a "export")) 8 [(Sym (a "__GI___strerror_r") 0)]);
  IFunc Unit_string__strerror_os.fn___GI___strerror_r;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e136;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e137;
  Unit_locale_SYS_libc_os.item___GI__libc_intl_domainname].
