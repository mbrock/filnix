(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition errlistdata_module_items_03 : module :=
  [Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e372;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e373;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e374;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e375;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e376;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e377;
  Unit_stdioZ2dcommon_errlistZ2ddataZ2dgen_os.item_glibc_errlist_data_gen'23str'2e378].
