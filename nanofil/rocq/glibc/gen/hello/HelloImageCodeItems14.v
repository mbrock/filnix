(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_locale_CZ2dtime_os Unit_locale_C_name_os Unit_locale_SYS_libc_os Unit_locale_findlocale_os Unit_locale_globalZ2dlocale_os Unit_locale_lcZ2dctype_os Unit_locale_loadarchive_os.
From Glibc Require Import Unit_locale_loadlocale_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_14 : module :=
  [Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e69;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e70;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e71;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e72;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e73;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e74;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e75;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e76;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e77;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e78;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e79;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e80;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e81;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e82;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e83;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e84;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e85;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e86;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e87;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e88;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e89;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e90;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e91;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e92;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e93;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e94;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e95;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e96;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e97;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e98;
  Unit_locale_CZ2dtime_os.item_glibc_C_time'23str'2e99;
  Unit_locale_C_name_os.item__nl_C_codeset;
  Unit_locale_C_name_os.item__nl_C_name;
  Unit_locale_C_name_os.item__nl_POSIX_name;
  Unit_locale_SYS_libc_os.item___GI__libc_intl_domainname;
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
  Unit_locale_findlocale_os.item_glibc_findlocale'23str'2e249;
  Unit_locale_globalZ2dlocale_os.item___libc_tsd_LOCALE;
  Unit_locale_globalZ2dlocale_os.item__nl_global_locale;
  IFunc Unit_locale_lcZ2dctype_os.fn__nl_postload_ctype;
  IFunc Unit_locale_loadarchive_os.fn__nl_load_locale_from_archive;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archfname;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archive_stat;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archloaded;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23archmapped;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23headmap;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e249;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e250;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e251;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e252;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e254;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e255;
  Unit_locale_loadarchive_os.item_glibc_loadarchive'23str'2e256;
  IFunc Unit_locale_loadlocale_os.fn__nl_intern_locale_data;
  IFunc Unit_locale_loadlocale_os.fn__nl_load_locale].

Lemma hello_image_linked_items_14_zero : zero_nonneg hello_image_linked_items_14 = true.
Proof. reflexivity. Qed.
