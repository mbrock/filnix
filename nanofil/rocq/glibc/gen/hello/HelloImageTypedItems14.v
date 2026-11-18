(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedNL04 HelloImageTypedNL05 HelloImageTypedObjects08.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_14 : module :=
  [hello_image_item_glibc_C_time'23str'2e69;
  hello_image_item_glibc_C_time'23str'2e70;
  hello_image_item_glibc_C_time'23str'2e71;
  hello_image_item_glibc_C_time'23str'2e72;
  hello_image_item_glibc_C_time'23str'2e73;
  hello_image_item_glibc_C_time'23str'2e74;
  hello_image_item_glibc_C_time'23str'2e75;
  hello_image_item_glibc_C_time'23str'2e76;
  hello_image_item_glibc_C_time'23str'2e77;
  hello_image_item_glibc_C_time'23str'2e78;
  hello_image_item_glibc_C_time'23str'2e79;
  hello_image_item_glibc_C_time'23str'2e80;
  hello_image_item_glibc_C_time'23str'2e81;
  hello_image_item_glibc_C_time'23str'2e82;
  hello_image_item_glibc_C_time'23str'2e83;
  hello_image_item_glibc_C_time'23str'2e84;
  hello_image_item_glibc_C_time'23str'2e85;
  hello_image_item_glibc_C_time'23str'2e86;
  hello_image_item_glibc_C_time'23str'2e87;
  hello_image_item_glibc_C_time'23str'2e88;
  hello_image_item_glibc_C_time'23str'2e89;
  hello_image_item_glibc_C_time'23str'2e90;
  hello_image_item_glibc_C_time'23str'2e91;
  hello_image_item_glibc_C_time'23str'2e92;
  hello_image_item_glibc_C_time'23str'2e93;
  hello_image_item_glibc_C_time'23str'2e94;
  hello_image_item_glibc_C_time'23str'2e95;
  hello_image_item_glibc_C_time'23str'2e96;
  hello_image_item_glibc_C_time'23str'2e97;
  hello_image_item_glibc_C_time'23str'2e98;
  hello_image_item_glibc_C_time'23str'2e99;
  hello_image_item__nl_C_codeset;
  hello_image_item__nl_C_name;
  hello_image_item__nl_POSIX_name;
  hello_image_item___GI__libc_intl_domainname;
  IFunc hello_image_fn__nl_find_locale;
  hello_image_item__nl_default_locale_path;
  hello_image_item_glibc_findlocale'23_nl_find_locale'2ecodeset_idx'2e245;
  hello_image_item__nl_locale_file_list;
  hello_image_item_glibc_findlocale'23valid_locale_name'2eslashdot'2e250;
  hello_image_item_glibc_findlocale'23str'2e243;
  hello_image_item_glibc_findlocale'23str'2e244;
  hello_image_item_glibc_findlocale'23str'2e246;
  hello_image_item_glibc_findlocale'23str'2e247;
  hello_image_item_glibc_findlocale'23str'2e248;
  hello_image_item_glibc_findlocale'23str'2e249;
  hello_image_item___libc_tsd_LOCALE;
  hello_image_item__nl_global_locale;
  IFunc hello_image_fn__nl_postload_ctype;
  IFunc hello_image_fn__nl_load_locale_from_archive;
  hello_image_item_glibc_loadarchive'23archfname;
  hello_image_item_glibc_loadarchive'23archive_stat;
  hello_image_item_glibc_loadarchive'23archloaded;
  hello_image_item_glibc_loadarchive'23archmapped;
  hello_image_item_glibc_loadarchive'23headmap;
  hello_image_item_glibc_loadarchive'23str'2e249;
  hello_image_item_glibc_loadarchive'23str'2e250;
  hello_image_item_glibc_loadarchive'23str'2e251;
  hello_image_item_glibc_loadarchive'23str'2e252;
  hello_image_item_glibc_loadarchive'23str'2e254;
  hello_image_item_glibc_loadarchive'23str'2e255;
  hello_image_item_glibc_loadarchive'23str'2e256;
  IFunc hello_image_fn__nl_intern_locale_data;
  IFunc hello_image_fn__nl_load_locale].

Lemma hello_image_items_14_zero : zero_nonneg hello_image_items_14 = true.
Proof. reflexivity. Qed.
