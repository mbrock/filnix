(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_iconv_gconv_conf_os Unit_iconv_gconv_db_os Unit_iconv_gconv_dl_os Unit_iconv_gconv_open_os Unit_iconv_gconv_simple_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_05 : module :=
  [Unit_iconv_gconv_conf_os.item_glibc_gconv_conf'23str'2e301;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_alias_compare;
  IFunc Unit_iconv_gconv_db_os.fn_glibc_gconv_db'23derivation_compare;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_release_step;
  IFunc Unit_iconv_gconv_db_os.fn_glibc_gconv_db'23find_derivation;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_compare_alias;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_find_transform;
  IFunc Unit_iconv_gconv_db_os.fn___gconv_close_transform;
  Unit_iconv_gconv_db_os.item___gconv_alias_db;
  Unit_iconv_gconv_db_os.item___gconv_lock;
  Unit_iconv_gconv_db_os.item___gconv_modules_db;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23known_derivations;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e275;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e276;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e277;
  Unit_iconv_gconv_db_os.item_glibc_gconv_db'23str'2e278;
  IFunc Unit_iconv_gconv_dl_os.fn_glibc_gconv_dl'23known_compare;
  IFunc Unit_iconv_gconv_dl_os.fn___gconv_find_shlib;
  IFunc Unit_iconv_gconv_dl_os.fn_glibc_gconv_dl'23do_release_shlib;
  IFunc Unit_iconv_gconv_dl_os.fn___gconv_release_shlib;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23loaded;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e274;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e275;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e276;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e277;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e278;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e279;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e280;
  Unit_iconv_gconv_dl_os.item_glibc_gconv_dl'23str'2e281;
  IFunc Unit_iconv_gconv_open_os.fn___GI___gconv_open;
  Unit_iconv_gconv_open_os.item_glibc_gconv_open'23str'2e243;
  Unit_iconv_gconv_open_os.item_glibc_gconv_open'23str'2e244;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_btwoc_ascii;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs4;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs4_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs4le;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs4le_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ascii_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ascii;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_utf8;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_utf8_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs2_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs2;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_ucs2reverse_internal;
  IFunc Unit_iconv_gconv_simple_os.fn___gconv_transform_internal_ucs2reverse;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23utf8_internal_loop_single'2einmask'2e318;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e270;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e271;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e272;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e273;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e274;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e275;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e276;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e277;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e278;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e279;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e280;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e281;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e282;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e283;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e284;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e285;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e286;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e287].

Lemma hello_image_linked_items_05_zero : zero_nonneg hello_image_linked_items_05 = true.
Proof. reflexivity. Qed.
