(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedDE HelloImageTypedDO HelloImageTypedFI HelloImageTypedGC02 HelloImageTypedGC03 HelloImageTypedGC04 HelloImageTypedGC05 HelloImageTypedGC06 HelloImageTypedGC07 HelloImageTypedGC08 HelloImageTypedGC09 HelloImageTypedGC10 HelloImageTypedGC11 HelloImageTypedGC12 HelloImageTypedKN HelloImageTypedObjects02.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_05 : module :=
  [hello_image_item_glibc_gconv_conf'23str'2e301;
  IFunc hello_image_fn___gconv_alias_compare;
  IFunc hello_image_fn_glibc_gconv_db'23derivation_compare;
  IFunc hello_image_fn___gconv_release_step;
  IFunc hello_image_fn_glibc_gconv_db'23find_derivation;
  IFunc hello_image_fn___gconv_compare_alias;
  IFunc hello_image_fn___gconv_find_transform;
  IFunc hello_image_fn___gconv_close_transform;
  hello_image_item___gconv_alias_db;
  hello_image_item___gconv_lock;
  hello_image_item___gconv_modules_db;
  hello_image_item_glibc_gconv_db'23known_derivations;
  hello_image_item_glibc_gconv_db'23str'2e275;
  hello_image_item_glibc_gconv_db'23str'2e276;
  hello_image_item_glibc_gconv_db'23str'2e277;
  hello_image_item_glibc_gconv_db'23str'2e278;
  IFunc hello_image_fn_glibc_gconv_dl'23known_compare;
  IFunc hello_image_fn___gconv_find_shlib;
  IFunc hello_image_fn_glibc_gconv_dl'23do_release_shlib;
  IFunc hello_image_fn___gconv_release_shlib;
  hello_image_item_glibc_gconv_dl'23loaded;
  hello_image_item_glibc_gconv_dl'23str'2e274;
  hello_image_item_glibc_gconv_dl'23str'2e275;
  hello_image_item_glibc_gconv_dl'23str'2e276;
  hello_image_item_glibc_gconv_dl'23str'2e277;
  hello_image_item_glibc_gconv_dl'23str'2e278;
  hello_image_item_glibc_gconv_dl'23str'2e279;
  hello_image_item_glibc_gconv_dl'23str'2e280;
  hello_image_item_glibc_gconv_dl'23str'2e281;
  IFunc hello_image_fn___GI___gconv_open;
  hello_image_item_glibc_gconv_open'23str'2e243;
  hello_image_item_glibc_gconv_open'23str'2e244;
  IFunc hello_image_fn___gconv_btwoc_ascii;
  IFunc hello_image_fn___gconv_transform_internal_ucs4;
  IFunc hello_image_fn___gconv_transform_ucs4_internal;
  IFunc hello_image_fn___gconv_transform_internal_ucs4le;
  IFunc hello_image_fn___gconv_transform_ucs4le_internal;
  IFunc hello_image_fn___gconv_transform_ascii_internal;
  IFunc hello_image_fn___gconv_transform_internal_ascii;
  IFunc hello_image_fn___gconv_transform_internal_utf8;
  IFunc hello_image_fn___gconv_transform_utf8_internal;
  IFunc hello_image_fn___gconv_transform_ucs2_internal;
  IFunc hello_image_fn___gconv_transform_internal_ucs2;
  IFunc hello_image_fn___gconv_transform_ucs2reverse_internal;
  IFunc hello_image_fn___gconv_transform_internal_ucs2reverse;
  hello_image_item_glibc_gconv_simple'23utf8_internal_loop_single'2einmask'2e318;
  hello_image_item_glibc_gconv_simple'23str'2e270;
  hello_image_item_glibc_gconv_simple'23str'2e271;
  hello_image_item_glibc_gconv_simple'23str'2e272;
  hello_image_item_glibc_gconv_simple'23str'2e273;
  hello_image_item_glibc_gconv_simple'23str'2e274;
  hello_image_item_glibc_gconv_simple'23str'2e275;
  hello_image_item_glibc_gconv_simple'23str'2e276;
  hello_image_item_glibc_gconv_simple'23str'2e277;
  hello_image_item_glibc_gconv_simple'23str'2e278;
  hello_image_item_glibc_gconv_simple'23str'2e279;
  hello_image_item_glibc_gconv_simple'23str'2e280;
  hello_image_item_glibc_gconv_simple'23str'2e281;
  hello_image_item_glibc_gconv_simple'23str'2e282;
  hello_image_item_glibc_gconv_simple'23str'2e283;
  hello_image_item_glibc_gconv_simple'23str'2e284;
  hello_image_item_glibc_gconv_simple'23str'2e285;
  hello_image_item_glibc_gconv_simple'23str'2e286;
  hello_image_item_glibc_gconv_simple'23str'2e287].

Lemma hello_image_items_05_zero : zero_nonneg hello_image_items_05 = true.
Proof. reflexivity. Qed.
