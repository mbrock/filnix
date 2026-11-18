(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedFP HelloImageTypedFU HelloImageTypedFX HelloImageTypedGE03 HelloImageTypedGR HelloImageTypedObjects10 HelloImageTypedPA01 HelloImageTypedPA02 HelloImageTypedPR01 HelloImageTypedVF.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_20 : module :=
  [hello_image_item_glibc_errlist_data_gen'23str'2e341;
  hello_image_item_glibc_errlist_data_gen'23str'2e342;
  hello_image_item_glibc_errlist_data_gen'23str'2e343;
  hello_image_item_glibc_errlist_data_gen'23str'2e344;
  hello_image_item_glibc_errlist_data_gen'23str'2e345;
  hello_image_item_glibc_errlist_data_gen'23str'2e346;
  hello_image_item_glibc_errlist_data_gen'23str'2e347;
  hello_image_item_glibc_errlist_data_gen'23str'2e348;
  hello_image_item_glibc_errlist_data_gen'23str'2e349;
  hello_image_item_glibc_errlist_data_gen'23str'2e350;
  hello_image_item_glibc_errlist_data_gen'23str'2e351;
  hello_image_item_glibc_errlist_data_gen'23str'2e352;
  hello_image_item_glibc_errlist_data_gen'23str'2e353;
  hello_image_item_glibc_errlist_data_gen'23str'2e354;
  hello_image_item_glibc_errlist_data_gen'23str'2e355;
  hello_image_item_glibc_errlist_data_gen'23str'2e356;
  hello_image_item_glibc_errlist_data_gen'23str'2e357;
  hello_image_item_glibc_errlist_data_gen'23str'2e358;
  hello_image_item_glibc_errlist_data_gen'23str'2e359;
  hello_image_item_glibc_errlist_data_gen'23str'2e360;
  hello_image_item_glibc_errlist_data_gen'23str'2e361;
  hello_image_item_glibc_errlist_data_gen'23str'2e362;
  hello_image_item_glibc_errlist_data_gen'23str'2e363;
  hello_image_item_glibc_errlist_data_gen'23str'2e364;
  hello_image_item_glibc_errlist_data_gen'23str'2e365;
  hello_image_item_glibc_errlist_data_gen'23str'2e366;
  hello_image_item_glibc_errlist_data_gen'23str'2e367;
  hello_image_item_glibc_errlist_data_gen'23str'2e368;
  hello_image_item_glibc_errlist_data_gen'23str'2e369;
  hello_image_item_glibc_errlist_data_gen'23str'2e370;
  hello_image_item_glibc_errlist_data_gen'23str'2e371;
  hello_image_item_glibc_errlist_data_gen'23str'2e372;
  hello_image_item_glibc_errlist_data_gen'23str'2e373;
  hello_image_item_glibc_errlist_data_gen'23str'2e374;
  hello_image_item_glibc_errlist_data_gen'23str'2e375;
  hello_image_item_glibc_errlist_data_gen'23str'2e376;
  hello_image_item_glibc_errlist_data_gen'23str'2e377;
  hello_image_item_glibc_errlist_data_gen'23str'2e378;
  IFunc hello_image_fn___get_errlist;
  IFunc hello_image_fn___get_errname;
  hello_image_item_glibc_errname'23_sys_errname;
  hello_image_item_glibc_errname'23_sys_errnameidx;
  IFunc hello_image_fn___fprintf;
  hello_image_item_fprintf;
  IFunc hello_image_fn___GI___funlockfile;
  hello_image_item__IO_funlockfile;
  IFunc hello_image_fn___vfxprintf;
  IFunc hello_image_fn___fxprintf;
  IFunc hello_image_fn___fxprintf_nocancel;
  IFunc hello_image_fn___grouping_iterator_init_none;
  IFunc hello_image_fn___grouping_iterator_init;
  IFunc hello_image_fn___grouping_iterator_next;
  hello_image_item_glibc_grouping_iterator'23str'2e41;
  hello_image_item_glibc_grouping_iterator'23str'2e42;
  hello_image_item_glibc_grouping_iterator'23str'2e43;
  hello_image_item___GI__itoa_lower_digits;
  hello_image_item___GI__itoa_upper_digits;
  hello_image_item__itowa_lower_digits;
  hello_image_item__itowa_upper_digits;
  IFunc hello_image_fn___parse_one_specmb;
  IFunc hello_image_fn___parse_one_specwc;
  IFunc hello_image_fn___printf;
  hello_image_item_printf;
  IFunc hello_image_fn___printf_buffer_as_file_overflow].

Lemma hello_image_items_20_zero : zero_nonneg hello_image_items_20 = true.
Proof. reflexivity. Qed.
