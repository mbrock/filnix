(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCT HelloImageTypedCU HelloImageTypedDL HelloImageTypedLI01 HelloImageTypedMA HelloImageTypedNE HelloImageTypedOB HelloImageTypedObjects08 HelloImageTypedObjects09 HelloImageTypedPR01 HelloImageTypedPT01 HelloImageTypedSE.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_15 : module :=
  [hello_image_item_glibc_loadlocale'23_nl_category_num_items;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_ADDRESS;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_COLLATE;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_CTYPE;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_IDENTIFICATION;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MEASUREMENT;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MESSAGES;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_MONETARY;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_NAME;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_NUMERIC;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_PAPER;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_TELEPHONE;
  hello_image_item_glibc_loadlocale'23_nl_value_type_LC_TIME;
  hello_image_item_glibc_loadlocale'23_nl_value_types;
  hello_image_item_glibc_loadlocale'23str'2e240;
  hello_image_item_glibc_loadlocale'23str'2e241;
  hello_image_item_glibc_loadlocale'23str'2e242;
  hello_image_item_glibc_loadlocale'23str'2e243;
  IFunc hello_image_fn___current_locale_name;
  IFunc hello_image_fn___ctype_get_mb_cur_max;
  IFunc hello_image_fn_glibc_setlocale'23new_composite_name;
  IFunc hello_image_fn___GI_setlocale;
  hello_image_item___libc_setlocale_lock;
  hello_image_item__nl_category_name_idxs;
  hello_image_item__nl_category_name_sizes;
  hello_image_item__nl_category_names;
  hello_image_item_glibc_setlocale'23_nl_category_postload;
  hello_image_item_glibc_setlocale'23str'2e234;
  hello_image_item_setlocale;
  hello_image_item__nl_C_locobj;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_mmap_threshold;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_mmaps_max;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_top_pad;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_perturb_byte;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_trim_threshold;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_arena_max;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_arena_test;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_tcache_max;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_tcache_count;
  IFunc hello_image_fn_glibc_malloc'23_dl_tunable_set_hugetlb;
  IFunc hello_image_fn___ptmalloc_init;
  IFunc hello_image_fn_glibc_malloc'23__libc_malloc2;
  IFunc hello_image_fn___GI___libc_malloc;
  IFunc hello_image_fn___GI___libc_free;
  IFunc hello_image_fn___GI___libc_realloc;
  IFunc hello_image_fn___libc_calloc;
  IFunc hello_image_fn_glibc_malloc'23malloc_printerr;
  hello_image_item_malloc;
  hello_image_item_realloc;
  hello_image_item_free;
  hello_image_item_calloc;
  hello_image_item_glibc_malloc'23__always_fail_morecore;
  hello_image_item_glibc_malloc'23__tcache_dummy;
  hello_image_item_glibc_malloc'23main_arena;
  hello_image_item_glibc_malloc'23mp_;
  hello_image_item_glibc_malloc'23perturb_byte;
  hello_image_item_tcache;
  hello_image_item_glibc_malloc'23tcache_key;
  hello_image_item_thread_arena;
  hello_image_item_glibc_malloc'23str'2e407;
  hello_image_item_glibc_malloc'23str'2e408;
  hello_image_item_glibc_malloc'23str'2e421;
  IFunc hello_image_fn___GI__obstack_newchunk;
  IFunc hello_image_fn_glibc_obstack'23print_and_abort].

Lemma hello_image_items_15_zero : zero_nonneg hello_image_items_15 = true.
Proof. reflexivity. Qed.
