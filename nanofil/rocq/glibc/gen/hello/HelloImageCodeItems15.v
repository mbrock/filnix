(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_locale_loadlocale_os Unit_locale_localename_os Unit_locale_mb_cur_max_os Unit_locale_setlocale_os Unit_locale_xlocale_os Unit_malloc_malloc_os Unit_malloc_obstack_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_15 : module :=
  [Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_category_num_items;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_ADDRESS;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_COLLATE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_CTYPE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_IDENTIFICATION;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MEASUREMENT;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MESSAGES;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_MONETARY;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_NAME;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_NUMERIC;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_PAPER;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_TELEPHONE;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_type_LC_TIME;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23_nl_value_types;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e240;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e241;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e242;
  Unit_locale_loadlocale_os.item_glibc_loadlocale'23str'2e243;
  IFunc Unit_locale_localename_os.fn___current_locale_name;
  IFunc Unit_locale_mb_cur_max_os.fn___ctype_get_mb_cur_max;
  IFunc Unit_locale_setlocale_os.fn_glibc_setlocale'23new_composite_name;
  IFunc Unit_locale_setlocale_os.fn___GI_setlocale;
  Unit_locale_setlocale_os.item___libc_setlocale_lock;
  Unit_locale_setlocale_os.item__nl_category_name_idxs;
  Unit_locale_setlocale_os.item__nl_category_name_sizes;
  Unit_locale_setlocale_os.item__nl_category_names;
  Unit_locale_setlocale_os.item_glibc_setlocale'23_nl_category_postload;
  Unit_locale_setlocale_os.item_glibc_setlocale'23str'2e234;
  Unit_locale_setlocale_os.item_setlocale;
  Unit_locale_xlocale_os.item__nl_C_locobj;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_mmap_threshold;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_mmaps_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_top_pad;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_perturb_byte;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_trim_threshold;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_arena_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_arena_test;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_tcache_max;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_tcache_count;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23_dl_tunable_set_hugetlb;
  IFunc Unit_malloc_malloc_os.fn___ptmalloc_init;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23__libc_malloc2;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_malloc;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_free;
  IFunc Unit_malloc_malloc_os.fn___GI___libc_realloc;
  IFunc Unit_malloc_malloc_os.fn___libc_calloc;
  IFunc Unit_malloc_malloc_os.fn_glibc_malloc'23malloc_printerr;
  Unit_malloc_malloc_os.item_malloc;
  Unit_malloc_malloc_os.item_realloc;
  Unit_malloc_malloc_os.item_free;
  Unit_malloc_malloc_os.item_calloc;
  Unit_malloc_malloc_os.item_glibc_malloc'23__always_fail_morecore;
  Unit_malloc_malloc_os.item_glibc_malloc'23__tcache_dummy;
  Unit_malloc_malloc_os.item_glibc_malloc'23main_arena;
  Unit_malloc_malloc_os.item_glibc_malloc'23mp_;
  Unit_malloc_malloc_os.item_glibc_malloc'23perturb_byte;
  Unit_malloc_malloc_os.item_tcache;
  Unit_malloc_malloc_os.item_glibc_malloc'23tcache_key;
  Unit_malloc_malloc_os.item_thread_arena;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e407;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e408;
  Unit_malloc_malloc_os.item_glibc_malloc'23str'2e421;
  IFunc Unit_malloc_obstack_os.fn___GI__obstack_newchunk;
  IFunc Unit_malloc_obstack_os.fn_glibc_obstack'23print_and_abort].

Lemma hello_image_linked_items_15_zero : zero_nonneg hello_image_linked_items_15 = true.
Proof. reflexivity. Qed.
