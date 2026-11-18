(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedER HelloImageTypedFU HelloImageTypedGE03 HelloImageTypedGE04 HelloImageTypedGN HelloImageTypedIN HelloImageTypedIS HelloImageTypedLI01 HelloImageTypedMA HelloImageTypedMM HelloImageTypedNE HelloImageTypedObjects09 HelloImageTypedPT01 HelloImageTypedSE HelloImageTypedTF HelloImageTypedTR HelloImageTypedTS HelloImageTypedTW.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_16 : module :=
  [hello_image_item_obstack_alloc_failed_handler;
  hello_image_item_obstack_exit_failure;
  hello_image_item_glibc_obstack'23str'2e148;
  hello_image_item_glibc_obstack'23str'2e149;
  IFunc hello_image_fn___GI___libc_scratch_buffer_grow_preserve;
  IFunc hello_image_fn___GI___libc_scratch_buffer_set_array_size;
  IFunc hello_image_fn___error_internal;
  IFunc hello_image_fn___error;
  hello_image_item_error;
  hello_image_item_error_message_count;
  hello_image_item_error_print_progname;
  hello_image_item_glibc_error'23str'2e252;
  hello_image_item_glibc_error'23str'2e253;
  hello_image_item_glibc_error'23str'2e254;
  hello_image_item_glibc_error'23str'2e255;
  IFunc hello_image_fn___getclktck;
  IFunc hello_image_fn___getdtablesize;
  IFunc hello_image_fn___GI___getpagesize;
  hello_image_item_glibc_getpagesize'23str'2e279;
  hello_image_item_glibc_getpagesize'23str'2e280;
  hello_image_item_glibc_getpagesize'23str'2e281;
  IFunc hello_image_fn_glibc_getsysstats'23next_line;
  IFunc hello_image_fn___GI___get_nprocs;
  IFunc hello_image_fn___GI___get_nprocs_conf;
  IFunc hello_image_fn___GI___get_phys_pages;
  IFunc hello_image_fn___GI___get_avphys_pages;
  hello_image_item_glibc_getsysstats'23str'2e311;
  hello_image_item_glibc_getsysstats'23str'2e312;
  hello_image_item_glibc_getsysstats'23str'2e313;
  hello_image_item_glibc_getsysstats'23str'2e314;
  hello_image_item_glibc_getsysstats'23str'2e315;
  hello_image_item_glibc_getsysstats'23str'2e316;
  hello_image_item_glibc_getsysstats'23str'2e317;
  IFunc hello_image_fn___init_misc;
  hello_image_item_program_invocation_name;
  hello_image_item_program_invocation_short_name;
  hello_image_item___progname;
  hello_image_item___progname_full;
  hello_image_item_glibc_init_misc'23str'2e61;
  IFunc hello_image_fn___gnu_dev_major;
  IFunc hello_image_fn___GI___mmap64;
  hello_image_item___GI___mmap;
  hello_image_item_glibc_mmap64'23str'2e279;
  hello_image_item___munmap;
  hello_image_item___GI___munmap;
  IFunc hello_image_fn___is_decorate_maps_enabled;
  IFunc hello_image_fn___set_vma_name;
  hello_image_item_glibc_setvmaname'23decorate_maps;
  hello_image_item_glibc_setvmaname'23str'2e282;
  hello_image_item___libc_single_threaded_internal;
  hello_image_item___libc_single_threaded;
  hello_image_item___sysinfo;
  IFunc hello_image_fn_glibc_tsearch'23maybe_split_for_insert;
  IFunc hello_image_fn___GI___tsearch;
  IFunc hello_image_fn___GI___tfind;
  IFunc hello_image_fn_glibc_tsearch'23trecurse_r;
  IFunc hello_image_fn___GI___twalk_r;
  IFunc hello_image_fn___GI___pthread_cleanup_push;
  IFunc hello_image_fn___GI___pthread_cleanup_pop;
  IFunc hello_image_fn___GI___futex_abstimed_wait64;
  hello_image_item_glibc_futex_internal'23str'2e244;
  hello_image_item_glibc_futex_internal'23str'2e245;
  hello_image_item_glibc_futex_internal'23str'2e246;
  hello_image_item_glibc_futex_internal'23str'2e247].

Lemma hello_image_items_16_zero : zero_nonneg hello_image_items_16 = true.
Proof. reflexivity. Qed.
