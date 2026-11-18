(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCL HelloImageTypedDL HelloImageTypedGE06 HelloImageTypedIN HelloImageTypedLI02 HelloImageTypedNP HelloImageTypedObjects13 HelloImageTypedPT02 HelloImageTypedTL.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_27 : module :=
  [IFunc hello_image_fn_glibc_libc_start'23internal_signal_block_all;
  hello_image_item___x86_data_cache_size;
  hello_image_item___x86_data_cache_size_half;
  hello_image_item___x86_memset_non_temporal_threshold;
  hello_image_item___x86_rep_movsb_stop_threshold;
  hello_image_item___x86_rep_movsb_threshold;
  hello_image_item___x86_rep_stosb_threshold;
  hello_image_item___x86_shared_cache_size;
  hello_image_item___x86_shared_cache_size_half;
  hello_image_item___x86_shared_non_temporal_threshold;
  hello_image_item___x86_string_control;
  hello_image_item__dl_x86_features_tlsdesc_state_size;
  hello_image_item_glibc_libc_start'23intel_02_known;
  hello_image_item_glibc_libc_start'23sigall_set;
  hello_image_item_glibc_libc_start'23str'2e301;
  hello_image_item_glibc_libc_start'23str'2e302;
  hello_image_item_glibc_libc_start'23str'2e303;
  hello_image_item_glibc_libc_start'23str'2e304;
  hello_image_item_glibc_libc_start'23str'2e319;
  hello_image_item_glibc_libc_start'23str'2e320;
  hello_image_item_glibc_libc_start'23str'2e321;
  hello_image_item_glibc_libc_start'23str'2e322;
  hello_image_item_glibc_libc_start'23str'2e323;
  hello_image_item_glibc_libc_start'23str'2e324;
  hello_image_item_glibc_libc_start'23str'2e325;
  hello_image_item_glibc_libc_start'23str'2e326;
  hello_image_item_glibc_libc_start'23str'2e327;
  hello_image_item___pthread_initialize_minimal;
  IFunc hello_image_fn___libc_setup_tls;
  IFunc hello_image_fn___libc_early_init;
  hello_image_item___libc_initial;
  IFunc hello_image_fn___tls_init_tp;
  hello_image_item___nptl_initial_report_events;
  hello_image_item___GI___default_pthread_attr;
  IFunc hello_image_fn___GI___nptl_deallocate_tsd;
  hello_image_item___GI___nptl_nthreads;
  IFunc hello_image_fn_glibc_pthread_mutex_conf'23_dl_tunable_set_mutex_spin_count;
  IFunc hello_image_fn___pthread_tunables_init;
  hello_image_item___GI___mutex_aconf;
  IFunc hello_image_fn___getrandom_early_init;
  hello_image_item___libc_dlerror_result_string;
  IFunc hello_image_fn_glibc_init_first'23_init_first;
  hello_image_item___libc_argc;
  hello_image_item___libc_argv;
  hello_image_item___nanofil_ctor__init_first;
  IFunc hello_image_fn___GI___clock_gettime].

Lemma hello_image_items_27_zero : zero_nonneg hello_image_items_27 = true.
Proof. reflexivity. Qed.
