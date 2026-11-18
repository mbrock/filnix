(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAR HelloImageTypedBS HelloImageTypedCA HelloImageTypedCO HelloImageTypedCX HelloImageTypedEX HelloImageTypedGE03 HelloImageTypedIN HelloImageTypedIS HelloImageTypedLI HelloImageTypedME01 HelloImageTypedMP01 HelloImageTypedMS HelloImageTypedNE HelloImageTypedObjects11 HelloImageTypedObjects12 HelloImageTypedPT02 HelloImageTypedQS HelloImageTypedRU HelloImageTypedST01 HelloImageTypedU01.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_24 : module :=
  [IFunc hello_image_fn___GI_bsearch;
  IFunc hello_image_fn___mpn_cmp;
  IFunc hello_image_fn___internal_atexit;
  IFunc hello_image_fn___GI___cxa_atexit;
  IFunc hello_image_fn___new_exitfn;
  hello_image_item___exit_funcs;
  hello_image_item___exit_funcs_lock;
  hello_image_item___new_exitfn_called;
  hello_image_item_glibc_cxa_atexit'23initial;
  hello_image_item_glibc_cxa_atexit'23str'2e233;
  hello_image_item_glibc_cxa_atexit'23str'2e234;
  hello_image_item_glibc_cxa_atexit'23str'2e235;
  hello_image_item_glibc_cxa_atexit'23str'2e236;
  hello_image_item_glibc_cxa_atexit'23str'2e237;
  hello_image_item___cxa_atexit;
  IFunc hello_image_fn___GI___call_tls_dtors;
  IFunc hello_image_fn___run_exit_handlers;
  IFunc hello_image_fn___GI_exit;
  hello_image_item___exit_funcs_done;
  hello_image_item_glibc_exit'23__exit_lock;
  hello_image_item_exit;
  hello_image_item___tens;
  hello_image_item__fpioconst_pow10;
  IFunc hello_image_fn___GI_getenv;
  IFunc hello_image_fn___correctly_grouped_prefixmb;
  IFunc hello_image_fn___mpn_lshift;
  IFunc hello_image_fn___mpn_mul;
  IFunc hello_image_fn_glibc_mul'23__mpn_add_1'2egnu_inline;
  IFunc hello_image_fn___mpn_mul_1;
  IFunc hello_image_fn_glibc_mul_1'23u128_lshift;
  IFunc hello_image_fn___mpn_impn_mul_n_basecase;
  IFunc hello_image_fn___mpn_impn_mul_n;
  IFunc hello_image_fn_glibc_mul_n'23__mpn_add_1'2egnu_inline;
  IFunc hello_image_fn_glibc_qsort'23msort_with_tmp;
  IFunc hello_image_fn___GI___qsort_r;
  IFunc hello_image_fn___GI_qsort;
  IFunc hello_image_fn_glibc_qsort'23__pthread_cleanup_combined_routine_voidptr;
  IFunc hello_image_fn___mpn_rshift;
  hello_image_item_glibc_rshift'23str'2e62;
  hello_image_item_glibc_rshift'23str'2e63;
  hello_image_item_glibc_rshift'23str'2e64;
  IFunc hello_image_fn___GI___libc_secure_getenv;
  hello_image_item_secure_getenv;
  IFunc hello_image_fn___GI___isoc23_strtol;
  IFunc hello_image_fn___GI_____strtol_l_internal;
  hello_image_item___strtol_ul_max_tab;
  hello_image_item___strtol_ul_rem_tab;
  IFunc hello_image_fn___GI___isoc23_strtoul;
  IFunc hello_image_fn___GI_____strtoul_l_internal;
  IFunc hello_image_fn___mpn_sub_n;
  IFunc hello_image_fn___mpn_submul_1;
  IFunc hello_image_fn_glibc_submul_1'23u128_lshift;
  IFunc hello_image_fn___GI___strerror_r;
  hello_image_item_glibc__strerror'23str'2e136;
  hello_image_item_glibc__strerror'23str'2e137;
  IFunc hello_image_fn___argz_add_sep;
  IFunc hello_image_fn___argz_create_sep;
  IFunc hello_image_fn___GI___argz_next;
  IFunc hello_image_fn___cache_sysconf;
  IFunc hello_image_fn___memchr;
  hello_image_item___GI_memchr;
  hello_image_item_memchr;
  IFunc hello_image_fn___GI_memcmp;
  hello_image_item_memcmp].

Lemma hello_image_items_24_zero : zero_nonneg hello_image_items_24 = true.
Proof. reflexivity. Qed.
