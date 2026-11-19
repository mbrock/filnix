(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_stdlib_bsearch_os Unit_stdlib_cmp_os Unit_stdlib_cxa_atexit_os Unit_stdlib_cxa_thread_atexit_impl_os Unit_stdlib_exit_os Unit_stdlib_fpioconst_os Unit_stdlib_getenv_os.
From Glibc Require Import Unit_stdlib_grouping_os Unit_stdlib_lshift_os Unit_stdlib_mul_1_os Unit_stdlib_mul_n_os Unit_stdlib_mul_os Unit_stdlib_qsort_os Unit_stdlib_rshift_os Unit_stdlib_secureZ2dgetenv_os.
From Glibc Require Import Unit_stdlib_strtol_l_os Unit_stdlib_strtol_os Unit_stdlib_strtoul_l_os Unit_stdlib_strtoul_os Unit_stdlib_sub_n_os Unit_stdlib_submul_1_os Unit_string__strerror_os Unit_string_argzZ2daddsep_os.
From Glibc Require Import Unit_string_argzZ2dctsep_os Unit_string_argzZ2dnext_os Unit_string_cacheinfo_os Unit_string_memchr_os Unit_string_memcmp_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_24 : module :=
  [IFunc Unit_stdlib_bsearch_os.fn___GI_bsearch;
  IFunc Unit_stdlib_cmp_os.fn___mpn_cmp;
  IFunc Unit_stdlib_cxa_atexit_os.fn___internal_atexit;
  IFunc Unit_stdlib_cxa_atexit_os.fn___GI___cxa_atexit;
  IFunc Unit_stdlib_cxa_atexit_os.fn___new_exitfn;
  Unit_stdlib_cxa_atexit_os.item___exit_funcs;
  Unit_stdlib_cxa_atexit_os.item___exit_funcs_lock;
  Unit_stdlib_cxa_atexit_os.item___new_exitfn_called;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23initial;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e233;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e234;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e235;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e236;
  Unit_stdlib_cxa_atexit_os.item_glibc_cxa_atexit'23str'2e237;
  Unit_stdlib_cxa_atexit_os.item___cxa_atexit;
  IFunc Unit_stdlib_cxa_thread_atexit_impl_os.fn___GI___call_tls_dtors;
  IFunc Unit_stdlib_exit_os.fn___run_exit_handlers;
  IFunc Unit_stdlib_exit_os.fn___GI_exit;
  Unit_stdlib_exit_os.item___exit_funcs_done;
  Unit_stdlib_exit_os.item_glibc_exit'23__exit_lock;
  Unit_stdlib_exit_os.item_exit;
  Unit_stdlib_fpioconst_os.item___tens;
  Unit_stdlib_fpioconst_os.item__fpioconst_pow10;
  IFunc Unit_stdlib_getenv_os.fn___GI_getenv;
  IFunc Unit_stdlib_grouping_os.fn___correctly_grouped_prefixmb;
  IFunc Unit_stdlib_lshift_os.fn___mpn_lshift;
  IFunc Unit_stdlib_mul_os.fn___mpn_mul;
  IFunc Unit_stdlib_mul_os.fn_glibc_mul'23__mpn_add_1'2egnu_inline;
  IFunc Unit_stdlib_mul_1_os.fn___mpn_mul_1;
  IFunc Unit_stdlib_mul_1_os.fn_glibc_mul_1'23u128_lshift;
  IFunc Unit_stdlib_mul_n_os.fn___mpn_impn_mul_n_basecase;
  IFunc Unit_stdlib_mul_n_os.fn___mpn_impn_mul_n;
  IFunc Unit_stdlib_mul_n_os.fn_glibc_mul_n'23__mpn_add_1'2egnu_inline;
  IFunc Unit_stdlib_qsort_os.fn_glibc_qsort'23msort_with_tmp;
  IFunc Unit_stdlib_qsort_os.fn___GI___qsort_r;
  IFunc Unit_stdlib_qsort_os.fn___GI_qsort;
  IFunc Unit_stdlib_qsort_os.fn_glibc_qsort'23__pthread_cleanup_combined_routine_voidptr;
  IFunc Unit_stdlib_rshift_os.fn___mpn_rshift;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e62;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e63;
  Unit_stdlib_rshift_os.item_glibc_rshift'23str'2e64;
  IFunc Unit_stdlib_secureZ2dgetenv_os.fn___GI___libc_secure_getenv;
  Unit_stdlib_secureZ2dgetenv_os.item_secure_getenv;
  IFunc Unit_stdlib_strtol_os.fn___GI___isoc23_strtol;
  IFunc Unit_stdlib_strtol_l_os.fn___GI_____strtol_l_internal;
  Unit_stdlib_strtol_l_os.item___strtol_ul_max_tab;
  Unit_stdlib_strtol_l_os.item___strtol_ul_rem_tab;
  IFunc Unit_stdlib_strtoul_os.fn___GI___isoc23_strtoul;
  IFunc Unit_stdlib_strtoul_l_os.fn___GI_____strtoul_l_internal;
  IFunc Unit_stdlib_sub_n_os.fn___mpn_sub_n;
  IFunc Unit_stdlib_submul_1_os.fn___mpn_submul_1;
  IFunc Unit_stdlib_submul_1_os.fn_glibc_submul_1'23u128_lshift;
  IFunc Unit_string__strerror_os.fn___GI___strerror_r;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e136;
  Unit_string__strerror_os.item_glibc__strerror'23str'2e137;
  IFunc Unit_string_argzZ2daddsep_os.fn___argz_add_sep;
  IFunc Unit_string_argzZ2dctsep_os.fn___argz_create_sep;
  IFunc Unit_string_argzZ2dnext_os.fn___GI___argz_next;
  IFunc Unit_string_cacheinfo_os.fn___cache_sysconf;
  IFunc Unit_string_memchr_os.fn___memchr;
  Unit_string_memchr_os.item___GI_memchr;
  Unit_string_memchr_os.item_memchr;
  IFunc Unit_string_memcmp_os.fn___GI_memcmp;
  Unit_string_memcmp_os.item_memcmp].

Lemma hello_image_linked_items_24_zero : zero_nonneg hello_image_linked_items_24 = true.
Proof. reflexivity. Qed.
