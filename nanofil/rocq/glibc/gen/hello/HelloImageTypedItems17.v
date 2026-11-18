(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedCL HelloImageTypedEX HelloImageTypedGE04 HelloImageTypedGE05 HelloImageTypedHA01 HelloImageTypedLI01 HelloImageTypedLL HelloImageTypedObjects09 HelloImageTypedPR01 HelloImageTypedPT01 HelloImageTypedPT02 HelloImageTypedUN.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_17 : module :=
  [IFunc hello_image_fn___GI___libc_cleanup_push_defer;
  IFunc hello_image_fn___GI___libc_cleanup_pop_restore;
  IFunc hello_image_fn___GI___lll_lock_wait_private;
  IFunc hello_image_fn___GI___lll_lock_wake_private;
  IFunc hello_image_fn_glibc_pthread_once'23clear_once_control;
  IFunc hello_image_fn_glibc_pthread_once'23__pthread_once_slow;
  IFunc hello_image_fn____pthread_once;
  IFunc hello_image_fn_glibc_pthread_once'23__pthread_cleanup_combined_routine_voidptr;
  hello_image_item___fork_generation;
  hello_image_item___GI___pthread_once;
  IFunc hello_image_fn____pthread_rwlock_init;
  hello_image_item_glibc_pthread_rwlock_init'23default_rwlockattr;
  hello_image_item___GI___pthread_rwlock_init;
  IFunc hello_image_fn____pthread_rwlock_rdlock;
  hello_image_item___GI___pthread_rwlock_rdlock;
  hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e286;
  hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e287;
  hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e288;
  hello_image_item_glibc_pthread_rwlock_rdlock'23str'2e289;
  IFunc hello_image_fn____pthread_rwlock_unlock;
  hello_image_item___GI___pthread_rwlock_unlock;
  hello_image_item_glibc_pthread_rwlock_unlock'23str'2e286;
  hello_image_item_glibc_pthread_rwlock_unlock'23str'2e287;
  hello_image_item_glibc_pthread_rwlock_unlock'23str'2e288;
  hello_image_item_glibc_pthread_rwlock_unlock'23str'2e289;
  IFunc hello_image_fn____pthread_rwlock_wrlock;
  hello_image_item___GI___pthread_rwlock_wrlock;
  hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e286;
  hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e287;
  hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e288;
  hello_image_item_glibc_pthread_rwlock_wrlock'23str'2e289;
  IFunc hello_image_fn___GI___pthread_setcancelstate;
  IFunc hello_image_fn_glibc_unwind'23unwind_stop;
  IFunc hello_image_fn_glibc_unwind'23unwind_cleanup;
  IFunc hello_image_fn___GI___pthread_unwind;
  hello_image_item_glibc_unwind'23str'2e287;
  hello_image_item_glibc_unwind'23str'2e288;
  hello_image_item_glibc_unwind'23str'2e289;
  hello_image_item_glibc_unwind'23str'2e290;
  hello_image_item_glibc_unwind'23str'2e291;
  IFunc hello_image_fn___hash_string;
  IFunc hello_image_fn___GI__exit;
  hello_image_item__exit;
  hello_image_item___environ;
  hello_image_item___environ_counter;
  IFunc hello_image_fn___get_child_max;
  IFunc hello_image_fn_glibc_getopt'23process_long_option;
  IFunc hello_image_fn__getopt_internal_r;
  IFunc hello_image_fn__getopt_internal;
  hello_image_item_glibc_getopt'23getopt_data;
  hello_image_item_optarg;
  hello_image_item_opterr;
  hello_image_item_optind;
  hello_image_item_optopt;
  hello_image_item_glibc_getopt'23str'2e138;
  hello_image_item_glibc_getopt'23str'2e139;
  hello_image_item_glibc_getopt'23str'2e140;
  hello_image_item_glibc_getopt'23str'2e141;
  hello_image_item_glibc_getopt'23str'2e142;
  hello_image_item_glibc_getopt'23str'2e143;
  hello_image_item_glibc_getopt'23str'2e144;
  hello_image_item_glibc_getopt'23str'2e145;
  hello_image_item_glibc_getopt'23str'2e146;
  hello_image_item_glibc_getopt'23str'2e147].

Lemma hello_image_items_17_zero : zero_nonneg hello_image_items_17 = true.
Proof. reflexivity. Qed.
