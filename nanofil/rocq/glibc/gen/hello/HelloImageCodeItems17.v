(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_nptl_libcZ2dcleanup_os Unit_nptl_lowlevellock_os Unit_nptl_pthread_once_os Unit_nptl_pthread_rwlock_init_os Unit_nptl_pthread_rwlock_rdlock_os Unit_nptl_pthread_rwlock_unlock_os Unit_nptl_pthread_rwlock_wrlock_os.
From Glibc Require Import Unit_nptl_pthread_setcancelstate_os Unit_nptl_unwind_os Unit_nss_hashZ2dstring_os Unit_posix__exit_os Unit_posix_environ_os Unit_posix_get_child_max_os Unit_posix_getopt_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_17 : module :=
  [IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_push_defer;
  IFunc Unit_nptl_libcZ2dcleanup_os.fn___GI___libc_cleanup_pop_restore;
  IFunc Unit_nptl_lowlevellock_os.fn___GI___lll_lock_wait_private;
  IFunc Unit_nptl_lowlevellock_os.fn___GI___lll_lock_wake_private;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23clear_once_control;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23__pthread_once_slow;
  IFunc Unit_nptl_pthread_once_os.fn____pthread_once;
  IFunc Unit_nptl_pthread_once_os.fn_glibc_pthread_once'23__pthread_cleanup_combined_routine_voidptr;
  Unit_nptl_pthread_once_os.item___fork_generation;
  Unit_nptl_pthread_once_os.item___GI___pthread_once;
  IFunc Unit_nptl_pthread_rwlock_init_os.fn____pthread_rwlock_init;
  Unit_nptl_pthread_rwlock_init_os.item_glibc_pthread_rwlock_init'23default_rwlockattr;
  Unit_nptl_pthread_rwlock_init_os.item___GI___pthread_rwlock_init;
  IFunc Unit_nptl_pthread_rwlock_rdlock_os.fn____pthread_rwlock_rdlock;
  Unit_nptl_pthread_rwlock_rdlock_os.item___GI___pthread_rwlock_rdlock;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e286;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e287;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e288;
  Unit_nptl_pthread_rwlock_rdlock_os.item_glibc_pthread_rwlock_rdlock'23str'2e289;
  IFunc Unit_nptl_pthread_rwlock_unlock_os.fn____pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item___GI___pthread_rwlock_unlock;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e286;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e287;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e288;
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e289;
  IFunc Unit_nptl_pthread_rwlock_wrlock_os.fn____pthread_rwlock_wrlock;
  Unit_nptl_pthread_rwlock_wrlock_os.item___GI___pthread_rwlock_wrlock;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e286;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e287;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e288;
  Unit_nptl_pthread_rwlock_wrlock_os.item_glibc_pthread_rwlock_wrlock'23str'2e289;
  IFunc Unit_nptl_pthread_setcancelstate_os.fn___GI___pthread_setcancelstate;
  IFunc Unit_nptl_unwind_os.fn_glibc_unwind'23unwind_stop;
  IFunc Unit_nptl_unwind_os.fn_glibc_unwind'23unwind_cleanup;
  IFunc Unit_nptl_unwind_os.fn___GI___pthread_unwind;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e287;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e288;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e289;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e290;
  Unit_nptl_unwind_os.item_glibc_unwind'23str'2e291;
  IFunc Unit_nss_hashZ2dstring_os.fn___hash_string;
  IFunc Unit_posix__exit_os.fn___GI__exit;
  Unit_posix__exit_os.item__exit;
  Unit_posix_environ_os.item___environ;
  Unit_posix_environ_os.item___environ_counter;
  IFunc Unit_posix_get_child_max_os.fn___get_child_max;
  IFunc Unit_posix_getopt_os.fn_glibc_getopt'23process_long_option;
  IFunc Unit_posix_getopt_os.fn__getopt_internal_r;
  IFunc Unit_posix_getopt_os.fn__getopt_internal;
  Unit_posix_getopt_os.item_glibc_getopt'23getopt_data;
  Unit_posix_getopt_os.item_optarg;
  Unit_posix_getopt_os.item_opterr;
  Unit_posix_getopt_os.item_optind;
  Unit_posix_getopt_os.item_optopt;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e138;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e139;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e140;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e141;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e142;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e143;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e144;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e145;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e146;
  Unit_posix_getopt_os.item_glibc_getopt'23str'2e147].

Lemma hello_image_linked_items_17_zero : zero_nonneg hello_image_linked_items_17 = true.
Proof. reflexivity. Qed.
