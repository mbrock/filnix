(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_locale_localename_os Unit_misc_tsearch_os Unit_nptl_pthread_rwlock_rdlock_os Unit_nptl_pthread_rwlock_unlock_os Unit_string_memcpy_os Unit_string_mempcpy_os.
From Glibc Require Import Unit_string_stpcpy_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition gettextlink_module : module :=
  [(IData (a "gettextlink_roots") (LRo (a "export")) 8 [(Sym (a "__GI___dcgettext") 0)]);
  IFunc Unit_intl_dcgettext_os.fn___GI___dcgettext;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23transcmp;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23plural_eval_recurse;
  IFunc Unit_intl_dcigettext_os.fn___dcigettext;
  IFunc Unit_intl_dcigettext_os.fn__nl_find_msg;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23get_output_charset;
  IFunc Unit_intl_dcigettext_os.fn_glibc_dcigettext'23__bswap_32;
  Unit_intl_dcigettext_os.item__nl_current_default_domain;
  Unit_intl_dcigettext_os.item__nl_default_default_domain;
  Unit_intl_dcigettext_os.item___GI__nl_default_dirname;
  Unit_intl_dcigettext_os.item__nl_domain_bindings;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2efreemem'2e283;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2efreemem_size'2e284;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23_nl_find_msg'2elock'2e282;
  Unit_intl_dcigettext_os.item__nl_state_lock;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cache'2e286;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cached'2e287;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23root;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23transmem_list;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23tree_lock;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e275;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e276;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e277;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e278;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e279;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e280;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e281;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e285;
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e288;
  IFunc Unit_string_stpcpy_os.fn___GI___stpcpy;
  Unit_string_stpcpy_os.item___GI_stpcpy;
  IFunc Unit_string_mempcpy_os.fn___GI___mempcpy;
  Unit_string_mempcpy_os.item___GI_mempcpy;
  IFunc Unit_string_memcpy_os.fn___GI_memcpy;
  IFunc Unit_misc_tsearch_os.fn_glibc_tsearch'23maybe_split_for_insert;
  IFunc Unit_misc_tsearch_os.fn___GI___tsearch;
  IFunc Unit_misc_tsearch_os.fn___GI___tfind;
  IFunc Unit_locale_localename_os.fn___current_locale_name;
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
  Unit_nptl_pthread_rwlock_unlock_os.item_glibc_pthread_rwlock_unlock'23str'2e289].
