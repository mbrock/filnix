(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_iconv_gconv_simple_os Unit_iconv_gconv_trans_os Unit_intl_dcgettext_os Unit_intl_dcigettext_os Unit_intl_explodename_os Unit_intl_finddomain_os Unit_intl_l10nflist_os.
From Glibc Require Import Unit_intl_loadmsgcat_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_06 : module :=
  [Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e288;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e289;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e290;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e291;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e292;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e293;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e294;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e295;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e297;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e300;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e304;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e306;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e309;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e315;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e316;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e317;
  Unit_iconv_gconv_simple_os.item_glibc_gconv_simple'23str'2e319;
  IFunc Unit_iconv_gconv_trans_os.fn___GI___gconv_transliterate;
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
  IFunc Unit_intl_explodename_os.fn__nl_explode_name;
  IFunc Unit_intl_finddomain_os.fn__nl_find_domain;
  Unit_intl_finddomain_os.item_glibc_finddomain'23_nl_find_domain'2elock'2e265;
  Unit_intl_finddomain_os.item_glibc_finddomain'23_nl_loaded_domains;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23argz_count__;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23argz_stringify__;
  IFunc Unit_intl_l10nflist_os.fn__nl_make_l10nflist;
  IFunc Unit_intl_l10nflist_os.fn__nl_normalize_codeset;
  IFunc Unit_intl_l10nflist_os.fn_glibc_l10nflist'23pop;
  Unit_intl_l10nflist_os.item_glibc_l10nflist'23str'2e130;
  IFunc Unit_intl_loadmsgcat_os.fn_glibc_loadmsgcat'23get_sysdep_segment_value;
  IFunc Unit_intl_loadmsgcat_os.fn__nl_load_domain;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23_nl_load_domain'2elock'2e289;
  Unit_intl_loadmsgcat_os.item__nl_msg_cat_cntr;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e264;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e265;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e266].

Lemma hello_image_linked_items_06_zero : zero_nonneg hello_image_linked_items_06 = true.
Proof. reflexivity. Qed.
