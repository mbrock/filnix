(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAR HelloImageTypedBS HelloImageTypedDC HelloImageTypedGC13 HelloImageTypedGE01 HelloImageTypedGE02 HelloImageTypedNL01 HelloImageTypedNL02 HelloImageTypedObjects02 HelloImageTypedPL HelloImageTypedPO HelloImageTypedTR.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_06 : module :=
  [hello_image_item_glibc_gconv_simple'23str'2e288;
  hello_image_item_glibc_gconv_simple'23str'2e289;
  hello_image_item_glibc_gconv_simple'23str'2e290;
  hello_image_item_glibc_gconv_simple'23str'2e291;
  hello_image_item_glibc_gconv_simple'23str'2e292;
  hello_image_item_glibc_gconv_simple'23str'2e293;
  hello_image_item_glibc_gconv_simple'23str'2e294;
  hello_image_item_glibc_gconv_simple'23str'2e295;
  hello_image_item_glibc_gconv_simple'23str'2e297;
  hello_image_item_glibc_gconv_simple'23str'2e300;
  hello_image_item_glibc_gconv_simple'23str'2e304;
  hello_image_item_glibc_gconv_simple'23str'2e306;
  hello_image_item_glibc_gconv_simple'23str'2e309;
  hello_image_item_glibc_gconv_simple'23str'2e315;
  hello_image_item_glibc_gconv_simple'23str'2e316;
  hello_image_item_glibc_gconv_simple'23str'2e317;
  hello_image_item_glibc_gconv_simple'23str'2e319;
  IFunc hello_image_fn___GI___gconv_transliterate;
  IFunc hello_image_fn___GI___dcgettext;
  IFunc hello_image_fn_glibc_dcigettext'23transcmp;
  IFunc hello_image_fn_glibc_dcigettext'23plural_eval_recurse;
  IFunc hello_image_fn___dcigettext;
  IFunc hello_image_fn__nl_find_msg;
  IFunc hello_image_fn_glibc_dcigettext'23get_output_charset;
  IFunc hello_image_fn_glibc_dcigettext'23__bswap_32;
  hello_image_item__nl_current_default_domain;
  hello_image_item__nl_default_default_domain;
  hello_image_item___GI__nl_default_dirname;
  hello_image_item__nl_domain_bindings;
  hello_image_item_glibc_dcigettext'23_nl_find_msg'2efreemem'2e283;
  hello_image_item_glibc_dcigettext'23_nl_find_msg'2efreemem_size'2e284;
  hello_image_item_glibc_dcigettext'23_nl_find_msg'2elock'2e282;
  hello_image_item__nl_state_lock;
  hello_image_item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cache'2e286;
  hello_image_item_glibc_dcigettext'23get_output_charset'2eoutput_charset_cached'2e287;
  hello_image_item_glibc_dcigettext'23root;
  hello_image_item_glibc_dcigettext'23transmem_list;
  hello_image_item_glibc_dcigettext'23tree_lock;
  hello_image_item_glibc_dcigettext'23str'2e275;
  hello_image_item_glibc_dcigettext'23str'2e276;
  hello_image_item_glibc_dcigettext'23str'2e277;
  hello_image_item_glibc_dcigettext'23str'2e278;
  hello_image_item_glibc_dcigettext'23str'2e279;
  hello_image_item_glibc_dcigettext'23str'2e280;
  hello_image_item_glibc_dcigettext'23str'2e281;
  hello_image_item_glibc_dcigettext'23str'2e285;
  hello_image_item_glibc_dcigettext'23str'2e288;
  IFunc hello_image_fn__nl_explode_name;
  IFunc hello_image_fn__nl_find_domain;
  hello_image_item_glibc_finddomain'23_nl_find_domain'2elock'2e265;
  hello_image_item_glibc_finddomain'23_nl_loaded_domains;
  IFunc hello_image_fn_glibc_l10nflist'23argz_count__;
  IFunc hello_image_fn_glibc_l10nflist'23argz_stringify__;
  IFunc hello_image_fn__nl_make_l10nflist;
  IFunc hello_image_fn__nl_normalize_codeset;
  IFunc hello_image_fn_glibc_l10nflist'23pop;
  hello_image_item_glibc_l10nflist'23str'2e130;
  IFunc hello_image_fn_glibc_loadmsgcat'23get_sysdep_segment_value;
  IFunc hello_image_fn__nl_load_domain;
  hello_image_item_glibc_loadmsgcat'23_nl_load_domain'2elock'2e289;
  hello_image_item__nl_msg_cat_cntr;
  hello_image_item_glibc_loadmsgcat'23str'2e264;
  hello_image_item_glibc_loadmsgcat'23str'2e265;
  hello_image_item_glibc_loadmsgcat'23str'2e266].

Lemma hello_image_items_06_zero : zero_nonneg hello_image_items_06 = true.
Proof. reflexivity. Qed.
