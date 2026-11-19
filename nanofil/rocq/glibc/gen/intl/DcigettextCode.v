(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_intl_dcigettext_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition dcigettext_module : module :=
  [(IData (a "dcigettext_roots") (LRo (a "export")) 8 [(Sym (a "__dcigettext") 0)]);
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
  Unit_intl_dcigettext_os.item_glibc_dcigettext'23str'2e288].
