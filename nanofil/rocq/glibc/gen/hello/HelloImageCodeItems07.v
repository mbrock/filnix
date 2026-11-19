(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_intl_loadmsgcat_os Unit_intl_localealias_os Unit_intl_pluralZ2dexp_os Unit_intl_plural_os Unit_io_close_nocancel_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_07 : module :=
  [Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e267;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e268;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e269;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e270;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e271;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e272;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e273;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e274;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e275;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e276;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e277;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e278;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e279;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e280;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e281;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e282;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e283;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e284;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e285;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e286;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e287;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e288;
  Unit_intl_loadmsgcat_os.item_glibc_loadmsgcat'23str'2e293;
  IFunc Unit_intl_localealias_os.fn__nl_expand_alias;
  IFunc Unit_intl_localealias_os.fn_glibc_localealias'23read_alias_file;
  IFunc Unit_intl_localealias_os.fn_glibc_localealias'23alias_compare;
  Unit_intl_localealias_os.item_glibc_localealias'23_nl_expand_alias'2elocale_alias_path'2e266;
  Unit_intl_localealias_os.item_glibc_localealias'23lock;
  Unit_intl_localealias_os.item_glibc_localealias'23map;
  Unit_intl_localealias_os.item_glibc_localealias'23maxmap;
  Unit_intl_localealias_os.item_glibc_localealias'23nmap;
  Unit_intl_localealias_os.item_glibc_localealias'23read_alias_file'2ealiasfile'2e268;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space_act;
  Unit_intl_localealias_os.item_glibc_localealias'23string_space_max;
  Unit_intl_localealias_os.item_glibc_localealias'23str'2e267;
  Unit_intl_localealias_os.item_glibc_localealias'23str'2e269;
  IFunc Unit_intl_pluralZ2dexp_os.fn___gettext_extract_plural;
  Unit_intl_pluralZ2dexp_os.item___gettext_germanic_plural;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23plone;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23plvar;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23str'2e134;
  Unit_intl_pluralZ2dexp_os.item_glibc_plural_exp'23str'2e135;
  IFunc Unit_intl_plural_os.fn___gettextparse;
  IFunc Unit_intl_plural_os.fn___gettext_free_exp;
  Unit_intl_plural_os.item_glibc_plural'23__gettextparse'2eyyval_default'2e125;
  Unit_intl_plural_os.item_glibc_plural'23yycheck;
  Unit_intl_plural_os.item_glibc_plural'23yydefact;
  Unit_intl_plural_os.item_glibc_plural'23yydefgoto;
  Unit_intl_plural_os.item_glibc_plural'23yypact;
  Unit_intl_plural_os.item_glibc_plural'23yypgoto;
  Unit_intl_plural_os.item_glibc_plural'23yyr1;
  Unit_intl_plural_os.item_glibc_plural'23yyr2;
  Unit_intl_plural_os.item_glibc_plural'23yystos;
  Unit_intl_plural_os.item_glibc_plural'23yytable;
  Unit_intl_plural_os.item_glibc_plural'23yytranslate;
  Unit_intl_plural_os.item_glibc_plural'23str'2e124;
  Unit_intl_plural_os.item_glibc_plural'23str'2e126;
  Unit_intl_plural_os.item_glibc_plural'23str'2e127;
  Unit_intl_plural_os.item_glibc_plural'23str'2e128;
  Unit_intl_plural_os.item_glibc_plural'23str'2e129;
  Unit_intl_plural_os.item_glibc_plural'23str'2e130;
  Unit_intl_plural_os.item_glibc_plural'23str'2e131;
  IFunc Unit_io_close_nocancel_os.fn___GI___close_nocancel].

Lemma hello_image_linked_items_07_zero : zero_nonneg hello_image_linked_items_07 = true.
Proof. reflexivity. Qed.
