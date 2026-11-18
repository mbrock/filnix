(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedAL HelloImageTypedCL HelloImageTypedGE01 HelloImageTypedNL04 HelloImageTypedObjects02 HelloImageTypedRE.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_07 : module :=
  [hello_image_item_glibc_loadmsgcat'23str'2e267;
  hello_image_item_glibc_loadmsgcat'23str'2e268;
  hello_image_item_glibc_loadmsgcat'23str'2e269;
  hello_image_item_glibc_loadmsgcat'23str'2e270;
  hello_image_item_glibc_loadmsgcat'23str'2e271;
  hello_image_item_glibc_loadmsgcat'23str'2e272;
  hello_image_item_glibc_loadmsgcat'23str'2e273;
  hello_image_item_glibc_loadmsgcat'23str'2e274;
  hello_image_item_glibc_loadmsgcat'23str'2e275;
  hello_image_item_glibc_loadmsgcat'23str'2e276;
  hello_image_item_glibc_loadmsgcat'23str'2e277;
  hello_image_item_glibc_loadmsgcat'23str'2e278;
  hello_image_item_glibc_loadmsgcat'23str'2e279;
  hello_image_item_glibc_loadmsgcat'23str'2e280;
  hello_image_item_glibc_loadmsgcat'23str'2e281;
  hello_image_item_glibc_loadmsgcat'23str'2e282;
  hello_image_item_glibc_loadmsgcat'23str'2e283;
  hello_image_item_glibc_loadmsgcat'23str'2e284;
  hello_image_item_glibc_loadmsgcat'23str'2e285;
  hello_image_item_glibc_loadmsgcat'23str'2e286;
  hello_image_item_glibc_loadmsgcat'23str'2e287;
  hello_image_item_glibc_loadmsgcat'23str'2e288;
  hello_image_item_glibc_loadmsgcat'23str'2e293;
  IFunc hello_image_fn__nl_expand_alias;
  IFunc hello_image_fn_glibc_localealias'23read_alias_file;
  IFunc hello_image_fn_glibc_localealias'23alias_compare;
  hello_image_item_glibc_localealias'23_nl_expand_alias'2elocale_alias_path'2e266;
  hello_image_item_glibc_localealias'23lock;
  hello_image_item_glibc_localealias'23map;
  hello_image_item_glibc_localealias'23maxmap;
  hello_image_item_glibc_localealias'23nmap;
  hello_image_item_glibc_localealias'23read_alias_file'2ealiasfile'2e268;
  hello_image_item_glibc_localealias'23string_space;
  hello_image_item_glibc_localealias'23string_space_act;
  hello_image_item_glibc_localealias'23string_space_max;
  hello_image_item_glibc_localealias'23str'2e267;
  hello_image_item_glibc_localealias'23str'2e269;
  IFunc hello_image_fn___gettext_extract_plural;
  hello_image_item___gettext_germanic_plural;
  hello_image_item_glibc_plural_exp'23plone;
  hello_image_item_glibc_plural_exp'23plvar;
  hello_image_item_glibc_plural_exp'23str'2e134;
  hello_image_item_glibc_plural_exp'23str'2e135;
  IFunc hello_image_fn___gettextparse;
  IFunc hello_image_fn___gettext_free_exp;
  hello_image_item_glibc_plural'23__gettextparse'2eyyval_default'2e125;
  hello_image_item_glibc_plural'23yycheck;
  hello_image_item_glibc_plural'23yydefact;
  hello_image_item_glibc_plural'23yydefgoto;
  hello_image_item_glibc_plural'23yypact;
  hello_image_item_glibc_plural'23yypgoto;
  hello_image_item_glibc_plural'23yyr1;
  hello_image_item_glibc_plural'23yyr2;
  hello_image_item_glibc_plural'23yystos;
  hello_image_item_glibc_plural'23yytable;
  hello_image_item_glibc_plural'23yytranslate;
  hello_image_item_glibc_plural'23str'2e124;
  hello_image_item_glibc_plural'23str'2e126;
  hello_image_item_glibc_plural'23str'2e127;
  hello_image_item_glibc_plural'23str'2e128;
  hello_image_item_glibc_plural'23str'2e129;
  hello_image_item_glibc_plural'23str'2e130;
  hello_image_item_glibc_plural'23str'2e131;
  IFunc hello_image_fn___GI___close_nocancel].

Lemma hello_image_items_07_zero : zero_nonneg hello_image_items_07 = true.
Proof. reflexivity. Qed.
