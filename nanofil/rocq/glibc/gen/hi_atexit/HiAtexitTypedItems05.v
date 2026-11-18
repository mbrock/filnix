(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HiAtexitTypedCL HiAtexitTypedME HiAtexitTypedObjects01 HiAtexitTypedObjects02 HiAtexitTypedObjects03 HiAtexitTypedObjects04 HiAtexitTypedObjects05 HiAtexitTypedObjects06 HiAtexitTypedST.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_items_05 : module :=
  [hi_item___progname;
  hi_item___progname_full;
  hi_item_glibc_init_misc'23str'2e61;
  IFunc hi_fn___GI_strrchr;
  IFunc hi_fn___GI___clock_gettime;
  IFunc hi_fn___GI___memrchr;
  hi_item___libc_tsd_LOCALE;
  hi_item__nl_global_locale;
  hi_item__nl_C_LC_ADDRESS;
  hi_item__nl_C_LC_COLLATE;
  hi_item__nl_C_LC_IDENTIFICATION;
  hi_item__nl_C_LC_MEASUREMENT;
  hi_item__nl_C_LC_MESSAGES;
  hi_item__nl_C_LC_MONETARY;
  hi_item__nl_C_LC_NAME;
  hi_item__nl_C_LC_NUMERIC;
  hi_item__nl_C_LC_PAPER;
  hi_item__nl_C_LC_TELEPHONE;
  hi_item__nl_C_LC_TIME;
  hi_item__nl_C_LC_CTYPE;
  hi_item__nl_C_LC_CTYPE_class;
  hi_item__nl_C_LC_CTYPE_class32;
  hi_item__nl_C_LC_CTYPE_class_alnum;
  hi_item__nl_C_LC_CTYPE_class_alpha;
  hi_item__nl_C_LC_CTYPE_class_blank;
  hi_item__nl_C_LC_CTYPE_class_cntrl;
  hi_item__nl_C_LC_CTYPE_class_digit;
  hi_item__nl_C_LC_CTYPE_class_graph;
  hi_item__nl_C_LC_CTYPE_class_lower;
  hi_item__nl_C_LC_CTYPE_class_print;
  hi_item__nl_C_LC_CTYPE_class_punct;
  hi_item__nl_C_LC_CTYPE_class_space;
  hi_item__nl_C_LC_CTYPE_class_upper;
  hi_item__nl_C_LC_CTYPE_class_xdigit;
  hi_item__nl_C_LC_CTYPE_map_tolower;
  hi_item__nl_C_LC_CTYPE_map_toupper;
  hi_item__nl_C_LC_CTYPE_tolower;
  hi_item__nl_C_LC_CTYPE_toupper;
  hi_item__nl_C_LC_CTYPE_width;
  hi_item_glibc_C_ctype'23lc_ctype_data;
  hi_item_glibc_C_ctype'23translit_from_idx;
  hi_item_glibc_C_ctype'23translit_from_tbl;
  hi_item_glibc_C_ctype'23translit_to_idx;
  hi_item_glibc_C_ctype'23translit_to_tbl;
  hi_item_glibc_C_ctype'23str'2e258;
  hi_item_glibc_C_ctype'23str'2e259;
  hi_item_glibc_C_ctype'23str'2e260;
  hi_item_glibc_C_ctype'23str'2e261;
  hi_item_glibc_C_ctype'23str'2e262;
  hi_item_glibc_C_ctype'23str'2e263;
  hi_item_glibc_C_ctype'23str'2e264;
  hi_item_glibc_C_ctype'23str'2e265;
  hi_item_glibc_C_ctype'23str'2e266;
  hi_item_glibc_C_ctype'23str'2e267;
  hi_item_glibc_C_ctype'23str'2e268;
  hi_item_glibc_C_ctype'23str'2e269;
  hi_item_glibc_C_ctype'23str'2e270;
  hi_item_glibc_C_ctype'23str'2e271;
  hi_item_glibc_C_ctype'23str'2e272;
  hi_item_glibc_C_ctype'23str'2e273;
  hi_item_glibc_C_ctype'23str'2e274;
  hi_item_glibc_C_ctype'23str'2e275;
  hi_item_glibc_C_ctype'23str'2e276;
  hi_item_glibc_C_ctype'23str'2e277].
