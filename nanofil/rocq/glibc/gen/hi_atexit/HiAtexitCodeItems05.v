(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import Unit_locale_CZ2dctype_os Unit_locale_globalZ2dlocale_os Unit_misc_initZ2dmisc_os Unit_string_memrchr_os Unit_string_strrchr_os Unit_time_clock_gettime_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hi_linked_items_05 : module :=
  [Unit_misc_initZ2dmisc_os.item___progname;
  Unit_misc_initZ2dmisc_os.item___progname_full;
  Unit_misc_initZ2dmisc_os.item_glibc_init_misc'23str'2e61;
  IFunc Unit_string_strrchr_os.fn___GI_strrchr;
  IFunc Unit_time_clock_gettime_os.fn___GI___clock_gettime;
  IFunc Unit_string_memrchr_os.fn___GI___memrchr;
  Unit_locale_globalZ2dlocale_os.item___libc_tsd_LOCALE;
  Unit_locale_globalZ2dlocale_os.item__nl_global_locale;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_ADDRESS;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_COLLATE;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_IDENTIFICATION;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MEASUREMENT;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MESSAGES;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_MONETARY;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_NAME;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_NUMERIC;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_PAPER;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_TELEPHONE;
  Unit_locale_globalZ2dlocale_os.item__nl_C_LC_TIME;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class32;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alnum;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_alpha;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_blank;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_cntrl;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_digit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_graph;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_lower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_print;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_punct;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_space;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_upper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_class_xdigit;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_tolower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_map_toupper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_tolower;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_toupper;
  Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_width;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23lc_ctype_data;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_idx;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_from_tbl;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_idx;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23translit_to_tbl;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e258;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e259;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e260;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e261;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e262;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e263;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e264;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e265;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e266;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e267;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e268;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e269;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e270;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e271;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e272;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e273;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e274;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e275;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e276;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e277].
