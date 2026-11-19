(** This module assembles the selected IR items in link order.
    The glibc code generator reproduces this file. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem Unit_locale_CZ2dctype_os Unit_locale_CZ2didentification_os Unit_locale_CZ2dmeasurement_os Unit_locale_CZ2dmessages_os Unit_locale_CZ2dmonetary_os Unit_locale_CZ2dname_os Unit_locale_CZ2dnumeric_os.
From Glibc Require Import Unit_locale_CZ2dpaper_os Unit_locale_CZ2dtelephone_os.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_linked_items_12 : module :=
  [Unit_locale_CZ2dctype_os.item__nl_C_LC_CTYPE_toupper;
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
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e277;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e278;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e279;
  Unit_locale_CZ2dctype_os.item_glibc_C_ctype'23str'2e280;
  Unit_locale_CZ2didentification_os.item__nl_C_LC_IDENTIFICATION;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e40;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e41;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e42;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e43;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e44;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e45;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e46;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e47;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e48;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e49;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e50;
  Unit_locale_CZ2didentification_os.item_glibc_C_identification'23str'2e51;
  Unit_locale_CZ2dmeasurement_os.item__nl_C_LC_MEASUREMENT;
  Unit_locale_CZ2dmeasurement_os.item_glibc_C_measurement'23str'2e40;
  Unit_locale_CZ2dmessages_os.item__nl_C_LC_MESSAGES;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e40;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e41;
  Unit_locale_CZ2dmessages_os.item_glibc_C_messages'23str'2e42;
  Unit_locale_CZ2dmonetary_os.item__nl_C_LC_MONETARY;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23conversion_rate;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23not_available;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23str'2e40;
  Unit_locale_CZ2dmonetary_os.item_glibc_C_monetary'23str'2e41;
  Unit_locale_CZ2dname_os.item__nl_C_LC_NAME;
  Unit_locale_CZ2dname_os.item_glibc_C_name'23str'2e40;
  Unit_locale_CZ2dname_os.item_glibc_C_name'23str'2e41;
  Unit_locale_CZ2dnumeric_os.item__nl_C_LC_NUMERIC;
  Unit_locale_CZ2dnumeric_os.item_glibc_C_numeric'23str'2e40;
  Unit_locale_CZ2dnumeric_os.item_glibc_C_numeric'23str'2e41;
  Unit_locale_CZ2dpaper_os.item__nl_C_LC_PAPER;
  Unit_locale_CZ2dtelephone_os.item__nl_C_LC_TELEPHONE;
  Unit_locale_CZ2dtelephone_os.item_glibc_C_telephone'23str'2e40;
  Unit_locale_CZ2dtelephone_os.item_glibc_C_telephone'23str'2e41].

Lemma hello_image_linked_items_12_zero : zero_nonneg hello_image_linked_items_12 = true.
Proof. reflexivity. Qed.
