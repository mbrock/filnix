(** This file contains checked IR from the linked image. The glibc code
    generator reproduces it from the capture. Do not edit. *)

From Stdlib Require Import String ZArith List Ascii.
From Nanofil Require Import Term Syntax.
From Glibc Require Import HelloImageEraseMem HelloImageTypedObjects03 HelloImageTypedObjects04 HelloImageTypedObjects05 HelloImageTypedObjects06 HelloImageTypedObjects07 HelloImageTypedObjects08.
Import ListNotations.
Open Scope string_scope.
Open Scope Z_scope.
Open Scope list_scope.
Local Abbreviation a := TAtom.
Local Notation "'t' s" := (Tmp (TAtom s)) (at level 10, s at next level).

Definition hello_image_items_12 : module :=
  [hello_image_item__nl_C_LC_CTYPE_toupper;
  hello_image_item__nl_C_LC_CTYPE_width;
  hello_image_item_glibc_C_ctype'23lc_ctype_data;
  hello_image_item_glibc_C_ctype'23translit_from_idx;
  hello_image_item_glibc_C_ctype'23translit_from_tbl;
  hello_image_item_glibc_C_ctype'23translit_to_idx;
  hello_image_item_glibc_C_ctype'23translit_to_tbl;
  hello_image_item_glibc_C_ctype'23str'2e258;
  hello_image_item_glibc_C_ctype'23str'2e259;
  hello_image_item_glibc_C_ctype'23str'2e260;
  hello_image_item_glibc_C_ctype'23str'2e261;
  hello_image_item_glibc_C_ctype'23str'2e262;
  hello_image_item_glibc_C_ctype'23str'2e263;
  hello_image_item_glibc_C_ctype'23str'2e264;
  hello_image_item_glibc_C_ctype'23str'2e265;
  hello_image_item_glibc_C_ctype'23str'2e266;
  hello_image_item_glibc_C_ctype'23str'2e267;
  hello_image_item_glibc_C_ctype'23str'2e268;
  hello_image_item_glibc_C_ctype'23str'2e269;
  hello_image_item_glibc_C_ctype'23str'2e270;
  hello_image_item_glibc_C_ctype'23str'2e271;
  hello_image_item_glibc_C_ctype'23str'2e272;
  hello_image_item_glibc_C_ctype'23str'2e273;
  hello_image_item_glibc_C_ctype'23str'2e274;
  hello_image_item_glibc_C_ctype'23str'2e275;
  hello_image_item_glibc_C_ctype'23str'2e276;
  hello_image_item_glibc_C_ctype'23str'2e277;
  hello_image_item_glibc_C_ctype'23str'2e278;
  hello_image_item_glibc_C_ctype'23str'2e279;
  hello_image_item_glibc_C_ctype'23str'2e280;
  hello_image_item__nl_C_LC_IDENTIFICATION;
  hello_image_item_glibc_C_identification'23str'2e40;
  hello_image_item_glibc_C_identification'23str'2e41;
  hello_image_item_glibc_C_identification'23str'2e42;
  hello_image_item_glibc_C_identification'23str'2e43;
  hello_image_item_glibc_C_identification'23str'2e44;
  hello_image_item_glibc_C_identification'23str'2e45;
  hello_image_item_glibc_C_identification'23str'2e46;
  hello_image_item_glibc_C_identification'23str'2e47;
  hello_image_item_glibc_C_identification'23str'2e48;
  hello_image_item_glibc_C_identification'23str'2e49;
  hello_image_item_glibc_C_identification'23str'2e50;
  hello_image_item_glibc_C_identification'23str'2e51;
  hello_image_item__nl_C_LC_MEASUREMENT;
  hello_image_item_glibc_C_measurement'23str'2e40;
  hello_image_item__nl_C_LC_MESSAGES;
  hello_image_item_glibc_C_messages'23str'2e40;
  hello_image_item_glibc_C_messages'23str'2e41;
  hello_image_item_glibc_C_messages'23str'2e42;
  hello_image_item__nl_C_LC_MONETARY;
  hello_image_item_glibc_C_monetary'23conversion_rate;
  hello_image_item_glibc_C_monetary'23not_available;
  hello_image_item_glibc_C_monetary'23str'2e40;
  hello_image_item_glibc_C_monetary'23str'2e41;
  hello_image_item__nl_C_LC_NAME;
  hello_image_item_glibc_C_name'23str'2e40;
  hello_image_item_glibc_C_name'23str'2e41;
  hello_image_item__nl_C_LC_NUMERIC;
  hello_image_item_glibc_C_numeric'23str'2e40;
  hello_image_item_glibc_C_numeric'23str'2e41;
  hello_image_item__nl_C_LC_PAPER;
  hello_image_item__nl_C_LC_TELEPHONE;
  hello_image_item_glibc_C_telephone'23str'2e40;
  hello_image_item_glibc_C_telephone'23str'2e41].

Lemma hello_image_items_12_zero : zero_nonneg hello_image_items_12 = true.
Proof. reflexivity. Qed.
